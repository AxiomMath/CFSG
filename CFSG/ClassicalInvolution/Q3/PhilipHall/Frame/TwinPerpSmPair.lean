module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall CFSG.ClassicalInvolution.Q3.TA3

set_option linter.unusedSectionVars false


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_u1_of_outTwoCyclic (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) (hO : Nobq.OutTwoCyclic ↥N) :
    t ∈ N ∧ ∃ s ∈ tightCore R, s ∈ N ∧ orderOf s = 4 := by
  classical
  have hD := h.core.datum
  obtain ⟨r, hr, ⟨e⟩⟩ := hD.quat
  have hOut : ∀ P : Subgroup (Y ⧸ N), IsPGroup 2 P → IsCyclic P :=
    Nobq.isCyclic_of_outTwoCyclic N hC hO
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hn2 : 2 ≤ 2 ^ (r - 2) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinv : ∀ u ∈ R, orderOf u = 2 → u = t :=
    fun u huR hu => Nobq.eq_of_orderOf_eq_two_of_datum S e hD.mem hD.order hD.cent huR hu
  set S0 : Subgroup Y := (S : Subgroup R).map R.subtype with hS0
  have hS0le : S0 ≤ R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS0p : IsPGroup 2 S0 := S.isPGroup'.map R.subtype
  have hnc : ∃ a b : S0, a * b ≠ b * a :=
    Nobq.exists_not_commute_of_mulEquiv_quaternionGroup hn2
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e)
  have hA : ∃ s ∈ S0, s ∈ N ∧ orderOf s = 4 := by
    by_contra hA
    have hcent : ∀ x : S0, (x : Y) ∈ N → x ∈ Subgroup.center S0 := by
      intro x hxF
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS0p x
      have hk' : orderOf (x : Y) = 2 ^ k := by rw [Subgroup.orderOf_coe]; exact hk
      have hk1 : k ≤ 1 := by
        by_contra hk2
        refine hA ⟨(x : Y) ^ (2 ^ (k - 2)), S0.pow_mem x.2 _, N.pow_mem hxF _, ?_⟩
        rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
          (by rw [hk']; exact pow_dvd_pow 2 (by omega)), hk', Nat.pow_div (by omega) (by norm_num)]
        have : k - (k - 2) = 2 := by omega
        norm_num [this]
      rw [Subgroup.mem_center_iff]
      intro y
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
      · have : (x : Y) = 1 := orderOf_eq_one_iff.mp (by simpa using hk')
        have hx1 : x = 1 := Subtype.ext this
        rw [hx1]
        simp
      · have hxt : (x : Y) = t := hinv _ (hS0le x.2) (by simpa using hk')
        apply Subtype.ext
        have := Subgroup.mem_centralizer_singleton_iff.mp (hD.cent (hS0le y.2))
        simp only [Subgroup.coe_mul, hxt]
        exact this
    have : IsCyclic (S0.map (QuotientGroup.mk' N)) := hOut _ (hS0p.map _)
    let f : S0 →* S0.map (QuotientGroup.mk' N) :=
      ((QuotientGroup.mk' N).comp S0.subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
    have hf : f.ker ≤ Subgroup.center S0 := by
      intro x hx
      apply hcent
      have h1 : (QuotientGroup.mk' N) (x : Y) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((f.isMulCommutative_of_isCyclic_of_ker_le_center hf).is_comm.comm a b)
  obtain ⟨s, hsS0, hsN, hs4⟩ := hA
  have hsK : s ∈ tightCore R := hD.sylow_core.1 hsS0
  have hsR : s ∈ R := hS0le hsS0
  have hs2 : orderOf (s ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs4]; norm_num), hs4]
  have hst : s ^ 2 = t := hinv _ (R.pow_mem hsR 2) hs2
  refine ⟨hst ▸ N.pow_mem hsN 2, s, hsK, hsN, hs4⟩

theorem exists_twinPair_of_u1 (h : PerpHypS n Y R S t) {u₁ : Y} (hu₁K : u₁ ∈ tightCore R)
    (hu₁T : u₁ ∈ genFittingFStar Y) (hu₁4 : orderOf u₁ = 4) :
    TwinPair ↥(genFittingFStar Y) := by
  haveI hsimple := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hz : IsUniqueInvolution (tightCore R) t := uniqueInv_core h
  obtain ⟨g, hgc, hne, ⟨hK'Ω⟩, hz'⟩ := exists_twin h
  have hg : conjSub g (tightCore R) = conjSub g (tightCore R) := rfl
  set K' : Subgroup Y := conjSub g (tightCore R) with hK'
  have hu₁sq : u₁ * u₁ = t := by
    have h1 : u₁ ^ 4 = 1 := by
      have := pow_orderOf_eq_one u₁
      rwa [hu₁4] at this
    have h2 : u₁ * u₁ ≠ 1 := fun h' => by
      have h3 : u₁ ^ 2 = 1 := by rw [pow_two]; exact h'
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hu₁4] at this
      omega
    have h3 : (u₁ * u₁) * (u₁ * u₁) = 1 := by
      calc (u₁ * u₁) * (u₁ * u₁) = u₁ ^ 4 := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := h1
    exact (hz.unique _ ((tightCore R).mul_mem hu₁K hu₁K) h3).resolve_left h2
  have htT : t ∈ genFittingFStar Y := hu₁sq ▸ (genFittingFStar Y).mul_mem hu₁T hu₁T
  set u₂ : Y := g * u₁ * g⁻¹ with hu₂def
  have hu₂K' : u₂ ∈ K' := conj_mem_conjSub hu₁K
  have hu₂T : u₂ ∈ genFittingFStar Y := hTn.conj_mem u₁ hu₁T g
  have hu₂4 : orderOf u₂ = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) u₁
    rw [MulAut.conj_apply] at this
    rw [hu₂def, this, hu₁4]
  have hu₂sq : u₂ * u₂ = t := by
    have h1 : u₂ ^ 4 = 1 := by
      have := pow_orderOf_eq_one u₂
      rwa [hu₂4] at this
    have h2 : u₂ * u₂ ≠ 1 := fun h' => by
      have h3 : u₂ ^ 2 = 1 := by rw [pow_two]; exact h'
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hu₂4] at this
      omega
    have h3 : (u₂ * u₂) * (u₂ * u₂) = 1 := by
      calc (u₂ * u₂) * (u₂ * u₂) = u₂ ^ 4 := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := h1
    exact (hz'.unique _ (K'.mul_mem hu₂K' hu₂K') h3).resolve_left h2
  set T : Subgroup Y := genFittingFStar Y with hTdef
  let z : ↥T := ⟨t, htT⟩
  have hz2 : orderOf z = 2 := by
    rw [Subgroup.orderOf_mk]; exact h.core.datum.order
  have hK₀solv : Group.IsSolvable ↥(tightCore R) := isSolvable_core h
  have hK'solv : Group.IsSolvable ↥K' := isSolvable_conjSub g hK₀solv
  have hcz : (Subgroup.centralizer ({t} : Set Y)).comap T.subtype =
      Subgroup.centralizer ({z} : Set ↥T) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    constructor
    · intro hx; exact Subtype.ext hx
    · intro hx; exact congrArg Subtype.val hx
  have hsub₁ : CFSG.Open.IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_core h
  have hsub₂ : CFSG.Open.IsSubnormal K' (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen hΩ ⟨g, rfl⟩ hz'
  have hsub₁' := hsub₁.comap T.subtype
  have hsub₂' := hsub₂.comap T.subtype
  rw [hcz] at hsub₁' hsub₂'
  refine ⟨z, (tightCore R).comap T.subtype, K'.comap T.subtype, ⟨u₁, hu₁T⟩, ⟨u₂, hu₂T⟩, hz2,
    isSolvable_comap_subtype hK₀solv, isSolvable_comap_subtype hK'solv, hsub₁', hsub₂', hu₁K, hu₂K',
    by rw [Subgroup.orderOf_mk]; exact hu₁4, by rw [Subgroup.orderOf_mk]; exact hu₂4,
    Subtype.ext hu₁sq, Subtype.ext hu₂sq, ?_⟩
  intro hmem
  have hu₂K : u₂ ∈ tightCore R := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have : u₂ = u₁ ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [this]
    exact zpow_mem hu₁K k
  have hcmem : u₂ ∈ tightCore R ⊓ K' := Subgroup.mem_inf.mpr ⟨hu₂K, hu₂K'⟩
  have hdvd : 2 ^ 2 ∣ Nat.card ↥(tightCore R ⊓ K') := by
    have := Subgroup.orderOf_dvd_natCard (tightCore R ⊓ K') hcmem
    rw [hu₂4] at this
    simpa using this
  have h4 := (hΩ.omega4 (tightCore R) (CoreAssembly.mem_conjClass_self _) K' ⟨g, rfl⟩
    (Ne.symm hne)).1
  have h3 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
  omega

theorem false_of_outTwoCyclic_of_noTwinPair (h : PerpHypS n Y R S t)
    (hO : Nobq.OutTwoCyclic ↥(genFittingFStar Y))
    (hno : ¬ TwinPair ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  obtain ⟨-, s, hsK, hsT, hs4⟩ := exists_u1_of_outTwoCyclic h hC hO
  exact hno (exists_twinPair_of_u1 h hsK hsT hs4)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
