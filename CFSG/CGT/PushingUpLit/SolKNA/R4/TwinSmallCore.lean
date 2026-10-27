module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocDefs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

@[expose] def TwinPair (F : Type) [Group F] : Prop :=
  ∃ (z : F) (X₁ X₂ : Subgroup F) (u₁ u₂ : F), orderOf z = 2 ∧ Group.IsSolvable ↥X₁ ∧
    Group.IsSolvable ↥X₂ ∧ CFSG.Open.IsSubnormal X₁ (Subgroup.centralizer ({z} : Set F)) ∧
    CFSG.Open.IsSubnormal X₂ (Subgroup.centralizer ({z} : Set F)) ∧ u₁ ∈ X₁ ∧ u₂ ∈ X₂ ∧
    orderOf u₁ = 4 ∧ orderOf u₂ = 4 ∧ u₁ * u₁ = z ∧ u₂ * u₂ = z ∧ u₂ ∉ Subgroup.zpowers u₁

@[expose] def TwinCyc4 (F : Type) [Group F] : Prop :=
  ∀ z : F, orderOf z = 2 → ∃ A : Subgroup F, IsCyclic ↥A ∧
    ∀ X : Subgroup F, Group.IsSolvable ↥X →
      CFSG.Open.IsSubnormal X (Subgroup.centralizer ({z} : Set F)) →
        ∀ u ∈ X, orderOf u = 4 → u ∈ A

theorem isSolvable_of_quotient_twoGroup {G : Type*} [Group G] [Finite G]
    (h : IsPGroup 2 (G ⧸ classicalInvolutionOddCore G)) : Group.IsSolvable G := by
  have hO : Group.IsSolvable (classicalInvolutionOddCore G) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card G)
  haveI : Group.IsNilpotent (G ⧸ classicalInvolutionOddCore G) := h.isNilpotent
  exact solvable_of_ker_le_range (classicalInvolutionOddCore G).subtype
    (QuotientGroup.mk' (classicalInvolutionOddCore G)) (by simp [QuotientGroup.ker_mk'])

theorem isSolvable_comap_subtype {Y : Type*} [Group Y] {T K : Subgroup Y}
    (hK : Group.IsSolvable ↥K) : Group.IsSolvable ↥(K.comap T.subtype) := by
  let f : ↥(K.comap T.subtype) →* ↥K :=
    { toFun := fun x => ⟨((x : ↥T) : Y), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  exact solvable_of_solvable_injective hf

theorem isSolvable_conjSub {Y : Type*} [Group Y] {K : Subgroup Y} (g : Y)
    (hK : Group.IsSolvable ↥K) : Group.IsSolvable ↥(conjSub g K) := by
  haveI := hK
  exact solvable_of_surjective (f := (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toMonoidHom)
    (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).surjective

open QuaternionGroup in
theorem quaternion_comm {r : ℕ} (hr : 4 ≤ r) :
    ∃ u v w : QuaternionGroup (2 ^ (r - 2)), orderOf u = 4 ∧ u = ⁅v, w⁆ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
  have hN : 2 ^ (k + 4 - 2) = 4 * 2 ^ k := by
    rw [show k + 4 - 2 = k + 2 by omega, pow_add]; ring
  have : NeZero (2 ^ (k + 4 - 2)) := ⟨by positivity⟩
  refine ⟨a ((2 ^ (k + 1) : ℕ) : ZMod (2 * 2 ^ (k + 4 - 2))), xa 0,
    a (-((2 ^ k : ℕ) : ZMod (2 * 2 ^ (k + 4 - 2)))), ?_, ?_⟩
  · rw [← a_one_pow, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero), orderOf_a_one]
    · rw [hN]
      have : 2 * (4 * 2 ^ k) = 2 ^ (k + 1) * 4 := by ring
      rw [this, Nat.mul_div_cancel_left _ (by positivity)]
    · rw [orderOf_a_one, hN]
      exact ⟨4, by ring⟩
  · set n : ℕ := 2 ^ (k + 4 - 2) with hn
    have h2n : (2 : ZMod (2 * n)) * (n : ZMod (2 * n)) = 0 := by
      exact_mod_cast ZMod.natCast_self (2 * n)
    have e1 : (xa 0 : QuaternionGroup n)⁻¹ = xa ((n : ZMod (2 * n)) + 0) := rfl
    have e2 : (a (-((2 ^ k : ℕ) : ZMod (2 * n))) : QuaternionGroup n)⁻¹ =
        a (-(-((2 ^ k : ℕ) : ZMod (2 * n)))) := rfl
    rw [commutatorElement_def, e1, e2, xa_mul_a, xa_mul_xa, a_mul_a]
    congr 1
    push_cast
    linear_combination (-1 : ZMod (2 * n)) * h2n

theorem not_twinPair_of_twinCyc4 {F : Type} [Group F] [Finite F] (hcyc : TwinCyc4 F) :
    ¬ TwinPair F := by
  rintro ⟨z, X₁, X₂, u₁, u₂, hz, hX₁, hX₂, hs₁, hs₂, hu₁, hu₂, ho₁, ho₂, -, -, hne⟩
  obtain ⟨A, hAcyc, hA⟩ := hcyc z hz
  have hu₁A : u₁ ∈ A := hA X₁ hX₁ hs₁ u₁ hu₁ ho₁
  have hu₂A : u₂ ∈ A := hA X₂ hX₂ hs₂ u₂ hu₂ ho₂
  have hp : ∀ u : F, orderOf u = 4 → IsPGroup 2 (Subgroup.zpowers u) := fun u hu => by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hu]
    norm_num
  obtain ⟨c, hc, hco⟩ := soc_exists_common_orderOf_four (A := A) (P₁ := Subgroup.zpowers u₁)
    (P₂ := Subgroup.zpowers u₂) hAcyc (Subgroup.zpowers_le.mpr hu₁A) (Subgroup.zpowers_le.mpr hu₂A)
    (hp _ ho₁) (hp _ ho₂) (Subgroup.isCyclic_zpowers _) (Subgroup.isCyclic_zpowers _)
    (by rw [Nat.card_zpowers, ho₁]) (by rw [Nat.card_zpowers, ho₂])
  obtain ⟨hc₁, hc₂⟩ := Subgroup.mem_inf.mp hc
  have hcard : ∀ u : F, orderOf u = 4 → c ∈ Subgroup.zpowers u → Subgroup.zpowers u =
      Subgroup.zpowers c := fun u hu hcu => by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcu) ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, hu, hco]
  apply hne
  rw [hcard u₁ ho₁ hc₁, ← hcard u₂ ho₂ hc₂]
  exact Subgroup.mem_zpowers u₂


theorem exists_twinPair_of_perp {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t)
    (hcomm : SocleComm2 ↥(genFittingFStar Y)) : TwinPair ↥(genFittingFStar Y) := by
  haveI hsimple := h.core.simple
  have hnab := h.core.nonab
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hnab
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  obtain ⟨K', hK'tw, hne⟩ := h.core.twin
  obtain ⟨hK'Ω, z', hz'0, hz'⟩ := hK'tw
  have hzt : t = z' := hz.eq hz'0
  rw [← hzt] at hz'
  obtain ⟨g, hg⟩ := hK'Ω
  set R₁ : Subgroup Y := (S : Subgroup R).map R.subtype with hR₁def
  have hR₁ : IsSylow2In R₁ (tightCore R) := h.core.datum.sylow_core
  obtain ⟨e⟩ := h.core.quat
  let e₁ : ↥R₁ ≃* QuaternionGroup (2 ^ (r - 2)) :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans e
  obtain ⟨u, v, w, hu4, huvw⟩ := quaternion_comm hr
  set u₁ : Y := ((e₁.symm u : ↥R₁) : Y) with hu₁def
  have hu₁R : u₁ ∈ R₁ := (e₁.symm u).2
  have hu₁4 : orderOf u₁ = 4 := by
    rw [hu₁def, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hu4
  have hu₁c : u₁ ∈ ⁅R₁, R₁⁆ := by
    have : u₁ = ⁅((e₁.symm v : ↥R₁) : Y), ((e₁.symm w : ↥R₁) : Y)⁆ := by
      rw [hu₁def, huvw, map_commutatorElement]; rfl
    rw [this]
    exact Subgroup.commutator_mem_commutator (e₁.symm v).2 (e₁.symm w).2
  have hu₁T : u₁ ∈ genFittingFStar Y :=
    hcomm Y (genFittingFStar Y) hTn ⟨MulEquiv.refl _⟩ hC R₁ hR₁.2.1 hu₁c
  have hu₁K : u₁ ∈ tightCore R := hR₁.1 hu₁R
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
  have hu₂K' : u₂ ∈ K' := hg ▸ conj_mem_conjSub hu₁K
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
  have hRsolv : Group.IsSolvable ↥R := isSolvable_of_quotient_twoGroup h.core.datum.twoGroup
  have hK₀solv : Group.IsSolvable ↥(tightCore R) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (tightCore_le R))
  have hK'solv : Group.IsSolvable ↥K' := hg ▸ isSolvable_conjSub g hK₀solv
  have hcz : (Subgroup.centralizer ({t} : Set Y)).comap T.subtype =
      Subgroup.centralizer ({z} : Set ↥T) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    constructor
    · intro hx; exact Subtype.ext hx
    · intro hx; exact congrArg Subtype.val hx
  have hsub₁ : CFSG.Open.IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen hΩ (CoreAssembly.mem_conjClass_self _) hz
  have hsub₂ : CFSG.Open.IsSubnormal K' (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen hΩ ⟨g, hg⟩ hz'
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
  have h4 := (hΩ.omega4 (tightCore R) (CoreAssembly.mem_conjClass_self _) K' ⟨g, hg⟩
    (Ne.symm hne)).1
  have h3 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
  omega

theorem false_of_twinCyc4 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t)
    (hcomm : SocleComm2 ↥(genFittingFStar Y)) (hcyc : TwinCyc4 ↥(genFittingFStar Y)) : False :=
  not_twinPair_of_twinCyc4 hcyc (exists_twinPair_of_perp hr h hcomm)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
