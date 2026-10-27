module

public import CFSG.GH74.GLS.Stage2.Local.P27.P1Abs
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassS
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OneCls
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327Proof
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L4G

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Main
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem p1_exists_diag_L2 (hP : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂)
    (ht2 : t * t = 1) :
    ∃ (A : Subgroup (CentralizerBar z)) (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = q ∧ A ≤ CL z t ∧ (∀ c ∈ CL z t, ∀ a ∈ A, c * a * c⁻¹ ∈ A) ∧
      Nonempty (↥A ≃* IVK.L2 F) ∧
      (∀ B : Subgroup (CentralizerBar z), B ≤ CL z t → ⁅B, B⁆ = B → B ≤ A) ∧
      Nat.card ↥A * 2 = Nat.card ↥(CL z t) := by
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := exists_CL_iso hP hsw ht2
  let φ : ↥(CL z t) →* Multiplicative (ZMod 2) := (MonoidHom.snd _ _).comp e.toMonoidHom
  let K : Subgroup ↥(CL z t) := φ.ker
  let A : Subgroup (CentralizerBar z) := K.map (CL z t).subtype
  have hKn : K.Normal := φ.normal_ker
  have hAiso : Nonempty (↥A ≃* IVK.L2 F) := by
    let g : ↥K →* IVK.L2 F := ((MonoidHom.fst _ _).comp e.toMonoidHom).comp K.subtype
    have hginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      refine Prod.ext hxy ?_
      have hx : (e (x : ↥(CL z t))).2 = 1 := x.2
      have hy : (e (y : ↥(CL z t))).2 = 1 := y.2
      exact hx.trans hy.symm
    have hgsurj : Function.Surjective g := by
      intro a
      refine ⟨⟨e.symm (a, 1), ?_⟩, ?_⟩
      · show (e (e.symm (a, 1))).2 = 1
        simp
      · show (e (e.symm (a, 1))).1 = a
        simp
    exact ⟨(Subgroup.equivMapOfInjective K (CL z t).subtype (CL z t).subtype_injective).symm.trans
      (MulEquiv.ofBijective g ⟨hginj, hgsurj⟩)⟩
  have hAcard : Nat.card ↥A * 2 = Nat.card ↥(CL z t) := by
    obtain ⟨eA⟩ := hAiso
    have h1 : Nat.card ↥A = Nat.card (IVK.L2 F) := Nat.card_congr eA.toEquiv
    have h2 : Nat.card ↥(CL z t) = Nat.card (IVK.L2 F × Multiplicative (ZMod 2)) :=
      Nat.card_congr e.toEquiv
    have h3 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 2
    rw [h1, h2, Nat.card_prod, h3]
  refine ⟨A, F, iF, fF, hFq, Subgroup.map_subtype_le _, ?_, hAiso, ?_, hAcard⟩
  · intro c hc a ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact ⟨⟨c, hc⟩ * k * ⟨c, hc⟩⁻¹, hKn.conj_mem k hk ⟨c, hc⟩, rfl⟩
  · intro B hB hperf b hb
    have hperf' : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
    let ψ : ↥B →* Multiplicative (ZMod 2) := φ.comp (Subgroup.inclusion hB)
    have hψ : ψ = 1 := by
      ext x
      have : x ∈ commutator ↥B := by rw [hperf'.commutator_eq_top]; exact Subgroup.mem_top x
      exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker ψ this)
    exact ⟨⟨b, hB hb⟩, MonoidHom.mem_ker.2 (congrArg (fun f : ↥B →* Multiplicative (ZMod 2) => f ⟨b, hb⟩) hψ), rfl⟩

theorem p1_ringChar_ne_two_of_odd_card {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    ringChar F ≠ 2 := by
  intro h2
  have : CharP F 2 := by rw [← h2]; exact ringChar.charP F
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn] at h
  exact absurd h (by
    rw [Nat.not_odd_iff_even]
    exact (Nat.even_pow.2 ⟨by norm_num, by exact PNat.ne_zero n⟩))

theorem p1_even_card_L2 {F₀ : Type} [Field F₀] [Finite F₀]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F₀)) : 2 ∣ Nat.card (IVK.L2 F₀) := by
  have h1 : Nat.card (IVK.L2 F₀) = Nat.card (GorensteinWalter.PSL2 F₀) :=
    Nat.card_congr (IVK.L2.equivPSL F₀).toEquiv
  rw [h1, GorensteinWalter.psl2_card_formula F₀ hodd]
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hodd
  rw [hq]
  have hodd' : Odd (p ^ n) := hpodd.pow
  obtain ⟨k, hk⟩ := hodd'
  rw [hk]
  have : (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) / 2 = (2 * k + 1) * (2 * (k * (k + 1))) := by
    have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    rw [this]
    have : (2 * k + 1) * (4 * (k * (k + 1))) = 2 * ((2 * k + 1) * (2 * (k * (k + 1)))) := by ring
    rw [this]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [this]
  exact ⟨(2 * k + 1) * (k * (k + 1)), by ring⟩

theorem ixz_L2_ext (hz : IsCentralInvolution z) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ S) (htc : IsConj z t)
    (hsw : Swaps z t L₁ L₂) :
    (Ixz z (t * z) ≠ ⊥ ∧ IVK.IsL2 (↥(Ixz z (t * z)) ⧸ pPrimeCore 2 ↥(Ixz z (t * z)))
      (fun r => r = q)) ∧
    ∃ A : Subgroup (CentralizerBar z), barOf z (Ixz z (t * z)) = A ∧ A ≤ CL z t ∧
      Nat.card ↥A * 2 = Nat.card ↥(CL z t) ∧
      ∀ B : Subgroup (CentralizerBar z), B ≤ CL z t → ⁅B, B⁆ = B → B ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : S ≤ Cen z := by
    obtain ⟨Q, hQ⟩ := hS
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have htC : t ∈ Cen z := hSC ht
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have ht2 : t * t = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  set Y : Subgroup G := centralizer ({t * z, z} : Set G) with hY
  have hYC : Y ≤ Cen z := fun y hy =>
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact Subgroup.mem_centralizer_iff.1 hy z (by simp))
  have hYt : ∀ y ∈ Y, y * t = t * y := by
    intro y hy
    have h1 : t * z * y = y * (t * z) := Subgroup.mem_centralizer_iff.1 hy (t * z) (by simp)
    have h2 : z * y = y * z := Subgroup.mem_centralizer_iff.1 hy z (by simp)
    calc y * t = y * t * (z * z) := by rw [hzz, mul_one]
      _ = (y * (t * z)) * z := by group
      _ = (t * z * y) * z := by rw [h1]
      _ = t * (z * y) * z := by group
      _ = t * (y * z) * z := by rw [h2]
      _ = t * y * (z * z) := by group
      _ = t * y := by rw [hzz, mul_one]
  have hmemY : ∀ c : ↥(Cen z), c * (⟨t, htC⟩ : ↥(Cen z)) = ⟨t, htC⟩ * c → (c : G) ∈ Y := by
    intro c hc
    have hct : (c : G) * t = t * c := congrArg Subtype.val hc
    have hcz : z * (c : G) = c * z := Subgroup.mem_centralizer_iff.1 c.2 z (by simp)
    rw [hY, Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · calc (t * z) * c = t * (z * c) := by group
        _ = t * (c * z) := by rw [hcz]
        _ = (t * c) * z := by group
        _ = (c * t) * z := by rw [hct]
        _ = c * (t * z) := by group
    · exact hcz
  let ρX : ↥Y →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hYC)
  have hodd : ∀ x ∈ ρX.ker, Odd (orderOf x) := by
    intro x hx
    have h1 : Subgroup.inclusion hYC x ∈ (toBar z).ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)
    rw [ker_toBar] at h1
    have h2 : Odd (orderOf (Subgroup.inclusion hYC x)) := by
      have hd : orderOf (⟨Subgroup.inclusion hYC x, h1⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
          Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hd
      exact Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))) hd
    rwa [orderOf_injective (Subgroup.inclusion hYC) (Subgroup.inclusion_injective hYC)] at h2
  obtain ⟨A, F, iF, fF, hFq, hACL, hAnorm, hAiso, hAperf, hAcard⟩ := p1_exists_diag_L2 hP hsw ht2
  obtain ⟨eA⟩ := hAiso
  have h4 : 4 ≤ Nat.card F := by have := hP.gt3; omega
  obtain ⟨hL2s, hL2n⟩ := Stage1.Main.l2_simple_nonab h4
  have := hL2s
  have hAs : IsSimpleGroup ↥A := eA.isSimpleGroup
  have hAn : ∃ a b : ↥A, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hL2n
    exact ⟨eA.symm a, eA.symm b, fun h => hab (by simpa using congrArg eA h)⟩
  have hA2 : 2 ∣ Nat.card ↥A := by
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      LinearGroups.isOddPrimePower_card_of_ringChar_ne_two
        (p1_ringChar_ne_two_of_odd_card (by rw [hFq]; exact hP.odd))
    rw [Nat.card_congr eA.toEquiv]
    exact p1_even_card_L2 hodd
  set R0 : Subgroup ↥(Cen z) := pPrimeCore 2 ↥(Cen z) with hR0
  have hRodd : Odd (Nat.card R0) := by rw [hR0, ← ker_toBar z]; exact odd_card_ker_toBar z
  let t₀ : ↥(Cen z) := ⟨t, htC⟩
  have ht₀2 : t₀ ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using ht2)
  have hcentr := ComponentClassification.UnbalancingLocal.centralizer_mk_eq_map_of_odd R0 hRodd ht₀2
  have hρcent : ∀ x : ↥Y, toBar z t₀ * ρX x = ρX x * toBar z t₀ := by
    intro x
    show toBar z t₀ * toBar z (Subgroup.inclusion hYC x) = toBar z (Subgroup.inclusion hYC x) * toBar z t₀
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hYt x x.2).symm
  have hCL := CL_eq_centralizer (z := z) htC hP.prod.1
  have hAle : A ≤ ρX.range := by
    intro a ha
    have haCL : a ∈ CL z t := hACL ha
    rw [hCL] at haCL
    have hcent' : a ∈ centralizer ({QuotientGroup.mk' R0 t₀} : Set (↥(Cen z) ⧸ R0)) :=
      (Subgroup.mem_inf.1 haCL).1
    rw [hcentr] at hcent'
    obtain ⟨c, hc, hca⟩ := hcent'
    have hcY : (c : G) ∈ Y := hmemY c (Subgroup.mem_centralizer_singleton_iff.1 hc)
    exact ⟨⟨c, hcY⟩, hca⟩
  have hLnorm : (LBar z).Normal := Stage1.Thm6.Prod.LBar_isNormal z
  have hCLmem : ∀ x : ↥Y, ρX x ∈ LBar z → ρX x ∈ CL z t := by
    intro x hx
    rw [hCL]
    refine Subgroup.mem_inf.2 ⟨?_, by rw [hP.prod.1]; exact hx⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hρcent x).symm
  have hsub : (A.comap ρX).IsSubnormal := by
    have hle : A.comap ρX ≤ (LBar z).comap ρX := by
      intro x hx
      have h1 : ρX x ∈ CL z t := hACL hx
      rw [hCL, hP.prod.1] at h1
      exact (Subgroup.mem_inf.1 h1).2
    refine Subgroup.IsSubnormal.step _ _ hle (hLnorm.comap ρX).isSubnormal ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    have hconj : ∀ x ∈ (LBar z).comap ρX, ∀ a ∈ A.comap ρX, x * a * x⁻¹ ∈ A.comap ρX := by
      intro x hx a ha
      have hxCL : ρX x ∈ CL z t := hCLmem x hx
      have := hAnorm (ρX x) hxCL (ρX a) ha
      simpa using this
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => hconj x hx a ha
    · intro h
      have hx' : x⁻¹ ∈ (LBar z).comap ρX := ((LBar z).comap ρX).inv_mem hx
      have h2 := hconj x⁻¹ hx' _ h
      have h3 : x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a := by group
      rwa [h3] at h2
  have hperf : ∀ B : Subgroup ↥Y, ⁅B, B⁆ = B → B.map ρX ≤ A := by
    intro B hB
    let B' : Subgroup G := B.map Y.subtype
    have hB' : ⁅B', B'⁆ = B' := by
      show ⁅B.map Y.subtype, B.map Y.subtype⁆ = B.map Y.subtype
      rw [← Subgroup.map_commutator, hB]
    have hB'C : B' ≤ Cen z := fun g hg => by
      obtain ⟨b, -, rfl⟩ := hg
      exact hYC b.2
    have hB'LC : B' ≤ LC z :=
      IVK.Proofs2.Ivk93Adapt.perfect_le_LC z (perfInner_of_pair hP) hB'C (Subgroup.isPerfect_iff.mpr hB')
    have hBCL : B.map ρX ≤ CL z t := by
      rintro _ ⟨b, hb, rfl⟩
      apply hCLmem
      have hbLC : (b : G) ∈ LC z := hB'LC ⟨b, hb, rfl⟩
      exact ⟨⟨b, hYC b.2⟩, (Subgroup.mem_subgroupOf).2 hbLC, rfl⟩
    have hperfB : ⁅B.map ρX, B.map ρX⁆ = B.map ρX := by rw [← Subgroup.map_commutator, hB]
    exact hAperf _ hBCL hperfB
  obtain ⟨P, hPuniq, hPmap, ⟨e₂⟩⟩ :=
    unique_pComponent_of_simple_image ρX hodd A hAs hAn hA2 hAle hsub hperf
  have hI : Ixz z (t * z) = P.map Y.subtype := by
    show pLayerOf 2 Y = P.map Y.subtype
    unfold pLayerOf
    have hset : {L : Subgroup G | IsPCompIn 2 Y L} = {P.map Y.subtype} := by
      ext L
      simp only [Set.mem_singleton_iff]
      show IsPCompIn 2 Y L ↔ L = P.map Y.subtype
      constructor
      · rintro ⟨hLY, hLc⟩
        have := (hPuniq _).1 hLc
        rw [← Subgroup.map_subgroupOf_eq_of_le hLY, this]
      · rintro rfl
        refine ⟨Subgroup.map_subtype_le _, ?_⟩
        have h1 : (P.map Y.subtype).subgroupOf Y = P :=
          Subgroup.comap_map_eq_self_of_injective Y.subtype_injective P
        rw [h1]
        exact (hPuniq P).2 rfl
    rw [hset, sSup_singleton]
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at hPmap
    obtain ⟨a, b, hab⟩ := hAn
    have hA0 : ∀ x : CentralizerBar z, x ∈ A → x = 1 := fun x hx =>
      Subgroup.mem_bot.1 (hPmap ▸ hx)
    have h1 : (a : CentralizerBar z) = 1 := hA0 a a.2
    apply hab
    have h2 : a = 1 := Subtype.ext h1
    rw [h2, one_mul, mul_one]
  have hbarI : barOf z (Ixz z (t * z)) = A := by
    rw [hI, ← hPmap]
    unfold barOf
    have h1 : (P.map Y.subtype).subgroupOf (Cen z) = P.map (Subgroup.inclusion hYC) := by
      ext c
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyc⟩
        exact ⟨y, hy, Subtype.ext hyc⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [h1, Subgroup.map_map]
  refine ⟨?_, A, hbarI, hACL, hAcard, hAperf⟩
  rw [hI]
  refine ⟨fun h => hPne ((Subgroup.map_eq_bot_iff_of_injective P Y.subtype_injective).1 h), F, iF, fF, hFq, ?_⟩
  let eI : ↥P ≃* ↥(P.map Y.subtype) :=
    Subgroup.equivMapOfInjective P Y.subtype Y.subtype_injective
  have hmap : (pPrimeCore 2 ↥P).map eI.toMonoidHom = pPrimeCore 2 ↥(P.map Y.subtype) :=
    pPrimeCore_map_iso 2 eI
  exact ⟨(QuotientGroup.congr (pPrimeCore 2 ↥P) (pPrimeCore 2 ↥(P.map Y.subtype)) eI hmap).symm.trans
    (e₂.trans eA)⟩

theorem ixz_L2 (hz : IsCentralInvolution z) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ S) (htc : IsConj z t)
    (hsw : Swaps z t L₁ L₂) :
    Ixz z (t * z) ≠ ⊥ ∧ IVK.IsL2 (↥(Ixz z (t * z)) ⧸ pPrimeCore 2 ↥(Ixz z (t * z)))
      (fun r => r = q) :=
  (ixz_L2_ext hz hS hP ht htc hsw).1

omit [Finite G] in
theorem p1_pLayerOf_le (H : Subgroup G) : pLayerOf 2 H ≤ H := sSup_le fun _ hL => hL.1

theorem p1_pLayerOf_normal (H : Subgroup G) : ((pLayerOf 2 H).subgroupOf H).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Stage1.Thm2.Recip.IG327B.pLayerOf_eq_map' 2 H,
    show ((pLayer ↥H 2).map H.subtype).subgroupOf H = pLayer ↥H 2 from
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
  have := ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic (G := ↥H) (p := 2)
  infer_instance

theorem p1_t_ne_z (hP : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂) : t ≠ z := by
  intro h
  obtain ⟨ht, h1, -⟩ := hsw
  apply hP.ne
  rw [← h1]
  have hc : toBar z ⟨t, ht⟩ ∈ center (CentralizerBar z) := by
    have : (⟨t, ht⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext h
    rw [this]
    exact toBar_z_mem_center z
  have hid : (MulAut.conj (toBar z ⟨t, ht⟩)⁻¹).toMonoidHom = MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    have hx := Subgroup.mem_center_iff.1 hc x
    show (toBar z ⟨t, ht⟩)⁻¹ * x * ((toBar z ⟨t, ht⟩)⁻¹)⁻¹ = x
    rw [inv_inv, mul_assoc, hx, ← mul_assoc, inv_mul_cancel, one_mul]
  unfold conjugate
  rw [hid, Subgroup.map_id]

omit [Finite G] in
theorem ixz_le_centralizer (z t : G) : Ixz z (t * z) ≤ centralizer ({t * z, z} : Set G) :=
  p1_pLayerOf_le _

theorem ixz_normal (z t : G) :
    ((Ixz z (t * z)).subgroupOf (centralizer ({t * z, z} : Set G))).Normal :=
  p1_pLayerOf_normal _

end CFSG.GH74.GLS.Stage2.Local.P27
