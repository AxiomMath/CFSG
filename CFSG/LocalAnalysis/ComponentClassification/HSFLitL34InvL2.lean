module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvSylow
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL2Outer
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup Equiv CFSG.GH74.KGroups CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.HSFLit.AutL2 CFSG.ComponentClassification.HSFLit.AutBeta

variable {G : Type} [Group G]

section Model

variable {J : Subgroup G} {n : ℕ} (M : AutModel (Jhat J) (Perm (Fin n)))

theorem rhoHom_eq_e (hPA : M.P ≤ M.A) {j : G} (hj : j ∈ J) :
    rhoHom M ⟨j, le_normalizer hj⟩ = (M.e (jq J ⟨j, hj⟩) : Perm (Fin n)) := by
  set e₀ : Perm (Fin n) := (M.e (jq J ⟨j, hj⟩) : Perm (Fin n)) with he₀
  set a : Perm (Fin n) := e₀ * rhoM M (le_normalizer hj) with ha
  have haA : a ∈ M.A := M.A.mul_mem (hPA (M.e (jq J ⟨j, hj⟩)).2) (rhoM_mem M _)
  have hfix : ∀ y : Jhat J, a * (M.e y : Perm (Fin n)) * a⁻¹ = M.e y := by
    intro y
    have h1 := rhoM_spec M (le_normalizer hj) y
    rw [betaHat_mem_K J hj y, map_mul, map_mul, map_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [ha, ← he₀] at *
    calc e₀ * rhoM M (le_normalizer hj) * (M.e y : Perm (Fin n)) *
        (e₀ * rhoM M (le_normalizer hj))⁻¹ =
        e₀ * (rhoM M (le_normalizer hj) * (M.e y : Perm (Fin n)) *
          (rhoM M (le_normalizer hj))⁻¹) * e₀⁻¹ := by group
      _ = e₀ * (e₀⁻¹ * (M.e y : Perm (Fin n)) * e₀) * e₀⁻¹ := by rw [← h1]
      _ = M.e y := by group
  obtain ⟨ψ, hψ⟩ := M.Φ.surjective ⟨a, haA⟩
  have hψ1 : ψ = 1 := by
    ext y
    apply M.e.injective
    apply Subtype.ext
    have h2 := M.spec ψ y
    rw [hψ] at h2
    rw [h2]
    exact hfix y
  have ha1 : a = 1 := by
    have := congrArg Subtype.val hψ
    rw [hψ1, map_one] at this
    exact this.symm
  rw [rhoHom_apply]
  rw [ha] at ha1
  rw [eq_inv_of_mul_eq_one_right ha1, inv_inv]

theorem exists_of_mem_P (hPA : M.P ≤ M.A) {p : Perm (Fin n)} (hp : p ∈ M.P) :
    ∃ (j : G) (hj : j ∈ J), rhoHom M ⟨j, le_normalizer hj⟩ = p := by
  obtain ⟨x, hx⟩ := M.e.surjective ⟨p, hp⟩
  obtain ⟨j, rfl⟩ := jq_surjective J x
  refine ⟨j, j.2, ?_⟩
  rw [rhoHom_eq_e M hPA j.2, hx]

theorem mem_oddIn_of_rhoHom (hPA : M.P ≤ M.A) {j : G} (hj : j ∈ J)
    (h1 : rhoHom M ⟨j, le_normalizer hj⟩ = 1) : j ∈ oddIn J := by
  rw [rhoHom_eq_e M hPA hj] at h1
  have h2 : M.e (jq J ⟨j, hj⟩) = 1 := Subtype.ext h1
  rw [map_eq_one_iff _ M.e.injective] at h2
  exact (mem_oddIn_iff hj).mpr h2

end Model

theorem mul_mem_of_card_le {M : Type*} [Group M] [Finite M] {P A : Subgroup M} (hPA : P ≤ A)
    (hcard : Nat.card A ≤ 2 * Nat.card P) {a b : M} (ha : a ∈ A) (hb : b ∈ A) (haP : a ∉ P)
    (hbP : b ∉ P) : a * b ∈ P := by
  set P' := P.subgroupOf A with hP'
  have h1 := card_mul_index P'
  have h2 : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hPA).toEquiv
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hidx : P'.index = 2 := by
    have hle : P'.index ≤ 2 := by
      by_contra h
      push Not at h
      have : Nat.card P * 3 ≤ Nat.card P * P'.index := Nat.mul_le_mul_left _ h
      rw [h2] at h1
      omega
    have hne : P'.index ≠ 1 := by
      intro h
      rw [index_eq_one] at h
      apply haP
      have : (⟨a, ha⟩ : A) ∈ P' := by rw [h]; exact mem_top _
      exact mem_subgroupOf.mp this
    have hne0 : P'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have h3 := (mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
    ⟨fun h => absurd (mem_subgroupOf.mp h) haP, fun h => absurd (mem_subgroupOf.mp h) hbP⟩
  exact mem_subgroupOf.mp h3

variable [Finite G]

theorem odd_orderOf_l2
    {K₁ : Subgroup G}
    (htype : IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) {c : G}
    (hc : c ∈ K₁) (hcC : c ∈ centralizer (K₁ : Set G)) : Odd (orderOf c) := by
  obtain ⟨n, M, hF, -⟩ := exists_l2Model' htype
  have hcK : c ∈ coreActionKernel K₁ :=
    GrS5.mem_coreActionKernel_of_commute fun l hl => (mem_centralizer_iff.mp hcC l hl).symm
  have h1 := (rhoHom_eq_one_iff M ⟨c, le_normalizer hc⟩).mpr hcK
  have h2 := mem_oddIn_of_rhoHom M hF.le hc h1
  have hoddO : Odd (Nat.card (oddIn K₁)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact Odd.of_dvd_nat hoddO (Subgroup.orderOf_dvd_natCard _ h2)

theorem exists_inner_l2
    {u t : G} {K₁ : Subgroup G}
    (hT₁ : GSUnbalancingTriple u t K₁)
    (htype : IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁))
    (htN : t ∈ normalizer (K₁ : Set G)) {z : G} (hzN : z ∈ normalizer (K₁ : Set G)) :
    ∃ z₀ ∈ ({z, t * z} : Set G), ∃ j ∈ K₁, j⁻¹ * z₀ ∈ coreActionKernel K₁ := by
  obtain ⟨n, M, hF, hidx⟩ := exists_l2Model' htype
  have houter := l2UnbalancingOuter G u t K₁ hT₁ htype
  have key : ∀ (g : G) (hg : g ∈ normalizer (K₁ : Set G)), rhoHom M ⟨g, hg⟩ ∈ M.P →
      ∃ j ∈ K₁, j⁻¹ * g ∈ coreActionKernel K₁ := by
    intro g hg hP
    obtain ⟨j, hj, hjg⟩ := exists_of_mem_P M hF.le hP
    refine ⟨j, hj, (rhoHom_eq_one_iff M ⟨j⁻¹ * g, mul_mem (inv_mem (le_normalizer hj)) hg⟩).mp ?_⟩
    have e : (⟨j⁻¹ * g, mul_mem (inv_mem (le_normalizer hj)) hg⟩ : ↥(normalizer (K₁ : Set G))) =
        (⟨j, le_normalizer hj⟩ : ↥(normalizer (K₁ : Set G)))⁻¹ * ⟨g, hg⟩ := rfl
    rw [e, map_mul, map_inv, hjg, inv_mul_cancel]
  have hA : ∀ g : ↥(normalizer (K₁ : Set G)), rhoHom M g ∈ M.A := fun g =>
    M.A.inv_mem (rhoM_mem M g.2)
  have htP : rhoHom M ⟨t, htN⟩ ∉ M.P := by
    intro hP
    obtain ⟨j, hj, hjt⟩ := key t htN hP
    exact houter j hj hjt
  by_cases hzP : rhoHom M ⟨z, hzN⟩ ∈ M.P
  · obtain ⟨j, hj, hjz⟩ := key z hzN hzP
    exact ⟨z, Or.inl rfl, j, hj, hjz⟩
  · have h1 := mul_mem_of_card_le hF.le hidx (hA _) (hA _) htP hzP
    rw [← map_mul] at h1
    obtain ⟨j, hj, hjz⟩ := key (t * z) (mul_mem htN hzN) h1
    exact ⟨t * z, Or.inr rfl, j, hj, hjz⟩

omit [Finite G] in
theorem mem_normalizer_inf' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  refine mem_normalizer_iff.mpr fun h => ?_
  rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp hA h, ← mem_normalizer_iff.mp hB h]

theorem card_le_of_isSylowTwoIn {D H Y : Subgroup G} (hD : IsSylowTwoIn D H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) : Nat.card Y ≤ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDH, P, hP⟩ := hD
  have hY' : IsPGroup 2 (Y.subgroupOf H) := hY.of_equiv (subgroupOfEquivOfLe hYH).symm
  obtain ⟨Q, hQ⟩ := hY'.exists_le_sylow
  have h1 : Nat.card Y = Nat.card (Y.subgroupOf H) :=
    (Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv).symm
  have h2 : Nat.card D = Nat.card (P : Subgroup ↥H) := by
    rw [hP]; exact (Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv).symm
  rw [h1, h2, Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity Q]
  exact Subgroup.card_le_of_le hQ

theorem four_le_card_centralizer {K P : Subgroup G} (hperf : ⁅K, K⁆ = K) (hP : IsSylowTwoIn P K)
    {z : G} (hzP : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    4 ≤ Nat.card ↥(P ⊓ centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := P ⊓ centralizer ({z} : Set G) with hY
  have hzY : zpowers z ≤ Y :=
    zpowers_le.mpr (mem_inf.mpr ⟨hzP, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hcz : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hdvd : 2 ∣ Nat.card Y := hcz ▸ Subgroup.card_dvd_of_le hzY
  have hne : Y ≠ zpowers z := by
    intro heq
    have hP2 : IsPGroup 2 P := GrS5.IsSylowTwoIn.isPGroup hP
    have : Nontrivial ↥P := ⟨⟨⟨z, hzP⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    have := hP2.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(center ↥P))
    have hcY : ((c : ↥P) : G) ∈ Y := by
      refine mem_inf.mpr ⟨(c : ↥P).2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := congrArg Subtype.val (mem_center_iff.mp c.2 ⟨z, hzP⟩)
      simp only [coe_mul] at h1
      exact h1.symm
    rw [heq] at hcY
    have hcz' : ((c : ↥P) : G) = z := by
      rcases GrS5.eq_one_or_eq_of_mem_zpowers' hz2 hcY with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hc1
      · exact h
    have hPY : P ≤ zpowers z := by
      intro p hp
      rw [← heq]
      refine mem_inf.mpr ⟨hp, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := congrArg Subtype.val (mem_center_iff.mp c.2 ⟨p, hp⟩)
      simp only [coe_mul] at h1
      rw [hcz'] at h1
      exact h1
    have hPbot : P ≠ ⊥ := fun h => hz1 (by rw [h] at hzP; exact mem_bot.mp hzP)
    exact not_isCyclic_of_perfect hperf hP hPbot (isCyclic_of_le hPY)
  have hle : 2 ≤ Nat.card Y := hcz ▸ Subgroup.card_le_of_le hzY
  have hne2 : Nat.card Y ≠ 2 := by
    intro h
    exact hne (Subgroup.eq_of_le_of_card_ge hzY (by rw [h, hcz])).symm
  omega

theorem exists_conj_l2
    {u t : G} {K₁ : Subgroup G}
    (hT₁ : GSUnbalancingTriple u t K₁)
    (htype : IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁))
    (hperf : ⁅K₁, K₁⁆ = K₁) (htN : t ∈ normalizer (K₁ : Set G)) (ht2 : t * t = 1) {z₁ : G}
    (hz₁K : z₁ ∈ K₁) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1) (hz₁t : z₁ * t = t * z₁) :
    ∃ v ∈ K₁, v * z₁ = z₁ * v ∧ v⁻¹ * t * v = t * z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have houter := l2UnbalancingOuter G u t K₁ hT₁ htype
  have htK : t ∉ K₁ := fun h => houter t h (by rw [inv_mul_cancel]; exact one_mem _)
  set H := K₁ ⊓ centralizer ({z₁} : Set G) with hH
  have hz₁H : z₁ ∈ H := mem_inf.mpr ⟨hz₁K, mem_centralizer_singleton_iff.mpr rfl⟩
  have htC : t ∈ centralizer ({z₁} : Set G) := mem_centralizer_singleton_iff.mpr hz₁t.symm
  have htz : t ∈ normalizer (zpowers z₁ : Set G) := GrS5.mem_normalizer_of_commute fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact ((show Commute t z₁ from hz₁t.symm).zpow_right k).eq
  have hXp : IsPGroup 2 ↥(zpowers t ⊔ zpowers z₁) :=
    (isPGroup_zpowers_of_mul_self ht2).to_sup_of_normal_right'
      (isPGroup_zpowers_of_mul_self hz₁2) (zpowers_le.mpr htz)
  have hXN : zpowers t ⊔ zpowers z₁ ≤ normalizer (H : Set G) :=
    sup_le (zpowers_le.mpr (mem_normalizer_inf' htN (le_normalizer htC)))
      (zpowers_le.mpr (le_normalizer hz₁H))
  obtain ⟨D, hDSyl, hXD, hXHD⟩ := exists_isSylowTwoIn_normalized hXp hXN
  have hz₁D : z₁ ∈ D := hXHD (mem_inf.mpr ⟨mem_sup_right (mem_zpowers z₁), hz₁H⟩)
  have htND : t ∈ normalizer (D : Set G) := hXD (mem_sup_left (mem_zpowers t))
  have hD2 : IsPGroup 2 D := GrS5.IsSylowTwoIn.isPGroup hDSyl
  have hDK : D ≤ K₁ := hDSyl.1.trans inf_le_left
  have hC : ∀ d ∈ D, d * t = t * d → d = 1 ∨ d = z₁ := by
    intro d hd hdt
    set R := D ⊓ centralizer ({t} : Set G) with hR
    have hR2 : IsPGroup 2 R := hD2.to_le inf_le_left
    have hRle : R ≤ K₁ ⊓ centralizer ({t} : Set G) := inf_le_inf_right _ hDK
    have h1 := (l2UnbalancingAutFact G u t K₁ R hT₁ htype hR2).2 hRle
    have hz₁R : zpowers z₁ ≤ R :=
      zpowers_le.mpr (mem_inf.mpr ⟨hz₁D, mem_centralizer_singleton_iff.mpr hz₁t⟩)
    have hcz : Nat.card (zpowers z₁) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hz₁2) hz₁1
    have heq : zpowers z₁ = R := Subgroup.eq_of_le_of_card_ge hz₁R (by omega)
    have hdR : d ∈ R := mem_inf.mpr ⟨hd, mem_centralizer_singleton_iff.mpr hdt⟩
    rw [← heq] at hdR
    exact GrS5.eq_one_or_eq_of_mem_zpowers' hz₁2 hdR
  have hcard : 4 ≤ Nat.card D := by
    obtain ⟨P₂, hP₂, -, hzP₂⟩ := exists_isSylowTwoIn_normalized (isPGroup_zpowers_of_mul_self hz₁2)
      (zpowers_le.mpr (le_normalizer hz₁K))
    have hz₁P₂ : z₁ ∈ P₂ := hzP₂ (mem_inf.mpr ⟨mem_zpowers z₁, hz₁K⟩)
    have h4 := four_le_card_centralizer hperf hP₂ hz₁P₂ hz₁2 hz₁1
    have hYH : P₂ ⊓ centralizer ({z₁} : Set G) ≤ H := inf_le_inf_right _ hP₂.1
    have hY2 : IsPGroup 2 ↥(P₂ ⊓ centralizer ({z₁} : Set G)) :=
      (GrS5.IsSylowTwoIn.isPGroup hP₂).to_le inf_le_left
    exact h4.trans (card_le_of_isSylowTwoIn hDSyl hYH hY2)
  obtain ⟨v, hvD, hv, hvz⟩ := exists_conj_mul hD2 ht2 (fun h => htK (hDK h)) htND hz₁D hz₁2 hz₁t
    hC hcard
  exact ⟨v, hDK hvD, hvz, hv⟩

end CFSG.ComponentClassification.HSFLit.L34Inv
