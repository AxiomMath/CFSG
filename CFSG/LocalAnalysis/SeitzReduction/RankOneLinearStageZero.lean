module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGoldschmidt
public import CFSG.LocalAnalysis.SteinbergBVGMSNormalRootSylowAlternatives
public import CFSG.LocalAnalysis.SteinbergBXGMSNormalRootPartition
public import CFSG.LocalAnalysis.SeitzReduction.RankOneKernel

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 goldschmidt1974_of_milestone)

section Generic

variable {D : Type*} [Group D] [Finite D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_normal_root_not_sylow_of_card_ne (h : GMSNormalRootData J R X U P n)
    (hR : Nat.card R ≠ 2 ^ n)
    (hsc : (∃ T : Sylow 2 D, (T : Subgroup D) = P) →
      ¬ IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D)) :
    (¬ ∃ T : Sylow 2 D, (T : Subgroup D) = P) ∧ 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard := by
  have hUcard : Nat.card U = 2 ^ n := h.2.2.2.2.1.2.2.2
  obtain ⟨-, halt, -⟩ := SteinbergBV.gms_normal_root_at_most_two_conjugates_sylow_alternatives h
  rcases halt with ⟨hsyl, hcl⟩ | ⟨P₁, -, -, -, -, -, ⟨y, -, hyU, -⟩, -⟩ | hc
  · exact absurd hcl (hsc hsyl)
  · refine absurd ?_ hR
    rw [← hyU, card_map_of_injective (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective,
      hUcard]
  · exact hc

theorem gms_isStronglyClosedIn_of_card_eq_two (hR2 : Nat.card R = 2)
    (hnz : ∀ Q ∈ gmsRootConjugates (U ⊔ R) R, ∀ v ∈ Q, v ≠ 1 → v ∉ U)
    (hpart : ∀ v ∈ U ⊔ R, v ∉ U → ∃ Q, Q ∈ gmsRootConjugates (U ⊔ R) R ∧ v ∈ Q) :
    IsStronglyClosedIn (U ⊔ R) (U : Set D) := by
  refine ⟨fun x hx => mem_sup_left hx, fun a ha g hg => ?_⟩
  by_contra hv
  obtain ⟨Q, ⟨k, rfl, -⟩, hvQ⟩ := hpart _ hg hv
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hv
    rw [mul_one, inv_mul_cancel]
    exact one_mem U
  set Q' : Subgroup D := (R.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom
    with hQ'
  have haQ' : a ∈ Q' := by
    rw [hQ', SteinbergBV.mem_map_conj_iff]
    exact hvQ
  have hQ'card : Nat.card Q' = 2 := by
    rw [hQ', card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective, hR2]
  have hoa : orderOf a = 2 := by
    have h1 := Subgroup.orderOf_dvd_natCard Q' haQ'
    rw [hQ'card] at h1
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) ha1
    · exact h2
  have hQ'eq : zpowers a = Q' :=
    eq_of_le_of_card_ge (zpowers_le.2 haQ') (by rw [hQ'card, Nat.card_zpowers, hoa])
  have hQ'Δ : Q' ∈ gmsRootConjugates (U ⊔ R) R := by
    refine ⟨k * g⁻¹, ?_, ?_⟩
    · rw [hQ', mul_inv_rev, inv_inv, SteinbergBV.map_conj_mul]
    · rw [← hQ'eq]
      exact (zpowers_le.2 ha).trans le_sup_left
  exact hnz Q' hQ'Δ a haQ' ha1 ha

theorem gms_normal_root_stage_zero (h : GMSNormalRootData J R X U P n) (hR2 : Nat.card R = 2)
    (hsc : (∃ T : Sylow 2 D, (T : Subgroup D) = P) →
      ¬ IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D)) :
    (¬ ∃ T : Sylow 2 D, (T : Subgroup D) = P) ∧
    (∀ g : D, CFSG.conjugate (U ⊔ R) g ≤ P → CFSG.conjugate (U ⊔ R) g = U ⊔ R) ∧
    normalizer (P : Set D) ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ∧
    normalizer ((U ⊔ R : Subgroup D) : Set D) ≤ normalizer (U : Set D) ∧
    (gmsRootConjugates (U ⊔ R) R).ncard = 2 ^ n ∧
    (∀ Q ∈ gmsRootConjugates (U ⊔ R) R, ∀ v ∈ Q, v ≠ 1 → v ∉ U) ∧
    (∀ v ∈ U ⊔ R, v ∉ U → ∃! Q, Q ∈ gmsRootConjugates (U ⊔ R) R ∧ v ∈ Q) ∧
    IsStronglyClosedIn (U ⊔ R) (U : Set D) ∧
    (∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (U ⊔ R) R, Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ Q₁ = Z₁ ∧ σ Q₂ = Z₂) := by
  have hn3 : 3 ≤ n := h.1
  have hR : Nat.card R ≠ 2 ^ n := by
    rw [hR2]
    intro h2
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  have hVP : U ⊔ R ≤ P := sup_le h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hnsyl, h3⟩ := gms_normal_root_not_sylow_of_card_ne h hR hsc
  have hweak := (SteinbergBV.gms_normal_root_at_most_two_conjugates_sylow_alternatives h).1
  obtain ⟨hLU, hΔcard, hnz, hpart, h2tr, -⟩ :=
    SteinbergBX.gms_normal_root_partition_and_two_transitivity h h3
  refine ⟨hnsyl, hweak, fun y hy => ?_, hLU, hΔcard, hnz, hpart,
    gms_isStronglyClosedIn_of_card_eq_two hR2 hnz fun v hv hvU => (hpart v hv hvU).exists, h2tr⟩
  have h1 : CFSG.conjugate (U ⊔ R) y ≤ P := by
    intro x hx
    rw [CFSG.conjugate, SteinbergBV.mem_map_conj_iff, inv_inv] at hx
    have h2 := (mem_normalizer_iff''.mp hy (y * x * y⁻¹)).mp (hVP hx)
    rwa [show y⁻¹ * (y * x * y⁻¹) * y = x by group] at h2
  have h2 : y⁻¹ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
    SteinbergBV.map_conj_eq_self_iff.1 (hweak y h1)
  simpa using inv_mem h2

end Generic

section Setting

variable {G : Type} [Group G] [Finite G]

theorem psl2_stage_zero_full_of_card_sylow_eq_two (hGold : Goldschmidt1974) {L : Subgroup G}
    (h : SeitzSetting G L) {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {T : Subgroup G}
    (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G))) :
    GMSNormalRootData (centralizer (L : Set G)) (zpowers t) L (T ⊓ L) T f ∧
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) ∧
    (∀ g : G, CFSG.conjugate (T ⊓ L ⊔ zpowers t) g ≤ T →
      CFSG.conjugate (T ⊓ L ⊔ zpowers t) g = T ⊓ L ⊔ zpowers t) ∧
    normalizer (T : Set G) ≤ normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) ∧
    normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
    (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t)).ncard = 2 ^ f ∧
    (∀ Q ∈ gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t), ∀ v ∈ Q, v ≠ 1 → v ∉ T ⊓ L) ∧
    (∀ v ∈ T ⊓ L ⊔ zpowers t, v ∉ T ⊓ L →
      ∃! Q, Q ∈ gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t) ∧ v ∈ Q) ∧
    IsStronglyClosedIn (T ⊓ L ⊔ zpowers t) ((T ⊓ L : Subgroup G) : Set G) ∧
    (∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t), Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (T ⊓ L ⊔ zpowers t) (zpowers t)).range,
        σ Q₁ = Z₁ ∧ σ Q₂ = Z₂) := by
  have hdata := gmsNormalRootData_of_psl2_of_card_sylow_eq_two h hf hL hS2 ht htC hTN hT
  have hR2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have hsc : (∃ S : Sylow 2 G, (S : Subgroup G) = T) →
      ¬ IsStronglyClosedIn T ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) := by
    rintro ⟨S, hS⟩ ⟨hVT, hcl⟩
    obtain ⟨-, -, ⟨hRel, -, -⟩, ⟨-, -, hXC⟩, ⟨hUel, hUX, -, -⟩, -⟩ := hdata
    have hRU : zpowers t ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      le_centralizer_iff.1 (hUX.trans hXC)
    have hVel := SteinbergBT.isElementaryAbelian_sup_of_centralizes hUel hRel hRU
    have hV1 : T ⊓ L ⊔ zpowers t ≠ ⊥ := by
      intro hbot
      have htV : t ∈ T ⊓ L ⊔ zpowers t := mem_sup_right (mem_zpowers t)
      rw [hbot, mem_bot] at htV
      rw [htV, orderOf_one] at ht
      exact absurd ht (by norm_num)
    subst hS
    exact false_of_stronglyClosed_abelian_of_goldschmidt hGold h (Or.inl ⟨f, hf, hL⟩) S hVT
      hVel.toIsMulCommutative hV1 hcl
  exact ⟨hdata, gms_normal_root_stage_zero hdata hR2 hsc⟩

theorem psl2_stage_zero_full_of_goldschmidt
    (hGold : Goldschmidt1974) {L : Subgroup G}
    (h : SeitzSetting G L) {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {T : Subgroup G}
    (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G))) :
    GMSNormalRootData (centralizer (L : Set G)) (zpowers t) L (T ⊓ L) T f ∧
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) ∧
    (∀ g : G, CFSG.conjugate (T ⊓ L ⊔ zpowers t) g ≤ T →
      CFSG.conjugate (T ⊓ L ⊔ zpowers t) g = T ⊓ L ⊔ zpowers t) ∧
    normalizer (T : Set G) ≤ normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) ∧
    normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
    (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t)).ncard = 2 ^ f ∧
    (∀ Q ∈ gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t), ∀ v ∈ Q, v ≠ 1 → v ∉ T ⊓ L) ∧
    (∀ v ∈ T ⊓ L ⊔ zpowers t, v ∉ T ⊓ L →
      ∃! Q, Q ∈ gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t) ∧ v ∈ Q) ∧
    IsStronglyClosedIn (T ⊓ L ⊔ zpowers t) ((T ⊓ L : Subgroup G) : Set G) ∧
    (∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t), Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (T ⊓ L ⊔ zpowers t) (zpowers t)).range,
        σ Q₁ = Z₁ ∧ σ Q₂ = Z₂) :=
  psl2_stage_zero_full_of_card_sylow_eq_two hGold h hf hL
    (rankOneKernel G L h (Or.inl ⟨f, hf, hL⟩)) ht htC hTN hT

end Setting

end CFSG.SeitzReduction.RankOne
