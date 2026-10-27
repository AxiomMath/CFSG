module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplitCentral
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingCommRadical

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3EndingRadicalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G), U3EndingData G L f t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v →
      ∃ Z J : Subgroup G, (∀ z ∈ Z, t * z * t⁻¹ ∈ Z → z = 1) ∧
        (∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
          k ∈ normalizer (Z : Set G)) ∧
        J ≤ U₁ ∧ (∀ x ∈ J, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ (2 ^ f) ^ 4 ≤ Nat.card J

section Certificates

namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem mem_normalizer_of_mem_borel (hD : U3EndingData G L f t T R₂ U₁ s) {k : G} (hkL : k ∈ L)
    (hkT : k ∈ normalizer (szT₁ L T : Set G)) :
    k ∈ normalizer (R₂ : Set G) ∧ k ∈ normalizer (U₁ : Set G) := by
  obtain ⟨-, -, -, hNR₁, hNR, -⟩ := hD.start.u3R2_canonical_of_card_sylow hD.card_sylow hD.r2
  have hkA : k ∈ normalizer (szA L T t : Set G) :=
    hD.start.inf_normalizer_le_normalizer_szA ⟨hkL, hkT⟩
  exact ⟨hNR hkA, hD.u1.normalizer_le (hNR₁ hkA)⟩

end U3EndingData

theorem u3EndingCommInput_of_radical (hrad : U3EndingRadicalInput) : U3EndingCommInput := by
  intro G _ _ L f t T R₂ U₁ s v hD hvT hv2 hvS hsv
  obtain ⟨Z, J, hZt, hZk, hJU, hJZ, hJcard⟩ := hrad G L f t T R₂ U₁ s v hD hvT hv2 hvS hsv
  have hU := hD.u1
  have hR := hD.r2
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hRU : R₂ ≤ U₁ := le_sup_right.trans hU.le
  have hcent : ∀ x ∈ U₁, (∀ y ∈ U₁, x * y = y * x) → x ∈ R₂ := fun x hx hxy =>
    hU.mem_of_forall_comm hR hx fun y hy => hxy y (hU.le (mem_sup_left hy))
  have hZt' : ∀ z ∈ Z, t⁻¹ * z * t ∈ Z → z = 1 := fun z hz hzt => by
    rw [htinv] at hzt
    exact hZt z hz (by rwa [htinv])
  have hcard : Nat.card U₁ * Nat.card R₂ ≤ Nat.card J * Nat.card J := by
    rw [hU.card, hR.card]
    calc (2 ^ f) ^ 6 * (2 ^ f) ^ 2 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
      _ ≤ Nat.card J * Nat.card J := Nat.mul_le_mul hJcard hJcard
  obtain ⟨J₁, J₂, hJ, hJinf, ht₁, ht₂, hk, hcomm⟩ :=
    exists_central_product_of_radical hU.comm_mem hUR hRU hcent htt
      (fun x hx => (mem_normalizer_iff.mp htU x).mp hx) hZt' hJU hJZ hcard
  exact ⟨J₁, J₂, hJ, hJinf, ht₁, ht₂, fun k hkL hkT hkodd =>
    hk k (hD.mem_normalizer_of_mem_borel hkL hkT).2 (hZk k hkL hkT hkodd), hcomm⟩

theorem u3EndingInput_of_radical (hrad : U3EndingRadicalInput) (hsyl : U3EndingSylowInput) :
    U3EndingInput :=
  u3EndingInput_of_comm (u3EndingCommInput_of_radical hrad) hsyl

end Certificates

end CFSG.SeitzReduction.RankOne
