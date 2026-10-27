module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Inputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {H : Type} [Group H]

structure Tim77Hyp (S Q : Subgroup H) : Prop where
  sylow : IsSylowOf 2 S ⊤
  le : Q ≤ S
  elem : IsElemAbelian 2 Q
  weak : ∀ h : H, rightConjugate Q h ≤ S → rightConjugate Q h = Q

namespace Tim77Hyp

variable [Finite H] {S Q : Subgroup H} (hQ : Tim77Hyp S Q)
include hQ

theorem exists_sylow : ∃ T : Sylow 2 H, (T : Subgroup H) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hQ.sylow
  rw [isSylowOf_iff, relIndex_top_right] at h
  obtain ⟨-, hpg, hidx⟩ := h
  exact ⟨hpg.toSylow hidx, IsPGroup.toSylow_coe hpg hidx⟩

theorem isPGroup : IsPGroup 2 Q := by
  obtain ⟨T, hT⟩ := hQ.exists_sylow
  exact T.isPGroup'.to_le (hT ▸ hQ.le)

theorem isPGroup_rightConjugate (a : H) : IsPGroup 2 (rightConjugate Q a) :=
  hQ.isPGroup.map _

theorem eq_of_le_of_isPGroup {P : Subgroup H} (hP : IsPGroup 2 P) {a b : H}
    (ha : rightConjugate Q a ≤ P) (hb : rightConjugate Q b ≤ P) :
    rightConjugate Q a = rightConjugate Q b := by
  obtain ⟨T, hT⟩ := hQ.exists_sylow
  obtain ⟨T', hPT'⟩ := hP.exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq H T' T
  have hmem : ∀ y, y ∈ S ↔ d⁻¹ * y * d ∈ (T' : Subgroup H) := fun y => by
    rw [← hT, ← hd, GoldschmidtFour.mem_smul_sylow_iff]
  have key : ∀ c : H, rightConjugate Q c ≤ P → rightConjugate Q d = rightConjugate Q c := by
    intro c hc
    have h1 : rightConjugate Q (c * d⁻¹) = Q := by
      refine hQ.weak _ fun y hy => (hmem y).2 (hPT' (hc ?_))
      rw [mem_rightConjugate_iff] at hy ⊢
      simpa [mul_assoc] using hy
    rw [show c = c * d⁻¹ * d by group, ← rightConjugate_mul, h1]
  rw [← key a ha, key b hb]

theorem le_normalizer_of_le {P : Subgroup H} (hP : IsPGroup 2 P) {a : H}
    (ha : rightConjugate Q a ≤ P) : P ≤ normalizer (rightConjugate Q a : Set H) := by
  intro x hx
  rw [← rightConjugate_eq_self_iff, rightConjugate_mul]
  refine hQ.eq_of_le_of_isPGroup hP ?_ ha
  intro y hy
  rw [← rightConjugate_mul, mem_rightConjugate_iff] at hy
  have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
  rw [this]
  exact P.mul_mem (P.mul_mem (P.inv_mem hx) (ha hy)) hx

theorem eq_of_le_normalizer {a b : H}
    (hab : rightConjugate Q a ≤ normalizer (rightConjugate Q b : Set H)) :
    rightConjugate Q a = rightConjugate Q b :=
  hQ.eq_of_le_of_isPGroup ((hQ.isPGroup_rightConjugate b).to_sup_of_normal_left'
    (hQ.isPGroup_rightConjugate a) hab) le_sup_right le_sup_left

theorem exists_le_normalizer {K P : Subgroup H} {a : H} (haK : rightConjugate Q a ≤ K)
    (hP : IsPGroup 2 P) (hPK : P ≤ K) :
    ∃ c ∈ K, P ≤ normalizer (rightConjugate Q (a * c) : Set H) := by
  obtain ⟨c, hcK, R, hR, hPR, hcR⟩ :=
    GoldschmidtFour.exists_conj_le_of_isPGroup (hQ.isPGroup_rightConjugate a) hP haK hPK
  rw [rightConjugate_mul] at hcR
  exact ⟨c, hcK, hPR.trans (hQ.le_normalizer_of_le hR hcR)⟩

theorem le_normalizer_S : S ≤ normalizer (Q : Set H) := by
  obtain ⟨T, hT⟩ := hQ.exists_sylow
  have h := hQ.le_normalizer_of_le (P := S) (hT ▸ T.isPGroup') (a := 1)
    (by rw [rightConjugate_one]; exact hQ.le)
  rwa [rightConjugate_one] at h

theorem exists_not_le (hns : ∃ x ∈ Q, ∃ h : H, h⁻¹ * x * h ∈ S ∧ h⁻¹ * x * h ∉ Q) :
    ∃ h : H, ¬ tim77D Q h ≤ Q := by
  obtain ⟨x, hx, h, hS, hQx⟩ := hns
  have hxh : h⁻¹ * x * h ∈ rightConjugate Q h := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hx
  exact ⟨h, fun hle => hQx (hle ⟨hxh, hQ.le_normalizer_S hS⟩)⟩

end Tim77Hyp

end CFSG.ComponentClassification.AS81
