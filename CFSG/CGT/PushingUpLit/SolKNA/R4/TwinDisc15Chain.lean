module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Base
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Clique

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Chain

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}

theorem exists_twoGroup_of_core_adj (hΩ : HypOmegaGen Ω) {K K' M₃ M₄ : Subgroup Y} {z : Y}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hM₃ : M₃ ∈ omegaOfSet Ω (twinSet Ω K)) (hM₄ : M₄ ∈ omegaOfSet Ω (twinSet Ω K))
    (hM₃tq : M₃ ∈ tqMembers3 Ω z) (hM₄tq : M₄ ∈ tqMembers3 Ω z) {U : Subgroup Y}
    (hU : U ∈ USet Ω) (hUM₃ : U ≤ TwinADescent.coreAt z M₃)
    (hUN : U ≤ Subgroup.normalizer ((TwinADescent.coreAt z M₄ : Subgroup Y) : Set Y)) :
    ∃ B : Subgroup Y, IsPGroup 2 B ∧ 2 < Nat.card ↥(K ⊓ B) ∧ 2 < Nat.card ↥(K' ⊓ B) ∧
      2 < Nat.card ↥(M₃ ⊓ B) ∧ 2 < Nat.card ↥(M₄ ⊓ B) := by
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_uniqueInvolution hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hK'Ω : K' ∈ Ω := hK'.1
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hUM₃' : U ≤ M₃ := hUM₃.trans (TwinADescent.coreAt_le_left z M₃)
  have hUz : U ≤ Subgroup.centralizer ({z} : Set Y) :=
    hUM₃.trans (TwinADescent.coreAt_le_centralizer z M₃)
  obtain ⟨P, hPs, hUP⟩ := exists_isPGroup_sup_sylow hU2 hUN
  obtain ⟨hPM₄, hPz⟩ := (TwinADescent.isSylow2In_coreAt_iff hc2 hM₄tq.2).mp hPs
  have hP8 : 8 ≤ Nat.card P :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM₄.1 hPM₄)
  have hM₃K : M₃ ≠ K := by
    intro h
    apply not_mem_twinSet_of_mem_omegaOfSet hK hz hM₃
    rw [h]
    exact mem_twinSet_self hK hz
  have hM₄K : M₄ ≠ K := by
    intro h
    apply not_mem_twinSet_of_mem_omegaOfSet hK hz hM₄
    rw [h]
    exact mem_twinSet_self hK hz
  have hM₃K' : M₃ ≠ K' := by
    intro h
    apply not_mem_twinSet_of_mem_omegaOfSet hK hz hM₃
    rw [h]
    exact hK'
  have hM₄K' : M₄ ≠ K' := by
    intro h
    apply not_mem_twinSet_of_mem_omegaOfSet hK hz hM₄
    rw [h]
    exact hK'
  have hUN₁ : U ≤ Subgroup.normalizer (K : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hM₃.1 hM₃K.symm hz hUM₃' hU2 (by omega) hUz
  have hUN₂ : U ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK'Ω hM₃.1 hM₃K'.symm hzK' hUM₃' hU2 (by omega) hUz
  have hPN₁ : P ≤ Subgroup.normalizer (K : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hM₄.1 hM₄K.symm hz hPM₄.1 hPM₄.2.1 (by omega) hPz
  have hPN₂ : P ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK'Ω hM₄.1 hM₄K'.symm hzK' hPM₄.1 hPM₄.2.1
      (by omega) hPz
  obtain ⟨R₁, hR₁, hB₁⟩ := exists_isPGroup_sup_sylow hUP (sup_le hUN₁ hPN₁ : U ⊔ P ≤ _)
  have hKN : K ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  have hB₁N : (U ⊔ P) ⊔ R₁ ≤ Subgroup.normalizer (K' : Set Y) :=
    sup_le (sup_le hUN₂ hPN₂) (hR₁.1.trans hKN)
  obtain ⟨R₂, hR₂, hB₂⟩ := exists_isPGroup_sup_sylow hB₁ hB₁N
  have hR₁8 : 8 ≤ Nat.card R₁ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)
  have hR₂8 : 8 ≤ Nat.card R₂ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK'Ω hR₂)
  have hUB : U ≤ ((U ⊔ P) ⊔ R₁) ⊔ R₂ := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have hPB : P ≤ ((U ⊔ P) ⊔ R₁) ⊔ R₂ := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hR₁B : R₁ ≤ ((U ⊔ P) ⊔ R₁) ⊔ R₂ := le_sup_of_le_left le_sup_right
  have hR₂B : R₂ ≤ ((U ⊔ P) ⊔ R₁) ⊔ R₂ := le_sup_right
  refine ⟨((U ⊔ P) ⊔ R₁) ⊔ R₂, hB₂, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by omega : 2 < Nat.card R₁)
      (Subgroup.card_le_of_le (le_inf hR₁.1 hR₁B))
  · exact lt_of_lt_of_le (by omega : 2 < Nat.card R₂)
      (Subgroup.card_le_of_le (le_inf hR₂.1 hR₂B))
  · exact lt_of_lt_of_le (by omega : 2 < Nat.card U)
      (Subgroup.card_le_of_le (le_inf hUM₃' hUB))
  · exact lt_of_lt_of_le (by omega : 2 < Nat.card P)
      (Subgroup.card_le_of_le (le_inf hPM₄.1 hPB))

end Chain

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
