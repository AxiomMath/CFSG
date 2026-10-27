module

public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem weak_closure_of_normal {M H : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) {L : Subgroup ↥M}
    (hLn : L.Normal) {A : Subgroup ↥M} (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L)
    (hA3 : Nat.card A = 3) (hAU : A.map M.subtype ∈ uniqueSet M) :
    ∀ h ∈ H, (A.map M.subtype).map (MulAut.conj h).toMonoidHom ≤
        Subgroup.normalizer ((A.map M.subtype : Subgroup G) : Set G) ⊓ (H ⊓ M) →
      (A.map M.subtype).map (MulAut.conj h).toMonoidHom = A.map M.subtype := by
  intro h _ hle
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup G := A.map M.subtype with hP
  set Q : Subgroup G := P.map (MulAut.conj h).toMonoidHom
  have hQN : Q ≤ Subgroup.normalizer (P : Set G) := hle.trans inf_le_left
  have hQM : Q ≤ M := hle.trans (inf_le_right.trans inf_le_right)
  have hPle : P ≤ M.map (MulAut.conj h⁻¹).toMonoidHom := by
    intro x hx
    exact ⟨h * x * h⁻¹, hQM ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply]; group⟩
  have hhM : h ∈ M := by
    have hMh := hAU.2 h⁻¹ hPle
    have : h⁻¹ ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_iff_map_conj_eq.2 hMh
    rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hM] at this
    simpa using M.inv_mem this
  have hQL : Q ≤ L.map M.subtype := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨⟨h, hhM⟩ * a * ⟨h, hhM⟩⁻¹, hLn.conj_mem a (hA.le ha) ⟨h, hhM⟩, ?_⟩
    simp [MulAut.conj_apply]
  have hAG : CFSG.ABGLocalTools.IsSylowOf 3 P (L.map M.subtype) :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M).2 hA
  have hPG3 : IsPGroup 3 P := hAG.isPGroup
  have hQ3 : IsPGroup 3 Q := hPG3.map _
  have hsup : IsPGroup 3 (Q ⊔ P : Subgroup G) := hQ3.to_sup_of_normal_right' hPG3 hQN
  have hPeq : Q ⊔ P = P := hAG.eq_of_le le_sup_right (sup_le hQL hAG.le) hsup
  have hQP : Q ≤ P := hPeq ▸ le_sup_left
  have hcardP : Nat.card P = 3 := by
    rw [hP, Subgroup.card_map_of_injective M.subtype_injective]
    exact hA3
  have hcardQ : Nat.card Q = 3 := by
    rw [← hcardP]
    exact Subgroup.card_map_of_injective (MulAut.conj h).injective
  exact Subgroup.eq_of_le_of_card_ge hQP (by rw [hcardP, hcardQ])

end CFSG.LocalAnalysis.RankThreeUC.S15
