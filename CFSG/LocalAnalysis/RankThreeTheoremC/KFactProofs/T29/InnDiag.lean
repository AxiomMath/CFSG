module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26SCL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (Field3Structure)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (IsLThreeEps)
open scoped MatrixGroups

section InnDiag

theorem id_mem_conj_of_mem_commutator {K : Type} [Group K] {F : Type} [Field F]
    {H : Subgroup (GL (Fin 3) F)} (e : (K ⧸ Subgroup.center K) ≃* StatedProj H)
    (hcomm : ∀ a b : MulAut (StatedProj H), IsConjByGL H (a * b * a⁻¹ * b⁻¹))
    {α : MulAut K} (hα : α ∈ commutator (MulAut K)) :
    ∃ φ : MulAut (StatedProj H), IsConjByGL H φ ∧
      ∀ y : K, e (QuotientGroup.mk (α y)) = φ (e (QuotientGroup.mk y)) := by
  let G : Subgroup (MulAut (StatedProj H)) :=
    { carrier := {φ | IsConjByGL H φ}
      mul_mem' := by
        rintro φ ψ ⟨g₁, hg₁, hφ⟩ ⟨g₂, hg₂, hψ⟩
        show IsConjByGL H (φ * ψ)
        refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, fun A A' h => ?_⟩
        have hA'' : g₂ * (A : GL (Fin 3) F) * g₂⁻¹ ∈ H :=
          (Subgroup.mem_normalizer_iff.1 hg₂ (A : GL (Fin 3) F)).1 A.2
        have h1 : ψ (QuotientGroup.mk A) = QuotientGroup.mk (⟨_, hA''⟩ : H) :=
          hψ A ⟨_, hA''⟩ rfl
        have h2 : φ (QuotientGroup.mk (⟨_, hA''⟩ : H)) = QuotientGroup.mk A' := by
          refine hφ _ A' ?_
          show (A' : GL (Fin 3) F) = g₁ * (g₂ * (A : GL (Fin 3) F) * g₂⁻¹) * g₁⁻¹
          rw [h]
          group
        show φ (ψ (QuotientGroup.mk A)) = QuotientGroup.mk A'
        rw [h1, h2]
      one_mem' := by
        show IsConjByGL H 1
        refine ⟨1, Subgroup.one_mem _, fun A A' h => ?_⟩
        have hAA : A' = A := Subtype.ext (by rw [h]; simp)
        subst hAA
        rfl
      inv_mem' := by
        rintro φ ⟨g, hg, hφ⟩
        show IsConjByGL H φ⁻¹
        refine ⟨g⁻¹, inv_mem hg, fun A A' h => ?_⟩
        rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
        refine (hφ A' A ?_).symm
        show (A : GL (Fin 3) F) = g * (A' : GL (Fin 3) F) * g⁻¹
        rw [h]
        group }
  have hcommle : commutator (MulAut (StatedProj H)) ≤ G := by
    show ⁅(⊤ : Subgroup (MulAut (StatedProj H))), ⊤⁆ ≤ G
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    exact hcomm a b
  let Θ : MulAut K →* MulAut (StatedProj H) :=
    (MulAut.congr e).toMonoidHom.comp (CFSG.RankThree.PartTwo.KFacts.centerDescend K)
  have h1 : Θ α ∈ ⁅(⊤ : Subgroup (MulAut K)).map Θ, (⊤ : Subgroup (MulAut K)).map Θ⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem Θ hα
  have h2 : ⁅(⊤ : Subgroup (MulAut K)).map Θ, (⊤ : Subgroup (MulAut K)).map Θ⁆ ≤
      commutator (MulAut (StatedProj H)) :=
    Subgroup.commutator_mono le_top le_top
  have hmem : Θ α ∈ G := hcommle (h2 h1)
  exact ⟨Θ α, hmem, fun y => CFSG.HardMathSupport.Solomon.Coordinator.descend_compat e α y⟩

theorem fieldAut_not_mem_commutator {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hT : IsThreeType K) {α : MulAut K}
    (hf : IsFieldAutThree α) (h1 : α ≠ 1) : α ∉ commutator (MulAut K) := by
  intro hα
  have hinn : IsInnDiagThree α := by
    rcases hT with ⟨F, _, _, ⟨e⟩⟩ | ⟨F, _, _, q, hcard, ⟨e⟩⟩
    · obtain ⟨φ, hφ, hcompat⟩ := id_mem_conj_of_mem_commutator (H := StatedSL 3 F) e
        (fun a b => CFSG.HardMathSupport.Solomon.Coordinator.isConjByGL_commutator_psl F a b) hα
      exact Or.inl ⟨F, inferInstance, inferInstance, e, φ, hφ, hcompat⟩
    · obtain ⟨p, f, rfl, ⟨hF⟩⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.exists_unitaryFieldData hcard
      have hq2 : 2 < p ^ f :=
        CFSG.HardMathSupport.Solomon.Coordinator.two_lt_pow_of_quasisimple hq hF
          (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hF (n := 3)
            (by norm_num)).symm)
      obtain ⟨φ, hφ, hcompat⟩ := id_mem_conj_of_mem_commutator (H := StatedSU 3 (p ^ f) F) e
        (fun a b => CFSG.HardMathSupport.Solomon.Coordinator.isConjByGL_commutator_psu hF hq2 a b)
        hα
      exact Or.inr ⟨F, inferInstance, inferInstance, p ^ f, e, φ, hcard, hφ, hcompat⟩
  exact h1 (AutL3.input7_fieldInnDiag_holds K hq α hf hinn)

theorem not_mem_commutator_of_fieldAut {X : Type} [Group X] [Finite X] {L : Subgroup X}
    [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L) (hT : IsThreeType ↥L) {y : X}
    (hf : IsFieldAutThree (MulAut.conjNormal y : MulAut ↥L))
    (h1 : (MulAut.conjNormal y : MulAut ↥L) ≠ 1) : y ∉ commutator X := by
  intro hy
  have hy' : y ∈ ⁅(⊤ : Subgroup X), ⊤⁆ := hy
  have h2 : (MulAut.conjNormal y : MulAut ↥L) ∈
      (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X).map (MulAut.conjNormal : X →* MulAut ↥L) :=
    Subgroup.mem_map_of_mem _ hy'
  rw [Subgroup.map_commutator] at h2
  have h3 : ⁅(⊤ : Subgroup X).map (MulAut.conjNormal : X →* MulAut ↥L),
      (⊤ : Subgroup X).map (MulAut.conjNormal : X →* MulAut ↥L)⁆ ≤
      commutator (MulAut ↥L) :=
    Subgroup.commutator_mono le_top le_top
  exact fieldAut_not_mem_commutator hq hT hf h1 (h3 h2)

end InnDiag

section FieldE27

theorem isInnDiagThree_one {K : Type} [Group K] (hT : IsThreeType K) :
    IsInnDiagThree (1 : MulAut K) := by
  rcases hT with ⟨F, hF, hFin, ⟨θ⟩⟩ | ⟨F, hF, hFin, q, hcard, ⟨θ⟩⟩
  · refine Or.inl ⟨F, hF, hFin, θ, 1, ⟨1, one_mem _, fun A A' h => ?_⟩, fun y => ?_⟩
    · have hAA : A' = A := Subtype.ext (by simpa using h)
      rw [hAA, MulAut.one_apply]
    · simp only [MulAut.one_apply]
  · refine Or.inr ⟨F, hF, hFin, q, θ, 1, hcard, ⟨1, one_mem _, fun A A' h => ?_⟩, fun y => ?_⟩
    · have hAA : A' = A := Subtype.ext (by simpa using h)
      rw [hAA, MulAut.one_apply]
    · simp only [MulAut.one_apply]

theorem isThreeType_of_isLThreeEps {Y : Type} [Group Y] (h : IsLThreeEps (Y ⧸ center Y)) :
    IsThreeType Y := by
  rcases h with ⟨K, hK, hKf, _, hne⟩ | ⟨K, hK, hKf, q, hcard, _, hne⟩
  · exact Or.inl ⟨K, hK, hKf, hne⟩
  · exact Or.inr ⟨K, hK, hKf, q, hcard, hne⟩

theorem exists_field_aut_of_E27 (hF2 : InnDiagRankTwo) (hFs : Field3Structure) {K : Type}
    [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hT : IsLThreeEps (K ⧸ center K))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) :
    ∃ α ∈ E, α ≠ 1 ∧ ∀ k : ℕ, IsFieldAutThree (α ^ k) := by
  have hT3 : IsThreeType K := isThreeType_of_isLThreeEps hT
  obtain ⟨α, hαE, hαn⟩ : ∃ α ∈ E, ¬ IsInnDiagThree α := by
    by_contra hcon
    have hall : ∀ α ∈ E, IsInnDiagThree α := fun α hα => by
      by_contra h
      exact hcon ⟨α, hα, h⟩
    have h9 : Nat.card E ≤ 9 := hF2 K hq hT E hE hall
    omega
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hαn (isInnDiagThree_one hT3)
  have hα3 : α ^ 3 = 1 := hE.2 α hαE
  have hαF : IsFieldAutThree α := by
    rcases (hFs K hq hT3).1 α hα3 with h | h
    · exact absurd h hαn
    · exact h
  have hinv3 : α⁻¹ ^ 3 = 1 := by rw [inv_pow, hα3, inv_one]
  have hαinv : IsFieldAutThree α⁻¹ := by
    rcases (hFs K hq hT3).1 α⁻¹ hinv3 with h | h
    · exfalso
      apply hαn
      have h' := CFSG.HardMathSupport.Solomon.Coordinator.i2326s_isInnDiagThree_inv h
      rwa [inv_inv] at h'
    · exact h
  refine ⟨α, hαE, hα1, fun k => ?_⟩
  have hk : α ^ k = α ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3]
    rw [pow_add, pow_mul, hα3, one_pow, one_mul]
  rw [hk]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · rw [h, pow_zero]
    exact Or.inl rfl
  · rw [h, pow_one]
    exact hαF
  · rw [h]
    have h2 : α ^ 2 = α⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc α ^ 2 * α = α ^ 3 := (pow_succ α 2).symm
        _ = 1 := hα3
    rw [h2]
    exact hαinv

end FieldE27

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
