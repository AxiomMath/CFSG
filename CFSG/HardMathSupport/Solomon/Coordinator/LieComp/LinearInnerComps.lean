module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LocalAnalysis.ComponentInitial

private theorem isSolvable_sl_two_of_card_lt_four' {E : Type} [Field E] [Fintype E]
    (h : Fintype.card E < 4) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
    have h2 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) E →* _))
    Matrix.SpecialLinearGroup.toGL_injective

private theorem four_le_card_of_surjective_sl_two' {E : Type} [Field E] [Fintype E] {K : Type*}
    [Group K] (hK : CFSG.Open.IsQuasisimple K)
    (f : Matrix.SpecialLinearGroup (Fin 2) E →* K) (hf : Function.Surjective f) :
    4 ≤ Fintype.card E := by
  by_contra hlt
  have := isSolvable_sl_two_of_card_lt_four' (not_le.1 hlt)
  have : Group.IsSolvable K := Group.isSolvable_of_surjective hf
  have : Group.IsPerfect K := ⟨hK.1⟩
  have : Nontrivial K := by
    have := hK.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (congrArg _ h)⟩
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem lieCompsExport_conjAut (hSL : SLFactorFacts) {p n : ℕ} {k : Type} [Field k] [Finite k]
    (hpk : (p : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    LieCompsExport (ringChar k) (LinearFlag.conjAut n k A) := by
  refine ⟨LieSemisimple.perfectInLayer_conjAut hpk hA, fun K hK => ?_⟩
  obtain ⟨E, _, _, m, hm, hchar, f, hf, hker⟩ := linear_inner_component_type hpk hA K hK
  have hX := hSL E m hm (by
    rintro rfl
    exact four_le_card_of_surjective_sl_two' hK.2.2 f hf)
  exact ⟨_, inferInstance, inferInstance, hchar ▸ hX, f, hf, hker⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
