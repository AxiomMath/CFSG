module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LocalAnalysis.ComponentInitial

private theorem isSolvable_sl_two_of_card_lt_four {E : Type} [Field E] [Fintype E]
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

private theorem four_le_card_of_surjective_sl_two {E : Type} [Field E] [Fintype E] {K : Type*}
    [Group K] (hK : CFSG.Open.IsQuasisimple K)
    (f : Matrix.SpecialLinearGroup (Fin 2) E →* K) (hf : Function.Surjective f) :
    4 ≤ Fintype.card E := by
  by_contra hlt
  have := isSolvable_sl_two_of_card_lt_four (not_le.1 hlt)
  have : Group.IsSolvable K := Group.isSolvable_of_surjective hf
  have : Group.IsPerfect K := ⟨hK.1⟩
  have : Nontrivial K := by
    have := hK.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (congrArg _ h)⟩
  exact Group.IsPerfect.not_isSolvable K inferInstance

private theorem ringChar_eq_three_of_card_eq_nine {E : Type} [Field E] [Fintype E]
    (h9 : Fintype.card E = 9) : ringChar E = 3 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card E (ringChar E)
  have hdvd : ringChar E ∣ 3 ^ 2 := by
    have : ringChar E ∣ ringChar E ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
    rw [← hn, h9] at this
    simpa using this
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)

theorem lieCompExport_conjAut (hSL : SLFactorFacts) (hA6 : SLAltSixFacts) {n : ℕ} {k : Type}
    [Field k] [Finite k] (h3 : (3 : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    LieCompExport (ringChar k) (LinearFlag.conjAut n k A) := by
  have h3' : ((3 : ℕ) : k) ≠ 0 := by exact_mod_cast h3
  have data : ∀ K : Subgroup (LinearFlag.projectiveSL n k),
      CFSG.Open.IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A)) →
      ∃ (E : Type) (_ : Field E) (_ : Fintype E) (m : ℕ), 2 ≤ m ∧ ringChar E = ringChar k ∧
        ∃ f : Matrix.SpecialLinearGroup (Fin m) E →* ↥K, Function.Surjective f ∧
          f.ker ≤ Subgroup.center _ ∧
          LieFactorData (ringChar E) (Matrix.SpecialLinearGroup (Fin m) E) := by
    intro K hK
    obtain ⟨E, _, _, m, hm, hchar, f, hf, hker⟩ := linear_inner_component_type h3' hA K hK
    refine ⟨E, inferInstance, inferInstance, m, hm, hchar, f, hf, hker, hSL E m hm ?_⟩
    rintro rfl
    exact four_le_card_of_surjective_sl_two hK.2.2 f hf
  refine ⟨LieSemisimple.perfectInLayer_conjAut h3' hA, fun K hK => ?_, fun ⟨K, hK, ⟨a⟩⟩ => ?_⟩
  · obtain ⟨E, _, _, m, hm, hchar, f, hf, hker, hX⟩ := data K hK
    exact ⟨_, inferInstance, inferInstance, hchar ▸ hX, f, hf, hker⟩
  · exfalso
    obtain ⟨E, _, _, m, hm, hchar, f, hf, hker, hX⟩ := data K hK
    obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hker
    obtain ⟨-, h9⟩ := hA6 E m hm ⟨e.trans a⟩
    apply h3'
    have h3E : ringChar k = 3 := hchar.symm.trans (ringChar_eq_three_of_card_eq_nine h9)
    have := CharP.cast_eq_zero k (ringChar k)
    rwa [h3E] at this

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
