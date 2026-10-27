module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeWhole

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

theorem G2_exceptional_field_involution_fixed_p_components
    (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ a) ^ 2 = 1 ∧
    ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ a ≠ 1 ∧
    (∀ g : adjointGroup ReeTag.G2.tag K,
      (ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ a) g = g ↔
        g ∈ ReeTag.G2.finiteReeFixedGroup K a) ∧
    (ReeTag.G2.finiteReeFixedGroup K a).map (adjointGroup ReeTag.G2.tag K).subtype =
      ReeTag.G2.reeGamma K a ∧
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (ReeTag.G2.finiteReeFixedGroup K a),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (a = 0 → Nat.card (ReeTag.G2.finiteReeFixedGroup K a) = 1512 ∧
      Nat.card (commutator (ReeTag.G2.finiteReeFixedGroup K a)) = 504 ∧
      IsSimpleGroup (commutator (ReeTag.G2.finiteReeFixedGroup K a)) ∧
      ∃ x y : commutator (ReeTag.G2.finiteReeFixedGroup K a), x * y ≠ y * x) := by
  classical
  set F := ReeTag.G2.finiteExceptionalAut K * ReeTag.G2.finiteFrobeniusAut K ^ a with hF
  set Γ := ReeTag.G2.finiteReeFixedGroup K a with hΓ
  obtain ⟨-, -, -, -, ⟨hsq, hne⟩, -, hodd⟩ :=
    G2_three_exact_automorphism_normal_form (f := 2 * a + 1) (by omega) K hK
  obtain ⟨hφF, -, -⟩ := hodd a rfl
  rw [hφF] at hsq hne
  let e : Γ ≃* ReeTag.G2.reeGamma K a :=
    Subgroup.equivMapOfInjective Γ (adjointGroup ReeTag.G2.tag K).subtype Subtype.val_injective
  obtain ⟨hsimple, hnab, -, -, hzero, hcomp⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components a K hK
  have hcommap : (commutator Γ).map e.toMonoidHom = commutator (ReeTag.G2.reeGamma K a) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  let ec : commutator Γ ≃* commutator (ReeTag.G2.reeGamma K a) :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hcommap)
  refine ⟨hsq, hne, fun g => Iff.rfl, rfl, fun p hp L hL => ?_, fun ha => ?_⟩
  ·
    have : Fact p.Prime := ⟨hp⟩
    have : Finite Γ := Subtype.finite
    have : Finite (ReeTag.G2.reeGamma K a) := Subtype.finite
    have hL' := (p_component_isomorphism_transport p hp e).1 L |>.1 hL
    have hq := (hcomp p hp _ hL').1
    exact (isQuasisimple_congr
      (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective)).2 hq
  ·
    subst ha
    have hK3 : Nat.card K = 3 := by simpa using hK
    obtain ⟨w₀, -, hw₀⟩ := Set.exists_max_image Set.univ
      (fun w : WeylGroup ReeTag.G2.tag => (coxeterSystem ReeTag.G2.tag).length w)
      Set.finite_univ Set.univ_nonempty
    have hw₀' : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
        (coxeterSystem ReeTag.G2.tag).length w₀ := fun w => hw₀ w (Set.mem_univ w)
    obtain ⟨hcard, -⟩ := small_Ree_three_derived_simple K hK3 w₀ hw₀'
    obtain ⟨-, hcard504, -⟩ := hzero rfl w₀ hw₀'
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hcard]
      exact Nat.card_congr e.toEquiv
    · rw [← hcard504]
      exact Nat.card_congr ec.toEquiv
    · have := hsimple
      exact ec.isSimpleGroup
    · obtain ⟨x, y, hxy⟩ := hnab
      exact ⟨ec.symm x, ec.symm y, fun h => hxy (by
        have := congrArg ec h
        simpa only [map_mul, MulEquiv.apply_symm_apply] using this)⟩

end CFSG.LieType.Ree
