module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Reduction
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.Simplicity.Finiteness

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

section Common

theorem chevalleyModel_cat_twistedE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    ChevalleyExceptionalModel (Cat ⟨.twistedE6 q, hv⟩) .twistedE6 q.p q.exponent := by
  obtain ⟨K, _, _, hK, -⟩ := exists_field_pow q (m := TwistTag.E6.order) TwistTag.E6.order_pos
  rw [TauCeti.PrimePower.card_def] at hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p q.exponent_pos K hK
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance, inferInstance, hK, σ.toRingHom,
    hσ'', ⟨φ.symm⟩⟩

theorem finite_isSimpleGroup_cat_twistedE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    Finite (Cat ⟨.twistedE6 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.twistedE6 q, hv⟩) :=
  have hm := chevalleyModel_cat_twistedE6 hv
  ⟨CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ _ _ _ hm,
    (CFSG.LieType.Simplicity.fam_2e6_simplicity _ _ _ hm).2⟩

theorem finite_isSimpleGroup_cat_E6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    Finite (Cat ⟨.E6 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.E6 q, hv⟩) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have : IsSimpleGroup (adjointGroup .E6 K) := isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K)
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, MulEquiv.isSimpleGroup e⟩

end Common

section E7

theorem finite_isSimpleGroup_cat_E7 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) :
    Finite (Cat ⟨.E7 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.E7 q, hv⟩) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have : Finite (adjointGroup .E7 K) := generated_group_finite .E7 K
  have : IsSimpleGroup (adjointGroup .E7 K) := isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K)
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, MulEquiv.isSimpleGroup e⟩

end E7

section E8

theorem finite_isSimpleGroup_cat_E8 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) :
    Finite (Cat ⟨.E8 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.E8 q, hv⟩) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Finite (adjointGroup .E8 K) := generated_group_finite .E8 K
  have : IsSimpleGroup (adjointGroup .E8 K) := isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K)
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, MulEquiv.isSimpleGroup e⟩

end E8

end CFSG.HardMathSupport.Timmesfeld.CrossChar
