module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LieType.Simplicity.TrialityD4

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

section Untwisted


theorem finite_isSimpleGroup_cat_G2
    {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid) :
    Finite (Cat ⟨.G2 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.G2 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  have : IsSimpleGroup (adjointGroup .G2 K) := isSimpleGroup_adjointGroup_G2 q hv K hK
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, MulEquiv.isSimpleGroup e⟩

theorem finite_isSimpleGroup_cat_F4
    {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid) :
    Finite (Cat ⟨.F4 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  have : IsSimpleGroup (adjointGroup .F4 K) :=
    isSimpleGroup_adjointGroup_of_isQuasisimple (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K)
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, MulEquiv.isSimpleGroup e⟩

theorem finite_isSimpleGroup_cat_trialityD4
    {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) :
    Finite (Cat ⟨.trialityD4 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.trialityD4 q, hv⟩) :=
  have hm := chevalleyModel_cat_trialityD4 hv
  ⟨CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ _ _ _ hm,
    (CFSG.LieType.Simplicity.fam_3d4_simplicity _ _ _ hm).2⟩

theorem finite_isSimpleGroup_cat_reeF4 {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) :
    Finite (Cat ⟨.reeF4 m, hv⟩) ∧ IsSimpleGroup (Cat ⟨.reeF4 m, hv⟩) :=
  have hm := reeTitsModel_cat_reeF4 hv
  ⟨CFSG.LieType.Simplicity.fam_ree_tits_finiteness _ _ _ _ hm,
    (CFSG.LieType.Simplicity.fam_2f4_simplicity _ _ _ hm).2⟩

theorem finiteSimple_G2 :
    ∀ d : ValidLieTypeIndex, IsG2Index d.1 → Finite (Cat d) ∧ IsSimpleGroup (Cat d) := by
  rintro ⟨d, hv⟩ ⟨q, rfl⟩
  exact finite_isSimpleGroup_cat_G2 hv

theorem finiteSimple_F4 :
    ∀ d : ValidLieTypeIndex, IsF4Index d.1 → Finite (Cat d) ∧ IsSimpleGroup (Cat d) := by
  rintro ⟨d, hv⟩ ⟨q, rfl⟩
  exact finite_isSimpleGroup_cat_F4 hv

theorem finiteSimple_triality :
    ∀ d : ValidLieTypeIndex, IsTrialityIndex d.1 → Finite (Cat d) ∧ IsSimpleGroup (Cat d) := by
  rintro ⟨d, hv⟩ ⟨q, rfl⟩
  exact finite_isSimpleGroup_cat_trialityD4 hv

theorem finiteSimple_reeF4 :
    ∀ d : ValidLieTypeIndex, IsReeF4Index d.1 → Finite (Cat d) ∧ IsSimpleGroup (Cat d) := by
  rintro ⟨d, hv⟩ ⟨m, rfl⟩
  exact finite_isSimpleGroup_cat_reeF4 hv

end Untwisted

end CFSG.LieType.SeitzGeneration
