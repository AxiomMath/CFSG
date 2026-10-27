module

public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.CTP.SeitzU5Eigen
public import CFSG.RankThree.PartOne.D4RC.CW6
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Open
  CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 TauCeti

section Ree


theorem map_baseChangeGL_reeGamma {t : ReeTag} {X k : Type} [Field X] [Finite X]
    [CharP X t.prime] [Field k] [Finite k] [CharP k t.prime] (φ : X ≃+* k) (b : ℕ) :
    (t.reeGamma X b).map (CFSG.LieType.Chevalley.baseChangeGL (φ : X →+* k)) =
      t.reeGamma k b := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxC, hxF⟩ := ReeTag.mem_reeGamma.1 hx
    refine ReeTag.mem_reeGamma.2
      ⟨CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hxC, ?_⟩
    have h := CFSG.SignalizerFunctorTheorem.CatalogBridge.baseChange_finiteReeAut (t := t)
      (φ : X →+* k) b ⟨x, hxC⟩
    rw [hxF] at h
    exact h.symm
  · intro hg
    obtain ⟨hgC, hgF⟩ := ReeTag.mem_reeGamma.1 hg
    have hmem : g ∈ (adjointGroup t.tag X).map
        (CFSG.LieType.Chevalley.baseChangeGL (φ : X →+* k)) := by
      rw [CFSG.TauCetiBridge.map_baseChangeGL_adjointGroup_eq φ]
      exact hgC
    obtain ⟨x, hxC, rfl⟩ := hmem
    refine ⟨x, ReeTag.mem_reeGamma.2 ⟨hxC, ?_⟩, rfl⟩
    refine CFSG.LieType.Chevalley.adjointBaseChangeHom_injective t.tag (φ : X →+* k) ?_
    rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.baseChange_finiteReeAut]
    exact hgF

@[expose] noncomputable def reeGammaCongr {t : ReeTag} {X k : Type} [Field X] [Finite X]
    [CharP X t.prime] [Field k] [Finite k] [CharP k t.prime] (φ : X ≃+* k) (b : ℕ) :
    t.reeGamma X b ≃* t.reeGamma k b :=
  ((t.reeGamma X b).equivMapOfInjective _
    (CFSG.LieType.Chevalley.baseChangeGL_injective (φ : X →+* k))).trans
    (MulEquiv.subgroupCongr (map_baseChangeGL_reeGamma φ b))

theorem reeGamma_equiv_cat_of_card {b : ℕ} (hb : 1 ≤ b) (hv : (LieTypeIndex.reeF4 b).Valid)
    {k : Type} [Field k] [Finite k] [CharP k F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    Nonempty (Cat ⟨.reeF4 b, hv⟩ ≃* F4.reeGamma k b) := by
  obtain ⟨X, _, _, _, -, hX, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : Fintype X := Fintype.ofFinite X
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card X = Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hX, hk]
  exact ⟨e.trans (reeGammaCongr (FiniteField.ringEquivOfCardEq hcard) b)⟩

end Ree

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
