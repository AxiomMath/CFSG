module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Tools

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem model_adjointGroup_F4
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) :
    ChevalleyExceptionalModel ↥(adjointGroup .F4 k) .F4 2 f :=
  ⟨⟨Nat.prime_two, hf, rfl⟩, k, inferInstance, inferInstance, hk,
    ⟨QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).symm⟩⟩

theorem F4_centralizer_not_isPGroup
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hF4 : InvolutionCentralizerNotTwoGroup .F4) (s : adjointGroup .F4 k) (hs : orderOf s = 2) :
    ¬ IsPGroup 2 (↥(centralizer ({s} : Set (adjointGroup .F4 k))) ⧸
      pPrimeCore 2 ↥(centralizer ({s} : Set (adjointGroup .F4 k)))) := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  have := finite_modGL (τ := Tag.F4) (K := k)
  have hsimp : IsSimpleGroup ↥(adjointGroup .F4 k) :=
    ExcSelector.isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 k)
  have h := inner_not_isPGroup (Y := ↥(adjointGroup .F4 k)) (C := ↥(adjointGroup .F4 k))
    (MulEquiv.refl _)
    (fun c hc2 hc1 => isCharacteristicP_centralizer (RootWeightDatum.ordinary Tag.F4) hc2 hc1)
    (hF4 _ f (model_adjointGroup_F4 hf hk) hsimp) s hs
  rwa [Ree.fixedPoints_conj] at h

end CFSG.ComponentClassification.HarrisLit.L33.E2
