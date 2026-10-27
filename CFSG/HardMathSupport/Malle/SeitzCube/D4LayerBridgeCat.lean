module

public import CFSG.HardMathSupport.Malle.SeitzCube.D4LayerBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open TauCeti CFSG.LieType.SeitzGeneration CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley

theorem graphFixedRootGroup_equiv_of_card {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {K K' : Type} [Field K] [Field K'] {σ : K →+* K} {σ' : K' →+* K'}
    (hK : Nat.card K = (ℓ ^ d) ^ 3) (hK' : Nat.card K' = (ℓ ^ d) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ d)) (hσ' : ∀ c, σ' c = c ^ (ℓ ^ d)) :
    Nonempty (graphFixedRootGroup TwistTag.D4 K σ ≃* graphFixedRootGroup TwistTag.D4 K' σ') := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hfin' : Finite K' := Nat.finite_of_card_ne_zero (by
    rw [hK']; exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K' := Fintype.ofFinite K'
  obtain ⟨ι⟩ : Nonempty (K ≃+* K') :=
    ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hK'])⟩
  have hmap := map_baseChangeGL_graphFixedRootGroup_eq TwistTag.D4 hℓ hd K hK σ hσ
    (ι : K →+* K') hσ' (Finite.surjective_of_injective σ'.injective)
  exact ⟨(Subgroup.equivMapOfInjective _ (baseChangeGL (ι : K →+* K'))
    (baseChangeGL_injective _)).trans (MulEquiv.subgroupCongr hmap)⟩

theorem nonempty_d4Layer_equiv_cat {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {σ : K →+* K} {Fr : Ω →+* Ω} (hK : Nat.card K = (ℓ ^ d) ^ 3)
    {e : ℕ} (he : e = 1 ∨ e = 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ d)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d))
    (hv : (LieTypeIndex.trialityD4 ⟨ℓ, d, hℓ, hd⟩).Valid) :
    Nonempty (d4Layer Fr e ≃* Cat ⟨.trialityD4 ⟨ℓ, d, hℓ, hd⟩, hv⟩) := by
  obtain ⟨φ, -⟩ := exists_d4Layer_equiv (Ω := Ω) hℓ hd hK he hσ hFr
  obtain ⟨K', _, _, σ', hK', hσ', -, ⟨c⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 ⟨ℓ, d, hℓ, hd⟩ hv
  obtain ⟨m⟩ := graphFixedRootGroup_equiv_of_card hℓ hd hK hK' hσ
    (σ' := σ'.toRingHom) hσ'
  exact ⟨φ.trans (m.trans c.symm)⟩

end CFSG.HardMathSupport.Malle.SeitzCube
