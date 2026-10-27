module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal.E8Diag
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

theorem outerComm_graphFixedRootGroup_D4
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    OuterComm (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact outerComm_of_hom (SeitzNonNormal.ringEquiv_mul_comm_of_finite K) Θ hker.le
  · obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
    exact outerComm_of_hom (SeitzNonNormal.ringEquiv_mul_comm_of_finite K) Θ hker.le

theorem p1OffCharAlmostSimpleNonNormalAt_trialityD4
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    CFSG.AGLEmbedding.P1OffCharAlmostSimpleNonNormalAt ⟨.trialityD4 q, hv⟩ := by
  obtain ⟨-, hm⟩ := chevalleyModel_cat_trialityD4 hv
  have hm' : TwistedChevalleyModel (Cat ⟨.trialityD4 q, hv⟩) .D4 (q.p ^ q.exponent) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 q.prime_p q.exponent_pos hm'
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm
    (OuterComm.of_mulEquiv e (outerComm_graphFixedRootGroup_D4 q.prime_p q.exponent_pos K hK σ hσ))

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
