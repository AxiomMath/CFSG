module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwTag
public import CFSG.LieType.SeitzGeneration.LinearOuterLocal

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GroupTheory

theorem planeGen_of_normalized_rSubgroup_graphFixedRootGroup
    (t : TwistTag) {K : Type} [Field K] [Finite K]
    {r : ℕ} [Fact r.Prime] [CharP K r] (hr2 : r ≠ 2)
    (σ : K ≃+* K) (hσ : σ ^ t.order = 1)
    [IsSimpleGroup ↥(graphFixedRootGroup t K σ.toRingHom)]
    (E : Subgroup (MulAut ↥(graphFixedRootGroup t K σ.toRingHom)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (R : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom))
    (hR : R ≠ ⊥) (hRr : IsPGroup r R)
    (hER : ∀ e ∈ E, R.map e.toMonoidHom = R) :
    CFSG.LieType.SeitzGeneration.PlaneGen E := by
  have := finite_modGL (τ := t.tag) (K := K)
  exact planeGen_of_normalized_rSubgroup_of_hasGoodOppositePRadicals hr2
    (fun Q hQ hQrad =>
      CFSG.StandardType.GGOppRadExc.hasGoodOppositePRadicals_top_graphFixedRootGroup
        t σ hσ hQ hQrad) E hE h4 R hR hRr hER

theorem planeGen_of_normalized_rSubgroup_twistedE6
    {K : Type} [Field K] [Finite K]
    {r f : ℕ} [Fact r.Prime] [CharP K r]
    (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (r ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (r ^ f))
    [IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)]
    (E : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (R : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hR : R ≠ ⊥) (hRr : IsPGroup r R)
    (hER : ∀ e ∈ E, R.map e.toMonoidHom = R) :
    CFSG.LieType.SeitzGeneration.PlaneGen E := by
  have _ := hf
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    show σ ^ 2 = 1
    refine RingEquiv.ext fun c => ?_
    have hq : r ^ f * r ^ f = Nat.card K := by rw [hK, pow_two]
    have h2 : σ (σ c) = c := by
      rw [hσ (σ c), hσ c, ← pow_mul, hq]
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [pow_two]
    simpa using h2
  exact planeGen_of_normalized_rSubgroup_graphFixedRootGroup TwistTag.E6 hr2 σ hσ2
    E hE h4 R hR hRr hER

end CFSG.LieType.SeitzGeneration
