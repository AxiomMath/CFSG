module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Datum
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Timmesfeld.ExceptionalOrders


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

theorem surjective_of_finite : Function.Surjective σ :=
  Finite.surjective_of_injective σ.injective

include hf hK hσ in
theorem card_orbitField_e6 (a : Fin TwistTag.E6.foldedTag.rank) :
    Nat.card (orbitField TwistTag.E6 K σ a) = (2 ^ f) ^ (TwistTag.E6.orbit a).card :=
  card_orbitField Nat.prime_two hf hK hσ a

include hf hK hσ in
@[expose] def twistedE6Datum :
    CurtisDatum ↥(graphFixedRootGroup TwistTag.E6 K σ) (relCs TwistTag.E6) 2 :=
  twistedDatum 2 e6LongestData (surjective_of_finite σ) (card_orbitField_e6 hf hK σ hσ)

@[expose] def derivedCentralQuotientEquiv {t : TwistTag} {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    DerivedCentralQuotient (twistedFixedGroup t K σ) ≃* ↥(graphFixedRootGroup t K σ) := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have h3 := (finite_fixed_root_group_perfect t hp hf K hK σ hσ).2.2.1
  set σ' := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩
  have hσ' : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  have hZ := exceptional_fixed_center_trivial t K σ'
  rw [hσ'] at hZ
  let e1 : ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ ≃*
      ↥(graphFixedRootGroup t K σ) := MulEquiv.subgroupCongr h3
  have hc : Subgroup.center ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : e1 x ∈ Subgroup.center ↥(graphFixedRootGroup t K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := e1.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g]
    rw [hZ, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact e1.injective (hx'.trans (map_one e1).symm)
  exact (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e1)

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
