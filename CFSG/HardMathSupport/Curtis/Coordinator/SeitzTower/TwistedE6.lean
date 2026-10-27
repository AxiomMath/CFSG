module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharDetCover
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding
  CFSG.HardMathSupport.Timmesfeld.DefChar
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section


theorem outTowerAt_twistedE6RootGroup {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    OutTowerAt (twistedE6RootGroup K σ) p := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hinn : (twistedE6Inn K σ).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hcomm : ∀ a b : RingAut K, a * b = b * a := fun a b =>
    (IsCyclic.commGroup (α := K ≃+* K)).mul_comm a b
  set D := Θ.ker with hD
  have hab : ∀ γ α : MulAut (twistedE6RootGroup K σ), (∃ k : ℕ, α ^ (p ^ k) = 1) →
      γ * α * γ⁻¹ * α⁻¹ ∈ D := by
    intro γ α _
    rw [hD, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm (Θ γ) (Θ α)]
    group
  refine outTowerAt_of_card_le D hab ?_
  set I := twistedE6Inn K σ with hI
  let ψ : D →* Outer (twistedE6RootGroup K σ) := (QuotientGroup.mk' I).comp D.subtype
  have hker : ψ.ker = I.subgroupOf D := by
    ext x
    simp [ψ, hI, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hψ3 := lot_card_range_diag_outer_le_three hK σ hσ
  have hrange : ψ.range ≤ ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hx' : x ∈ I ⊔ twistedE6Diag K σ := by rw [← hΘker]; exact hx
    obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
    refine ⟨u, ?_⟩
    change QuotientGroup.mk' (twistedE6Inn K σ) (compatDiagAutHom TwistTag.E6 K σ.toRingHom u) =
      QuotientGroup.mk' I x
    have hy1 : QuotientGroup.mk' I y = 1 := (QuotientGroup.eq_one_iff y).2 hy
    rw [← hyz, map_mul, hy1, one_mul]
  have hfin : Finite ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range := inferInstance
  have h1 : Nat.card (D ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  rw [hker] at h1
  change Nat.card (D ⧸ I.subgroupOf D) ≤ p
  have h2 : Nat.card ψ.range ≤ 3 := (Subgroup.card_le_of_le hrange).trans hψ3
  omega

theorem p1OffCharAlmostSimpleNonNormalAt_twistedE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.twistedE6 q, hv⟩ := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ : Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
    by_cases hq2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hq2 K
        (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
    · exact CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq2 K
        (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e := eB.symm.trans eC
  exact p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun p _ hp2 _ _ =>
    Or.inl (OutTowerAt.of_mulEquiv e
      (outTowerAt_twistedE6RootGroup q.prime_p hf hK2 σ hσ (by
        have := (Fact.out : p.Prime).two_le
        omega)))

end

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
