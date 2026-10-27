module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.Chevalley
  (twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer subfieldRootGroupImage)

set_option linter.unusedSectionVars false


theorem lieCompExport_twE6_field
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ p = 1) (hη1 : Θ β ≠ 1) :
    LieCompExport ℓ β := by
  classical
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K hK
      σ hσ Θ hΘ hp hp2 β hβ hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, hcardk, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 (hp.odd_of_ne_two hp2) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ) with hJdef
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  haveI : Finite (fixSubfield κ) := Subtype.finite
  haveI : Finite C := Subtype.finite
  have eJC : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  haveI := hsimpleJ
  have hJs : IsSimpleGroup (J.subgroupOf C) := eJC.isSimpleGroup
  have hJn : ∃ x y : J.subgroupOf C, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  let q' : TauCeti.PrimePower := ⟨ℓ, d, hℓ, hd1⟩
  have hv' : (TauCeti.LieTypeIndex.twistedE6 q').Valid := TauCeti.LieTypeIndex.valid_twistedE6 q'
  have hcardk' : Nat.card (fixSubfield κ) = q'.card ^ 2 := by
    rw [hcardk, TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]
  have hσ₀k : ∀ c, (fixSubfieldRestrict T κ) c = c ^ q'.card := fun c =>
    Subtype.ext (by rw [hσ₀ c, TauCeti.PrimePower.card_def]; rfl)
  obtain ⟨eCat⟩ := catEquiv_twistedE6_of_field q' hv' (fixSubfield κ) hcardk'
    (fixSubfieldRestrict T κ) hσ₀k
  let eXJ : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom) ≃*
      ↥J :=
    (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom).equivMapOfInjective
      (baseChangeGL (fixSubfield κ).subtype) (baseChangeGL_injective _)
  let eX : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom) ≃*
      ↥(J.subgroupOf C) := eXJ.trans eJC.symm
  haveI : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom) := eX.isSimpleGroup
  have hXnc : ∃ a b : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hJn
    exact ⟨eX.symm x, eX.symm y, fun h => hxy (eX.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hchev := isChevSimple_of_lie (q := ℓ) ⟨.twistedE6 q', hv'⟩
    (by simp [TauCeti.LieTypeIndex.characteristic_twistedE6, q']) eCat.symm
  have hexp : LieCompExport ℓ δ := by
    refine lieCompExport_of_derived_eq_simple hder hJs hJn ?_ ?_
    · haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
          (fixSubfieldRestrict T κ).toRingHom) := Finite.of_equiv _ eX.toEquiv.symm
      refine ⟨_, inferInstance, inferInstance, lieFactorData_of_simple hXnc hchev,
        eX.toMonoidHom, eX.surjective, ?_⟩
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have : x = 1 := eX.injective (by rw [map_one]; exact hx)
      rw [this]
      exact one_mem _
    · exact isEmpty_quotient_center_alt6 (b3Lie_center_eq_bot hJn)
        ⟨fun f => (hA6 q' hv').false (eCat.trans (eX.trans f))⟩
  have hrβ : LieCompExport ℓ (β ^ r) := by
    refine lieCompExport_of_conj ψ (β ^ r) ?_
    rw [hψ]
    exact hexp
  exact lieCompExport_of_fixSubgroup_eq (fixSubgroup_pow_eq_of_pow_pow' hrs) hrβ

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
