module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.ConjA0
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.BModelCore
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Lin
import CFSG.Dihedral.Glauberman.DicksonMaxTrace

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

@[expose] noncomputable def bModelPsi (P : D4ParOdd ℓ f X σ) :
    Matrix.SpecialLinearGroup (Fin 2) X ≃* (KS11Lie4Proof.d4ShortSL2 X σ.toRingHom) :=
  (MonoidHom.ofInjective (iotaAOdd_injective P)).trans (MulEquiv.subgroupCongr (iotaAOdd_range P))

theorem bModelPsi_coe (P : D4ParOdd ℓ f X σ) (A : Matrix.SpecialLinearGroup (Fin 2) X) :
    ((bModelPsi P A : KS11Lie4Proof.d4ShortSL2 X σ.toRingHom) : C0 σ) = iotaAOdd P A :=
  rfl

theorem fieldActor_eq_self_of_mem_centralizer (P : D4ParOdd ℓ f X σ) {c : C0 σ}
    (hc : c ∈ Subgroup.centralizer
      ((KS11Lie4Proof.d4ShortSL2 X σ.toRingHom : Subgroup (C0 σ)) : Set (C0 σ))) :
    fieldActor (t := TwistTag.D4) σ σ c = c := by
  haveI : Fact ℓ.Prime := ⟨P.prime⟩
  exact bModel_fieldActor_eq_self_of_mem_centralizer P.one_le P.ne_three P.card P.frob hc

theorem conj_mem_short_of_mem_cen (P : D4ParOdd ℓ f X σ) {z : C0 σ}
    (hzS : z ∈ Subgroup.centralizer
      ((KS11Lie4Proof.d4ShortSL2 X σ.toRingHom : Subgroup (C0 σ)) : Set (C0 σ)))
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {g : C0 σ} (hg : g * z = z * g) {s : C0 σ}
    (hs : s ∈ KS11Lie4Proof.d4ShortSL2 X σ.toRingHom) :
    g * s * g⁻¹ ∈ KS11Lie4Proof.d4ShortSL2 X σ.toRingHom := by
  have h := (KS11Lie6Proof.d4ThreeBCent_holds X (ℓ ^ f) σ P.card P.frob P.not_three_dvd z hzS
    hz3 hz1).1 g (Subgroup.mem_centralizer_singleton_iff.mpr hg) s
    (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzS s hs))
  have e : g * s * g⁻¹ = (g * s * g⁻¹ * s⁻¹) * s := by group
  rw [e]
  exact Subgroup.mul_mem _ h hs

theorem exists_GL2_action (P : D4ParOdd ℓ f X σ) {z : C0 σ}
    (hzS : z ∈ Subgroup.centralizer
      ((KS11Lie4Proof.d4ShortSL2 X σ.toRingHom : Subgroup (C0 σ)) : Set (C0 σ)))
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {g : C0 σ} (hg : g * z = z * g) :
    ∃ N : GL (Fin 2) X, ∀ A : Matrix.SpecialLinearGroup (Fin 2) X,
      g * ((bModelPsi P A : KS11Lie4Proof.d4ShortSL2 X σ.toRingHom) : C0 σ) * g⁻¹ =
        ((bModelPsi P (glConjSL N A) : KS11Lie4Proof.d4ShortSL2 X σ.toRingHom) : C0 σ) := by
  haveI := P.charP
  have h2 : (2 : X) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff X ℓ] at h'
    exact P.ne_two ((Nat.prime_dvd_prime_iff_eq P.prime Nat.prime_two).1 h')
  have hKm : (-1 : Xˣ) ≠ 1 := by
    intro h
    have h' : (-1 : X) = 1 := by simpa using congrArg Units.val h
    exact h2 (by linear_combination (-1 : X) * h')
  have hneg1 : (-1 : Matrix.SpecialLinearGroup (Fin 2) X) ≠ 1 := by
    intro h
    have h' := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) X =>
      (M : Matrix (Fin 2) (Fin 2) X) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h'
    exact h2 (by linear_combination (-1 : X) * h')
  have hσ3 := P.sigma_cube_hom
  have hι : ∀ A, eCOdd P (iotaAOdd P A) =
      CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom hσ3 A := fun A =>
    (eCOdd P).apply_symm_apply _
  have hrange : (twistedIncl σ.toRingHom).range = graphFixedRootGroup TwistTag.D4 X σ.toRingHom := by
    rw [graphFixed_eq_map_twisted_odd P, twistedIncl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hC₀ : graphFixedRootGroup TwistTag.D4 X σ.toRingHom ≤ (twistedIncl σ.toRingHom).range :=
    hrange.ge
  have hgF : ∀ g : CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom,
      twistedIncl σ.toRingHom g ∈ graphFixedRootGroup TwistTag.D4 X σ.toRingHom := fun g =>
    hrange ▸ (⟨g, rfl⟩ : twistedIncl σ.toRingHom g ∈ (twistedIncl σ.toRingHom).range)
  have hgcomm : g * iotaAOdd P (-1) = iotaAOdd P (-1) * g := by
    have hmem : g * iotaAOdd P (-1) * g⁻¹ ∈ (iotaAOdd P).range :=
      (iotaAOdd_range P).ge (conj_mem_short_of_mem_cen P hzS hz3 hz1 hg
        ((iotaAOdd_range P).le ⟨-1, rfl⟩))
    obtain ⟨B, hB⟩ := hmem
    have hB2 : B * B = 1 := by
      apply iotaAOdd_injective P
      rw [map_mul, hB, map_one]
      calc g * iotaAOdd P (-1) * g⁻¹ * (g * iotaAOdd P (-1) * g⁻¹) =
          g * iotaAOdd P ((-1) * (-1)) * g⁻¹ := by rw [map_mul]; group
        _ = 1 := by rw [neg_mul_neg, mul_one, map_one]; group
    rcases CFSG.Glauberman.Dickson.MaxTrace.eq_one_or_neg_of_mul_self h2 hB2 with h1 | h1
    · exfalso
      rw [h1, map_one] at hB
      apply hneg1
      apply iotaAOdd_injective P
      rw [map_one]
      have e : iotaAOdd P (-1) = g⁻¹ * (g * iotaAOdd P (-1) * g⁻¹) * g := by group
      rw [e, ← hB]
      group
    · rw [h1] at hB
      calc g * iotaAOdd P (-1) = (g * iotaAOdd P (-1) * g⁻¹) * g := by group
        _ = iotaAOdd P (-1) * g := by rw [← hB]
  have hx : eCOdd P g * CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom hσ3 (-1) =
      CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom hσ3 (-1) * eCOdd P g := by
    rw [← hι, ← map_mul, ← map_mul, hgcomm]
  obtain ⟨N, hN⟩ := linAct_of_centralizes_short hσ3 hKm h2 hC₀ hgF hx
  refine ⟨N, fun A => ?_⟩
  apply (eCOdd P).injective
  rw [bModelPsi_coe, bModelPsi_coe, map_mul, map_mul, map_inv, hι, hι]
  exact hN A

theorem mem_zpowers_of_mem_centralizer_short (P : D4ParOdd ℓ f X σ) {z b : C0 σ}
    (hzS : z ∈ Subgroup.centralizer
      ((KS11Lie4Proof.d4ShortSL2 X σ.toRingHom : Subgroup (C0 σ)) : Set (C0 σ)))
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hbS : b ∈ Subgroup.centralizer
      ((KS11Lie4Proof.d4ShortSL2 X σ.toRingHom : Subgroup (C0 σ)) : Set (C0 σ)))
    (hb3 : b ^ 3 = 1) (hbz : b * z = z * b) : b ∈ Subgroup.zpowers z := by
  haveI : Fact ℓ.Prime := ⟨P.prime⟩
  exact bModel_mem_zpowers_of_mem_centralizer P.one_le P.ne_three P.card P.frob hzS hz3 hz1 hbS hb3
    hbz

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
