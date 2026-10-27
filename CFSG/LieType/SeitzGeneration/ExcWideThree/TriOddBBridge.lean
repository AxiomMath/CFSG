module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddJ
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddCore
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open scoped MatrixGroups

section Prelim

variable {X : Type} [Field X] [Finite X]

theorem triOdd_two_le_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) : 2 ≤ ℓ ^ f :=
  calc 2 ≤ ℓ := hℓ.two_le
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf

theorem triOdd_ringChar_ne_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) : ringChar X ≠ 2 := by
  have hX' : Nat.card X = ℓ ^ (3 * f) := by rw [hX, ← pow_mul]; ring_nf
  haveI : CharP X ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 3 * f) (by omega) hX'
  rw [ringChar.eq X ℓ]
  exact hℓ2

end Prelim

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)


@[expose] noncomputable def triOddOrbitIncl (h3 : ∀ c : X, σ (σ (σ c)) = c) :
    X →+* orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer :=
  (RingHom.id X).codRestrict _ fun c => by
    rw [orbitField_D4_zero_eq_top σ h3]
    exact Subfield.mem_top c


theorem map_triOddOrbitIncl_surjective (h3 : ∀ c : X, σ (σ (σ c)) = c) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ h3) :
      Matrix.SpecialLinearGroup (Fin 2) X →*
        Matrix.SpecialLinearGroup (Fin 2) (orbitField TwistTag.D4 X σ.toRingHom
          KS11Lie4Proof.d4Outer)) := by
  intro g'
  let v : orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer →+* X := Subfield.subtype _
  have hdet : (v.mapMatrix g'.1).det = 1 := by
    rw [← RingHom.map_det, g'.2, map_one]
  refine ⟨⟨v.mapMatrix g'.1, hdet⟩, ?_⟩
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  show triOddOrbitIncl σ h3 ((g'.1 i j).1) = g'.1 i j
  exact Subtype.ext rfl

section Orbit

variable (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

include hσ3

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem triOdd_slShort_upper_eq_orbit (c : X) :
    (((slShort σ.toRingHom hσ3 (CFSG.LieType.Steinberg.sl2Upper c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (uSL (triOddOrbitIncl σ hσ3 c)) := by
  have h1 := congrArg (fun y : adjointGroup d4 X => (y : ModGL d4 X))
    (CFSG.HardMathSupport.Seitz.TrialityOdd.slShort_upper_xA_odd hσ3 c)
  refine h1.trans ?_
  rw [orbitRankOneHom_uSL, coe_orbitX]
  obtain ⟨h0, h1', h2⟩ := orbit_perm_vals
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [orbit_card_three, hr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h0, h1', h2]
  have hv : ((triOddOrbitIncl σ hσ3 c : orbitField TwistTag.D4 X σ.toRingHom
      KS11Lie4Proof.d4Outer) : X) = c := rfl
  have e0 : ((σ.toRingHom ^ 0) c) = c := rfl
  have e1 : ((σ.toRingHom ^ 1) c) = σ c := by simp
  have e2 : ((σ.toRingHom ^ 2) c) = σ (σ c) := by simp [pow_two]
  rw [hv, e0, e1, e2]
  simp only [Subgroup.coe_mul]
  rw [xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_0,
    xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_1,
    xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_3, mul_assoc]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem triOdd_slShort_lower_eq_orbit (c : X) :
    (((slShort σ.toRingHom hσ3 (CFSG.LieType.Steinberg.sl2Lower c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (vSL (triOddOrbitIncl σ hσ3 c)) := by
  have h1 := congrArg (fun y : adjointGroup d4 X => (y : ModGL d4 X))
    (CFSG.HardMathSupport.Seitz.TrialityOdd.slShort_lower_xAm_odd hσ3 c)
  refine h1.trans ?_
  rw [orbitRankOneHom_vSL, coe_orbitY]
  obtain ⟨h0, h1', h2⟩ := orbit_perm_vals
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [orbit_card_three, hr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h0, h1', h2]
  have hv : ((triOddOrbitIncl σ hσ3 c : orbitField TwistTag.D4 X σ.toRingHom
      KS11Lie4Proof.d4Outer) : X) = c := rfl
  have e0 : ((σ.toRingHom ^ 0) c) = c := rfl
  have e1 : ((σ.toRingHom ^ 1) c) = σ c := by simp
  have e2 : ((σ.toRingHom ^ 2) c) = σ (σ c) := by simp [pow_two]
  rw [hv, e0, e1, e2]
  simp only [Subgroup.coe_mul]
  rw [xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_0,
    xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_1,
    xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_3, mul_assoc]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem triOdd_slShort_eq_orbit (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    (((slShort σ.toRingHom hσ3 g : twistedGroup σ.toRingHom) :
      adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3) g) := by
  let Φ₂ : Matrix.SpecialLinearGroup (Fin 2) X →* ModGL d4 X :=
    (adjointGroup d4 X).subtype.comp ((twistedGroup σ.toRingHom).subtype.comp
      (slShort σ.toRingHom hσ3))
  let Φ₁ : Matrix.SpecialLinearGroup (Fin 2) X →* ModGL TwistTag.D4.tag X :=
    (orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer).comp
      (Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3))
  have hgen : Set.EqOn Φ₂ Φ₁ (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X)) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have h := triOdd_slShort_upper_eq_orbit σ hσ3 c
      have e : Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X c) = uSL (triOddOrbitIncl σ hσ3 c) :=
        CFSG.LieType.Chevalley.map_uSL (triOddOrbitIncl σ hσ3) c
      show _ = orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        (Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X c))
      rw [e]
      exact h
    · have h := triOdd_slShort_lower_eq_orbit σ hσ3 c
      have e : Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X c) = vSL (triOddOrbitIncl σ hσ3 c) :=
        CFSG.LieType.Chevalley.map_vSL (triOddOrbitIncl σ hσ3) c
      show _ = orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        (Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X c))
      rw [e]
      exact h
  exact MonoidHom.eqOn_closure hgen
    (by rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := X)]
        exact Set.mem_univ _)

end Orbit

section Main

open CFSG.LieType.Steinberg.TwistedD4

theorem triOdd_eqRoot_slShort_coe (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (hK2 : ringChar X ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hX : Nat.card X = q ^ 3)
    (hσ : ∀ c : X, σ c = c ^ q) (M : Matrix.SpecialLinearGroup (Fin 2) X) :
    ((triOddEqRoot σ hK2 hq hX hσ (slShort σ.toRingHom hσ3 M) : C0 σ) :
        ModGL TwistTag.D4.tag X) =
      orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        (Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3) M) := by
  rw [triOddEqRoot_coe]
  exact triOdd_slShort_eq_orbit σ hσ3 M

theorem triOdd_eqRoot_slShort_mem_Asub {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (_hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (M : Matrix.SpecialLinearGroup (Fin 2) X) :
    triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hX) (triOdd_two_le_pow hℓ hf) hX hσ
      (slShort σ.toRingHom hσ3 M) ∈ Asub σ :=
  Subgroup.mem_comap.mpr ⟨Matrix.SpecialLinearGroup.map (triOddOrbitIncl σ hσ3) M,
    (triOdd_eqRoot_slShort_coe σ hσ3 (triOdd_ringChar_ne_two hℓ hℓ2 hf hX)
      (triOdd_two_le_pow hℓ hf) hX hσ M).symm⟩

theorem triOdd_Asub_eq_eqRoot_slShort {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (_hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) (a : C0 σ) (ha : a ∈ Asub σ) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) X,
      triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hX) (triOdd_two_le_pow hℓ hf) hX hσ
        (slShort σ.toRingHom hσ3 M) = a := by
  obtain ⟨g', hg'⟩ := Subgroup.mem_comap.mp ha
  obtain ⟨M, rfl⟩ := map_triOddOrbitIncl_surjective σ hσ3 g'
  exact ⟨M, Subtype.ext ((triOdd_eqRoot_slShort_coe σ hσ3 (triOdd_ringChar_ne_two hℓ hℓ2 hf hX)
    (triOdd_two_le_pow hℓ hf) hX hσ M).trans hg')⟩

theorem triOdd_slShort_injective (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) :
    Function.Injective (slShort σ.toRingHom hσ3) :=
  CFSG.LieType.Steinberg.TwistedD4.slShort_injective (σ := σ.toRingHom) hσ3

end Main


end Model

end CFSG.LieType.SeitzGeneration.ExcWideThree
