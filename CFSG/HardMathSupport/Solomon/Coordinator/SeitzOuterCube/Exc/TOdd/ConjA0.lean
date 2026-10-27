module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Par
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTau

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.Sec19

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

section Plain

theorem sl2_three_conj_subfield_odd {F : Type} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    (k : Subfield F) (x : Matrix.SpecialLinearGroup (Fin 2) F) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, ∃ y : Matrix.SpecialLinearGroup (Fin 2) k,
      g * x * g⁻¹ = Matrix.SpecialLinearGroup.map k.subtype y := by
  obtain ⟨hB3, hB1⟩ := KS11Lie4Proof.sl2Three_pow_three F
  obtain ⟨A, hA⟩ := Item1118Res3Proof.exists_conj_of_pow_three h3 hx3 hx1 hB3 hB1
  refine ⟨A, KS11Lie4Proof.sl2Three k, ?_⟩
  rw [hA]
  apply Subtype.ext
  show (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) F) =
    k.subtype.mapMatrix (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) k)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Plain

section Model

variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem three_ne_zero_odd (P : D4ParOdd ℓ f X σ) : (3 : X) ≠ 0 := by
  haveI := P.charP
  intro h
  have h1 : ℓ ∣ 3 := (CharP.cast_eq_zero_iff X ℓ 3).1 (by exact_mod_cast h)
  exact P.ne_three ((Nat.prime_dvd_prime_iff_eq P.prime Nat.prime_three).1 h1)

theorem graphFixed_eq_map_twisted_odd (P : D4ParOdd ℓ f X σ) :
    graphFixedRootGroup TwistTag.D4 X σ.toRingHom =
      (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom).map
        (adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X).subtype := by
  have hq2 : 2 ≤ ℓ ^ f := le_trans (by norm_num) P.five_le
  exact (finite_fixed_root_group_perfect TwistTag.D4 P.prime P.one_le X P.card
      σ.toRingHom P.frob).2.2.1.symm.trans
    (CFSG.LieType.Steinberg.TwistedD4.commutator_twistedFixedGroup_eq_map σ.toRingHom hq2 P.card
      P.frob)

@[expose] noncomputable def eCOdd (P : D4ParOdd ℓ f X σ) :
    C0 σ ≃* CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom :=
  CFSG.RankThree.PartOne.SEITZ8.eGamma (graphFixed_eq_map_twisted_odd P)

theorem coe_eCOdd (P : D4ParOdd ℓ f X σ) (x : C0 σ) :
    (((eCOdd P x : CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
      adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
        ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) = (x : ModGL TwistTag.D4.tag X) :=
  CFSG.RankThree.PartOne.SEITZ8.coe_eGamma (graphFixed_eq_map_twisted_odd P) x

@[expose] noncomputable def iotaAOdd (P : D4ParOdd ℓ f X σ) :
    Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ :=
  (eCOdd P).symm.toMonoidHom.comp
    (CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom)

theorem iotaAOdd_injective (P : D4ParOdd ℓ f X σ) : Function.Injective (iotaAOdd P) :=
  (eCOdd P).symm.injective.comp
    (CFSG.LieType.Steinberg.TwistedD4.slShort_injective (σ := σ.toRingHom)
      P.sigma_cube_hom)

theorem coe_iotaAOdd (P : D4ParOdd ℓ f X σ) (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    ((iotaAOdd P g : C0 σ) : ModGL TwistTag.D4.tag X) =
      (((CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom g :
        CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) :
          adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 X) :
            ModGL CFSG.LieType.Steinberg.TwistedD4.d4 X) := by
  have h1 := coe_eCOdd P (iotaAOdd P g)
  have h2 : eCOdd P (iotaAOdd P g) =
      CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom P.sigma_cube_hom g :=
    (eCOdd P).apply_symm_apply _
  rw [h2] at h1
  exact h1.symm

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_upper_xA_odd (σ' : X →+* X) (hσ : ∀ c, σ' (σ' (σ' c)) = c) (c : X) :
    ((slShort σ' hσ (CFSG.LieType.Steinberg.sl2Upper c) : twistedGroup σ') : adjointGroup d4 X) =
      xA σ' c := by
  rw [slShort_upper]
  simp only [xOuter, xA, ← d4Root_dict.2.2.1, ← d4Root_dict.2.2.2.1, ← d4Root_dict.2.2.2.2.1]

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_lower_xAm_odd (σ' : X →+* X) (hσ : ∀ c, σ' (σ' (σ' c)) = c) (c : X) :
    ((slShort σ' hσ (CFSG.LieType.Steinberg.sl2Lower c) : twistedGroup σ') : adjointGroup d4 X) =
      xAm σ' c := by
  rw [slShort_lower]
  simp only [xOuter, xAm, ← d4Root_dict.2.2.2.2.2.1, ← d4Root_dict.2.2.2.2.2.2.1,
    ← d4Root_dict.2.2.2.2.2.2.2]

@[expose] noncomputable def orbitInclOdd (P : D4ParOdd ℓ f X σ) :
    X →+* orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer :=
  (RingHom.id X).codRestrict _ (fun c => KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three c)

theorem map_orbitInclOdd_surjective (P : D4ParOdd ℓ f X σ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (orbitInclOdd P) :
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
  show orbitInclOdd P ((g'.1 i j).1) = g'.1 i j
  exact Subtype.ext rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_upper_eq_orbit_odd (P : D4ParOdd ℓ f X σ) (c : X) :
    (((slShort σ.toRingHom P.sigma_cube_hom (CFSG.LieType.Steinberg.sl2Upper c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (uSL (⟨c, KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three c⟩ :
        orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer)) := by
  have h1 := congrArg (fun y : adjointGroup d4 X => (y : ModGL d4 X))
    (slShort_upper_xA_odd σ.toRingHom P.sigma_cube_hom c)
  refine h1.trans ?_
  rw [orbitRankOneHom_uSL, coe_orbitX]
  obtain ⟨h0, h1', h2⟩ := orbit_perm_vals
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [orbit_card_three, hr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h0, h1', h2]
  have e0 : ((σ.toRingHom ^ 0) c) = c := rfl
  have e1 : ((σ.toRingHom ^ 1) c) = σ c := by simp
  have e2 : ((σ.toRingHom ^ 2) c) = σ (σ c) := by simp [pow_two]
  rw [e0, e1, e2]
  simp only [xA, Subgroup.coe_mul]
  rw [xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_0,
    xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_1,
    xd_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_3, mul_assoc]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_lower_eq_orbit_odd (P : D4ParOdd ℓ f X σ) (c : X) :
    (((slShort σ.toRingHom P.sigma_cube_hom (CFSG.LieType.Steinberg.sl2Lower c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (vSL (⟨c, KS11Lie4Proof.mem_orbitField_d4Outer P.sigma_pow_three c⟩ :
        orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer)) := by
  have h1 := congrArg (fun y : adjointGroup d4 X => (y : ModGL d4 X))
    (slShort_lower_xAm_odd σ.toRingHom P.sigma_cube_hom c)
  refine h1.trans ?_
  rw [orbitRankOneHom_vSL, coe_orbitY]
  obtain ⟨h0, h1', h2⟩ := orbit_perm_vals
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [orbit_card_three, hr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h0, h1', h2]
  have e0 : ((σ.toRingHom ^ 0) c) = c := rfl
  have e1 : ((σ.toRingHom ^ 1) c) = σ c := by simp
  have e2 : ((σ.toRingHom ^ 2) c) = σ (σ c) := by simp [pow_two]
  rw [e0, e1, e2]
  simp only [xAm, Subgroup.coe_mul]
  rw [xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_0,
    xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_1,
    xd_neg_simple_unit _ CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_3, mul_assoc]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem slShort_eq_orbit_odd (P : D4ParOdd ℓ f X σ) (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    (((slShort σ.toRingHom P.sigma_cube_hom g : twistedGroup σ.toRingHom) :
      adjointGroup d4 X) : ModGL d4 X) =
    orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
      (Matrix.SpecialLinearGroup.map (orbitInclOdd P) g) := by
  let Φ₂ : Matrix.SpecialLinearGroup (Fin 2) X →* ModGL d4 X :=
    (adjointGroup d4 X).subtype.comp ((twistedGroup σ.toRingHom).subtype.comp
      (slShort σ.toRingHom P.sigma_cube_hom))
  let Φ₁ : Matrix.SpecialLinearGroup (Fin 2) X →* ModGL TwistTag.D4.tag X :=
    (orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer).comp
      (Matrix.SpecialLinearGroup.map (orbitInclOdd P))
  have hgen : Set.EqOn Φ₂ Φ₁ (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X)) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have h := slShort_upper_eq_orbit_odd P c
      have e : Matrix.SpecialLinearGroup.map (orbitInclOdd P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X c) = uSL (orbitInclOdd P c) :=
        map_uSL (f := orbitInclOdd P) c
      show _ = orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        (Matrix.SpecialLinearGroup.map (orbitInclOdd P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X c))
      rw [e]
      exact h
    · have h := slShort_lower_eq_orbit_odd P c
      have e : Matrix.SpecialLinearGroup.map (orbitInclOdd P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X c) = vSL (orbitInclOdd P c) :=
        map_vSL (f := orbitInclOdd P) c
      show _ = orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
        (Matrix.SpecialLinearGroup.map (orbitInclOdd P)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X c))
      rw [e]
      exact h
  exact MonoidHom.eqOn_closure hgen
    (by rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := X)]
        exact Set.mem_univ _)

theorem iotaAOdd_range (P : D4ParOdd ℓ f X σ) : (iotaAOdd P).range = Asub σ := by
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) X,
      ((iotaAOdd P g : C0 σ) : ModGL TwistTag.D4.tag X) =
        orbitRankOneHom TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer
          (Matrix.SpecialLinearGroup.map (orbitInclOdd P) g) := by
    intro g
    rw [coe_iotaAOdd P g]
    exact slShort_eq_orbit_odd P g
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact Subgroup.mem_comap.mpr ⟨Matrix.SpecialLinearGroup.map (orbitInclOdd P) g, (key g).symm⟩
  · intro hx
    obtain ⟨g', hg'⟩ := Subgroup.mem_comap.mp hx
    obtain ⟨g, rfl⟩ := map_orbitInclOdd_surjective P g'
    refine ⟨g, Subtype.ext ?_⟩
    rw [key g]
    exact hg'

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem entrywise_xA_odd (c : X) :
    Units.map (entrywiseHom σ.toRingHom) ((xA σ.toRingHom c : adjointGroup d4 X) : ModGL d4 X) =
      ((xA σ.toRingHom (σ c) : adjointGroup d4 X) : ModGL d4 X) := by
  simp only [xA, Subgroup.coe_mul, map_mul]
  rw [CFSG.RankThree.PartOne.SEITZ8.entrywise_xe_simple σ.toRingHom (nd 0)
      CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_0 c,
    CFSG.RankThree.PartOne.SEITZ8.entrywise_xe_simple σ.toRingHom (nd 1)
      CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_1,
    CFSG.RankThree.PartOne.SEITZ8.entrywise_xe_simple σ.toRingHom (nd 3)
      CFSG.RankThree.PartOne.SEITZ8.d4Root_simple_3]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4 in
theorem entrywise_xAm_odd (c : X) :
    Units.map (entrywiseHom σ.toRingHom) ((xAm σ.toRingHom c : adjointGroup d4 X) : ModGL d4 X) =
      ((xAm σ.toRingHom (σ c) : adjointGroup d4 X) : ModGL d4 X) := by
  simp only [xAm, Subgroup.coe_mul, map_mul]
  rw [CFSG.RankThree.PartOne.SEITZ8.entrywise_xe_neg σ.toRingHom (nd 0)
      CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_0 c,
    CFSG.RankThree.PartOne.SEITZ8.entrywise_xe_neg σ.toRingHom (nd 1)
      CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_1,
    CFSG.RankThree.PartOne.SEITZ8.entrywise_xe_neg σ.toRingHom (nd 3)
      CFSG.RankThree.PartOne.SEITZ8.d4Root_neg_3]
  rfl

open CFSG.RankThree.PartOne.SEITZ7 CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint in
theorem tau_iotaAOdd (P : D4ParOdd ℓ f X σ) (g : Matrix.SpecialLinearGroup (Fin 2) X) :
    tauAut σ (iotaAOdd P g) = iotaAOdd P (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  let Ψ₁ : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ := (tauAut σ).toMonoidHom.comp (iotaAOdd P)
  let Ψ₂ : Matrix.SpecialLinearGroup (Fin 2) X →* C0 σ :=
    (iotaAOdd P).comp (Matrix.SpecialLinearGroup.map σ.toRingHom)
  have hgen : Set.EqOn Ψ₁ Ψ₂ (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X)) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · apply Subtype.ext
      show ((tauAut σ (iotaAOdd P (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) :
          ModGL TwistTag.D4.tag X) =
        ((iotaAOdd P (Matrix.SpecialLinearGroup.map σ.toRingHom
          (CFSG.LieType.Steinberg.sl2Upper c)) : C0 σ) : ModGL TwistTag.D4.tag X)
      have e : Matrix.SpecialLinearGroup.map σ.toRingHom (CFSG.LieType.Steinberg.sl2Upper c) =
          CFSG.LieType.Steinberg.sl2Upper (σ c) := map_uSL (f := σ.toRingHom) c
      rw [e, coe_tauAut, coe_iotaAOdd, coe_iotaAOdd, slShort_upper_xA_odd, slShort_upper_xA_odd]
      exact entrywise_xA_odd c
    · apply Subtype.ext
      show ((tauAut σ (iotaAOdd P (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) :
          ModGL TwistTag.D4.tag X) =
        ((iotaAOdd P (Matrix.SpecialLinearGroup.map σ.toRingHom
          (CFSG.LieType.Steinberg.sl2Lower c)) : C0 σ) : ModGL TwistTag.D4.tag X)
      have e : Matrix.SpecialLinearGroup.map σ.toRingHom (CFSG.LieType.Steinberg.sl2Lower c) =
          CFSG.LieType.Steinberg.sl2Lower (σ c) := map_vSL (f := σ.toRingHom) c
      rw [e, coe_tauAut, coe_iotaAOdd, coe_iotaAOdd, slShort_lower_xAm_odd, slShort_lower_xAm_odd]
      exact entrywise_xAm_odd c
  have hmem : g ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper X) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower X)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := X)]
    exact Subgroup.mem_top g
  exact MonoidHom.eqOn_closure hgen hmem

theorem mem_A0sub_iff_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ} :
    x ∈ A0sub σ ↔ ∃ y : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
      x = iotaAOdd P (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype y) := by
  constructor
  · rintro ⟨hA, hG⟩
    rw [← iotaAOdd_range P] at hA
    obtain ⟨g, rfl⟩ := hA
    have hτ : tauAut σ (iotaAOdd P g) = iotaAOdd P g := hG
    rw [tau_iotaAOdd P g] at hτ
    have h1 := iotaAOdd_injective P hτ
    obtain ⟨y, hy⟩ := (sl2_map_sigma_eq_iff σ g).mp h1
    exact ⟨y, by rw [← hy]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← iotaAOdd_range P]
      exact ⟨_, rfl⟩
    · show tauAut σ (iotaAOdd P _) = iotaAOdd P _
      rw [tau_iotaAOdd P, (sl2_map_sigma_eq_iff σ _).mpr ⟨y, rfl⟩]

theorem exists_conj_A0_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ} (hx : x ∈ Asub σ)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : ∃ g ∈ Asub σ, g * x * g⁻¹ ∈ A0sub σ := by
  rw [← iotaAOdd_range P] at hx
  obtain ⟨x', rfl⟩ := hx
  have hx'3 : x' ^ 3 = 1 := by
    apply iotaAOdd_injective P
    rw [map_pow, map_one]
    exact hx3
  have hx'1 : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨g, y, hg⟩ :=
    sl2_three_conj_subfield_odd (three_ne_zero_odd P) (fixSubfield σ) x' hx'3 hx'1
  refine ⟨iotaAOdd P g, ?_, ?_⟩
  · rw [← iotaAOdd_range P]
    exact ⟨g, rfl⟩
  · rw [← map_mul, ← map_inv, ← map_mul, hg]
    exact (mem_A0sub_iff_odd P).mpr ⟨y, rfl⟩

end Model

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
