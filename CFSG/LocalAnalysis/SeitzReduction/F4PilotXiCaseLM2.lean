module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignLevi
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RootSpace
open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.E6Pilot (corootTuple rootChar_corootTuple
  rootDiagUnit_corootTuple_mem_adjointGroup)

local instance f4PilotXiCaseLM2NeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance f4PilotXiCaseLM2NeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def xiLRootOne : Fin (Tag.rank .E6) → ℤ := ![0, 0, 1, 1, 1, 0]

@[expose] def xiLRootTwo : Fin (Tag.rank .E6) → ℤ := ![1, 0, 1, 1, 1, 1]

@[expose] def xiLRootThree : Fin (Tag.rank .E6) → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def xiLPerpRoots : List (Fin (Tag.rank .E6) → ℤ) := [xiLRootOne, xiLRootTwo, xiLRootThree]

@[expose] def xiLPerpVec : Fin (Tag.rank .E6) → ℤ :=
  xiLRootOne + (5 : ℤ) • xiLRootTwo + (25 : ℤ) • xiLRootThree

theorem xiLPerpRoots_check : ∀ δ ∈ xiLPerpRoots, δ ∈ rootFinset .E6 ∧
    permLattice rhoE6 δ = δ ∧ iform δ (Pi.single 3 1) = 0 := by
  decide +kernel

theorem xiLPerp_kernel_check : ∀ γ ∈ rootFinset .E6, (∀ δ ∈ xiLPerpRoots, iform δ γ = 0) →
    ∀ i : Fin (Tag.rank .E6), i ≠ 3 → γ i = 0 := by
  decide +kernel

theorem xiLPerpVec_check : ∀ α ∈ rootFinset .E6, iform α xiLPerpVec = 0 →
    ∀ i : Fin (Tag.rank .E6), i ≠ 3 → α i = 0 := by
  decide +kernel

@[expose] def xiLTupleSet (A : Subgroup Kˣ) : Set (Fin (Tag.rank .E6) → Kˣ) :=
  {a | ∃ δ ∈ xiLPerpRoots, ∃ c ∈ A, corootTuple δ c = a}

section KernelWeyl


theorem coeff_eq_zero_of_mem_toralSetKernel_xiLTupleSet {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ toralSetKernel (xiLTupleSet A)) :
    ∀ i ∉ ({3} : Set (Fin (Tag.rank .E6))), γ i = 0 := by
  obtain ⟨c, hcA, hc⟩ := exists_mem_orderOf_eq_natCard hA
  intro i hi
  refine xiLPerp_kernel_check γ (mem_rootFinset.2 hγ.1) (fun δ hδ => ?_) i hi
  have hδR : IsRoot .E6 δ := mem_rootFinset.1 (xiLPerpRoots_check δ hδ).1
  have h1 := hγ.2 _ ⟨δ, hδ, c, hcA, rfl⟩
  rw [rootChar_corootTuple, ← orderOf_dvd_iff_zpow_eq_one, hc] at h1
  refine Int.eq_zero_of_abs_lt_dvd h1 ?_
  have := abs_le.1 (E6Pilot.abs_iform_le_two hδR hγ.1)
  have h3 : (3 : ℤ) ≤ ((Nat.card A : ℕ) : ℤ) := by exact_mod_cast hA
  rw [abs_lt]
  constructor <;> omega

theorem smul_apply_eq_of_forall_mem_xiLPerpRoots {w : WeylGroup .E6}
    (hw : ∀ δ ∈ xiLPerpRoots, w • δ = δ) :
    ∀ v : Fin (Tag.rank .E6) → ℤ, ∀ i ∉ ({3} : Set (Fin (Tag.rank .E6))), (w • v) i = v i := by
  have h1 := hw _ (List.mem_cons_self ..)
  have h2 := hw _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3 := hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hfix : w • xiLPerpVec = xiLPerpVec := by
    rw [xiLPerpVec, smul_add, smul_add, smul_comm w (5 : ℤ), smul_comm w (25 : ℤ), h1, h2, h3]
  have hstab : w ∈ weylStabilizer .E6 (ofLattice xiLPerpVec) := by
    rw [mem_weylStabilizer, weylAct_apply, weylLinear_ofLattice, hfix]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E6).2.2.2.2.2] at hstab
  obtain ⟨c0, hc0, hinner⟩ := E6Pilot.exists_inner_ofLattice_eq_iform_E6
  have hle : Subgroup.closure {s | ∃ α, IsRoot .E6 α ∧
      inner ℝ (ofLattice α) (ofLattice xiLPerpVec) = 0 ∧ s = rootReflection α} ≤
      parabolicWeylGroup .E6 ({3} : Set (Fin (Tag.rank .E6))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨α, hα, h0, rfl⟩
    have hα0 : iform α xiLPerpVec = 0 := by
      rw [hinner] at h0
      exact_mod_cast (mul_eq_zero.1 h0).resolve_left hc0.ne'
    have hαJ := xiLPerpVec_check α (mem_rootFinset.2 hα) hα0
    rw [(parabolic_Weyl_coordinate_stabilizer .E6 _).1]
    intro v i hi
    rw [rootReflection_smul hα, Pi.sub_apply, Pi.smul_apply, hαJ i hi, smul_zero, sub_zero]
  have hwJ := hle hstab
  rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer .E6 _).1] at hwJ
  exact fun v i hi => hwJ v i hi

theorem smul_apply_eq_of_mem_rootCharStabilizer_xiLTupleSet {A : Subgroup Kˣ}
    (hA : 3 ≤ Nat.card A) {w : WeylGroup .E6}
    (hw : ∀ a ∈ xiLTupleSet A, w ∈ rootCharStabilizer a) :
    ∀ v : Fin (Tag.rank .E6) → ℤ, ∀ i ∉ ({3} : Set (Fin (Tag.rank .E6))), (w • v) i = v i := by
  obtain ⟨c, hcA, hc⟩ := exists_mem_orderOf_eq_natCard hA
  refine smul_apply_eq_of_forall_mem_xiLPerpRoots fun δ hδ => ?_
  exact E6Pilot.smul_eq_of_mem_rootCharStabilizer_corootTuple
    (mem_rootFinset.1 (xiLPerpRoots_check δ hδ).1) (hc ▸ hA) (hw _ ⟨δ, hδ, c, hcA, rfl⟩)

end KernelWeyl

section Bound


theorem perfectCore_le_rootSpan_alpha4_of_forall_conj_eq {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {H : Subgroup (ModGL .E6 K)}
    (hH : ∀ g ∈ H, g ∈ adjointGroup .E6 K ∧ ∀ δ ∈ xiLPerpRoots, ∀ c ∈ A,
      rootDiagUnit .E6 (corootTuple δ c) * g * (rootDiagUnit .E6 (corootTuple δ c))⁻¹ = g) :
    perfectCore H ≤ rootSpan .E6 K (signedSimpleRoots ({3} : Set (Fin (Tag.rank .E6)))) :=
  perfectCore_le_rootSpan_of_forall_conj_eq (xiLTupleSet A) ({3} : Set (Fin (Tag.rank .E6)))
    (fun _ hγ _ => coeff_eq_zero_of_mem_toralSetKernel_xiLTupleSet hA hγ)
    (fun _ hw => smul_apply_eq_of_mem_rootCharStabilizer_xiLTupleSet hA hw)
    fun g hg => ⟨(hH g hg).1, by
      rintro _ ⟨δ, hδ, c, hc, rfl⟩
      exact (hH g hg).2 δ hδ c hc⟩

end Bound

theorem permLattice_rhoE6_single_three :
    permLattice rhoE6 (Pi.single (3 : Fin (Tag.rank .E6)) (1 : ℤ)) = Pi.single 3 1 := by
  decide +kernel

theorem xiLPerpRoots_iform_rho_check : ∀ δ ∈ xiLPerpRoots, ∀ i : Fin (Tag.rank .E6),
    iform δ (Pi.single (rhoE6 i) 1) = iform δ (Pi.single i 1) := by
  decide +kernel

section Diagram


theorem diagramMap_conj_eq_of_mem_rootSpan_alpha4 (h2 : (2 : K) = 0)
    {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ rootSpan TwistTag.E6.tag K (signedSimpleRoots ({3} : Set (Fin (Tag.rank .E6))))) :
    diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g := by
  have hle : rootSpan TwistTag.E6.tag K (signedSimpleRoots ({3} : Set (Fin (Tag.rank .E6)))) ≤
      centralizer ({diagramMap TwistTag.E6 K} : Set (ModGL TwistTag.E6.tag K)) := by
    rw [rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨α, hα, c, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hαR : IsRoot TwistTag.E6.tag α := isRoot_of_mem_signedSimpleRoots hα
    have hperm : permLattice TwistTag.E6.perm α = α := by
      obtain ⟨j, hj, rfl | rfl⟩ := hα
      · rw [Set.mem_singleton_iff.1 hj]
        exact permLattice_rhoE6_single_three
      · rw [Set.mem_singleton_iff.1 hj, permLattice_neg]
        exact congrArg Neg.neg permLattice_rhoE6_single_three
    have h := twistHom_id_pinnedX h2 hαR c
    rw [twistHom_id_eq, hperm] at h
    calc pinnedX TwistTag.E6.tag K α c * diagramMap TwistTag.E6 K =
        diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K α c *
          (diagramMap TwistTag.E6 K)⁻¹ * diagramMap TwistTag.E6 K := by rw [h]
      _ = diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K α c := by group
  have h := mem_centralizer_singleton_iff.1 (hle hg)
  rw [← h, mul_inv_cancel_right]

end Diagram

theorem rootChar_eq_rootChar_e6ToF4 {a : Fin Tag.E6.rank → Kˣ} (ha : ∀ i, a (rhoE6 i) = a i)
    (β : Fin Tag.E6.rank → ℤ) :
    rootChar a β = rootChar (fun j => a (f4IndexRep j)) (e6ToF4 β) := by
  have h5 : a 5 = a 0 := ha 0
  have h4 : a 4 = a 2 := ha 2
  have hL : rootChar a β =
      a 0 ^ β 0 * a 1 ^ β 1 * a 2 ^ β 2 * a 3 ^ β 3 * a 4 ^ β 4 * a 5 ^ β 5 := by
    unfold rootChar
    exact Fin.prod_univ_six _
  have hR : rootChar (fun j => a (f4IndexRep j)) (e6ToF4 β) =
      a 1 ^ β 1 * a 3 ^ β 3 * a 2 ^ (β 2 + β 4) * a 0 ^ (β 0 + β 5) := by
    unfold rootChar
    exact Fin.prod_univ_four _
  rw [hL, hR, h5, h4, zpow_add, zpow_add]
  set A0 := a 0 ^ β 0
  set A5 := a 0 ^ β 5
  set A1 := a 1 ^ β 1
  set A2 := a 2 ^ β 2
  set A4 := a 2 ^ β 4
  set A3 := a 3 ^ β 3
  calc A0 * A1 * A2 * A3 * A4 * A5 = A1 * A3 * (A2 * A4) * (A0 * A5) := by
        rw [mul_comm A0 A1, mul_assoc A1 A0 A2, mul_comm A0 A2, ← mul_assoc A1 A2 A0,
          mul_assoc (A1 * A2) A0 A3, mul_comm A0 A3, ← mul_assoc (A1 * A2) A3 A0,
          mul_assoc A1 A2 A3, mul_comm A2 A3, ← mul_assoc A1 A3 A2,
          mul_assoc (A1 * A3 * A2) A0 A4, mul_comm A0 A4, ← mul_assoc (A1 * A3 * A2) A4 A0]
        simp only [mul_assoc]

theorem rootDiag_apply {τ : Tag} (a : Fin τ.rank → Kˣ) (v : RootModule τ K) (b : Label τ) :
    rootDiag a v b = ((rootChar a (labelWt τ b) : Kˣ) : K) * v b := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hv, hw, mul_add]
  | single b' r =>
    rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, rootDiag_single]
    by_cases h : b' = b
    · subst h
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
      ring
    · have h0 : (Finsupp.single b' (1 : K)) b = 0 := by
        simp only [Finsupp.single_apply, h, ↓reduceIte]
      simp only [Finsupp.smul_apply, h0, smul_eq_mul, mul_zero]

theorem labelWt_e6LabelToF4
    (b : Label Tag.E6) : labelWt Tag.F4 (e6LabelToF4 b) = e6ToF4 (labelWt Tag.E6 b) := by
  rcases b with i | β
  · funext j
    simp only [e6LabelToF4, labelWt, e6ToF4, Pi.zero_apply]
    fin_cases j <;> rfl
  · rfl


theorem e6FixedToF4_rootDiagUnit {a : Fin Tag.E6.rank → Kˣ} (ha : ∀ i, a (rhoE6 i) = a i)
    (hmem : rootDiagUnit TwistTag.E6.tag a ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    e6FixedToF4 K ⟨_, hmem⟩ = rootDiagUnit .F4 (fun j => a (f4IndexRep j)) := by
  refine Units.ext ?_
  rw [coe_e6FixedToF4]
  have hcomm : rootDiag a ∘ₗ f4ToE6Module K =
      f4ToE6Module K ∘ₗ rootDiag (fun j => a (f4IndexRep j)) := by
    refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
    ext b
    simp only [LinearMap.comp_apply]
    rw [rootDiag_apply, f4ToE6Module_apply, f4ToE6Module_apply, rootDiag_apply]
    by_cases h : e6LabelToF4 b = c
    · rw [← h, labelWt_e6LabelToF4, ← rootChar_eq_rootChar_e6ToF4 ha]
    · have h' : ¬ c = e6LabelToF4 b := fun h'' => h h''.symm
      have h0 : (Finsupp.lsingle (R := K) c (1 : K)) (e6LabelToF4 b) = 0 := by
        simp only [Finsupp.lsingle_apply, Finsupp.single_apply, h', ↓reduceIte]
      rw [h0, mul_zero, mul_zero]
  change e6ToF4Module K ∘ₗ rootDiag a ∘ₗ f4ToE6Module K = rootDiag (fun j => a (f4IndexRep j))
  rw [hcomm, ← LinearMap.comp_assoc, e6ToF4Module_comp_f4ToE6Module, LinearMap.id_comp]

theorem corootTuple_rhoE6 {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ xiLPerpRoots) (c : Kˣ)
    (i : Fin Tag.E6.rank) : corootTuple δ c (rhoE6 i) = corootTuple δ c i := by
  simp only [corootTuple]
  rw [xiLPerpRoots_iform_rho_check δ hδ i]

theorem rootDiagUnit_corootTuple_mem_twistedFixedGroup {δ : Fin Tag.E6.rank → ℤ}
    (hδ : δ ∈ xiLPerpRoots) (c : Kˣ) :
    rootDiagUnit TwistTag.E6.tag (corootTuple δ c) ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (RingHom.id K)).2
    ⟨rootDiagUnit_corootTuple_mem_adjointGroup δ c, twistHom_rootDiagUnit fun i => ?_⟩
  exact corootTuple_rhoE6 hδ c i

theorem e6FixedToF4_corootTuple_mem_leviTorus {δ : Fin Tag.E6.rank → ℤ}
    (hδ : δ ∈ xiLPerpRoots) (c : Kˣ) :
    e6FixedToF4 K ⟨_, rootDiagUnit_corootTuple_mem_twistedFixedGroup hδ c⟩ ∈
      leviTorus K ({1} : Finset (Fin (Tag.rank .F4))) := by
  rw [e6FixedToF4_rootDiagUnit (corootTuple_rhoE6 hδ c)]
  refine rootDiagUnit_mem_leviTorus fun j hj => ?_
  rw [Finset.mem_singleton.1 hj]
  change c ^ iform δ (Pi.single 3 1) = 1
  rw [(xiLPerpRoots_check δ hδ).2.2, zpow_zero]

end CFSG.SeitzReduction.F4Pilot
