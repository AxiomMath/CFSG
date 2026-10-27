module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignLeviCheck
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignTori

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RootSpace

local instance twistedE6PilotAlignLeviWeylNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotAlignLeviWeylNeZeroE6' : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotAlignLeviWeylNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def relTupleSet (A : Subgroup Kˣ) (I : Finset (Fin Tag.F4.rank)) :
    Set (Fin TwistTag.E6.tag.rank → Kˣ) :=
  {a | ∃ B ∈ F4Pilot.leviTupleSet A I, relTuple B = a}

theorem apply_eq_one_of_mem_relTupleSet {A : Subgroup Kˣ} {I : Finset (Fin Tag.F4.rank)}
    {a : Fin TwistTag.E6.tag.rank → Kˣ} (ha : a ∈ relTupleSet A I) :
    ∀ j ∈ (relNodeSet I : Set (Fin TwistTag.E6.tag.rank)), a j = 1 := by
  rintro j hj
  obtain ⟨B, hB, rfl⟩ := ha
  exact hB.1 _ (mem_relNodeSet.1 hj)

theorem coeff_eq_zero_of_mem_toralSetKernel_relTupleSet
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : γ ∈ F4Pilot.toralSetKernel (relTupleSet A I)) :
    ∀ i ∉ (relNodeSet I : Set (Fin TwistTag.E6.tag.rank)), γ i = 0 := by
  have h : e6ToF4 γ ∈ F4Pilot.toralSetKernel (F4Pilot.leviTupleSet A I) :=
    ⟨isRoot_e6ToF4 hγ.1, fun B hB => by
      rw [← rootChar_relTuple]
      exact hγ.2 _ ⟨B, hB, rfl⟩⟩
  exact fun i hi => (forall_e6ToF4_eq_zero_iff hγ.1).1
    (F4Pilot.coeff_eq_zero_of_mem_toralSetKernel_leviTupleSet hA hI h) i hi

theorem dvd_e6ToF4_smul_sub {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} {w : WeylGroup TwistTag.E6.tag}
    (hw : ∀ a ∈ relTupleSet A I, w ∈ rootCharStabilizer a) :
    ∀ b ∉ I, ∀ v : Fin TwistTag.E6.tag.rank → ℤ,
      ((Nat.card A : ℕ) : ℤ) ∣ e6ToF4 (w • v) b - e6ToF4 v b := by
  intro b hb v
  obtain ⟨c, hcA, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  have h1 : rootChar (relTuple (Pi.mulSingle b c)) (w • v) =
      rootChar (relTuple (Pi.mulSingle b c)) v :=
    hw _ ⟨_, F4Pilot.mulSingle_mem_leviTupleSet hb hcA, rfl⟩ v
  rw [rootChar_relTuple, rootChar_relTuple, F4Pilot.rootChar_mulSingle_apply,
    F4Pilot.rootChar_mulSingle_apply] at h1
  rw [← hc, orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1, mul_inv_cancel]

@[expose] def relGen (I : Finset (Fin Tag.F4.rank)) : Fin TwistTag.E6.tag.rank → ℤ :=
  ∑ b ∈ Finset.univ \ I, (10 : ℤ) ^ (b : ℕ) • relWeight b

theorem relGen_check : ∀ I : Finset (Fin Tag.F4.rank), ∀ α ∈ rootFinset TwistTag.E6.tag,
    iform α (relGen I) = 0 → ∀ i : Fin TwistTag.E6.tag.rank, i ∉ relNodeSet I → α i = 0 := by
  decide +kernel

section Stabilizer

theorem exists_inner_ofLattice_eq_iform_twistedE6 :
    ∃ c : ℝ, 0 < c ∧ ∀ u v : Fin TwistTag.E6.tag.rank → ℤ,
      inner ℝ (ofLattice u) (ofLattice v) = c * (iform u v : ℝ) := by
  obtain ⟨c, hc, h⟩ := exists_inner_eq_smul TwistTag.E6.tag
  refine ⟨c, hc, fun u v => ?_⟩
  rw [h]
  congr 1
  simp only [ofLattice_apply, iform, Int.cast_sum, Int.cast_mul]

theorem smul_relWeight_eq {w : WeylGroup TwistTag.E6.tag} {b : Fin Tag.F4.rank}
    (h : ∀ j : Fin TwistTag.E6.tag.rank,
      e6ToF4 (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) b =
        e6ToF4 (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) b) :
    w • relWeight b = relWeight b := by
  have h1 : w⁻¹ • relWeight b = relWeight b := by
    refine sub_eq_zero.1 (EPilot.eq_zero_of_forall_iform_single_eq_zero fun j => ?_)
    rw [iform_sub_left, ← iform_smul w (w⁻¹ • relWeight b), smul_inv_smul, iform_relWeight,
      iform_relWeight, h j, sub_self]
  calc w • relWeight b = w • (w⁻¹ • relWeight b) := by rw [h1]
    _ = relWeight b := smul_inv_smul w _

theorem smul_relGen_eq {w : WeylGroup TwistTag.E6.tag} {I : Finset (Fin Tag.F4.rank)}
    (h : ∀ b ∉ I, w • relWeight b = relWeight b) : w • relGen I = relGen I := by
  rw [relGen, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [smul_comm, h b (Finset.mem_sdiff.1 hb).2]

theorem smul_apply_eq_of_smul_relGen_eq {w : WeylGroup TwistTag.E6.tag}
    {I : Finset (Fin Tag.F4.rank)} (hfix : w • relGen I = relGen I) :
    ∀ v : Fin TwistTag.E6.tag.rank → ℤ, ∀ i ∉ relNodeSet I, (w • v) i = v i := by
  have hstab : w ∈ weylStabilizer TwistTag.E6.tag (ofLattice (relGen I)) := by
    rw [mem_weylStabilizer, weylAct_apply, weylLinear_ofLattice, hfix]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers TwistTag.E6.tag).2.2.2.2.2] at hstab
  obtain ⟨c0, hc0, hinner⟩ := exists_inner_ofLattice_eq_iform_twistedE6
  have hle : Subgroup.closure {s | ∃ α, IsRoot TwistTag.E6.tag α ∧
      inner ℝ (ofLattice α) (ofLattice (relGen I)) = 0 ∧ s = rootReflection α} ≤
      parabolicWeylGroup TwistTag.E6.tag (relNodeSet I : Set (Fin TwistTag.E6.tag.rank)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨α, hα, h0, rfl⟩
    have hα0 : iform α (relGen I) = 0 := by
      rw [hinner] at h0
      exact_mod_cast (mul_eq_zero.1 h0).resolve_left hc0.ne'
    have hαJ := relGen_check I α (mem_rootFinset.2 hα) hα0
    rw [(parabolic_Weyl_coordinate_stabilizer TwistTag.E6.tag _).1]
    intro v i hi
    rw [rootReflection_smul hα, Pi.sub_apply, Pi.smul_apply, hαJ i hi, smul_zero, sub_zero]
  have hwJ := hle hstab
  rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer TwistTag.E6.tag _).1] at hwJ
  exact fun v i hi => hwJ v i hi

theorem smul_apply_eq_of_forall_e6ToF4 {w : WeylGroup TwistTag.E6.tag}
    {I : Finset (Fin Tag.F4.rank)}
    (h : ∀ b ∉ I, ∀ j : Fin TwistTag.E6.tag.rank,
      e6ToF4 (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) b =
        e6ToF4 (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) b) :
    ∀ v : Fin TwistTag.E6.tag.rank → ℤ, ∀ i ∉ relNodeSet I, (w • v) i = v i :=
  smul_apply_eq_of_smul_relGen_eq (smul_relGen_eq fun b hb => smul_relWeight_eq (h b hb))

end Stabilizer

theorem smul_eq_sum_smul_single {τ : Tag} (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ k, v k • (w • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm w (v k) _

theorem e6ToF4_single_check : ∀ (j : Fin Tag.E6.rank) (b : Fin Tag.F4.rank),
    e6ToF4 (Pi.single j 1 : Fin Tag.E6.rank → ℤ) b = 0 ∨
      e6ToF4 (Pi.single j 1 : Fin Tag.E6.rank → ℤ) b = 1 := by
  decide

theorem iform_single_tuple_values :
    iform (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) (Pi.single 1 1) = -1 ∧
    iform (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = -1 ∧
    iform (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = 0 ∧
    iform (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = -1 ∧
    iform (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 0 ∧
    iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 0 ∧
    iform (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = 0 ∧
    iform (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = 0 ∧
    iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = -1 ∧
    iform (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = 0 ∧
    iform (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 ∧
    iform (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 ∧
    iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 ∧
    iform (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = -1 ∧
    iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 := by
  decide

abbrev TupleCheck (m : ℤ) (I : Finset (Fin Tag.F4.rank)) : Prop :=
  ∀ b3 ∈ rootFinset Tag.E6, RelCong m I b3 3 →
  ∀ b1 ∈ rootFinset Tag.E6, RelCong m I b1 1 → iform b3 b1 = -1 →
  ∀ b2 ∈ rootFinset Tag.E6, RelCong m I b2 2 → iform b3 b2 = -1 → iform b1 b2 = 0 →
  ∀ b4 ∈ rootFinset Tag.E6, RelCong m I b4 4 → iform b3 b4 = -1 → iform b1 b4 = 0 →
    iform b2 b4 = 0 →
  ∀ b0 ∈ rootFinset Tag.E6, RelCong m I b0 0 → iform b3 b0 = 0 → iform b1 b0 = 0 →
    iform b2 b0 = -1 → iform b4 b0 = 0 →
  ∀ b5 ∈ rootFinset Tag.E6, RelCong m I b5 5 → iform b3 b5 = 0 → iform b1 b5 = 0 →
    iform b2 b5 = 0 → iform b4 b5 = -1 → iform b0 b5 = 0 →
  RelExact I b0 0 ∧ RelExact I b1 1 ∧ RelExact I b2 2 ∧ RelExact I b3 3 ∧
    RelExact I b4 4 ∧ RelExact I b5 5

section Weyl

theorem smul_single_mem_rootFinset (w : WeylGroup Tag.E6) (j : Fin Tag.E6.rank) :
    w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset Tag.E6 :=
  mem_rootFinset.2 (IsRoot.smul (isRoot_single _ j) w)

theorem e6ToF4_smul_single_eq_of_tupleCheck {m : ℤ} {I : Finset (Fin Tag.F4.rank)}
    (hcheck : TupleCheck m I) {w : WeylGroup Tag.E6}
    (hcong : ∀ b ∉ I, ∀ v : Fin Tag.E6.rank → ℤ, m ∣ e6ToF4 (w • v) b - e6ToF4 v b) :
    ∀ b ∉ I, ∀ j : Fin Tag.E6.rank,
      e6ToF4 (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) b =
        e6ToF4 (Pi.single j 1 : Fin Tag.E6.rank → ℤ) b := by
  have hm := smul_single_mem_rootFinset w
  have hc : ∀ j, RelCong m I (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) j :=
    fun j a ha => hcong a ha _
  obtain ⟨g31, g32, g12, g34, g14, g24, g30, g10, g20, g40, g35, g15, g25, g45, g05⟩ :=
    iform_single_tuple_values
  have hg := fun {i j : Fin Tag.E6.rank} {c : ℤ}
    (h : iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) = c) =>
      (iform_smul w (Pi.single i 1) (Pi.single j 1)).trans h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcheck _ (hm 3) (hc 3) _ (hm 1) (hc 1) (hg g31) _ (hm 2) (hc 2)
    (hg g32) (hg g12) _ (hm 4) (hc 4) (hg g34) (hg g14) (hg g24) _ (hm 0) (hc 0) (hg g30)
    (hg g10) (hg g20) (hg g40) _ (hm 5) (hc 5) (hg g35) (hg g15) (hg g25) (hg g45) (hg g05)
  intro b hb j
  revert j
  change ∀ j : Fin 6, e6ToF4 (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) b =
    e6ToF4 (Pi.single j 1 : Fin Tag.E6.rank → ℤ) b
  intro j
  fin_cases j
  exacts [h0 b hb, h1 b hb, h2 b hb, h3 b hb, h4 b hb, h5 b hb]

theorem e6ToF4_smul_single_eq_of_six_le {m : ℕ} (hm : 6 ≤ m) {I : Finset (Fin Tag.F4.rank)}
    {w : WeylGroup Tag.E6}
    (hcong : ∀ b ∉ I, ∀ v : Fin Tag.E6.rank → ℤ, (m : ℤ) ∣ e6ToF4 (w • v) b - e6ToF4 v b) :
    ∀ b ∉ I, ∀ j : Fin Tag.E6.rank,
      e6ToF4 (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) b =
        e6ToF4 (Pi.single j 1 : Fin Tag.E6.rank → ℤ) b := by
  intro b hb j
  have hroot := isRoot_e6ToF4 (IsRoot.smul (isRoot_single Tag.E6 j) w)
  have hbd := (F4Pilot.leviTorusOf_root_check _ (mem_rootFinset.2 hroot)).1 b
  have h01 := e6ToF4_single_check j b
  refine sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd (hcong b hb _) ?_)
  have hm' : (6 : ℤ) ≤ m := by exact_mod_cast hm
  rw [abs_le] at hbd
  rw [abs_lt]
  rcases h01 with h | h <;> rw [h] <;> constructor <;> omega

theorem commutator_smul_apply_eq_of_mem_tuples {T : List (Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ)}
    {Js : Finset (Fin Tag.E6.rank)}
    (hpair : ∀ t ∈ T, ∀ t' ∈ T, ∀ j i : Fin Tag.E6.rank, i ∉ Js →
      ∑ k, t' j k * t k i = ∑ k, t j k * t' k i)
    {w₁ w₂ : WeylGroup Tag.E6} (h₁ : (fun j => w₁ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ∈ T)
    (h₂ : (fun j => w₂ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ∈ T) :
    ∀ v : Fin Tag.E6.rank → ℤ, ∀ i ∉ Js, ((w₁ * w₂ * w₁⁻¹ * w₂⁻¹) • v) i = v i := by
  have hsingle : ∀ j, ∀ i ∉ Js, ((w₁ * w₂) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i =
      ((w₂ * w₁) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i := by
    intro j i hi
    rw [mul_smul, mul_smul, smul_eq_sum_smul_single w₁ (w₂ • _),
      smul_eq_sum_smul_single w₂ (w₁ • _), Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hpair _ h₁ _ h₂ j i hi
  have hall : ∀ x : Fin Tag.E6.rank → ℤ, ∀ i ∉ Js, ((w₁ * w₂) • x) i = ((w₂ * w₁) • x) i := by
    intro x i hi
    rw [smul_eq_sum_smul_single (w₁ * w₂) x, smul_eq_sum_smul_single (w₂ * w₁) x,
      Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [Pi.smul_apply, smul_eq_mul, hsingle j i hi]
  intro v i hi
  have e : w₁ * w₂ * w₁⁻¹ * w₂⁻¹ = (w₁ * w₂) * (w₂ * w₁)⁻¹ := by group
  rw [e, mul_smul, hall _ i hi, ← mul_smul, mul_inv_cancel, one_smul]

theorem tuple6_smul_single (w : WeylGroup Tag.E6) :
    tuple6 (w • Pi.single 0 1) (w • Pi.single 1 1) (w • Pi.single 2 1) (w • Pi.single 3 1)
        (w • Pi.single 4 1) (w • Pi.single 5 1) =
      fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  funext j
  revert j
  change ∀ j : Fin 6, _ = _
  intro j
  fin_cases j <;> rfl

theorem psiW_eq_tuple (w : WeylGroup Tag.E6) :
    psiW w = (w • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 -
      (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) 0 -
      (w • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 := by
  rw [psiW]
  change ∑ j : Fin 6, classVec j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) 0 = _
  rw [Fin.sum_univ_six]
  change 1 * (w • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 +
      0 * (w • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ)) 0 +
      (-1) * (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) 0 +
      0 * (w • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) 0 +
      1 * (w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) 0 +
      (-1) * (w • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 = _
  ring

abbrev CompleteCheck (I : Finset (Fin Tag.F4.rank))
    (T : List (Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ)) : Prop :=
  ∀ b3 ∈ rootFinset Tag.E6, RelCong 3 I b3 3 →
  ∀ b1 ∈ rootFinset Tag.E6, RelCong 3 I b1 1 → iform b3 b1 = -1 →
  ∀ b2 ∈ rootFinset Tag.E6, RelCong 3 I b2 2 → iform b3 b2 = -1 → iform b1 b2 = 0 →
  ∀ b4 ∈ rootFinset Tag.E6, RelCong 3 I b4 4 → iform b3 b4 = -1 → iform b1 b4 = 0 →
    iform b2 b4 = 0 →
  ∀ b0 ∈ rootFinset Tag.E6, RelCong 3 I b0 0 → iform b3 b0 = 0 → iform b1 b0 = 0 →
    iform b2 b0 = -1 → iform b4 b0 = 0 →
  ∀ b5 ∈ rootFinset Tag.E6, RelCong 3 I b5 5 → iform b3 b5 = 0 → iform b1 b5 = 0 →
    iform b2 b5 = 0 → iform b4 b5 = -1 → iform b0 b5 = 0 →
    (b0 0 - b2 0 + b4 0 - b5 0) % 3 = 1 → tuple6 b0 b1 b2 b3 b4 b5 ∈ T

theorem smul_single_mem_of_completeCheck {I : Finset (Fin Tag.F4.rank)}
    {T : List (Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ)} (hcheck : CompleteCheck I T)
    {w : WeylGroup Tag.E6}
    (hcong : ∀ b ∉ I, ∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ e6ToF4 (w • v) b - e6ToF4 v b) :
    (fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ∈ T := by
  have hm := smul_single_mem_rootFinset w
  have hc : ∀ j, RelCong 3 I (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) j :=
    fun j a ha => hcong a ha _
  obtain ⟨g31, g32, g12, g34, g14, g24, g30, g10, g20, g40, g35, g15, g25, g45, g05⟩ :=
    iform_single_tuple_values
  have hg := fun {i j : Fin Tag.E6.rank} {c : ℤ}
    (h : iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) = c) =>
      (iform_smul w (Pi.single i 1) (Pi.single j 1)).trans h
  have hψ : ((w • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 -
      (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) 0 -
      (w • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0) % 3 = 1 := by
    rw [← psiW_eq_tuple]
    exact psiW_emod w
  have h := hcheck _ (hm 3) (hc 3) _ (hm 1) (hc 1) (hg g31) _ (hm 2) (hc 2)
    (hg g32) (hg g12) _ (hm 4) (hc 4) (hg g34) (hg g14) (hg g24) _ (hm 0) (hc 0) (hg g30)
    (hg g10) (hg g20) (hg g40) _ (hm 5) (hc 5) (hg g35) (hg g15) (hg g25) (hg g45) (hg g05) hψ
  rwa [tuple6_smul_single] at h

end Weyl

section Main

theorem relNodeSet_bad_check : ∀ i : Fin Tag.E6.rank,
    (e6IndexToF4 i ∉ ({0, 1} : Finset (Fin Tag.F4.rank)) →
        i ∉ ({1, 3} : Finset (Fin Tag.E6.rank))) ∧
      (e6IndexToF4 i ∉ ({0, 2} : Finset (Fin Tag.F4.rank)) →
        i ∉ ({1, 2, 4} : Finset (Fin Tag.E6.rank))) ∧
      (e6IndexToF4 i ∉ ({0, 3} : Finset (Fin Tag.F4.rank)) →
        i ∉ ({0, 1, 5} : Finset (Fin Tag.E6.rank))) ∧
      (e6IndexToF4 i ∉ ({1, 3} : Finset (Fin Tag.F4.rank)) →
        i ∉ ({0, 3, 5} : Finset (Fin Tag.E6.rank))) := by
  decide

theorem smul_comm_apply_eq_of_mem_relTupleSet {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) {w₁ w₂ : WeylGroup TwistTag.E6.tag}
    (hw₁ : ∀ a ∈ relTupleSet A I, w₁ ∈ rootCharStabilizer a)
    (hw₂ : ∀ a ∈ relTupleSet A I, w₂ ∈ rootCharStabilizer a) :
    ∀ v : Fin TwistTag.E6.tag.rank → ℤ, ∀ i ∉ (relNodeSet I : Set (Fin TwistTag.E6.tag.rank)),
      ((w₁ * w₂ * w₁⁻¹ * w₂⁻¹) • v) i = v i := by
  have hc₁ := dvd_e6ToF4_smul_sub hA hw₁
  have hc₂ := dvd_e6ToF4_smul_sub hA hw₂
  have hgood : (∀ w : WeylGroup TwistTag.E6.tag, (∀ b ∉ I, ∀ v : Fin TwistTag.E6.tag.rank → ℤ,
      ((Nat.card A : ℕ) : ℤ) ∣ e6ToF4 (w • v) b - e6ToF4 v b) →
        ∀ b ∉ I, ∀ j : Fin TwistTag.E6.tag.rank,
          e6ToF4 (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) b =
            e6ToF4 (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) b) →
      ∀ v : Fin TwistTag.E6.tag.rank → ℤ, ∀ i ∉ (relNodeSet I : Set (Fin TwistTag.E6.tag.rank)),
        ((w₁ * w₂ * w₁⁻¹ * w₂⁻¹) • v) i = v i := by
    intro h
    have m₁ : w₁ ∈ parabolicWeylGroup TwistTag.E6.tag (relNodeSet I : Set _) := by
      rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer _ _).1]
      exact smul_apply_eq_of_forall_e6ToF4 (h w₁ hc₁)
    have m₂ : w₂ ∈ parabolicWeylGroup TwistTag.E6.tag (relNodeSet I : Set _) := by
      rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer _ _).1]
      exact smul_apply_eq_of_forall_e6ToF4 (h w₂ hc₂)
    have mc := mul_mem (mul_mem (mul_mem m₁ m₂) (inv_mem m₁)) (inv_mem m₂)
    rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer _ _).1] at mc
    exact mc
  have hcast : ∀ {n : ℕ}, Nat.card A = n → ∀ w : WeylGroup Tag.E6,
      (∀ b ∉ I, ∀ v : Fin Tag.E6.rank → ℤ,
        ((Nat.card A : ℕ) : ℤ) ∣ e6ToF4 (w • v) b - e6ToF4 v b) →
      ∀ b ∉ I, ∀ v : Fin Tag.E6.rank → ℤ, ((n : ℕ) : ℤ) ∣ e6ToF4 (w • v) b - e6ToF4 v b :=
    fun {n} hn w hw b hb v => hn ▸ hw b hb v
  rcases (show Nat.card A = 3 ∨ Nat.card A = 4 ∨ Nat.card A = 5 ∨ 6 ≤ Nat.card A by omega)
    with h3 | h4 | h5 | h6
  · by_cases hbad : RelBad I
    · have hc₁' := hcast h3 w₁ hc₁
      have hc₂' := hcast h3 w₂ hc₂
      push_cast at hc₁' hc₂'
      intro v i hi
      have hi' : e6IndexToF4 i ∉ I := fun h => hi (mem_relNodeSet.2 h)
      rcases hbad with rfl | rfl | rfl | rfl
      · exact commutator_smul_apply_eq_of_mem_tuples badTuples01_check
          (smul_single_mem_of_completeCheck badTuples01_complete hc₁')
          (smul_single_mem_of_completeCheck badTuples01_complete hc₂') v i
          ((relNodeSet_bad_check i).1 hi')
      · exact commutator_smul_apply_eq_of_mem_tuples badTuples02_check
          (smul_single_mem_of_completeCheck badTuples02_complete hc₁')
          (smul_single_mem_of_completeCheck badTuples02_complete hc₂') v i
          ((relNodeSet_bad_check i).2.1 hi')
      · exact commutator_smul_apply_eq_of_mem_tuples badTuples03_check
          (smul_single_mem_of_completeCheck badTuples03_complete hc₁')
          (smul_single_mem_of_completeCheck badTuples03_complete hc₂') v i
          ((relNodeSet_bad_check i).2.2.1 hi')
      · exact commutator_smul_apply_eq_of_mem_tuples badTuples13_check
          (smul_single_mem_of_completeCheck badTuples13_complete hc₁')
          (smul_single_mem_of_completeCheck badTuples13_complete hc₂') v i
          ((relNodeSet_bad_check i).2.2.2 hi')
    · exact hgood fun w hw => e6ToF4_smul_single_eq_of_tupleCheck
        (relWeyl_check_three I hI hbad) (by have := hcast h3 w hw; push_cast at this; exact this)
  · exact hgood fun w hw => e6ToF4_smul_single_eq_of_tupleCheck (relWeyl_check_four I hI)
      (by have := hcast h4 w hw; push_cast at this; exact this)
  · exact hgood fun w hw => e6ToF4_smul_single_eq_of_tupleCheck (relWeyl_check_five I hI)
      (by have := hcast h5 w hw; push_cast at this; exact this)
  · exact hgood fun w hw => e6ToF4_smul_single_eq_of_six_le h6 hw

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
