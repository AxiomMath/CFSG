module

public import CFSG.LargeExtraspecial.S14C12E6Coord
public import CFSG.LieType.Chevalley.E6GraphRadicalCocycle
public import CFSG.LieType.Chevalley.C2E6UnitaryFourCompound

public section

namespace CFSG.LargeExtraspecial.S14.TwoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap (K bar barHom barHom_apply bar_bar ω
  omega_sq_add_omega_add_one)
open scoped commutatorElement

theorem bar_eq_self_iff (c : K) : bar c = c ↔ c = 0 ∨ c = 1 := by
  rw [bar, pow_two]
  constructor
  · intro h
    have h' : c * (c - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
    rcases mul_eq_zero.1 h' with h0 | h1
    · exact .inl h0
    · exact .inr (sub_eq_zero.1 h1)
  · rintro (rfl | rfl) <;> simp

theorem eq_zero_of_forall_mul_add_mul_bar (a b : K) (h : ∀ d : K, a * d + b * bar d = 0) :
    a = 0 := by
  have h1 := h 1
  have hω := h ω
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [bar] at h1 hω
  linear_combination hω - ω ^ 2 * h1 + a * omega_sq_add_omega_add_one - a * ω * h2

theorem eq_e6HighestRoot_of_height_eq
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (h : height α = 11) :
    α = e6HighestRoot := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have hl : (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
      decide (height (TwistTag.E6.tag.rootCertificate.root k) = 11 →
        TwistTag.E6.tag.rootCertificate.root k = e6HighestRoot) := by decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hl
  exact hl k hk h

theorem not_isRoot_single_add_perm (i : Fin TwistTag.E6.tag.rank)
    (hi : TwistTag.E6.perm i ≠ i) :
    ¬IsRoot TwistTag.E6.tag (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) := by
  intro h
  obtain ⟨k, hk, hkv⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 h
  have hl : (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
      (List.finRange TwistTag.E6.tag.rank).all fun i => decide (TwistTag.E6.perm i ≠ i →
        TwistTag.E6.tag.rootCertificate.root k ≠
          Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) := by decide
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, decide_eq_true_eq,
    forall_const] at hl
  exact hl k hk i hi hkv

theorem twistHom_pinnedX_single
    (i : Fin TwistTag.E6.tag.rank) (d : K) :
    twistHom TwistTag.E6 K barHom (pinnedX TwistTag.E6.tag K (Pi.single i 1) d) =
      pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (bar d) := by
  rw [E6GraphRadical.twistHom_pinnedX_of_two CharTwo.two_eq_zero barHom (isRoot_single _ i),
    permLattice_single, barHom_apply]

theorem pinnedX_single_mem_posUnipotent
    (i : Fin TwistTag.E6.tag.rank) (d : K) :
    pinnedX TwistTag.E6.tag K (Pi.single i 1) d ∈ posUnipotent TwistTag.E6.tag K :=
  pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
    ⟨isRoot_single _ i, by rw [height_single]; norm_num⟩ d

theorem pinnedX_single_mem_of_fixed
    (i : Fin TwistTag.E6.tag.rank) (hi : TwistTag.E6.perm i = i) :
    pinnedX TwistTag.E6.tag K (Pi.single i 1) 1 ∈ graphFixedPosUnipotent TwistTag.E6 K barHom := by
  refine ⟨pinnedX_single_mem_posUnipotent i 1,
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2
      ⟨pinnedX_mem_adjointGroup _ _, ?_⟩⟩
  rw [twistHom_pinnedX_single, hi, C2E6Overlap.bar_one]

theorem pinnedX_pair_mem
    (i : Fin TwistTag.E6.tag.rank) (hi : TwistTag.E6.perm i ≠ i) (d : K) :
    pinnedX TwistTag.E6.tag K (Pi.single i 1) d *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (bar d) ∈
      graphFixedPosUnipotent TwistTag.E6 K barHom := by
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := .inr (.inl rfl)
  have hρρ : TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
    revert i
    decide
  have hne : (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single (TwistTag.E6.perm i) 1 :=
    fun h => by
      have h' := congrFun h i
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hi.symm] at h'
      exact one_ne_zero h'
  have hne' : (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      -Pi.single (TwistTag.E6.perm i) 1 := fun h => by
    have h' := congrArg height h
    rw [height_neg, height_single, height_single] at h'
    omega
  have hcomm := (simply_laced_root_commutator_unit TwistTag.E6.tag hτ (isRoot_single _ i)
    (isRoot_single _ _) hne hne').2 (not_isRoot_single_add_perm i hi) K _
    (mem_rootSubgroup.2 ⟨d, rfl⟩) _ (mem_rootSubgroup.2 ⟨bar d, rfl⟩)
  refine ⟨mul_mem (pinnedX_single_mem_posUnipotent _ _) (pinnedX_single_mem_posUnipotent _ _),
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2
      ⟨mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _), ?_⟩⟩
  rw [map_mul, twistHom_pinnedX_single, twistHom_pinnedX_single, hρρ, bar_bar]
  exact hcomm.eq.symm

theorem rootCoord_eq_zero_of_commute
    {h : ℤ} (h1 : 1 ≤ h) {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ heightSeries TwistTag.E6.tag K h)
    (hc : ∀ y ∈ graphFixedPosUnipotent TwistTag.E6 K barHom, z * y = y * z)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ)
    (hγh : height γ = h) (hne : γ ≠ e6HighestRoot) : rootCoord hγ z = 0 := by
  obtain ⟨i, hi⟩ := isRoot_add_single_of_ne hγ.1 hγ.2 hne
  have hβh : height (γ + Pi.single i 1) = h + 1 := by rw [height_add_e6, height_single, hγh]
  have hβ : IsRoot TwistTag.E6.tag (γ + Pi.single i 1) ∧ 0 < height (γ + Pi.single i 1) :=
    ⟨hi, by omega⟩
  have hπ1 : ∀ d : K, rootCoord hβ ⁅z, pinnedX TwistTag.E6.tag K (Pi.single i 1) d⁆ =
      rootCoord hγ z * d := fun d => rootCoord_commutator_single hz i d hβ hβh hγ rfl
  by_cases hρ : TwistTag.E6.perm i = i
  · have h0 := hπ1 1
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hc _ (pinnedX_single_mem_of_fixed i hρ)),
      rootCoord_one, mul_one] at h0
    exact h0.symm
  · obtain ⟨c', hc'⟩ : ∃ c' : K, ∀ d : K, rootCoord hβ
        ⁅z, pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) d⁆ = c' * d := by
      by_cases hr : IsRoot TwistTag.E6.tag (γ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1)
      · have hpos : 0 < height (γ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1) := by
          rw [height_sub_e6, height_single, hβh]
          omega
        exact ⟨rootCoord ⟨hr, hpos⟩ z, fun d =>
          rootCoord_commutator_single hz _ d hβ hβh ⟨hr, hpos⟩ (sub_add_cancel _ _)⟩
      · exact ⟨0, fun d => by
          rw [rootCoord_commutator_single_of_not_isRoot hz _ d hβ hβh hr, zero_mul]⟩
    refine eq_zero_of_forall_mul_add_mul_bar _ c' fun d => ?_
    have hw₁ := pinnedX_single_mem_posUnipotent i d
    have hm1 := commutator_single_mem hz i d
    have hm2 := commutator_single_mem hz (TwistTag.E6.perm i) (bar d)
    rw [← hβh] at hm1 hm2
    have hconj := (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hw₁) _).1 hm2
    have e1 : ⁅z, pinnedX TwistTag.E6.tag K (Pi.single i 1) d *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (bar d)⁆ =
        ⁅z, pinnedX TwistTag.E6.tag K (Pi.single i 1) d⁆ *
          (pinnedX TwistTag.E6.tag K (Pi.single i 1) d *
            ⁅z, pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (bar d)⁆ *
              (pinnedX TwistTag.E6.tag K (Pi.single i 1) d)⁻¹) := by
      simp only [commutatorElement_def]
      group
    have h0 := congrArg (rootCoord hβ) e1
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hc _ (pinnedX_pair_mem i hρ d)),
      rootCoord_one, rootCoord_mul hβ hm1 hconj, rootCoord_conj hβ hw₁ hm2, hπ1, hc'] at h0
    exact h0.symm

theorem mem_heightSeries_of_commute
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ graphFixedPosUnipotent TwistTag.E6 K barHom)
    (hc : ∀ y ∈ graphFixedPosUnipotent TwistTag.E6 K barHom, z * y = y * z) (n : ℕ)
    (hn : n ≤ 10) : z ∈ heightSeries TwistTag.E6.tag K ((n : ℤ) + 1) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_add, heightSeries_one]
    exact hz.1
  | succ n ih =>
    have hz' := ih (by omega)
    rw [Nat.cast_succ]
    exact mem_heightSeries_succ hz' fun γ hγ hγh =>
      rootCoord_eq_zero_of_commute (by omega) hz' hc hγ hγh fun he => by
        rw [he, height_e6HighestRoot] at hγh
        omega

theorem heightSeries_twelve :
    heightSeries TwistTag.E6.tag K 12 = ⊥ :=
  iSup₂_eq_bot.2 fun _ hα => absurd (height_le_eleven hα.1) (by linarith [hα.2.2])

theorem eq_one_or_eq_pinnedX_theta_of_commute
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ graphFixedPosUnipotent TwistTag.E6 K barHom)
    (hc : ∀ y ∈ graphFixedPosUnipotent TwistTag.E6 K barHom, z * y = y * z) :
    z = 1 ∨ z = pinnedX TwistTag.E6.tag K e6HighestRoot 1 := by
  have hθh : height e6HighestRoot = 11 := height_e6HighestRoot
  have h11 : z ∈ heightSeries TwistTag.E6.tag K (height e6HighestRoot) := by
    have h := mem_heightSeries_of_commute hz hc 10 le_rfl
    rw [hθh]
    exact h
  have hθ : IsRoot TwistTag.E6.tag e6HighestRoot ∧ 0 < height e6HighestRoot :=
    ⟨isRoot_e6HighestRoot, by rw [hθh]; norm_num⟩
  set c := rootCoord hθ z with hcdef
  have hX := pinnedX_mem_heightSeries_height (K := K) hθ (-c)
  have hz' : z * pinnedX TwistTag.E6.tag K e6HighestRoot (-c) ∈
      heightSeries TwistTag.E6.tag K 12 := by
    have h := mem_heightSeries_succ (mul_mem h11 hX) fun γ hγ hγh => by
      obtain rfl := eq_e6HighestRoot_of_height_eq hγ.1 (hγh.trans hθh)
      rw [rootCoord_mul hγ h11 hX, rootCoord_self]
      exact add_neg_cancel c
    rw [hθh] at h
    exact h
  rw [heightSeries_twelve, Subgroup.mem_bot, ← pinnedX_neg, mul_inv_eq_one] at hz'
  have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1 hz.2).2
  rw [hz', E6GraphRadical.twistHom_pinnedX_of_two CharTwo.two_eq_zero barHom isRoot_e6HighestRoot,
    permLattice_e6HighestRoot, barHom_apply] at hfix
  rcases (bar_eq_self_iff c).1 (pinnedX_injective _ _ _ hfix) with h0 | h0
  · left
    rw [hz', h0, pinnedX_zero]
  · right
    rw [hz', h0]

end CFSG.LargeExtraspecial.S14.TwoE6
