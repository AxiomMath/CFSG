module

public import CFSG.LargeExtraspecial.S14C12E6Coord
public import CFSG.LieType.Chevalley.E6GraphRadicalCocycle

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LargeExtraspecial.S14.TwoE6
open scoped commutatorElement

@[expose] def e6RootB (v : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  (List.range TwistTag.E6.tag.rootCertificate.roots.length).any
    fun k => decide (TwistTag.E6.tag.rootCertificate.root k = v)

theorem isRoot_iff_e6RootB
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    IsRoot TwistTag.E6.tag v ↔ e6RootB v = true := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check _), e6RootB]
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]

@[expose] def e6KillCheck : Bool :=
  (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
    decide (0 < height (TwistTag.E6.tag.rootCertificate.root k) →
      height (TwistTag.E6.tag.rootCertificate.root k) ≤ 7 →
      ∃ i : Fin TwistTag.E6.tag.rank,
        e6RootB (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1) = true ∧
        (TwistTag.E6.perm i = i ∨ e6RootB (TwistTag.E6.tag.rootCertificate.root k +
          Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1) = false))

theorem e6KillCheck_eq_true : e6KillCheck = true := by decide

theorem exists_killing_single
    {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ) (h7 : height γ ≤ 7) :
    ∃ i : Fin TwistTag.E6.tag.rank, IsRoot TwistTag.E6.tag (γ + Pi.single i 1) ∧
      (TwistTag.E6.perm i = i ∨
        ¬IsRoot TwistTag.E6.tag (γ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1)) := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  have h := e6KillCheck_eq_true
  simp only [e6KillCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨i, hi, hi'⟩ := h k hk hpos h7
  refine ⟨i, (isRoot_iff_e6RootB _).2 hi, hi'.imp id fun h' hr => ?_⟩
  rw [isRoot_iff_e6RootB, h'] at hr
  exact Bool.false_ne_true hr

@[expose] def e6Alpha (j : Bool) : Fin TwistTag.E6.tag.rank → ℤ :=
  Pi.single (if j then (5 : Fin 6) else (0 : Fin 6)) 1

@[expose] def e6HighCheck : Bool :=
  (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
    decide (8 ≤ height (TwistTag.E6.tag.rootCertificate.root k) →
      e6RootB (TwistTag.E6.tag.rootCertificate.root k + e6Alpha false) = false ∧
        e6RootB (TwistTag.E6.tag.rootCertificate.root k + e6Alpha true) = false)

theorem e6HighCheck_eq_true : e6HighCheck = true := by decide

theorem not_isRoot_add_e6Alpha
    {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hh : 8 ≤ height γ) (j : Bool) :
    ¬IsRoot TwistTag.E6.tag (γ + e6Alpha j) := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  have h := e6HighCheck_eq_true
  simp only [e6HighCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h k hk hh
  intro hr
  rw [isRoot_iff_e6RootB] at hr
  cases j
  · rw [h1] at hr
    exact Bool.false_ne_true hr
  · rw [h2] at hr
    exact Bool.false_ne_true hr

theorem height_e6Alpha (j : Bool) : height (e6Alpha j) = 1 := by
  rw [e6Alpha, height_single]

variable {F : Type} [Field F]

@[expose] noncomputable def e6Test
    (F : Type) [Field F] (i : Fin TwistTag.E6.tag.rank) : ModGL TwistTag.E6.tag F :=
  if TwistTag.E6.perm i = i then pinnedX TwistTag.E6.tag F (Pi.single i 1) 1
  else pinnedX TwistTag.E6.tag F (Pi.single i 1) 1 *
    pinnedX TwistTag.E6.tag F (Pi.single (TwistTag.E6.perm i) 1) 1

theorem not_isRoot_single_add_perm'
    (i : Fin TwistTag.E6.tag.rank)
    (hi : TwistTag.E6.perm i ≠ i) :
    ¬IsRoot TwistTag.E6.tag (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) := by
  rw [isRoot_iff_e6RootB]
  revert hi
  revert i
  decide

theorem single_ne_perm (i : Fin TwistTag.E6.tag.rank) (hi : TwistTag.E6.perm i ≠ i) :
    (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single (TwistTag.E6.perm i) 1 ∧
      (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ -Pi.single (TwistTag.E6.perm i) 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := congrFun h i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hi.symm] at h'
    exact one_ne_zero h'
  · have h' := congrArg height h
    rw [height_neg, height_single, height_single] at h'
    omega

theorem commute_single_perm
    (i : Fin TwistTag.E6.tag.rank) (hi : TwistTag.E6.perm i ≠ i)
    (c d : F) :
    Commute (pinnedX TwistTag.E6.tag F (Pi.single i 1) c)
      (pinnedX TwistTag.E6.tag F (Pi.single (TwistTag.E6.perm i) 1) d) :=
  (simply_laced_root_commutator_unit TwistTag.E6.tag (.inr (.inl rfl)) (isRoot_single _ i)
    (isRoot_single _ _) (single_ne_perm i hi).1 (single_ne_perm i hi).2).2
    (not_isRoot_single_add_perm' i hi) F _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _
    (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem perm_perm (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  revert i
  decide

theorem pinnedX_single_mem_posUnipotent'
    (i : Fin TwistTag.E6.tag.rank) (d : F) :
    pinnedX TwistTag.E6.tag F (Pi.single i 1) d ∈ posUnipotent TwistTag.E6.tag F :=
  pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
    ⟨isRoot_single _ i, by rw [height_single]; norm_num⟩ d

theorem e6Test_mem_posUnipotent
    (i : Fin TwistTag.E6.tag.rank) : e6Test F i ∈ posUnipotent TwistTag.E6.tag F := by
  unfold e6Test
  split_ifs
  · exact pinnedX_single_mem_posUnipotent' i 1
  · exact mul_mem (pinnedX_single_mem_posUnipotent' i 1) (pinnedX_single_mem_posUnipotent' _ 1)

theorem e6Test_mem_twistedFixedGroup
    (h2 : (2 : F) = 0) (i : Fin TwistTag.E6.tag.rank) :
    e6Test F i ∈ twistedFixedGroup TwistTag.E6 F (RingHom.id F) := by
  have hX : ∀ j : Fin TwistTag.E6.tag.rank, twistHom TwistTag.E6 F (RingHom.id F)
      (pinnedX TwistTag.E6.tag F (Pi.single j 1) 1) =
        pinnedX TwistTag.E6.tag F (Pi.single (TwistTag.E6.perm j) 1) 1 := fun j => by
    rw [E6GraphRadical.twistHom_pinnedX_of_two h2 _ (isRoot_single _ j), permLattice_single,
      RingHom.id_apply]
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 F (RingHom.id F)).2 ⟨?_, ?_⟩
  · unfold e6Test
    split_ifs
    · exact pinnedX_mem_adjointGroup _ _
    · exact mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)
  · unfold e6Test
    split_ifs with hi
    · rw [hX, hi]
    · rw [map_mul, hX, hX, perm_perm]
      exact (commute_single_perm i hi 1 1).eq.symm

theorem rootCoord_eq_zero_of_commute_tests
    [Finite F] [CharP F 2] {h : ℤ}
    (h1 : 1 ≤ h) (h7 : h ≤ 7) {z : ModGL TwistTag.E6.tag F}
    (hz : z ∈ heightSeries TwistTag.E6.tag F h) (hc : ∀ i, z * e6Test F i = e6Test F i * z)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ)
    (hγh : height γ = h) : rootCoord hγ z = 0 := by
  obtain ⟨i, hi, hkill⟩ := exists_killing_single hγ.1 hγ.2 (by omega)
  have hβh : height (γ + Pi.single i 1) = h + 1 := by rw [height_add_e6, height_single, hγh]
  have hβ : IsRoot TwistTag.E6.tag (γ + Pi.single i 1) ∧ 0 < height (γ + Pi.single i 1) :=
    ⟨hi, by omega⟩
  have hπ1 : rootCoord hβ ⁅z, pinnedX TwistTag.E6.tag F (Pi.single i 1) 1⁆ =
      rootCoord hγ z * 1 := rootCoord_commutator_single hz i 1 hβ hβh hγ rfl
  by_cases hρ : TwistTag.E6.perm i = i
  · have hT : e6Test F i = pinnedX TwistTag.E6.tag F (Pi.single i 1) 1 := by
      simp only [e6Test, hρ, ↓reduceIte]
    rw [← hT, commutatorElement_eq_one_iff_mul_comm.2 (hc i), rootCoord_one, mul_one] at hπ1
    exact hπ1.symm
  · have hnr := hkill.resolve_left hρ
    have hc' : rootCoord hβ ⁅z, pinnedX TwistTag.E6.tag F
        (Pi.single (TwistTag.E6.perm i) 1) 1⁆ = 0 :=
      rootCoord_commutator_single_of_not_isRoot hz _ 1 hβ hβh hnr
    have hT : e6Test F i = pinnedX TwistTag.E6.tag F (Pi.single i 1) 1 *
        pinnedX TwistTag.E6.tag F (Pi.single (TwistTag.E6.perm i) 1) 1 := by
      simp only [e6Test, hρ, ↓reduceIte]
    have hw₁ := pinnedX_single_mem_posUnipotent' (F := F) i 1
    have hm1 := commutator_single_mem hz i (1 : F)
    have hm2 := commutator_single_mem hz (TwistTag.E6.perm i) (1 : F)
    rw [← hβh] at hm1 hm2
    have hconj := (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer F _ hw₁) _).1 hm2
    have e1 : ⁅z, pinnedX TwistTag.E6.tag F (Pi.single i 1) 1 *
        pinnedX TwistTag.E6.tag F (Pi.single (TwistTag.E6.perm i) 1) 1⁆ =
        ⁅z, pinnedX TwistTag.E6.tag F (Pi.single i 1) 1⁆ *
          (pinnedX TwistTag.E6.tag F (Pi.single i 1) 1 *
            ⁅z, pinnedX TwistTag.E6.tag F (Pi.single (TwistTag.E6.perm i) 1) 1⁆ *
              (pinnedX TwistTag.E6.tag F (Pi.single i 1) 1)⁻¹) := by
      simp only [commutatorElement_def]
      group
    have h0 := congrArg (rootCoord hβ) e1
    rw [← hT, commutatorElement_eq_one_iff_mul_comm.2 (hc i), rootCoord_one,
      rootCoord_mul hβ hm1 hconj, rootCoord_conj hβ hw₁ hm2, hπ1, hc', mul_one, add_zero] at h0
    exact h0.symm

theorem mem_heightSeries_eight_of_commute
    [Finite F] [CharP F 2]
    {z : ModGL TwistTag.E6.tag F} (hz : z ∈ posUnipotent TwistTag.E6.tag F)
    (hc : ∀ i, z * e6Test F i = e6Test F i * z) :
    z ∈ heightSeries TwistTag.E6.tag F 8 := by
  have key : ∀ n : ℕ, n ≤ 7 → z ∈ heightSeries TwistTag.E6.tag F ((n : ℤ) + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.cast_zero, zero_add, heightSeries_one]
      exact hz
    | succ n ih =>
      intro hn
      have hz' := ih (by omega)
      rw [Nat.cast_succ]
      exact mem_heightSeries_succ hz' fun γ hγ hγh =>
        rootCoord_eq_zero_of_commute_tests (by omega) (by omega) hz' hc hγ hγh
  have h := key 7 le_rfl
  norm_num at h
  exact h

theorem commute_e6Alpha_of_mem
    {z : ModGL TwistTag.E6.tag F}
    (hz : z ∈ heightSeries TwistTag.E6.tag F 8) (j : Bool) (c : F) :
    Commute z (pinnedX TwistTag.E6.tag F (e6Alpha j) c) := by
  rw [heightSeries, rootSpan_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨γ, ⟨hγ, hpos, hh⟩, d, rfl⟩ := hg
    have hne : γ ≠ e6Alpha j := fun h => by
      rw [h, height_e6Alpha] at hh
      omega
    have hne' : γ ≠ -e6Alpha j := fun h => by
      rw [h, height_neg, height_e6Alpha] at hh
      omega
    exact (simply_laced_root_commutator_unit TwistTag.E6.tag (.inr (.inl rfl)) hγ
      (isRoot_single _ _) hne hne').2 (not_isRoot_add_e6Alpha hγ hh j) F _
      (mem_rootSubgroup.2 ⟨d, rfl⟩) _ (mem_rootSubgroup.2 ⟨c, rfl⟩)
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

end CFSG.ComponentClassification.RankTwoExcHypII
