module

public import CFSG.LieType.SpecialLinear.SLModel.Basic
public import CFSG.LieType.SpecialLinear.BorelTwist.CoverType

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.SpecialLinear
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Universal.Unitary CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

@[expose] def bR0 (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) : Finset (Fin f) :=
  Finset.univ.filter fun r => s.succ ∈ ε r

@[expose] noncomputable def bShiftSet (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    (p : Fin f × Fin (m + 1)) : Set.powersetCard (Fin (m + 1)) (bdeg ε p) :=
  if h : p.2 = s.succ ∧ s.succ ∈ ε p.1 then
    ⟨insert s.succ (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))).erase s.castSucc), by
      have hb : bdeg ε p = (s.succ : ℕ) := by
        rw [bdeg, h.1, if_pos h.2]
      have hmem : s.castSucc ∈ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1))) := by
        rw [btop, ktop, mem_initSeg (bdeg_le ε p), hb]
        exact Nat.lt_succ_self _
      have hnot : s.succ ∉ (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1))).erase s.castSucc) := by
        intro hmem'
        have hb' : s.succ ∈ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
            Finset (Fin (m + 1))) := Finset.mem_of_mem_erase hmem'
        rw [btop, ktop, mem_initSeg (bdeg_le ε p), hb] at hb'
        exact absurd hb' (Nat.lt_irrefl _)
      change (insert s.succ (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))).erase s.castSucc)).card = bdeg ε p
      rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hmem, (btop ε p).2, hb]
      simp⟩
  else btop ε p

@[expose] noncomputable def bShift (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    (R : Finset (Fin f)) : BIdx ε :=
  fun p => if p.2 = s.succ ∧ p.1 ∈ R then bShiftSet ε s p else btop ε p

theorem bShift_apply_of_mem (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    {R : Finset (Fin f)} {p : Fin f × Fin (m + 1)} (hp : p.2 = s.succ ∧ p.1 ∈ R) :
    bShift ε s R p = bShiftSet ε s p := by
  simp [bShift, hp]

theorem bShift_apply_of_not_mem (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    {R : Finset (Fin f)} {p : Fin f × Fin (m + 1)} (hp : ¬ (p.2 = s.succ ∧ p.1 ∈ R)) :
    bShift ε s R p = btop ε p := by
  simp [bShift, hp]

theorem bShiftSet_of_mem (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    {r : Fin f} (hr : r ∈ bR0 ε s) :
    ((bShiftSet ε s (r, s.succ) : Set.powersetCard (Fin (m + 1))
      (bdeg ε (r, s.succ))) : Finset (Fin (m + 1))) =
      insert s.succ (((btop ε (r, s.succ) : Set.powersetCard (Fin (m + 1))
        (bdeg ε (r, s.succ))) : Finset (Fin (m + 1))).erase s.castSucc) := by
  have h : (r, s.succ).2 = s.succ ∧ s.succ ∈ ε (r, s.succ).1 := by
    refine ⟨rfl, ?_⟩
    simpa [bR0] using hr
  rw [bShiftSet, dif_pos h]

theorem bdeg_succ_of_mem (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) {r : Fin f}
    (hr : r ∈ bR0 ε s) : bdeg ε (r, s.succ) = (s.succ : ℕ) := by
  rw [bdeg]
  have h : s.succ ∈ ε r := by simpa [bR0] using hr
  rw [if_pos h]

theorem succ_notMem_btop (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) {r : Fin f}
    (hr : r ∈ bR0 ε s) :
    s.succ ∉ ((btop ε (r, s.succ) : Set.powersetCard (Fin (m + 1))
      (bdeg ε (r, s.succ))) : Finset (Fin (m + 1))) := by
  intro h
  rw [btop, ktop, mem_initSeg (bdeg_le ε (r, s.succ)), bdeg_succ_of_mem ε s hr] at h
  exact absurd h (Nat.lt_irrefl _)

theorem succ_mem_bShiftSet (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) {r : Fin f}
    (hr : r ∈ bR0 ε s) :
    s.succ ∈ ((bShiftSet ε s (r, s.succ) : Set.powersetCard (Fin (m + 1))
      (bdeg ε (r, s.succ))) : Finset (Fin (m + 1))) := by
  rw [bShiftSet_of_mem ε s hr]
  exact Finset.mem_insert_self _ _

theorem bShiftSet_ne_btop (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) {r : Fin f}
    (hr : r ∈ bR0 ε s) :
    bShiftSet ε s (r, s.succ) ≠ btop ε (r, s.succ) := by
  intro h
  have h1 := succ_mem_bShiftSet ε s hr
  rw [h] at h1
  exact succ_notMem_btop ε s hr h1

theorem move_iff (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    (p : Fin f × Fin (m + 1)) :
    (s.castSucc ∈ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))) ∧
      s.succ ∉ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1)))) ↔ p.2 = s.succ ∧ p.1 ∈ bR0 ε s := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [btop, ktop, mem_initSeg (bdeg_le ε p)] at h1 h2
    have h2' : ¬ (s.succ : ℕ) < bdeg ε p := h2
    have hb : bdeg ε p = (s.succ : ℕ) := by
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2'
      by_cases hj : p.2 ∈ ε p.1
      · have h1' : (s : ℕ) < (p.2 : ℕ) := by simpa [bdeg, hj] using h1
        have h2'' : ¬ (s : ℕ) + 1 < (p.2 : ℕ) := by simpa [bdeg, hj] using h2'
        rw [Fin.val_succ]
        omega
      · simp [bdeg, hj] at h1
    have hj : p.2 ∈ ε p.1 := by
      by_contra hj
      unfold bdeg at hb
      rw [if_neg hj] at hb
      omega
    refine ⟨?_, ?_⟩
    · ext
      have hp : (p.2 : ℕ) = (s.succ : ℕ) := by
        unfold bdeg at hb
        rw [if_pos hj] at hb
        exact hb
      exact hp
    · have hp2 : p.2 = s.succ := by
        have hp : (p.2 : ℕ) = (s.succ : ℕ) := by
          unfold bdeg at hb
          rw [if_pos hj] at hb
          exact hb
        exact Fin.ext hp
      rw [bR0]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← hp2]
  · rintro ⟨hp2, hr0⟩
    have hj : s.succ ∈ ε p.1 := by simpa [bR0] using hr0
    have hb : bdeg ε p = (s.succ : ℕ) := by
      unfold bdeg
      rw [hp2, if_pos hj]
    constructor
    · rw [btop, ktop, mem_initSeg (bdeg_le ε p), hb]
      exact Nat.lt_succ_self _
    · rw [btop, ktop, mem_initSeg (bdeg_le ε p), hb]
      exact Nat.lt_irrefl _

theorem bShiftSet_eq_insert (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    {p : Fin f × Fin (m + 1)} (hp : p.2 = s.succ ∧ p.1 ∈ bR0 ε s) :
    ((bShiftSet ε s p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))) =
      insert s.succ (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))).erase s.castSucc) := by
  have h : p.2 = s.succ ∧ s.succ ∈ ε p.1 := by
    refine ⟨hp.1, ?_⟩
    simpa [bR0] using hp.2
  rw [bShiftSet, dif_pos h]

omit [CharP k 2] in
theorem prod_factor_bShift (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (x : Fin f → k)
    {S : Finset (Fin f)} (hS : S ⊆ bR0 ε s) :
    (∏ p : Fin f × Fin (m + 1),
      (if bShift ε s S p = btop ε p then 1
       else if p.2 = s.succ ∧ p.1 ∈ bR0 ε s ∧ bShift ε s S p = bShiftSet ε s p
         then x p.1 else 0)) = ∏ r ∈ S, x r := by
  rw [← Finset.prod_subset (Finset.subset_univ (S.image fun r => (r, s.succ)))]
  · rw [Finset.prod_image]
    · refine Finset.prod_congr rfl fun r hr => ?_
      have hp : (r, s.succ).2 = s.succ ∧ r ∈ S := ⟨rfl, hr⟩
      rw [bShift_apply_of_mem ε s hp]
      simp only [hS hr, true_and]
      rw [if_neg]
      · rfl
      · exact bShiftSet_ne_btop ε s (hS hr)
    · intro r _ r' _ h
      exact congrArg Prod.fst h
  · intro p _ hp
    have hnot : ¬ (p.2 = s.succ ∧ p.1 ∈ S) := by
      intro h
      apply hp
      rw [Finset.mem_image]
      exact ⟨p.1, h.2, Prod.ext rfl h.1.symm⟩
    rw [bShift_apply_of_not_mem ε s hnot]
    simp

@[expose] noncomputable def bShiftSubset (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    (u : BIdx ε) : Finset (Fin f) :=
  (bR0 ε s).filter fun r => u (r, s.succ) = bShiftSet ε s (r, s.succ)

theorem bShiftSubset_subset (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (u : BIdx ε) :
    bShiftSubset ε s u ⊆ bR0 ε s :=
  Finset.filter_subset _ _

theorem bShiftSubset_bShift (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    {R : Finset (Fin f)} (hR : R ⊆ bR0 ε s) : bShiftSubset ε s (bShift ε s R) = R := by
  ext r
  constructor
  · intro hr
    rw [bShiftSubset, Finset.mem_filter] at hr
    obtain ⟨hr0, heq⟩ := hr
    by_contra hrR
    have h1 : bShift ε s R (r, s.succ) = btop ε (r, s.succ) :=
      bShift_apply_of_not_mem ε s (by simp [hrR])
    rw [h1] at heq
    exact bShiftSet_ne_btop ε s hr0 heq.symm
  · intro hrR
    rw [bShiftSubset, Finset.mem_filter]
    refine ⟨hR hrR, ?_⟩
    rw [bShift_apply_of_mem ε s ⟨rfl, hrR⟩]

omit [CharP k 2] in
theorem prod_factor_eq (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (x : Fin f → k)
    (u : BIdx ε) :
    (∏ p : Fin f × Fin (m + 1),
      (if u p = btop ε p then 1
       else if p.2 = s.succ ∧ p.1 ∈ bR0 ε s ∧ u p = bShiftSet ε s p then x p.1 else 0)) =
      (∏ r ∈ bShiftSubset ε s u, x r) *
        (if u = bShift ε s (bShiftSubset ε s u) then 1 else 0) := by
  by_cases hu : u = bShift ε s (bShiftSubset ε s u)
  · rw [if_pos hu, mul_one]
    conv_lhs => rw [hu]
    exact prod_factor_bShift ε s x (bShiftSubset_subset ε s u)
  · rw [if_neg hu, mul_zero]
    by_contra hprod
    apply hu
    have hfac : ∀ p : Fin f × Fin (m + 1),
        (if u p = btop ε p then 1
         else if p.2 = s.succ ∧ p.1 ∈ bR0 ε s ∧ u p = bShiftSet ε s p then x p.1 else 0) ≠ 0 :=
      fun p => Finset.prod_ne_zero_iff.mp hprod p (Finset.mem_univ p)
    funext p
    by_cases hp : p.2 = s.succ ∧ p.1 ∈ bShiftSubset ε s u
    · have hp' : (p.1, s.succ) = p := Prod.ext rfl hp.1.symm
      have ht : u (p.1, s.succ) = bShiftSet ε s (p.1, s.succ) :=
        (Finset.mem_filter.mp hp.2).2
      rw [bShift_apply_of_mem ε s hp]
      rw [hp'] at ht
      exact ht
    · rw [bShift_apply_of_not_mem ε s hp]
      by_contra hne
      have h0 := hfac p
      rw [if_neg hne] at h0
      by_cases hcond : p.2 = s.succ ∧ p.1 ∈ bR0 ε s ∧ u p = bShiftSet ε s p
      · obtain ⟨hp2, hp0, hpt⟩ := hcond
        apply hp
        refine ⟨hp2, ?_⟩
        rw [bShiftSubset, Finset.mem_filter]
        refine ⟨hp0, ?_⟩
        have hp' : (p.1, s.succ) = p := Prod.ext rfl hp2.symm
        rw [← hp'] at hpt
        exact hpt
      · exact h0 (if_neg hcond)

theorem factor_iff (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (u : BIdx ε)
    (p : Fin f × Fin (m + 1)) :
    (s.castSucc ∈ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))) ∧
      s.succ ∉ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))) ∧
      ((u p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))) =
        insert s.succ (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1))).erase s.castSucc)) ↔
    (p.2 = s.succ ∧ p.1 ∈ bR0 ε s ∧
      ((u p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))) =
        ((bShiftSet ε s p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1)))) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hp : p.2 = s.succ ∧ p.1 ∈ bR0 ε s := (move_iff ε s p).mp ⟨h1, h2⟩
    refine ⟨hp.1, hp.2, ?_⟩
    rw [bShiftSet_eq_insert ε s hp]
    exact h3
  · rintro ⟨hp2, hp0, h3⟩
    have hp : p.2 = s.succ ∧ p.1 ∈ bR0 ε s := ⟨hp2, hp0⟩
    have hmove := (move_iff ε s p).mpr hp
    refine ⟨hmove.1, hmove.2, ?_⟩
    rw [bShiftSet_eq_insert ε s hp] at h3
    exact h3

theorem bMat_lower_mulVec_bvec (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (x : Fin f → k) :
    bMat ε (fun r => 1 + Matrix.single s.succ s.castSucc (x r)) *ᵥ bvec ε =
      ∑ R ∈ Finset.univ.filter (fun R : Finset (Fin f) => R ⊆ bR0 ε s),
        (∏ r ∈ R, x r) • Pi.single (bShift ε s R) 1 := by
  classical
  ext u
  rw [bvec, Matrix.mulVec_single_one, Matrix.col_apply]
  change kronMinor (d := bdeg ε)
    (fun p : Fin f × Fin (m + 1) => 1 + Matrix.single s.succ s.castSucc (x p.1)) u
      (btop ε) = _
  rw [kronMinor_one_add_single (CharTwo.two_eq_zero (R := k))
    (Fin.castSucc_lt_succ (i := s)).ne' (fun p : Fin f × Fin (m + 1) => x p.1) u (btop ε)]
  have hprod : (∏ p : Fin f × Fin (m + 1),
      (if u p = btop ε p then 1
       else if p.2 = s.succ ∧ p.1 ∈ bR0 ε s ∧ u p = bShiftSet ε s p then x p.1 else 0)) =
      (∏ p : Fin f × Fin (m + 1),
      (if u p = btop ε p then 1
       else if s.castSucc ∈ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1))) ∧
         s.succ ∉ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1))) ∧
         u p = insert s.succ (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1))).erase s.castSucc) then x p.1 else 0)) := by
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hu0 : u p = btop ε p
    · rw [if_pos hu0, if_pos hu0]
    · rw [if_neg hu0, if_neg hu0]
      simp only [factor_iff ε s u p, Subtype.ext_iff]
  rw [← hprod, prod_factor_eq ε s x u]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hS : bShiftSubset ε s u ∈ Finset.univ.filter (fun R : Finset (Fin f) => R ⊆ bR0 ε s) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, bShiftSubset_subset ε s u⟩
  have hother : ∀ R ∈ Finset.univ.filter (fun R : Finset (Fin f) => R ⊆ bR0 ε s),
      R ≠ bShiftSubset ε s u →
      (∏ r ∈ R, x r) * (if u = bShift ε s R then 1 else 0) = 0 := by
    intro R hR hne
    have hne' : u ≠ bShift ε s R := by
      intro h
      apply hne
      rw [h]
      exact (bShiftSubset_bShift ε s (Finset.mem_filter.mp hR).2).symm
    rw [if_neg hne']
    simp
  rw [Finset.sum_eq_single_of_mem (bShiftSubset ε s u) hS hother]

theorem initSeg_map_swap (d : ℕ) (hd : d ≤ m + 1) (s : Fin m) :
    (((initSeg hd : Set.powersetCard (Fin (m + 1)) d) : Finset (Fin (m + 1))).map
      (Equiv.swap s.castSucc s.succ).toEmbedding) =
    if d = (s.succ : ℕ) then
      insert s.succ (((initSeg hd : Set.powersetCard (Fin (m + 1)) d) :
        Finset (Fin (m + 1))).erase s.castSucc)
    else ((initSeg hd : Set.powersetCard (Fin (m + 1)) d) : Finset (Fin (m + 1))) := by
  classical
  by_cases hd' : d = (s.succ : ℕ)
  · rw [if_pos hd']
    have hmem : s.castSucc ∈ ((initSeg hd : Set.powersetCard (Fin (m + 1)) d) :
        Finset (Fin (m + 1))) := by
      rw [mem_initSeg, hd']
      exact Nat.lt_succ_self _
    have hfix : ((((initSeg hd : Set.powersetCard (Fin (m + 1)) d) :
        Finset (Fin (m + 1))).erase s.castSucc).map
          (Equiv.swap s.castSucc s.succ).toEmbedding) =
        (((initSeg hd : Set.powersetCard (Fin (m + 1)) d) :
          Finset (Fin (m + 1))).erase s.castSucc) := by
      refine Finset.map_eq_of_subset ?_
      intro a ha
      rw [Finset.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [Finset.mem_erase, mem_initSeg] at hb
      have hlt : (b : ℕ) < (s : ℕ) := by
        have hne : (b : ℕ) ≠ (s : ℕ) := by
          intro h
          apply hb.1
          ext
          simpa using h
        rw [hd', Fin.val_succ] at hb
        omega
      have h1 : b ≠ s.castSucc := by
        intro h
        rw [h, Fin.val_castSucc] at hlt
        omega
      have h2 : b ≠ s.succ := by
        intro h
        rw [h, Fin.val_succ] at hlt
        omega
      rw [Equiv.toEmbedding_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
      rw [Finset.mem_erase, mem_initSeg]
      exact ⟨h1, hb.2⟩
    rw [← Finset.insert_erase hmem, Finset.map_insert, hfix]
    simp only [Equiv.toEmbedding_apply, Equiv.swap_apply_left]
    rw [Finset.erase_insert (Finset.notMem_erase _ _)]
  · rw [if_neg hd']
    by_cases hle : d ≤ (s : ℕ)
    · refine Finset.map_eq_of_subset ?_
      intro a ha
      rw [Finset.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [mem_initSeg] at hb
      have h1 : b ≠ s.castSucc := by
        intro h
        rw [h, Fin.val_castSucc] at hb
        omega
      have h2 : b ≠ s.succ := by
        intro h
        rw [h, Fin.val_succ] at hb
        omega
      rw [Equiv.toEmbedding_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact (mem_initSeg hd b).mpr hb
    · have hge : (s : ℕ) + 2 ≤ d := by
        have hlt : (s : ℕ) < d := Nat.lt_of_not_le hle
        have hne : d ≠ (s : ℕ) + 1 := by
          intro h
          apply hd'
          rw [h, Fin.val_succ]
        omega
      refine Finset.map_eq_of_subset ?_
      intro a ha
      rw [Finset.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [mem_initSeg] at hb
      by_cases h1 : b = s.castSucc
      · subst h1
        rw [Equiv.toEmbedding_apply, Equiv.swap_apply_left, mem_initSeg, Fin.val_succ]
        omega
      · by_cases h2 : b = s.succ
        · subst h2
          rw [Equiv.toEmbedding_apply, Equiv.swap_apply_right, mem_initSeg, Fin.val_castSucc]
          omega
        · rw [Equiv.toEmbedding_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
          rwa [mem_initSeg]

theorem btop_map_swap (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    (p : Fin f × Fin (m + 1)) :
    (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))).map (Equiv.swap s.castSucc s.succ).toEmbedding) =
      if bdeg ε p = (s.succ : ℕ) then
        insert s.succ (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
          Finset (Fin (m + 1))).erase s.castSucc)
      else ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))) := by
  simpa [btop, ktop] using initSeg_map_swap (m := m) (bdeg ε p) (bdeg_le ε p) s

theorem bShift_map_swap (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m)
    (p : Fin f × Fin (m + 1)) :
    (((bShift ε s (bR0 ε s) p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1))).map (Equiv.swap s.castSucc s.succ).toEmbedding) =
      (((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) :
        Finset (Fin (m + 1)))) := by
  classical
  by_cases hmove : p.2 = s.succ ∧ p.1 ∈ bR0 ε s
  · have hb : bdeg ε p = (s.succ : ℕ) := by
      have hj : s.succ ∈ ε p.1 := by simpa [bR0] using hmove.2
      simp [bdeg, hmove.1, hj]
    have h := btop_map_swap ε s p
    rw [if_pos hb] at h
    rw [bShift_apply_of_mem ε s hmove, bShiftSet_eq_insert ε s hmove]
    rw [← h]
    rw [Finset.map_map]
    ext x
    simp
  · have hnot : ¬ (p.2 = s.succ ∧ p.1 ∈ bR0 ε s) := hmove
    have hdne : bdeg ε p ≠ (s.succ : ℕ) := by
      intro hd
      have hj : p.2 ∈ ε p.1 := by
        by_contra hj
        rw [bdeg, if_neg hj, Fin.val_succ] at hd
        omega
      have hp2 : p.2 = s.succ := by
        have hval : (p.2 : ℕ) = (s.succ : ℕ) := by
          rw [bdeg, if_pos hj] at hd
          exact hd
        exact Fin.ext hval
      have hp0 : p.1 ∈ bR0 ε s := by
        rw [bR0]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hp2]
      exact hnot ⟨hp2, hp0⟩
    rw [bShift_apply_of_not_mem ε s hnot]
    have h := btop_map_swap ε s p
    rw [if_neg hdne] at h
    exact h

theorem bMat_weyl_mulVec_bvec (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) :
    bMat ε (fun _ => (Equiv.swap s.castSucc s.succ).permMatrix k) *ᵥ bvec ε =
      Pi.single (bShift ε s (bR0 ε s)) 1 := by
  classical
  rw [bvec, Matrix.mulVec_single_one]
  ext u
  rw [Matrix.col_apply, bMat]
  rw [kronMinor_permMatrix (d := bdeg ε) (CharTwo.two_eq_zero (R := k))
    (fun _ => Equiv.swap s.castSucc s.succ) u (btop ε)]
  rw [Pi.single_apply]
  have hmap2 : ∀ p : Fin f × Fin (m + 1),
      ∀ x : Set.powersetCard (Fin (m + 1)) (bdeg ε p),
      (((x : Finset (Fin (m + 1))).map (Equiv.swap s.castSucc s.succ).toEmbedding).map
        (Equiv.swap s.castSucc s.succ).toEmbedding) = (x : Finset (Fin (m + 1))) := by
    intro p x
    rw [Finset.map_map]
    ext y
    simp
  by_cases hu : u = bShift ε s (bR0 ε s)
  · rw [if_pos hu, if_pos]
    intro p
    rw [hu]
    exact bShift_map_swap ε s p
  · rw [if_neg hu, if_neg]
    intro h
    apply hu
    funext p
    have hp := congrArg (fun X : Finset (Fin (m + 1)) =>
      X.map (Equiv.swap s.castSucc s.succ).toEmbedding) (h p)
    rw [hmap2 p (u p)] at hp
    rw [← bShift_map_swap ε s p, hmap2 p (bShift ε s (bR0 ε s) p)] at hp
    exact Subtype.ext hp

omit [Fintype F] [CharP F 2] in
theorem one_add_single_mul_permMatrix (i j : Fin (m + 1)) (_hij : i ≠ j) (c : F) :
    (1 + Matrix.single i j c) * (Equiv.swap i j).permMatrix F =
      (Equiv.swap i j).permMatrix F * (1 + Matrix.single j i c) := by
  rw [Equiv.Perm.permMatrix]
  rw [add_mul, one_mul, mul_add, mul_one]
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  change (Equiv.toPEquiv (Equiv.swap i j)).toMatrix +
      (single i j c).submatrix (⇑(Equiv.refl (Fin (m + 1)))) (⇑(Equiv.swap i j).symm) =
    (Equiv.toPEquiv (Equiv.swap i j)).toMatrix +
      (single j i c).submatrix (⇑(Equiv.swap i j)) (⇑(Equiv.refl (Fin (m + 1))))
  rw [Matrix.submatrix_single_equiv (Equiv.refl _) (Equiv.swap i j).symm i j c]
  rw [Matrix.submatrix_single_equiv (Equiv.swap i j) (Equiv.refl _) j i c]
  simp

omit [Fintype F] in
theorem transvection_mul_weylRep (s : Fin m) (c : F) :
    SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne c * weylRep m F s =
      weylRep m F s *
        SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne.symm c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_weylRep', weylMatrix_eq_permMatrix,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.permMatrix_eq,
    Equiv.swap_inv, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  exact one_add_single_mul_permMatrix s.castSucc s.succ
    (Fin.castSucc_lt_succ (i := s)).ne c

theorem rankOne_x_mul_nhat (s : Fin m) (c : F) :
    (rankOne m F 2).x s c * (coverId m F 2).nhat s =
      (coverId m F 2).nhat s * (rankOne m F 2).y s c := by
  have hn : (coverId m F 2).nhat s = weylRep m F s := by
    rw [CentralCoverData.nhat, coverId_nhatW]
  rw [hn]
  exact transvection_mul_weylRep s c

omit [Fintype F] in
theorem slModelRep_mul_apply (ε : Fin f → Finset (Fin (m + 1)))
    (g h : SpecialLinearGroup (Fin (m + 1)) F) (v : BModel k ε) :
    slModelRep (F := F) (k := k) ε (g * h) v =
      slModelRep (F := F) (k := k) ε g (slModelRep (F := F) (k := k) ε h v) := by
  rw [map_mul]
  rfl

@[expose] noncomputable def bY (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (c : F) :
    bCyc (k := k) ε :=
  ⟨bMat ε (fun r => ((rankOne m F 2).y s c :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r)) *ᵥ bvec ε, by
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using
      bMat_mulVec_mem_bCyc ε
        (fun r => SpecialLinearGroup.map (frobTwist F k f r) ((rankOne m F 2).y s c))
        (bvec_mem_bCyc ε)⟩

theorem slModelRep_y_bTop (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (c : F) :
    slModelRep (F := F) (k := k) ε ((rankOne m F 2).y s c) (bTop ε) =
      Submodule.Quotient.mk (bY (k := k) ε s c) := by
  rw [bTop, slModelRep_mk]
  rfl

theorem bY_val_eq (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (c : F) :
    (bY (k := k) ε s c : BIdx ε → k) =
      bMat ε (fun r => 1 + Matrix.single s.succ s.castSucc (frobTwist F k f r c)) *ᵥ
        bvec ε := by
  unfold bY
  change bMat ε (fun r => ((rankOne m F 2).y s c :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r)) *ᵥ bvec ε =
    bMat ε (fun r => 1 + Matrix.single s.succ s.castSucc
      (frobTwist F k f r c)) *ᵥ bvec ε
  have hfam : (fun r => ((rankOne m F 2).y s c :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r)) =
      fun r => 1 + Matrix.single s.succ s.castSucc (frobTwist F k f r c) := by
    funext r
    change ((SpecialLinearGroup.transvection
      (Fin.castSucc_lt_succ (i := s)).ne.symm c :
        SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
      (frobTwist F k f r) = _
    rw [show ((SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ (i := s)).ne.symm c :
          SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        1 + Matrix.single s.succ s.castSucc c from rfl,
      Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single]
  rw [hfam]

theorem sum_pow_card_sub_one (K : Type*) [Field K] [Fintype K] [DecidableEq K] :
    ∑ x : K, x ^ (Fintype.card K - 1) = -1 := by
  have hn : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ]
    constructor
    · rintro ⟨a, rfl⟩ hx
      exact a.ne_zero hx
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  calc ∑ x : K, x ^ (Fintype.card K - 1)
      = ∑ x ∈ Finset.univ \ {(0 : K)}, x ^ (Fintype.card K - 1) := by
        rw [← Finset.sum_sdiff ({0} : Finset K).subset_univ, Finset.sum_singleton,
          zero_pow hn.ne', add_zero]
    _ = ∑ x : Kˣ, ((x : K) ^ (Fintype.card K - 1)) := by
        simp [φ, ← hmap, Finset.univ.sum_map φ]
    _ = -1 := by
        rw [FiniteField.sum_pow_units K (Fintype.card K - 1)]
        simp

omit [CharP F 2] in
theorem sum_algebraMap_pow (hF : Fintype.card F = 2 ^ f) {e : ℕ} (he : e < 2 ^ f) :
    (∑ c : F, (algebraMap F k c) ^ e) = if e = 2 ^ f - 1 then 1 else 0 := by
  classical
  by_cases h : e = 2 ^ f - 1
  · rw [if_pos h]
    have hsum : (∑ c : F, c ^ e) = -1 := by
      rw [h, ← hF]
      exact sum_pow_card_sub_one F
    calc ∑ c : F, (algebraMap F k c) ^ e
        = algebraMap F k (∑ c : F, c ^ e) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun c _ => (map_pow _ _ _).symm
      _ = algebraMap F k (-1) := by rw [hsum]
      _ = 1 := by rw [map_neg, map_one, CharTwo.neg_eq]
  · rw [if_neg h]
    have hlt : e < Fintype.card F - 1 := by
      rw [hF]
      omega
    have h0 := FiniteField.sum_pow_lt_card_sub_one F e hlt
    calc ∑ c : F, (algebraMap F k c) ^ e
        = algebraMap F k (∑ c : F, c ^ e) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun c _ => (map_pow _ _ _).symm
      _ = 0 := by rw [h0, map_zero]

theorem sum_frob_prod (hF : Fintype.card F = 2 ^ f) (R : Finset (Fin f)) :
    (∑ c : F, ∏ r ∈ R, frobTwist F k f r c) = if R = Finset.univ then 1 else 0 := by
  have hprod : ∀ c : F,
      (∏ r ∈ R, frobTwist F k f r c) = (algebraMap F k c) ^ (∑ r ∈ R, 2 ^ (r : ℕ)) := by
    intro c
    calc (∏ r ∈ R, frobTwist F k f r c)
        = ∏ r ∈ R, algebraMap F k (c ^ 2 ^ (r : ℕ)) := by
          exact Finset.prod_congr rfl fun r _ => frobTwist_apply r c
      _ = algebraMap F k (∏ r ∈ R, c ^ 2 ^ (r : ℕ)) := by rw [map_prod]
      _ = algebraMap F k (c ^ ∑ r ∈ R, 2 ^ (r : ℕ)) := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = (algebraMap F k c) ^ (∑ r ∈ R, 2 ^ (r : ℕ)) := by rw [map_pow]
  simp_rw [hprod]
  have hlt : (∑ r ∈ R, 2 ^ (r : ℕ)) < 2 ^ f := by
    calc (∑ r ∈ R, 2 ^ (r : ℕ)) ≤ ∑ r : Fin f, 2 ^ (r : ℕ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
            (fun i _ _ => Nat.zero_le _)
      _ = 2 ^ f - 1 := sum_fin_two_pow_eq
      _ < 2 ^ f := Nat.sub_lt (pow_pos (by norm_num : (0:ℕ) < 2) f) (by norm_num)
  rw [sum_algebraMap_pow (k := k) hF hlt]
  by_cases hR : R = Finset.univ
  · rw [if_pos hR, hR, sum_fin_two_pow_eq, if_pos rfl]
  · rw [if_neg hR, if_neg]
    intro he
    apply hR
    have himg : R.image (Fin.val : Fin f → ℕ) = Finset.range f := by
      have hsumR : (∑ r ∈ R.image (Fin.val : Fin f → ℕ), 2 ^ r) =
          ∑ r ∈ R, 2 ^ (r : ℕ) := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Fin.val_injective h
      have hsumU : (∑ r ∈ Finset.range f, 2 ^ r) = 2 ^ f - 1 := by
        rw [← Fin.sum_univ_eq_sum_range (fun r => 2 ^ r) f, sum_fin_two_pow_eq]
      have hEq : (∑ r ∈ R.image (Fin.val : Fin f → ℕ), 2 ^ r) =
          ∑ r ∈ Finset.range f, 2 ^ r := by
        rw [hsumR, hsumU, he]
      exact Finset.geomSum_injective (n := 2) (by norm_num) hEq
    apply Finset.eq_univ_of_forall
    intro r
    have hmem : (r : ℕ) ∈ R.image (Fin.val : Fin f → ℕ) := by
      rw [himg]
      exact Finset.mem_range.mpr r.isLt
    rw [Finset.mem_image] at hmem
    obtain ⟨s, hs, hsr⟩ := hmem
    rwa [Fin.val_injective hsr] at hs

theorem sum_bY_val_eq (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) :
    (∑ c : F, (bY (k := k) ε s c : BIdx ε → k)) =
      ∑ R ∈ (Finset.univ.filter fun R : Finset (Fin f) => R ⊆ bR0 ε s),
        (if R = Finset.univ then (1 : k) else 0) • Pi.single (bShift ε s R) 1 := by
  classical
  simp_rw [bY_val_eq]
  simp_rw [bMat_lower_mulVec_bvec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [← Finset.sum_smul]
  have h : (∑ c : F, ∏ r ∈ R, frobTwist F k f r c) =
      (if R = Finset.univ then (1 : k) else 0) := sum_frob_prod (k := k) hF R
  rw [h]

theorem heckeT_bTop_eq (_hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) :
    (coverId m F 2).datum.heckeT (slModelRep (F := F) (k := k) ε) s (bTop ε) =
      slModelRep (F := F) (k := k) ε ((coverId m F 2).nhat s)
        (Submodule.Quotient.mk (∑ c : F, bY (k := k) ε s c)) := by
  rw [(rankOne m F 2).heckeT_datum (C := coverId m F 2)
    (slModelRep (F := F) (k := k) ε) s (bTop ε)]
  calc (∑ c : F, slModelRep (F := F) (k := k) ε
        ((rankOne m F 2).x s c * (coverId m F 2).nhat s) (bTop ε))
      = ∑ c : F, slModelRep (F := F) (k := k) ε ((coverId m F 2).nhat s)
          (Submodule.Quotient.mk (bY (k := k) ε s c)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [rankOne_x_mul_nhat, slModelRep_mul_apply, slModelRep_y_bTop]
    _ = slModelRep (F := F) (k := k) ε ((coverId m F 2).nhat s)
          (∑ c : F, Submodule.Quotient.mk (bY (k := k) ε s c)) := by
        rw [map_sum]
    _ = slModelRep (F := F) (k := k) ε ((coverId m F 2).nhat s)
          (Submodule.Quotient.mk (∑ c : F, bY (k := k) ε s c)) := by
        congr 1
        let p : Submodule k (bCyc (k := k) ε) :=
          (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype
        change (∑ c : F, p.mkQ (bY (k := k) ε s c)) = p.mkQ (∑ c : F, bY (k := k) ε s c)
        rw [← map_sum]

theorem sum_bY_of_bR0_eq_empty (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (h0 : bR0 ε s = ∅) :
    (∑ c : F, bY (k := k) ε s c) = 0 := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  rw [sum_bY_val_eq (k := k) hF]
  rw [h0]
  have hf : 0 < f := by
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    rw [hF] at h2
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0] at h2
    norm_num at h2
  have hne : (∅ : Finset (Fin f)) ≠ Finset.univ := by
    intro h
    have huniv : (Finset.univ : Finset (Fin f)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hf⟩⟩
    exact huniv.ne_empty h.symm
  have hfilter : (Finset.univ.filter fun R : Finset (Fin f) => R ⊆ ∅) = {∅} := by
    ext R
    simp [Finset.subset_empty]
  rw [hfilter, Finset.sum_singleton]
  simp [hne]

theorem sum_bY_val_of_bR0_eq_univ (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (hU : bR0 ε s = Finset.univ) :
    (∑ c : F, (bY (k := k) ε s c : BIdx ε → k)) =
      Pi.single (bShift ε s Finset.univ) 1 := by
  rw [sum_bY_val_eq (k := k) hF]
  rw [hU]
  refine (Finset.sum_eq_single_of_mem Finset.univ ?_ ?_).trans ?_
  · simp
  · intro R hR hne
    simp [hne]
  · simp

omit [Fintype F] in
theorem weylRep_coe_eq_permMatrix (s : Fin m) :
    ((weylRep m F s : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (Equiv.swap s.castSucc s.succ).permMatrix F := by
  rw [coe_weylRep', weylMatrix_eq_permMatrix,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.permMatrix_eq, Equiv.swap_inv]

omit [CharP k 2] in
theorem bMat_permMatrix_mul_self (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) :
    bMat ε (fun _ => (Equiv.swap s.castSucc s.succ).permMatrix k) *
      bMat ε (fun _ => (Equiv.swap s.castSucc s.succ).permMatrix k) = 1 := by
  rw [← bMat_mul]
  have hfam : (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k *
      (Equiv.swap s.castSucc s.succ).permMatrix k) =
      fun _ : Fin f => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    funext r
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self]
    simp
  rw [hfam, bMat_one]

theorem heckeT_bTop_eq_zero (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (h0 : bR0 ε s = ∅) :
    (curtisDatum m F 2).heckeT (slModelRep (F := F) (k := k) ε) s (bTop ε) = 0 := by
  rw [← coverId_datum_heckeT_eq]
  rw [heckeT_bTop_eq (k := k) hF]
  have hsum : (∑ c : F, bY (k := k) ε s c) = 0 :=
    sum_bY_of_bR0_eq_empty (k := k) hF ε s h0
  rw [hsum]
  simp

theorem sum_bY_of_bR0_eq_univ (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (hU : bR0 ε s = Finset.univ) :
    (∑ c : F, bY (k := k) ε s c) =
      ⟨Pi.single (bShift ε s Finset.univ) 1, by
        rw [← sum_bY_val_of_bR0_eq_univ (k := k) hF ε s hU]
        simpa only [Submodule.coe_sum] using
          (∑ c : F, bY (k := k) ε s c).2⟩ := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  exact sum_bY_val_of_bR0_eq_univ (k := k) hF ε s hU

omit [Fintype F] [CharP k 2] in
theorem permMatrix_map_frob (σ : Equiv.Perm (Fin (m + 1))) (r : Fin f) :
    ((σ.permMatrix F).map (frobTwist F k f r)) = σ.permMatrix k := by
  ext i j
  rw [Matrix.map_apply, Equiv.Perm.permMatrix]
  simp [PEquiv.toMatrix]

theorem heckeT_bTop_eq_self (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (hU : bR0 ε s = Finset.univ) :
    (curtisDatum m F 2).heckeT (slModelRep (F := F) (k := k) ε) s (bTop ε) = bTop ε := by
  rw [← coverId_datum_heckeT_eq]
  rw [heckeT_bTop_eq (k := k) hF]
  rw [sum_bY_of_bR0_eq_univ (k := k) hF ε s hU]
  have hn : (coverId m F 2).nhat s = weylRep m F s := by
    rw [CentralCoverData.nhat, coverId_nhatW]
  have hfam : (fun r => (((coverId m F 2).nhat s :
      SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
      (frobTwist F k f r)) =
      fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k := by
    funext r
    rw [hn, weylRep_coe_eq_permMatrix, permMatrix_map_frob]
  have hPvec : bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) *ᵥ
      bvec ε = Pi.single (bShift ε s Finset.univ) 1 := by
    rw [bMat_weyl_mulVec_bvec ε s, hU]
  have hP2 : bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) *
      bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) = 1 :=
    bMat_permMatrix_mul_self ε s
  have hsingle : bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) *ᵥ
      Pi.single (bShift ε s Finset.univ) 1 = bvec ε := by
    calc bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) *ᵥ
          Pi.single (bShift ε s Finset.univ) 1
        = bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) *ᵥ
            (bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) *ᵥ bvec ε) := by
          rw [hPvec]
      _ = (bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k) *
            bMat ε (fun _ : Fin f => (Equiv.swap s.castSucc s.succ).permMatrix k)) *ᵥ bvec ε := by
          rw [← Matrix.mulVec_mulVec]
      _ = bvec ε := by rw [hP2, Matrix.one_mulVec]
  rw [slModelRep_mk, bTop]
  refine congrArg (Submodule.Quotient.mk (p :=
    (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)) (Subtype.ext ?_)
  change bMat ε (fun r =>
      (((coverId m F 2).nhat s : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
        (frobTwist F k f r))) *ᵥ Pi.single (bShift ε s Finset.univ) 1 = bvec ε
  rw [hfam, hsingle]

omit [CharP k 2] in
theorem slChiEps_hh_ne_one_of_bDigit_ne_zero (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (hd : bDigit ε s.succ ≠ 0)
    (hdt : bDigit ε s.succ ≠ 2 ^ f - 1) :
    ∃ u : Fˣ, slChiEps m (algebraMap F k) ε ((rankOne m F 2).hh s u) ≠ 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨g, ?_⟩
  rw [show (rankOne m F 2).hh s g = hdiag m F s g from rfl, slChiEps_hdiag]
  intro h
  have hpow : ((g : F) ^ bDigit ε s.succ) = 1 := by
    apply (algebraMap F k).injective
    simpa only [map_pow, map_one] using h
  have hpowU : g ^ bDigit ε s.succ = 1 := by
    ext
    simpa [Units.val_pow_eq_pow_val, Units.val_one] using hpow
  have hdvd : orderOf g ∣ bDigit ε s.succ := orderOf_dvd_of_pow_eq_one hpowU
  have hord : orderOf g = Fintype.card F - 1 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_units] using hg
  have hlt : bDigit ε s.succ < Fintype.card F - 1 := by
    rw [hF]
    have hlt' := bDigit_lt ε s.succ
    omega
  have hle : Fintype.card F - 1 ≤ bDigit ε s.succ := by
    rw [← hord]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd
  omega

end

end CFSG.LieType.SpecialLinear.SLModel
