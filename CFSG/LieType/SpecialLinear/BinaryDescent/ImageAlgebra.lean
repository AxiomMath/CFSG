module

public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open ExteriorModel

variable {n i j : ℕ} {F : Type*} [Field F] [CharP F 2]

noncomputable def extTwistImage (n i j : ℕ) (F : Type*) [Field F] [CharP F 2] :
    Subring (Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F) :=
  Subring.closure (Set.range (extTwist n i j F))

theorem extTwist_mem_image (g : Matrix.SpecialLinearGroup (Fin n) F) :
    extTwist n i j F g ∈ extTwistImage n i j F :=
  Subring.subset_closure ⟨g, rfl⟩

theorem one_mem_image : (1 : Matrix (Set.powersetCard (Fin n) i)
    (Set.powersetCard (Fin n) i) F) ∈ extTwistImage n i j F := by
  simp

theorem smul_extUnit_mem [Fintype F] {a b : Fin n} (hab : a ≠ b) (c : F) :
    c • extUnit n i F a b ∈ extTwistImage n i j F := by
  classical
  have hinj : Function.Injective (iterateFrobenius F 2 j) :=
    @iterateFrobenius_inj F _ _ 2 j (ExpChar.prime Nat.prime_two)
  obtain ⟨t, ht⟩ := (Finite.surjective_of_injective hinj) c
  have h := extTwist_mem_image (n := n) (i := i) (j := j) (F := F)
    (Matrix.SpecialLinearGroup.transvection hab t)
  rw [extTwist_transvection hab t, ht] at h
  have h1 : (1 : Matrix (Set.powersetCard (Fin n) i)
      (Set.powersetCard (Fin n) i) F) ∈ extTwistImage n i j F := one_mem_image
  have hsub := Subring.sub_mem _ h h1
  simpa [add_sub_cancel_left] using hsub

theorem extUnit_mem [Fintype F] {a b : Fin n} (hab : a ≠ b) :
    extUnit n i F a b ∈ extTwistImage n i j F := by
  simpa using smul_extUnit_mem (n := n) (i := i) (j := j) (F := F) hab (1 : F)

theorem smul_diagonal_mem [Fintype F] {b0 : Fin n} :
    ∀ (S : Finset (Fin n)), S.Nonempty → b0 ∉ S → ∀ c : F,
      c • Matrix.diagonal (fun t : Set.powersetCard (Fin n) i =>
        if S ⊆ (t : Finset (Fin n)) ∧ b0 ∉ (t : Finset (Fin n)) then (1 : F) else 0) ∈
        extTwistImage n i j F := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro hS; exact (Finset.not_nonempty_empty hS).elim
  | insert a S ha ih =>
      intro _hS hb0 c
      have hab : a ≠ b0 := fun h => hb0 (h ▸ Finset.mem_insert_self a S)
      by_cases hS' : S.Nonempty
      · have hb0S : b0 ∉ S := fun h => hb0 (Finset.mem_insert_of_mem h)
        have hP : extUnit n i F a b0 * extUnit n i F b0 a ∈ extTwistImage n i j F :=
          Subring.mul_mem _ (extUnit_mem (n := n) (i := i) (j := j) (F := F) hab)
            (extUnit_mem (n := n) (i := i) (j := j) (F := F) hab.symm)
        have hmul := Subring.mul_mem _ (ih hS' hb0S c) hP
        rw [Matrix.smul_mul, extUnit_mul_extUnit hab, Matrix.diagonal_mul_diagonal] at hmul
        have hdiag : Matrix.diagonal (fun t : Set.powersetCard (Fin n) i =>
            (if S ⊆ (t : Finset (Fin n)) ∧ b0 ∉ (t : Finset (Fin n)) then (1 : F) else 0) *
            (if a ∈ (t : Finset (Fin n)) ∧ b0 ∉ (t : Finset (Fin n)) then (1 : F) else 0)) =
            Matrix.diagonal (fun t : Set.powersetCard (Fin n) i =>
              if insert a S ⊆ (t : Finset (Fin n)) ∧ b0 ∉ (t : Finset (Fin n)) then
                (1 : F) else 0) := by
          congr 1
          funext t
          by_cases hb : b0 ∈ (t : Finset (Fin n))
          · simp [hb]
          · by_cases hSa : S ⊆ (t : Finset (Fin n))
            · by_cases haT : a ∈ (t : Finset (Fin n))
              · simp [hb, hSa, haT, Finset.insert_subset_iff]
              · simp [hb, hSa, haT, Finset.insert_subset_iff]
            · simp [hb, hSa, Finset.insert_subset_iff]
        rw [hdiag] at hmul
        exact hmul
      · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
        subst hSempty
        have hmul := Subring.mul_mem _ (smul_extUnit_mem (n := n) (i := i) (j := j) (F := F)
          hab c) (extUnit_mem (n := n) (i := i) (j := j) (F := F) hab.symm)
        rw [Matrix.smul_mul, extUnit_mul_extUnit hab] at hmul
        have hdiag : Matrix.diagonal (fun t : Set.powersetCard (Fin n) i =>
            if a ∈ (t : Finset (Fin n)) ∧ b0 ∉ (t : Finset (Fin n)) then (1 : F) else 0) =
            Matrix.diagonal (fun t : Set.powersetCard (Fin n) i =>
              if insert a ∅ ⊆ (t : Finset (Fin n)) ∧ b0 ∉ (t : Finset (Fin n)) then
                (1 : F) else 0) := by
          congr 1
          funext t
          simp [Finset.singleton_subset_iff]
        rw [hdiag] at hmul
        exact hmul

theorem smul_single_diagonal_mem [Fintype F] (hi : 1 ≤ i) {b0 : Fin n}
    (s : Set.powersetCard (Fin n) i) (hb0 : b0 ∉ (s : Finset (Fin n))) (c : F) :
    c • Matrix.single s s 1 ∈ extTwistImage n i j F := by
  classical
  have hne : (s : Finset (Fin n)).Nonempty :=
    Finset.card_pos.mp (by rw [Set.powersetCard.card_eq]; exact hi)
  have hmem := smul_diagonal_mem (n := n) (i := i) (j := j) (F := F)
    (s : Finset (Fin n)) hne hb0 c
  have hdiag : Matrix.diagonal (fun t : Set.powersetCard (Fin n) i =>
      if (s : Finset (Fin n)) ⊆ (t : Finset (Fin n)) ∧
        b0 ∉ (t : Finset (Fin n)) then (1 : F) else 0) =
      Matrix.single s s 1 := by
    ext t u
    rw [Matrix.diagonal_apply, Matrix.single_apply]
    by_cases htu : t = u
    · subst htu
      by_cases hts : t = s
      · subst hts
        simp [hb0]
      · have hst : ¬ (s = t ∧ s = t) := fun h => hts h.1.symm
        have hnot : ¬ ((s : Finset (Fin n)) ⊆ (t : Finset (Fin n)) ∧
            b0 ∉ (t : Finset (Fin n))) := by
          rintro ⟨hsub, -⟩
          exact hts (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by
            rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq])).symm)
        rw [if_neg hst, if_neg hnot]
        simp
    · have hst : ¬ (s = t ∧ s = u) := fun h => htu (h.1.symm.trans h.2)
      rw [if_neg htu, if_neg hst]
  rw [hdiag] at hmem
  exact hmem

omit [CharP F 2] in
theorem extUnit_mul_single {a b : Fin n} {s t : Set.powersetCard (Fin n) i}
    (hs : b ∈ (s : Finset (Fin n)))
    (ha : a ∉ (s : Finset (Fin n))) {s' : Set.powersetCard (Fin n) i}
    (hs' : (s' : Finset (Fin n)) = insert a ((s : Finset (Fin n)).erase b)) :
    extUnit n i F a b * Matrix.single s t 1 = Matrix.single s' t 1 := by
  classical
  ext u v
  rw [Matrix.mul_apply]
  by_cases hv : v = t
  · subst hv
    rw [Finset.sum_eq_single s]
    · rw [Matrix.single_apply, Matrix.single_apply]
      have hu : ((u : Finset (Fin n)) = insert a ((s : Finset (Fin n)).erase b)) ↔ s' = u := by
        constructor
        · intro h; exact Subtype.ext (h.trans hs'.symm).symm
        · intro h; rw [← congrArg Subtype.val h]; exact hs'
      simp [extUnit, hs, ha, hu]
    · intro w _ hws
      rw [Matrix.single_apply]
      simp [Ne.symm hws]
    · intro h; exact absurd (Finset.mem_univ s) h
  · rw [Finset.sum_eq_zero]
    · rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hv rfl
    · intro w _
      rw [Matrix.single_apply]
      simp [Ne.symm hv]

theorem smul_single_mem [Fintype F] (hi : 1 ≤ i) (hin : i < n)
    (s t : Set.powersetCard (Fin n) i) (c : F) :
    c • Matrix.single s t 1 ∈ extTwistImage n i j F := by
  classical
  suffices H : ∀ k : ℕ, ∀ s t : Set.powersetCard (Fin n) i,
      ((s : Finset (Fin n)) \ (t : Finset (Fin n))).card = k →
      ∀ c : F, c • Matrix.single s t 1 ∈ extTwistImage n i j F by
    exact H _ s t rfl c
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro s t hk c
      by_cases hsub : (s : Finset (Fin n)) ⊆ (t : Finset (Fin n))
      · have hst : s = t := Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by
            rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq]))
        subst hst
        obtain ⟨b0, -, hb0⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (s := (s : Finset (Fin n))) (t := Finset.univ) (by
            rw [Finset.card_univ, Fintype.card_fin, Set.powersetCard.card_eq]
            exact hin)
        exact smul_single_diagonal_mem (n := n) (i := i) (j := j) (F := F) hi s hb0 c
      · obtain ⟨b, hb⟩ := Finset.sdiff_nonempty.mpr hsub
        have hb_mem : b ∈ (s : Finset (Fin n)) := (Finset.mem_sdiff.mp hb).1
        have hb_not : b ∉ (t : Finset (Fin n)) := (Finset.mem_sdiff.mp hb).2
        have ht_not_sub : ¬ (t : Finset (Fin n)) ⊆ (s : Finset (Fin n)) := by
          intro htsub
          have hts : t = s := Subtype.ext (Finset.eq_of_subset_of_card_le htsub (by
            rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq]))
          exact hb_not (by rw [hts]; exact hb_mem)
        obtain ⟨a, ha⟩ := Finset.sdiff_nonempty.mpr ht_not_sub
        have ha_mem : a ∈ (t : Finset (Fin n)) := (Finset.mem_sdiff.mp ha).1
        have ha_not : a ∉ (s : Finset (Fin n)) := (Finset.mem_sdiff.mp ha).2
        have hab : a ≠ b := fun h => ha_not (h ▸ hb_mem)
        have hcard : (insert a ((s : Finset (Fin n)).erase b)).card = i := by
          rw [Finset.card_insert_of_notMem (by simp [ha_not]),
            Finset.card_erase_of_mem hb_mem, Set.powersetCard.card_eq]
          omega
        let s' : Set.powersetCard (Fin n) i := ⟨insert a ((s : Finset (Fin n)).erase b), hcard⟩
        have hs' : (s' : Finset (Fin n)) = insert a ((s : Finset (Fin n)).erase b) := rfl
        have hdiff : ((s' : Finset (Fin n)) \ (t : Finset (Fin n))) =
            ((s : Finset (Fin n)) \ (t : Finset (Fin n))).erase b := by
          ext x
          simp only [hs', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨hx | hx, hxt⟩
            · exact absurd (by rw [hx]; exact ha_mem) hxt
            · exact ⟨hx.1, hx.2, hxt⟩
          · rintro ⟨hxb, hxs, hxt⟩
            exact ⟨Or.inr ⟨hxb, hxs⟩, hxt⟩
        have hk' : ((s' : Finset (Fin n)) \ (t : Finset (Fin n))).card < k := by
          have hpos : 0 < ((s : Finset (Fin n)) \ (t : Finset (Fin n))).card :=
            Finset.card_pos.mpr ⟨b, hb⟩
          rw [hdiff, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hb_mem, hb_not⟩), hk]
          omega
        have ha_s' : a ∈ (s' : Finset (Fin n)) := by
          rw [hs']; exact Finset.mem_insert_self a ((s : Finset (Fin n)).erase b)
        have hb_s' : b ∉ (s' : Finset (Fin n)) := by
          rw [hs']
          simp [hab.symm]
        have hs'_erase : (s' : Finset (Fin n)).erase a = (s : Finset (Fin n)).erase b := by
          rw [hs', Finset.erase_insert (by simp [ha_not])]
        have hs_eq : s = insert b ((s' : Finset (Fin n)).erase a) := by
          rw [hs'_erase, Finset.insert_erase hb_mem]
        have hrec := ih _ hk' s' t rfl c
        have hX : extUnit n i F b a ∈ extTwistImage n i j F :=
          extUnit_mem (n := n) (i := i) (j := j) (F := F)
            (fun h => ha_not (h ▸ hb_mem))
        have hmul := Subring.mul_mem _ hX hrec
        have hsingle : extUnit n i F b a * (c • Matrix.single s' t (1 : F)) =
            c • Matrix.single s t (1 : F) := by
          rw [Matrix.mul_smul, extUnit_mul_single ha_s' hb_s' hs_eq]
        rwa [hsingle] at hmul

theorem mem_image_of_matrix [Fintype F] (hi : 1 ≤ i) (hin : i < n)
    (M : Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F) :
    M ∈ extTwistImage n i j F := by
  rw [Matrix.matrix_eq_sum_single M]
  refine Subring.sum_mem _ (fun s _ => ?_)
  refine Subring.sum_mem _ (fun t _ => ?_)
  have h := smul_single_mem (n := n) (i := i) (j := j) (F := F) hi hin s t (M s t)
  convert h using 1
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem closure_extTwistImage_eq_top [Fintype F] (hi : 1 ≤ i) (hin : i < n) :
    extTwistImage n i j F = ⊤ := by
  refine le_antisymm le_top ?_
  intro M _
  exact mem_image_of_matrix (n := n) (i := i) (j := j) (F := F) hi hin M

theorem addSubgroup_closure_range_extTwist_eq_top [Fintype F] (hi : 1 ≤ i) (hin : i < n) :
    AddSubgroup.closure (Set.range (extTwist n i j F)) = ⊤ := by
  have hR : extTwistImage n i j F = ⊤ := closure_extTwistImage_eq_top hi hin
  have hclo : (Submonoid.closure (Set.range (extTwist n i j F)) :
      Set (Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F)) =
      Set.range (extTwist n i j F) := by
    ext M
    rw [MonoidHom.mclosure_range]
    change M ∈ MonoidHom.mrange (extTwist n i j F) ↔ M ∈ Set.range (extTwist n i j F)
    rw [MonoidHom.mem_mrange]
    rfl
  refine le_antisymm le_top ?_
  intro M _
  have hM : M ∈ extTwistImage n i j F := by rw [hR]; trivial
  rw [extTwistImage, Subring.mem_closure_iff] at hM
  rwa [hclo] at hM

end CFSG.LieType.SpecialLinear
