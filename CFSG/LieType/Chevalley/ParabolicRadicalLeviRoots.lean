module

public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.PositiveRootCollection

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem parabolicDegree_add (J : Set (Fin τ.rank)) (u v : Fin τ.rank → ℤ) :
    parabolicDegree τ J (u + v) = parabolicDegree τ J u + parabolicDegree τ J v := by
  simp only [parabolicDegree, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem parabolicDegree_nsmul (J : Set (Fin τ.rank)) (k : ℕ) (v : Fin τ.rank → ℤ) :
    parabolicDegree τ J (k • v) = k * parabolicDegree τ J v := by
  simp only [parabolicDegree, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem parabolicDegree_zero (J : Set (Fin τ.rank)) : parabolicDegree τ J 0 = 0 := by
  simp [parabolicDegree]

theorem parabolicDegree_neg (J : Set (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    parabolicDegree τ J (-v) = -parabolicDegree τ J v := by
  simp only [parabolicDegree, Pi.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem parabolicDegree_single_of_mem {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) :
    parabolicDegree τ J (Pi.single j 1) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · rfl
  · exact Pi.single_eq_of_ne (fun h => hi (by rw [h]; exact hj)) _

theorem parabolicDegree_reflect {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J)
    (v : Fin τ.rank → ℤ) : parabolicDegree τ J (reflect τ j v) = parabolicDegree τ J v := by
  rw [reflect, sub_eq_add_neg, parabolicDegree_add, ← neg_smul, show
    (-(∑ k, τ.cartan j k * v k)) • (Pi.single j 1 : Fin τ.rank → ℤ) =
      Pi.single j (-(∑ k, τ.cartan j k * v k)) by rw [← Pi.single_smul, smul_eq_mul, mul_one]]
  have : parabolicDegree τ J (Pi.single j (-(∑ k, τ.cartan j k * v k))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · rfl
    · exact Pi.single_eq_of_ne (fun h => hi (by rw [h]; exact hj)) _
  rw [this, add_zero]

theorem parabolicDegree_nonneg {J : Set (Fin τ.rank)} {v : Fin τ.rank → ℤ}
    (hv : ∀ j, 0 ≤ v j) : 0 ≤ parabolicDegree τ J v :=
  Finset.sum_nonneg fun i _ => by split_ifs; exacts [le_rfl, hv i]

theorem exists_not_mem_ne_zero_of_parabolicDegree_ne_zero {J : Set (Fin τ.rank)}
    {v : Fin τ.rank → ℤ} (h : parabolicDegree τ J v ≠ 0) : ∃ i ∉ J, v i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (Finset.sum_eq_zero fun i _ => by split_ifs with hi; exacts [rfl, hcon i hi])

theorem mem_parabolicRadicalRoots_iff {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ} :
    α ∈ parabolicRadicalRoots τ J ↔
      IsRoot τ α ∧ 0 < height α ∧ ∃ i ∉ J, α i ≠ 0 := by
  constructor
  · rintro ⟨⟨hα, hpos⟩, hnot⟩
    refine ⟨hα, hpos, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hnot ⟨⟨hα, hcon⟩, hα, hpos⟩
  · rintro ⟨hα, hpos, i, hi, hαi⟩
    exact ⟨⟨hα, hpos⟩, fun h => hαi (h.1.2 i hi)⟩

theorem one_le_parabolicDegree_of_mem
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots τ J) : 1 ≤ parabolicDegree τ J α := by
  classical
  obtain ⟨hroot, hpos, i, hi, hαi⟩ := mem_parabolicRadicalRoots_iff.1 hα
  have hnn := (IsRoot.height_pos_iff hroot).1 hpos
  have h1 : 1 ≤ α i := by have := hnn i; omega
  calc (1 : ℤ) ≤ α i := h1
    _ = if i ∈ J then 0 else α i := by simp [hi]
    _ ≤ parabolicDegree τ J α :=
      Finset.single_le_sum (f := fun k => if k ∈ J then 0 else α k)
        (fun k _ => by split_ifs; exacts [le_rfl, hnn k]) (Finset.mem_univ i)

theorem mem_parabolicRadicalRoots_of_degree {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hpos : 0 < height α) (hd : parabolicDegree τ J α ≠ 0) :
    α ∈ parabolicRadicalRoots τ J := by
  obtain ⟨i, hi, hαi⟩ := exists_not_mem_ne_zero_of_parabolicDegree_ne_zero hd
  exact mem_parabolicRadicalRoots_iff.2 ⟨hα, hpos, i, hi, hαi⟩

theorem add_mem_parabolicRadicalRoots
    {J : Set (Fin τ.rank)} {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α ∧ 0 < height α) (hβ : β ∈ parabolicRadicalRoots τ J) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ parabolicRadicalRoots τ J := by
  have hβ' := mem_parabolicRadicalRoots_iff.1 hβ
  have hpos : 0 < height (a • α + b • β) := by
    rw [height_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith [hα.2, hβ'.2.1]
  refine mem_parabolicRadicalRoots_of_degree hr hpos ?_
  rw [parabolicDegree_add, parabolicDegree_nsmul, parabolicDegree_nsmul]
  have h1 := one_le_parabolicDegree_of_mem hβ
  have h2 := parabolicDegree_nonneg (J := J) ((IsRoot.height_pos_iff hα.1).1 hα.2)
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have ha' : (0 : ℤ) ≤ a := by exact_mod_cast Nat.zero_le a
  nlinarith

theorem add_mem_parabolicRadicalRootsGe
    {J : Set (Fin τ.rank)} {h : ℤ} {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α ∧ 0 < height α) (hβ : β ∈ parabolicRadicalRootsGe τ J h) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ parabolicRadicalRootsGe τ J h := by
  refine ⟨add_mem_parabolicRadicalRoots hα hβ.1 ha hb hr, ?_⟩
  rw [height_nsmul_add_nsmul]
  have hβ' := mem_parabolicRadicalRoots_iff.1 hβ.1
  have ha' : (0 : ℤ) ≤ a := by exact_mod_cast Nat.zero_le a
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hα.2, hβ'.2.1, hβ.2]

theorem add_mem_parabolicPosRoots {J : Set (Fin τ.rank)} {α β : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicPosRoots τ J) (hβ : β ∈ parabolicPosRoots τ J) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ parabolicPosRoots τ J := by
  refine ⟨⟨hr, fun i hi => ?_⟩, hr, ?_⟩
  · simp [hα.1.2 i hi, hβ.1.2 i hi]
  · rw [height_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith [hα.2.2, hβ.2.2]

theorem parabolicRadicalRoots_pos {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots τ J) : IsRoot τ α ∧ 0 < height α :=
  hα.1

theorem parabolicPosRoots_pos {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicPosRoots τ J) : IsRoot τ α ∧ 0 < height α :=
  hα.2

theorem disjoint_parabolicRadicalRoots_parabolicPosRoots (J : Set (Fin τ.rank)) :
    Disjoint (parabolicRadicalRoots τ J) (parabolicPosRoots τ J) :=
  Set.disjoint_left.2 fun _ h h' => h.2 h'

theorem parabolicRadicalRoots_union (J : Set (Fin τ.rank)) :
    parabolicRadicalRoots τ J ∪ parabolicPosRoots τ J = {α | IsRoot τ α ∧ 0 < height α} := by
  ext α
  constructor
  · rintro (h | h)
    exacts [h.1, h.2]
  · intro h
    by_cases hJ : α ∈ parabolicPosRoots τ J
    · exact Or.inr hJ
    · exact Or.inl ⟨h, hJ⟩

theorem reflect_mem_parabolicRadicalRoots
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J)
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRadicalRoots τ J) :
    reflect τ j α ∈ parabolicRadicalRoots τ J := by
  have hroot := IsRoot.reflect j hα.1.1
  have hd := one_le_parabolicDegree_of_mem hα
  rw [← parabolicDegree_reflect hj] at hd
  obtain ⟨i, hi, hαi⟩ := exists_not_mem_ne_zero_of_parabolicDegree_ne_zero (J := J)
    (show parabolicDegree τ J (reflect τ j α) ≠ 0 by omega)
  have hpos : 0 < height (reflect τ j α) := by
    rcases IsRoot.height_pos_or_neg hroot with h | h
    · exact h
    · exfalso
      have hle := (IsRoot.height_neg_iff hroot).1 h i
      have hnn := (IsRoot.height_pos_iff hα.1.1).1 hα.1.2 i
      have hcoord : reflect τ j α i = α i := by
        rw [reflect, Pi.sub_apply, Pi.smul_apply,
          Pi.single_eq_of_ne (fun h => hi (by rw [h]; exact hj)), smul_zero, sub_zero]
      rw [hcoord] at hle hαi
      omega
  exact mem_parabolicRadicalRoots_of_degree hroot hpos (by omega)

theorem image_reflect_parabolicRadicalRoots
    {J : Set (Fin τ.rank)} {j : Fin τ.rank}
    (hj : j ∈ J) : reflect τ j '' parabolicRadicalRoots τ J = parabolicRadicalRoots τ J := by
  refine Set.Subset.antisymm ?_ fun α hα => ⟨reflect τ j α,
    reflect_mem_parabolicRadicalRoots hj hα, reflect_reflect τ j α⟩
  rintro _ ⟨α, hα, rfl⟩
  exact reflect_mem_parabolicRadicalRoots hj hα

theorem exists_mem_parabolicWeylGroup_smul
    {J : Set (Fin τ.rank)} :
    ∀ (n : ℕ) (α : Fin τ.rank → ℤ), (height α).toNat = n → α ∈ parabolicPosRoots τ J →
      ∃ w ∈ parabolicWeylGroup τ J, ∃ j ∈ J, w • (Pi.single j 1 : Fin τ.rank → ℤ) = α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α hn hα
    obtain ⟨⟨hroot, hzero⟩, -, hpos⟩ := hα
    have hnn := (IsRoot.height_pos_iff hroot).1 hpos
    obtain ⟨i, hαi, hci⟩ := exists_cartan_pos (IsRoot.ne_zero hroot) hnn
    have hiJ : i ∈ J := by
      by_contra hi
      rw [hzero i hi] at hαi
      exact lt_irrefl 0 hαi
    by_cases hsimple : α = Pi.single i 1
    · exact ⟨1, one_mem _, i, hiJ, by rw [one_smul, hsimple]⟩
    · have hβ : reflect τ i α ∈ {β | IsRoot τ β ∧ 0 < height β ∧ β ≠ Pi.single i 1} :=
        (bijOn_reflect i).mapsTo ⟨hroot, hpos, hsimple⟩
      have hht : height (reflect τ i α) = height α - ∑ j, τ.cartan i j * α j := by
        simp [reflect, height, Finset.sum_sub_distrib, Pi.single_apply]
      have hβJ : reflect τ i α ∈ parabolicPosRoots τ J := by
        refine ⟨⟨hβ.1, fun k hk => ?_⟩, hβ.1, hβ.2.1⟩
        rw [reflect, Pi.sub_apply, Pi.smul_apply,
          Pi.single_eq_of_ne (fun h => hk (by rw [h]; exact hiJ)), smul_zero, sub_zero,
          hzero k hk]
      have hlt : (height (reflect τ i α)).toNat < n := by
        rw [← hn, hht]
        have := hβ.2.1
        omega
      obtain ⟨w, hw, j, hj, hwj⟩ := ih _ hlt _ rfl hβJ
      refine ⟨simple τ i * w, mul_mem (Subgroup.subset_closure ⟨i, hiJ, rfl⟩) hw, j, hj, ?_⟩
      rw [mul_smul, hwj, simple_smul, reflect_reflect]

end CFSG.LieType.Chevalley
