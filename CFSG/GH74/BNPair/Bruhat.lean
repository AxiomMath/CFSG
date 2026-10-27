module

public import CFSG.GH74.BNPair.Basic
public import CFSG.GH74.BNPair.Length

public section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {J : Set (WeylGroup B N)}

theorem BNCore.bruhat_aux (hJ : BNCore B N J) :
    ∀ k : ℕ,
      (∀ w ∈ Subgroup.closure J, wordLength J w = k → ∀ w' : WeylGroup B N,
        dc B N w = dc B N w' → w = w') ∧
      (∀ s ∈ J, ∀ w ∈ Subgroup.closure J, wordLength J w = k → wordLength J (s * w) = k + 1 →
        dc B N s * dc B N w ⊆ dc B N (s * w)) := by
  have hJ1 : ∀ s ∈ J, s * s = 1 := hJ.mul_self_eq_one
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro w hw hlen w' hdc
      have hw1 : w = 1 := (wordLength_eq_zero_iff hJ1 hw).1 hlen
      subst hw1
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w'
      have h : (n : X) ∈ (B : Set X) := by
        rw [← dc_one (B := B) (N := N), hdc]
        exact coe_mem_dc n
      exact (mk_eq_one_iff.2 h).symm
    · intro s _ w hw hlen _
      have hw1 : w = 1 := (wordLength_eq_zero_iff hJ1 hw).1 hlen
      subst hw1
      rw [mul_one]
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
      exact mem_dc_of_mem hy B.one_mem (mem_dc_one.1 hz) (by simp)
  | succ k ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    have hP : ∀ w ∈ Subgroup.closure J, wordLength J w = k + 1 → ∀ w' : WeylGroup B N,
        dc B N w = dc B N w' → w = w' := by
      intro w hw hlen w' hdc
      have hw1 : w ≠ 1 := by
        rintro rfl
        simp [wordLength_one] at hlen
      obtain ⟨s, hs, hdesc⟩ := exists_left_descent hJ1 hw hw1
      have hw₁mem : s * w ∈ Subgroup.closure J :=
        Subgroup.mul_mem _ (Subgroup.subset_closure hs) hw
      have hlen₁ : wordLength J (s * w) = k := by omega
      have hsw₁ : s * (s * w) = w := by rw [← mul_assoc, hJ1 s hs, one_mul]
      have hQ := ihQ s hs (s * w) hw₁mem hlen₁ (by rw [hsw₁]; exact hlen)
      rw [hsw₁] at hQ
      obtain ⟨n₁, hn₁⟩ := QuotientGroup.mk_surjective (s * w)
      have hy : (n₁ : X) ∈ dc B N (s * w) := by rw [← hn₁]; exact coe_mem_dc n₁
      obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.1 (hJ.subset_mul_self hs (Or.inl B.one_mem))
      have hvy : v * (n₁ : X) ∈ dc B N w := hQ (Set.mem_mul.2 ⟨v, hv, _, hy, rfl⟩)
      have hmem : (n₁ : X) ∈ dc B N s * dc B N w' := by
        rw [← hdc]
        exact Set.mem_mul.2 ⟨u, hu, v * n₁, hvy, by rw [← mul_assoc, huv, one_mul]⟩
      rcases hJ.mul_subset s hs w' hmem with h1 | h1
      · have h2 : dc B N (s * w) = dc B N (s * w') := dc_eq_of_mem hy h1
        have h3 := ihP (s * w) hw₁mem hlen₁ (s * w') h2
        have h4 : w = w' := by
          calc w = s * (s * w) := hsw₁.symm
            _ = s * (s * w') := by rw [h3]
            _ = w' := by rw [← mul_assoc, hJ1 s hs, one_mul]
        exact h4
      · have h2 : dc B N (s * w) = dc B N w' := dc_eq_of_mem hy h1
        have h3 := ihP (s * w) hw₁mem hlen₁ w (by rw [h2, hdc])
        exfalso
        exact hJ.ne_one s hs (by simpa using h3)
    refine ⟨hP, ?_⟩
    intro s hs w hw hlen hlen'
    have hw1 : w ≠ 1 := by
      rintro rfl
      simp [wordLength_one] at hlen
    obtain ⟨t, ht, hdesc⟩ := exists_right_descent hJ1 hw hw1
    have hw₀mem : w * t ∈ Subgroup.closure J :=
      Subgroup.mul_mem _ hw (Subgroup.subset_closure ht)
    have hlen₀ : wordLength J (w * t) = k := by omega
    have hwt : w * t * t = w := by rw [mul_assoc, hJ1 t ht, mul_one]
    have hsw₀mem : s * (w * t) ∈ Subgroup.closure J :=
      Subgroup.mul_mem _ (Subgroup.subset_closure hs) hw₀mem
    have hlen_sw₀ : wordLength J (s * (w * t)) = k + 1 := by
      have h1 := wordLength_mul_gen_le hJ1 ht hsw₀mem
      have h2 := wordLength_gen_mul_le hJ1 hs hw₀mem
      have h3 : s * (w * t) * t = s * w := by rw [mul_assoc, mul_assoc, hJ1 t ht, mul_one]
      rw [h3] at h1
      omega
    have hQ := ihQ s hs (w * t) hw₀mem hlen₀ hlen_sw₀
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    have hz' : z ∈ dc B N (w * t) * dc B N t := by
      have h5 := dc_mul_subset_of (B := B) (N := N) (w * t) t
      rw [hwt] at h5
      exact h5 hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.1 hz'
    have hyz₁ : y * z₁ ∈ dc B N (s * (w * t)) := hQ (Set.mem_mul.2 ⟨y, hy, z₁, hz₁, rfl⟩)
    have h6 : y * (z₁ * z₂) ∈ dc B N (s * (w * t) * t) ∪ dc B N (s * (w * t)) := by
      have h6' := hJ.mul_subset_right ht (s * (w * t))
        (Set.mem_mul.2 ⟨y * z₁, hyz₁, z₂, hz₂, rfl⟩)
      have e : y * z₁ * z₂ = y * (z₁ * z₂) := mul_assoc _ _ _
      rw [e] at h6'
      exact h6'
    have h3 : s * (w * t) * t = s * w := by rw [mul_assoc, mul_assoc, hJ1 t ht, mul_one]
    rw [h3] at h6
    rcases h6 with h6 | h6
    · exact h6
    · have hzw : y * (z₁ * z₂) ∈ dc B N (s * w) ∪ dc B N w :=
        hJ.mul_subset s hs w (Set.mem_mul.2 ⟨y, hy, _, hz, rfl⟩)
      rcases hzw with h7 | h7
      · exact h7
      · exfalso
        have h8 : dc B N w = dc B N (s * (w * t)) := dc_eq_of_mem h7 h6
        have h9 := hP w hw hlen _ h8
        have h10 : s * w = w * t := by
          calc s * w = s * (s * (w * t)) := by rw [← h9]
            _ = w * t := by rw [← mul_assoc, hJ1 s hs, one_mul]
        rw [h10] at hlen'
        omega

theorem BNCore.dc_inj (hJ : BNCore B N J) {w w' : WeylGroup B N} (hw : w ∈ Subgroup.closure J)
    (h : dc B N w = dc B N w') : w = w' :=
  (hJ.bruhat_aux (wordLength J w)).1 w hw rfl w' h

theorem BNCore.mul_subset_of_lt (hJ : BNCore B N J) {s w : WeylGroup B N} (hs : s ∈ J)
    (hw : w ∈ Subgroup.closure J) (h : wordLength J w < wordLength J (s * w)) :
    dc B N s * dc B N w ⊆ dc B N (s * w) := by
  have h1 := wordLength_gen_mul_le hJ.mul_self_eq_one hs hw
  exact (hJ.bruhat_aux (wordLength J w)).2 s hs w hw rfl (by omega)

theorem mem_closure_mul_gen {s : WeylGroup B N} (hs : s ∈ J) {w : WeylGroup B N}
    (hw : w ∈ Subgroup.closure J) : s * w ∈ Subgroup.closure J :=
  Subgroup.mul_mem _ (Subgroup.subset_closure hs) hw

theorem mem_parabolicSet_iff {x : X} :
    x ∈ parabolicSet B N J ↔ ∃ w ∈ Subgroup.closure J, x ∈ dc B N w := by
  simp only [parabolicSet, bruhatSet, Set.mem_iUnion]
  constructor
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, hx⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, hx⟩

theorem dc_subset_parabolicSet {w : WeylGroup B N} (hw : w ∈ Subgroup.closure J) :
    dc B N w ⊆ parabolicSet B N J :=
  fun _ hx => mem_parabolicSet_iff.2 ⟨w, hw, hx⟩

theorem BNCore.dc_mul_subset_parabolicSet (hJ : BNCore B N J) :
    ∀ (l : List (WeylGroup B N)), (∀ s ∈ l, s ∈ J) → ∀ a ∈ Subgroup.closure J,
      dc B N a * dc B N l.prod ⊆ parabolicSet B N J := by
  intro l
  induction l with
  | nil =>
    intro _ a ha x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    rw [List.prod_nil] at hz
    exact dc_subset_parabolicSet ha (mem_dc_of_mem hy B.one_mem (mem_dc_one.1 hz) (by simp))
  | cons s l ih =>
    intro hl a ha x hx
    have hs : s ∈ J := hl s (by simp)
    have hl' : ∀ t ∈ l, t ∈ J := fun t ht => hl t (by simp [ht])
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    rw [List.prod_cons] at hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_mul.1 (dc_mul_subset_of s l.prod hz)
    have hyz₁ := hJ.mul_subset_right hs a (Set.mem_mul.2 ⟨y, hy, z₁, hz₁, rfl⟩)
    have hmul : y * (z₁ * z₂) = y * z₁ * z₂ := (mul_assoc _ _ _).symm
    rw [hmul]
    rcases hyz₁ with h | h
    · exact ih hl' (a * s) (Subgroup.mul_mem _ ha (Subgroup.subset_closure hs))
        (Set.mem_mul.2 ⟨_, h, z₂, hz₂, rfl⟩)
    · exact ih hl' a ha (Set.mem_mul.2 ⟨_, h, z₂, hz₂, rfl⟩)

theorem BNCore.mul_mem_parabolicSet (hJ : BNCore B N J) {x y : X}
    (hx : x ∈ parabolicSet B N J) (hy : y ∈ parabolicSet B N J) :
    x * y ∈ parabolicSet B N J := by
  obtain ⟨a, ha, hxa⟩ := mem_parabolicSet_iff.1 hx
  obtain ⟨b, hb, hyb⟩ := mem_parabolicSet_iff.1 hy
  obtain ⟨l, hl, hprod⟩ := (mem_closure_iff_exists_list hJ.mul_self_eq_one).1 hb
  subst hprod
  exact hJ.dc_mul_subset_parabolicSet l hl a ha (Set.mem_mul.2 ⟨x, hxa, y, hyb, rfl⟩)

@[expose] def BNCore.parabolicSubgroup (hJ : BNCore B N J) : Subgroup X where
  carrier := parabolicSet B N J
  mul_mem' := hJ.mul_mem_parabolicSet
  one_mem' := mem_parabolicSet_iff.2 ⟨1, Subgroup.one_mem _, mem_dc_one.2 B.one_mem⟩
  inv_mem' := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_parabolicSet_iff.1 hx
    exact mem_parabolicSet_iff.2 ⟨w⁻¹, Subgroup.inv_mem _ hw, inv_mem_dc hxw⟩

theorem BNCore.coe_parabolicSubgroup (hJ : BNCore B N J) :
    (hJ.parabolicSubgroup : Set X) = parabolicSet B N J := rfl

theorem BNCore.parabolic_eq (hJ : BNCore B N J) : parabolic B N J = hJ.parabolicSubgroup := by
  unfold parabolic
  rw [← hJ.coe_parabolicSubgroup]
  exact Subgroup.closure_eq _

theorem BNCore.coe_parabolic (hJ : BNCore B N J) :
    (parabolic B N J : Set X) = parabolicSet B N J := by
  rw [hJ.parabolic_eq]
  rfl

theorem BNCore.mem_parabolic_iff (hJ : BNCore B N J) {x : X} :
    x ∈ parabolic B N J ↔ ∃ w ∈ Subgroup.closure J, x ∈ dc B N w := by
  rw [← SetLike.mem_coe, hJ.coe_parabolic]
  exact mem_parabolicSet_iff

end CFSG.GH74.BNPair
