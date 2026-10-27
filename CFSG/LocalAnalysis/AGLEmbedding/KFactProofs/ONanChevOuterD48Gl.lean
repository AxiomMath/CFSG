module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Letters

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

open CFSG.Quasithin

@[expose] def XGL (b : GF512) : GL (Fin 8) GF512 := ⟨Xm b, Xm b, Xm_mul_self b, Xm_mul_self b⟩

@[expose] def YGL (b : GF512) : GL (Fin 8) GF512 := ⟨Ym b, Ym b, Ym_mul_self b, Ym_mul_self b⟩

@[expose] def ZGL (s : Bool) (c : GF512) : GL (Fin 8) GF512 :=
  ⟨Zm s c, Zm s c, Zm_mul_self s c, Zm_mul_self s c⟩

theorem XGL_add (a b : GF512) : XGL (a + b) = XGL a * XGL b := Units.ext (Xm_add a b).symm

theorem YGL_add (a b : GF512) : YGL (a + b) = YGL a * YGL b := Units.ext (Ym_add a b).symm

theorem ZGL_add (s : Bool) (a b : GF512) : ZGL s (a + b) = ZGL s a * ZGL s b := by
  cases s
  · exact Units.ext (Zm_neg_add a b).symm
  · exact Units.ext (Zm_pos_add a b).symm

theorem XGL_zero : XGL 0 = 1 := Units.ext Xm_zero

theorem YGL_zero : YGL 0 = 1 := Units.ext Ym_zero

theorem ZGL_zero (s : Bool) : ZGL s 0 = 1 := by
  cases s
  · exact Units.ext (root_zero _)
  · exact Units.ext (root_zero _)

theorem letterGL_of_lt_nine {k : ℕ} (hk : k < 9) : letterGL k = XGL (parC k) :=
  Units.ext (by simp [letterGL, letterMat, hk, XGL])

theorem letterGL_of_mid_pos {k : ℕ} (hk : 9 ≤ k) (hk' : k < 12) :
    letterGL k = ZGL true (xC ^ (k - 9)) :=
  Units.ext (by simp [letterGL, letterMat, ZGL, show ¬ k < 9 by omega, hk'])

theorem letterGL_of_neg {k : ℕ} (hk : 12 ≤ k) (hk' : k < 21) :
    letterGL k = YGL (parC (k - 12)) :=
  Units.ext (by simp [letterGL, letterMat, YGL, show ¬ k < 9 by omega,
    show ¬ k < 12 by omega, hk'])

theorem letterGL_of_mid_neg {k : ℕ} (hk : 21 ≤ k) :
    letterGL k = ZGL false (xC ^ (k - 21)) :=
  Units.ext (by simp [letterGL, letterMat, ZGL, show ¬ k < 9 by omega,
    show ¬ k < 12 by omega, show ¬ k < 21 by omega])

theorem letterMat_zero_ne_one : letterMat 0 ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 1
  revert this
  decide +kernel

@[expose] def letterGroup : Subgroup (GL (Fin 8) GF512) :=
  Subgroup.closure {A | ∃ k, k < 24 ∧ letterGL k = A}

theorem letterGL_mem {k : ℕ} (hk : k < 24) : letterGL k ∈ letterGroup :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem gf8_bits_zero : ∀ u : GF8, ∃ j0 j1 j2 : Bool,
    (⟨u, 0, 0⟩ : GF512) = (if j0 then parC 0 else 0) + (if j1 then parC 1 else 0) +
      (if j2 then parC 2 else 0) := by decide +kernel

theorem gf8_bits_one : ∀ u : GF8, ∃ j0 j1 j2 : Bool,
    (⟨0, u, 0⟩ : GF512) = (if j0 then parC 3 else 0) + (if j1 then parC 4 else 0) +
      (if j2 then parC 5 else 0) := by decide +kernel

theorem gf8_bits_two : ∀ u : GF8, ∃ j0 j1 j2 : Bool,
    (⟨0, 0, u⟩ : GF512) = (if j0 then parC 6 else 0) + (if j1 then parC 7 else 0) +
      (if j2 then parC 8 else 0) := by decide +kernel

theorem gf512_split : ∀ b : GF512, b = ⟨b.c0, 0, 0⟩ + ⟨0, b.c1, 0⟩ + ⟨0, 0, b.c2⟩ := by
  decide +kernel

theorem gf512_fixed : ∀ c : GF512, c ^ 8 = c → c = ⟨c.c0, 0, 0⟩ := by decide +kernel

theorem gf8_bits_fixed : ∀ u : GF8, ∃ j0 j1 j2 : Bool,
    (⟨u, 0, 0⟩ : GF512) = (if j0 then 1 else 0) + (if j1 then xC else 0) +
      (if j2 then xC ^ 2 else 0) := by decide +kernel

theorem mem_of_basis {S : Set GF512} (h0 : (0 : GF512) ∈ S) (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
    (hb : ∀ t, t < 9 → parC t ∈ S) (b : GF512) : b ∈ S := by
  have hite : ∀ (j : Bool) (t : ℕ), t < 9 → (if j then parC t else 0) ∈ S := by
    intro j t ht
    cases j
    · simpa using h0
    · simpa using hb t ht
  have hsum : ∀ (t0 t1 t2 : ℕ), t0 < 9 → t1 < 9 → t2 < 9 → ∀ j0 j1 j2 : Bool,
      (if j0 then parC t0 else 0) + (if j1 then parC t1 else 0) + (if j2 then parC t2 else 0) ∈
        S := fun t0 t1 t2 h0' h1' h2' j0 j1 j2 =>
    hadd _ (hadd _ (hite j0 t0 h0') _ (hite j1 t1 h1')) _ (hite j2 t2 h2')
  rw [gf512_split b]
  refine hadd _ (hadd _ ?_ _ ?_) _ ?_
  · obtain ⟨j0, j1, j2, h⟩ := gf8_bits_zero b.c0
    rw [h]
    exact hsum 0 1 2 (by norm_num) (by norm_num) (by norm_num) j0 j1 j2
  · obtain ⟨j0, j1, j2, h⟩ := gf8_bits_one b.c1
    rw [h]
    exact hsum 3 4 5 (by norm_num) (by norm_num) (by norm_num) j0 j1 j2
  · obtain ⟨j0, j1, j2, h⟩ := gf8_bits_two b.c2
    rw [h]
    exact hsum 6 7 8 (by norm_num) (by norm_num) (by norm_num) j0 j1 j2

theorem xC_pow_eight_one : xC ^ 8 = xC := by decide +kernel

theorem xC_pow_eight (n : ℕ) : (xC ^ n) ^ 8 = xC ^ n := by
  rw [← pow_mul, mul_comm, pow_mul, xC_pow_eight_one]

theorem XGL_mem (b : GF512) : XGL b ∈ letterGroup := by
  refine mem_of_basis (S := {b | XGL b ∈ letterGroup}) ?_ ?_ ?_ b
  · show XGL 0 ∈ letterGroup
    rw [XGL_zero]; exact Subgroup.one_mem _
  · intro a ha b hb
    show XGL (a + b) ∈ letterGroup
    rw [XGL_add]; exact Subgroup.mul_mem _ ha hb
  · intro t ht
    show XGL (parC t) ∈ letterGroup
    rw [← letterGL_of_lt_nine ht]; exact letterGL_mem (by omega)

theorem YGL_mem (b : GF512) : YGL b ∈ letterGroup := by
  refine mem_of_basis (S := {b | YGL b ∈ letterGroup}) ?_ ?_ ?_ b
  · show YGL 0 ∈ letterGroup
    rw [YGL_zero]; exact Subgroup.one_mem _
  · intro a ha b hb
    show YGL (a + b) ∈ letterGroup
    rw [YGL_add]; exact Subgroup.mul_mem _ ha hb
  · intro t ht
    show YGL (parC t) ∈ letterGroup
    have := letterGL_of_neg (k := t + 12) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at this
    rw [← this]; exact letterGL_mem (by omega)

theorem ZGL_mem (s : Bool) {c : GF512} (hc : c ^ 8 = c) : ZGL s c ∈ letterGroup := by
  have hbase : ∀ j, j < 3 → ZGL s (xC ^ j) ∈ letterGroup := by
    intro j hj
    cases s
    · have := letterGL_of_mid_neg (k := j + 21) (by omega)
      rw [Nat.add_sub_cancel] at this
      rw [← this]; exact letterGL_mem (by omega)
    · have := letterGL_of_mid_pos (k := j + 9) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at this
      rw [← this]; exact letterGL_mem (by omega)
  have h0 : ZGL s 1 ∈ letterGroup := by simpa using hbase 0 (by norm_num)
  have h1 : ZGL s xC ∈ letterGroup := by simpa using hbase 1 (by norm_num)
  have h2 : ZGL s (xC ^ 2) ∈ letterGroup := hbase 2 (by norm_num)
  have hite : ∀ (j : Bool) (v : GF512), ZGL s v ∈ letterGroup →
      ZGL s (if j then v else 0) ∈ letterGroup := by
    intro j v hv
    cases j
    · simp only [Bool.false_eq_true, ite_false]
      rw [ZGL_zero]; exact Subgroup.one_mem _
    · simpa using hv
  obtain ⟨j0, j1, j2, h⟩ := gf8_bits_fixed c.c0
  rw [gf512_fixed c hc, h, ZGL_add, ZGL_add]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hite j0 1 h0) (hite j1 xC h1))
    (hite j2 (xC ^ 2) h2)

end CFSG.AGLEmbedding.ChevOuterD48
