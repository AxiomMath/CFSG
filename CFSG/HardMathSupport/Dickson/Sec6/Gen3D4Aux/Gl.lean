module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Letters

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.AGLEmbedding.ChevOuter CFSG.Quasithin

@[expose] def XGL (b : GF64) : GL (Fin 8) GF64 := ⟨Xm b, Xm b, Xm_mul_self b, Xm_mul_self b⟩

@[expose] def YGL (b : GF64) : GL (Fin 8) GF64 := ⟨Ym b, Ym b, Ym_mul_self b, Ym_mul_self b⟩

@[expose] def ZGL (s : Bool) (c : GF64) : GL (Fin 8) GF64 :=
  ⟨Zm s c, Zm s c, Zm_mul_self s c, Zm_mul_self s c⟩

theorem XGL_add (a b : GF64) : XGL (a + b) = XGL a * XGL b := Units.ext (Xm_add a b).symm

theorem YGL_add (a b : GF64) : YGL (a + b) = YGL a * YGL b := Units.ext (Ym_add a b).symm

theorem ZGL_add (s : Bool) (a b : GF64) : ZGL s (a + b) = ZGL s a * ZGL s b := by
  cases s
  · exact Units.ext (Zm_neg_add a b).symm
  · exact Units.ext (Zm_pos_add a b).symm

theorem XGL_zero : XGL 0 = 1 := Units.ext Xm_zero

theorem YGL_zero : YGL 0 = 1 := Units.ext Ym_zero

theorem ZGL_zero (s : Bool) : ZGL s 0 = 1 := by
  cases s
  · exact Units.ext (root_zero _)
  · exact Units.ext (root_zero _)

theorem letterGL_of_even {k : ℕ} (hk : k < 12) (he : k % 2 = 0) :
    letterGL k = XGL (wC ^ (k / 2)) :=
  Units.ext (by simp [letterGL, letterMat, hk, he, XGL])

theorem letterGL_of_odd {k : ℕ} (hk : k < 12) (ho : k % 2 = 1) :
    letterGL k = YGL (wC ^ (k / 2)) :=
  Units.ext (by simp [letterGL, letterMat, hk, ho, YGL])

theorem letterGL_pos_mid {k : ℕ} (hk : 12 ≤ k) (hk' : k < 16) (he : k % 2 = 0) :
    letterGL k = ZGL true (if k < 14 then 1 else wqC) :=
  Units.ext (by simp [letterGL, letterMat, ZGL, show ¬ k < 12 by omega, he])

theorem letterGL_neg_mid {k : ℕ} (hk : 12 ≤ k) (hk' : k < 16) (ho : k % 2 = 1) :
    letterGL k = ZGL false (if k < 14 then 1 else wqC) :=
  Units.ext (by simp [letterGL, letterMat, ZGL, show ¬ k < 12 by omega, ho])

theorem letterMat_zero_ne_one : letterMat 0 ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 1
  revert this
  decide +kernel

@[expose] def letterGroup : Subgroup (GL (Fin 8) GF64) :=
  Subgroup.closure {A | ∃ k, k < 16 ∧ letterGL k = A}

theorem letterGL_mem {k : ℕ} (hk : k < 16) : letterGL k ∈ letterGroup :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem gf64_bits : ∀ b : GF64, ∃ j0 j1 j2 j3 j4 j5 : Bool,
    b = (if j0 then wC ^ 0 else 0) + (if j1 then wC ^ 1 else 0) + (if j2 then wC ^ 2 else 0) +
      (if j3 then wC ^ 3 else 0) + (if j4 then wC ^ 4 else 0) + (if j5 then wC ^ 5 else 0) := by
  decide +kernel

theorem gf64_fixed_bits : ∀ c : GF64, c ^ 4 = c → ∃ j0 j1 : Bool,
    c = (if j0 then 1 else 0) + (if j1 then wqC else 0) := by decide +kernel

theorem mem_of_basis {S : Set GF64} (h0 : (0 : GF64) ∈ S) (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
    (hb : ∀ t, t < 6 → wC ^ t ∈ S) (b : GF64) : b ∈ S := by
  have hite : ∀ (j : Bool) (t : ℕ), t < 6 → (if j then wC ^ t else 0) ∈ S := by
    intro j t ht
    cases j
    · simpa using h0
    · simpa using hb t ht
  obtain ⟨j0, j1, j2, j3, j4, j5, h⟩ := gf64_bits b
  rw [h]
  exact hadd _ (hadd _ (hadd _ (hadd _ (hadd _ (hite j0 0 (by norm_num)) _
    (hite j1 1 (by norm_num))) _ (hite j2 2 (by norm_num))) _ (hite j3 3 (by norm_num))) _
    (hite j4 4 (by norm_num))) _ (hite j5 5 (by norm_num))

theorem wqC_pow_four : wqC ^ 4 = wqC := by decide +kernel

theorem XGL_mem (b : GF64) : XGL b ∈ letterGroup := by
  refine mem_of_basis (S := {b | XGL b ∈ letterGroup}) ?_ ?_ ?_ b
  · show XGL 0 ∈ letterGroup
    rw [XGL_zero]; exact Subgroup.one_mem _
  · intro a ha b hb
    show XGL (a + b) ∈ letterGroup
    rw [XGL_add]; exact Subgroup.mul_mem _ ha hb
  · intro t ht
    show XGL (wC ^ t) ∈ letterGroup
    have := letterGL_of_even (k := 2 * t) (by omega) (by omega)
    rw [show 2 * t / 2 = t by omega] at this
    rw [← this]; exact letterGL_mem (by omega)

theorem YGL_mem (b : GF64) : YGL b ∈ letterGroup := by
  refine mem_of_basis (S := {b | YGL b ∈ letterGroup}) ?_ ?_ ?_ b
  · show YGL 0 ∈ letterGroup
    rw [YGL_zero]; exact Subgroup.one_mem _
  · intro a ha b hb
    show YGL (a + b) ∈ letterGroup
    rw [YGL_add]; exact Subgroup.mul_mem _ ha hb
  · intro t ht
    show YGL (wC ^ t) ∈ letterGroup
    have := letterGL_of_odd (k := 2 * t + 1) (by omega) (by omega)
    rw [show (2 * t + 1) / 2 = t by omega] at this
    rw [← this]; exact letterGL_mem (by omega)

theorem ZGL_mem (s : Bool) {c : GF64} (hc : c ^ 4 = c) : ZGL s c ∈ letterGroup := by
  have h1 : ZGL s 1 ∈ letterGroup := by
    cases s
    · have := letterGL_neg_mid (k := 13) (by norm_num) (by norm_num) (by norm_num)
      simp only [show (13 : ℕ) < 14 by norm_num, ite_true] at this
      rw [← this]; exact letterGL_mem (by norm_num)
    · have := letterGL_pos_mid (k := 12) (by norm_num) (by norm_num) (by norm_num)
      simp only [show (12 : ℕ) < 14 by norm_num, ite_true] at this
      rw [← this]; exact letterGL_mem (by norm_num)
  have h2 : ZGL s wqC ∈ letterGroup := by
    cases s
    · have := letterGL_neg_mid (k := 15) (by norm_num) (by norm_num) (by norm_num)
      simp only [show ¬ (15 : ℕ) < 14 by norm_num, ite_false] at this
      rw [← this]; exact letterGL_mem (by norm_num)
    · have := letterGL_pos_mid (k := 14) (by norm_num) (by norm_num) (by norm_num)
      simp only [show ¬ (14 : ℕ) < 14 by norm_num, ite_false] at this
      rw [← this]; exact letterGL_mem (by norm_num)
  have hite : ∀ (j : Bool) (v : GF64), ZGL s v ∈ letterGroup →
      ZGL s (if j then v else 0) ∈ letterGroup := by
    intro j v hv
    cases j
    · simp only [Bool.false_eq_true, ite_false]
      rw [ZGL_zero]; exact Subgroup.one_mem _
    · simpa using hv
  obtain ⟨j0, j1, h⟩ := gf64_fixed_bits c hc
  rw [h, ZGL_add]
  exact Subgroup.mul_mem _ (hite j0 1 h1) (hite j1 wqC h2)

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
