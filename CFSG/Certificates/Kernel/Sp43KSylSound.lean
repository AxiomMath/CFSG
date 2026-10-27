module

public import Certificates.Data.Kernel.Sp43KSyl
public import CFSG.Certificates.Kernel.Sp43KNorm
public import CFSG.Certificates.Kernel.Sp43KOrbGrp

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43 Subgroup

theorem inG_of_mulT_one {a b : ℕ} (ha : InG a) (hb : ExT b) (h : mulT a b = oneT) : InG b := by
  refine ⟨hb, ?_⟩
  set a' : G := ⟨toMT a, ha.2⟩
  have h1 : toMT a * toMT b = 1 := by rw [← toMT_mulT ha.1 hb, h, toMT_oneT]
  have h2 : ((a'⁻¹ : G) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) * toMT a = 1 := by
    have := congrArg Subtype.val (inv_mul_cancel a')
    rw [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  have e : toMT b = ((a'⁻¹ : G) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) := by
    calc toMT b = (((a'⁻¹ : G) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) * toMT a) *
          toMT b := by rw [h2, Matrix.one_mul]
      _ = ((a'⁻¹ : G) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) *
          (toMT a * toMT b) := Matrix.mul_assoc _ _ _
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [e]
  exact (a'⁻¹).2

theorem sylGo_spec {d : ℕ} :
    ∀ (R : List (ℕ × ℕ)) (k : ℕ), sylGo d R k = true →
      (∀ m < R.length, okT (R.getD m (0, 0)).1 = true ∧ okT (R.getD m (0, 0)).2 = true ∧
        spT (R.getD m (0, 0)).1 = true ∧ mulT (R.getD m (0, 0)).1 (R.getD m (0, 0)).2 = oneT) ∧
      (R ≠ [] → k < keyT d (R.getD 0 (0, 0)).1 (R.getD 0 (0, 0)).2) ∧
      (∀ m, m + 1 < R.length → keyT d (R.getD m (0, 0)).1 (R.getD m (0, 0)).2 <
        keyT d (R.getD (m + 1) (0, 0)).1 (R.getD (m + 1) (0, 0)).2)
  | [], _, _ => ⟨fun m hm => by simp at hm, fun h => absurd rfl h, fun m hm => by simp at hm⟩
  | r :: R, k, h => by
    have h' : (okT r.1 && okT r.2 && spT r.1 && mulT r.1 r.2 == oneT &&
        decide (k < keyT d r.1 r.2) && sylGo d R (keyT d r.1 r.2)) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h'
    obtain ⟨i1, i2, i3⟩ := sylGo_spec R _ h6
    refine ⟨fun m hm => ?_, fun _ => h5, fun m hm => ?_⟩
    · rcases m with _ | m
      · exact ⟨h1, h2, h3, h4⟩
      · simp only [List.getD_cons_succ]
        exact i1 m (by simpa using hm)
    · rcases m with _ | m
      · simp only [List.getD_cons_succ, List.getD_cons_zero]
        exact i2 (by rintro rfl; simp at hm)
      · simp only [List.getD_cons_succ]
        exact i3 m (by simpa using hm)

theorem powT_ofT {c : ℕ} (hc : InG c) (e : ℕ) : InG (powT c e) ∧ ofT (powT c e) = ofT c ^ e :=
  powT_spec hc e

theorem keyT_cases (d g g' : ℕ) : keyT d g g' = conjT g g' d ∨
    keyT d g g' = conjT g g' (powT d 2) ∨ keyT d g g' = conjT g g' (powT d 3) ∨
    keyT d g g' = conjT g g' (powT d 4) := by
  unfold keyT
  omega

theorem keyT_le (d g g' : ℕ) : keyT d g g' ≤ conjT g g' d ∧
    keyT d g g' ≤ conjT g g' (powT d 2) ∧ keyT d g g' ≤ conjT g g' (powT d 3) ∧
    keyT d g g' ≤ conjT g g' (powT d 4) := by
  unfold keyT
  omega

theorem keyT_spec {d g g' : ℕ} (hd : InG d) (hd5 : orderOf (ofT d) = 5) (hg : InG g)
    (hg' : InG g') (hgg : mulT g g' = oneT) :
    (okT (keyT d g g') = true ∧ InG (keyT d g g') ∧ ofT (keyT d g g') ≠ 1 ∧
      ofT (keyT d g g') ∈ (zpowers (ofT d)).map (MulAut.conj (ofT g)).toMonoidHom) ∧
    ∀ c, okT c = true → InG c → ofT c ≠ 1 →
      ofT c ∈ (zpowers (ofT d)).map (MulAut.conj (ofT g)).toMonoidHom → keyT d g g' ≤ c := by
  have hc : ∀ k, InG (conjT g g' (powT d k)) ∧ okT (conjT g g' (powT d k)) = true ∧
      ofT (conjT g g' (powT d k)) = ofT g * ofT d ^ k * (ofT g)⁻¹ := fun k =>
    ⟨inG_conjT hg hg' (powT_ofT hd k).1, okT_conjT hg hg' (powT_ofT hd k).1,
      by rw [ofT_conjT hg hg' (powT_ofT hd k).1 hgg, (powT_ofT hd k).2]⟩
  have hc1 : conjT g g' d = conjT g g' (powT d 1) := by
    apply ofT_inj (inG_conjT hg hg' hd) (hc 1).1 (okT_conjT hg hg' hd) (hc 1).2.1
    rw [(hc 1).2.2, ofT_conjT hg hg' hd hgg, pow_one]
  have hne : ∀ k, 0 < k → k < 5 → ofT g * ofT d ^ k * (ofT g)⁻¹ ≠ 1 := by
    intro k hk0 hk5 e
    have : ofT d ^ k = 1 := by
      have := congrArg (fun y => (ofT g)⁻¹ * y * ofT g) e
      simpa [mul_assoc] using this
    have := orderOf_le_of_pow_eq_one hk0 this
    omega
  have hmemk : ∀ k, ofT g * ofT d ^ k * (ofT g)⁻¹ ∈
      (zpowers (ofT d)).map (MulAut.conj (ofT g)).toMonoidHom := fun k =>
    ⟨_, Subgroup.npow_mem_zpowers _ k, by simp⟩
  refine ⟨?_, ?_⟩
  · rcases keyT_cases d g g' with e | e | e | e
    · rw [e, hc1]
      exact ⟨(hc 1).2.1, (hc 1).1, by rw [(hc 1).2.2]; exact hne 1 (by norm_num) (by norm_num),
        by rw [(hc 1).2.2]; exact hmemk 1⟩
    · rw [e]
      exact ⟨(hc 2).2.1, (hc 2).1, by rw [(hc 2).2.2]; exact hne 2 (by norm_num) (by norm_num),
        by rw [(hc 2).2.2]; exact hmemk 2⟩
    · rw [e]
      exact ⟨(hc 3).2.1, (hc 3).1, by rw [(hc 3).2.2]; exact hne 3 (by norm_num) (by norm_num),
        by rw [(hc 3).2.2]; exact hmemk 3⟩
    · rw [e]
      exact ⟨(hc 4).2.1, (hc 4).1, by rw [(hc 4).2.2]; exact hne 4 (by norm_num) (by norm_num),
        by rw [(hc 4).2.2]; exact hmemk 4⟩
  · intro c hco hcG hc1' hcm
    obtain ⟨y, hy, ey⟩ := hcm
    rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, hd5, Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [Finset.mem_range] at hk
    have ec : ofT c = ofT g * ofT d ^ k * (ofT g)⁻¹ := by
      rw [← ey]
      simp
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hc1'
      rw [ec]
      group
    have eq : c = conjT g g' (powT d k) :=
      ofT_inj hcG (hc k).1 hco (hc k).2.1 (by rw [ec, (hc k).2.2])
    obtain ⟨l1, l2, l3, l4⟩ := keyT_le d g g'
    rw [hc1] at l1
    rw [eq]
    interval_cases k
    · exact absurd rfl hk0
    · exact l1
    · exact l2
    · exact l3
    · exact l4

theorem keyT_eq_of_conj {d g g' h h' : ℕ} (hd : InG d) (hd5 : orderOf (ofT d) = 5) (hg : InG g)
    (hg' : InG g') (hgg : mulT g g' = oneT) (hh : InG h) (hh' : InG h') (hhh : mulT h h' = oneT)
    (e : (zpowers (ofT d)).map (MulAut.conj (ofT g)).toMonoidHom =
      (zpowers (ofT d)).map (MulAut.conj (ofT h)).toMonoidHom) :
    keyT d g g' = keyT d h h' := by
  obtain ⟨⟨o1, i1, n1, m1⟩, l1⟩ := keyT_spec hd hd5 hg hg' hgg
  obtain ⟨⟨o2, i2, n2, m2⟩, l2⟩ := keyT_spec hd hd5 hh hh' hhh
  exact le_antisymm (l1 _ o2 i2 n2 (e ▸ m2)) (l2 _ o1 i1 n1 (e ▸ m1))

end CFSG.KC.Sp43K

end
