module

public import CFSG.Certificates.Kernel.Asc82Syl.Pc
public import CFSG.Certificates.Kernel.Asc82Syl.Core

public section

namespace CFSG.KS.Asc82Syl

variable {R : Type*} [Ring R]

@[expose] def PM (x y : R) : Prop := x = y ∨ x = -y

theorem PM.refl (x : R) : PM x x := Or.inl rfl

theorem PM.symm {x y : R} (h : PM x y) : PM y x := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (neg_neg _).symm

theorem PM.trans {x y z : R} (h1 : PM x y) (h2 : PM y z) : PM x z := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

theorem PM.mul {x x' y y' : R} (h1 : PM x x') (h2 : PM y y') : PM (x * y) (x' * y') := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp [PM]

theorem PM.of_eq {x y : R} (h : x = y) : PM x y := Or.inl h

theorem PM.cancel {a x y : R} (ha : IsUnit a) (h : PM (a * x) (a * y)) : PM x y := by
  rcases h with h | h
  · exact Or.inl (ha.mul_left_cancel h)
  · rw [← mul_neg] at h
    exact Or.inr (ha.mul_left_cancel h)

theorem Cpm_PM {x y : R} (h : Cpm x y) : PM (x * y) (y * x) := Cpm_iff.1 h

theorem PM_of_Spm {w : ℕ → R} {l : ℕ} {x : R} (h : x ∈ Spm w l) : ∃ e < 2 ^ l, PM x (w e) :=
  mem_Spm.1 h

theorem Spm_of_PM {w : ℕ → R} {l e : ℕ} {x : R} (he : e < 2 ^ l) (h : PM x (w e)) : x ∈ Spm w l :=
  mem_Spm.2 ⟨e, he, h⟩

structure PcHyp (w : ℕ → R) (k l : ℕ) : Prop where
  w0 : w 0 = 1
  cl : ∀ x ∈ Spm w (k + l), ∀ y ∈ Spm w (k + l), x * y ∈ Spm w (k + l)
  clE : ∀ x ∈ Spm w k, ∀ y ∈ Spm w k, x * y ∈ Spm w k
  ab : ∀ x ∈ Spm w k, ∀ y ∈ Spm w k, Cpm x y
  norm : ∀ y ∈ Spm w (k + l), ∀ x ∈ Spm w k, ∃ x' ∈ Spm w k, x * y = y * x'
  unit : ∀ e < 2 ^ (k + l), IsUnit (w e)
  inj : ∀ e < 2 ^ (k + l), ∀ f < 2 ^ (k + l), PM (w e) (w f) → e = f
  split : ∀ e < 2 ^ (k + l), w e = w (e % 2 ^ k) * w (e / 2 ^ k * 2 ^ k)

variable {w : ℕ → R} {k l : ℕ}

noncomputable def mulI (h : PcHyp w k l) (i j : Fin (2 ^ (k + l))) : Fin (2 ^ (k + l)) :=
  ⟨(PM_of_Spm (h.cl _ (Spm_w i.2) _ (Spm_w j.2))).choose,
    (PM_of_Spm (h.cl _ (Spm_w i.2) _ (Spm_w j.2))).choose_spec.1⟩

theorem mulI_spec (h : PcHyp w k l) (i j : Fin (2 ^ (k + l))) :
    PM (w (mulI h i j)) (w i * w j) :=
  PM.symm (PM_of_Spm (h.cl _ (Spm_w i.2) _ (Spm_w j.2))).choose_spec.2

theorem idx_eq (h : PcHyp w k l) {i j : Fin (2 ^ (k + l))} (hij : PM (w i) (w j)) : i = j :=
  Fin.ext (h.inj _ i.2 _ j.2 hij)

theorem mulI_eq (h : PcHyp w k l) {i j c : Fin (2 ^ (k + l))} (hc : PM (w c) (w i * w j)) :
    mulI h i j = c :=
  idx_eq h ((mulI_spec h i j).trans hc.symm)

@[expose] def oneI (k l : ℕ) : Fin (2 ^ (k + l)) := ⟨0, Nat.two_pow_pos _⟩

theorem ring_bound (h : PcHyp w k l) (Qm : ℕ → ℕ → ℕ)
    (hQ : ∀ u < 2 ^ l, ∀ v < 2 ^ l, Qm u v < 2 ^ l ∧
      ∃ f < 2 ^ k, PM (w (u * 2 ^ k) * w (v * 2 ^ k)) (w (f + Qm u v * 2 ^ k)))
    (𝓛 : Set (Finset (Fin (2 ^ l)))) (h0 : {⟨0, Nat.two_pow_pos l⟩} ∈ 𝓛)
    (h2 : ∀ X ∈ 𝓛, ∀ x : Fin (2 ^ l), x ∉ X →
      (⟨Qm x x, (hQ x x.2 x x.2).1⟩ : Fin (2 ^ l)) ∈ X →
      (∀ y ∈ X, Qm x y = Qm y x) →
      X ∪ X.image (fun y : Fin (2 ^ l) => (⟨Qm x y, (hQ x x.2 y y.2).1⟩ : Fin (2 ^ l))) ∈ 𝓛)
    (flag : Bool) (bound : ℕ)
    (hbound : ∀ X ∈ 𝓛, ∃ gens : Finset (Fin (2 ^ l)), gens ⊆ X ∧
      ∃ C : Finset (Fin (2 ^ (k + l))),
      (∀ c : Fin (2 ^ (k + l)), c.val < 2 ^ k →
        (∀ g ∈ gens, PM (w c * w (g.val * 2 ^ k)) (w (g.val * 2 ^ k) * w c)) →
        (flag = true → PM (w c * w c) 1) → c ∈ C) ∧ C.card * X.card ≤ bound)
    (H : Finset (Fin (2 ^ (k + l)))) (h1H : oneI k l ∈ H)
    (hmH : ∀ a ∈ H, ∀ b ∈ H, mulI h a b ∈ H) (hcH : ∀ a ∈ H, ∀ b ∈ H, mulI h a b = mulI h b a)
    (hfH : flag = true → ∀ a ∈ H, mulI h a a = oneI k l) : H.card ≤ bound := by
  have hk : 2 ^ k ≤ 2 ^ (k + l) := Nat.pow_le_pow_right (by omega) (by omega)
  have hkl : 2 ^ (k + l) = 2 ^ l * 2 ^ k := by rw [Nat.pow_add, Nat.mul_comm]
  have hw1 : w (oneI k l) = 1 := h.w0
  have hunit : ∀ i : Fin (2 ^ (k + l)), IsUnit (w i) := fun i => h.unit _ i.2
  let π : Fin (2 ^ (k + l)) → Fin (2 ^ l) := fun i => ⟨i.val / 2 ^ k, by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← hkl]
    exact i.2⟩
  have hrepb : ∀ u : Fin (2 ^ l), u.val * 2 ^ k < 2 ^ (k + l) := fun u => by
    rw [hkl]
    exact Nat.mul_lt_mul_of_pos_right u.2 (Nat.two_pow_pos k)
  let rep : Fin (2 ^ l) → Fin (2 ^ (k + l)) := fun u => ⟨u.val * 2 ^ k, hrepb u⟩
  have hsplitI : ∀ (c : Nat) (u : Fin (2 ^ l)), c < 2 ^ k →
      PM (w (c + u.val * 2 ^ k)) (w c * w (u.val * 2 ^ k)) ∧ c + u.val * 2 ^ k < 2 ^ (k + l) := by
    intro c u hc
    have hb : c + u.val * 2 ^ k < 2 ^ (k + l) := by
      rw [hkl]
      have := Nat.mul_le_mul_right (2 ^ k) (Nat.succ_le_of_lt u.2)
      rw [Nat.succ_mul] at this
      omega
    refine ⟨PM.of_eq ?_, hb⟩
    rw [h.split _ hb, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hc, Nat.zero_add]
  let qmQ : Fin (2 ^ l) → Fin (2 ^ l) → Fin (2 ^ l) := fun u v => ⟨Qm u v, (hQ u u.2 v v.2).1⟩
  refine core_table (mulI h) (oneI k l) (fun a b c => ?_) (fun a => ?_) (fun a => ?_)
    (fun a b b' hb => ?_) (fun i => i.val < 2 ^ k) (Nat.two_pow_pos k) (fun i j hi hj => ?_)
    (fun i j hi hj => ?_) (fun i j hi => ?_) π rep (fun i => ?_) (fun u v c hc hv => ?_) qmQ
    (fun u v => ?_) rfl 𝓛 ?_ (fun X hX x hx hxx hc => h2 X hX x hx hxx
      (fun y hy => congrArg Fin.val (hc y hy))) flag bound (fun X hX => ?_) H h1H hmH hcH hfH
  ·
    refine (mulI_eq h ?_).symm
    exact (((mulI_spec h (mulI h a b) c).trans ((mulI_spec h a b).mul (PM.refl (w c)))).trans
      (PM.of_eq (mul_assoc _ _ _))).trans ((PM.refl (w a)).mul (mulI_spec h b c).symm)
  · exact mulI_eq h (by rw [hw1, one_mul]; exact PM.refl _)
  · exact mulI_eq h (by rw [hw1, mul_one]; exact PM.refl _)
  · have e := (mulI_spec h a b).symm.trans (hb ▸ mulI_spec h a b')
    exact idx_eq h (PM.cancel (hunit a) e)
  · obtain ⟨e, he, hpm⟩ := PM_of_Spm (h.clE _ (Spm_w hi) _ (Spm_w hj))
    have : mulI h i j = ⟨e, Nat.lt_of_lt_of_le he hk⟩ := mulI_eq h (PM.symm hpm)
    rw [this]
    exact he
  · exact idx_eq h ((mulI_spec h i j).trans ((Cpm_PM (h.ab _ (Spm_w hi) _ (Spm_w hj))).trans
      (mulI_spec h j i).symm))
  · obtain ⟨x', hx', he⟩ := h.norm _ (Spm_w j.2) _ (Spm_w hi)
    obtain ⟨c, hc, hcx⟩ := PM_of_Spm hx'
    refine ⟨⟨c, Nat.lt_of_lt_of_le hc hk⟩, hc, idx_eq h ?_⟩
    refine (mulI_spec h i j).trans ?_
    rw [he]
    exact ((PM.refl _).mul hcx).trans (mulI_spec h j ⟨c, Nat.lt_of_lt_of_le hc hk⟩).symm
  · refine ⟨⟨i.val % 2 ^ k, Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) hk⟩,
      Nat.mod_lt _ (Nat.two_pow_pos k), (mulI_eq h ?_).symm⟩
    exact PM.of_eq (h.split _ i.2)
  · have h1 := (hsplitI c.val u hc).1
    have h2' : PM (w (rep v)) (w (c.val + u.val * 2 ^ k)) := by
      rw [hv]
      exact (mulI_spec h c (rep u)).trans h1.symm
    have e := h.inj _ (rep v).2 _ (hsplitI c.val u hc).2 h2'
    apply Fin.ext
    have e2 : (c.val + u.val * 2 ^ k) / 2 ^ k = u.val := by
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hc, Nat.zero_add]
    change v.val * 2 ^ k = c.val + u.val * 2 ^ k at e
    rw [← e2, ← e, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]
  · obtain ⟨-, f, hf, hpm⟩ := hQ u u.2 v v.2
    have hb := (hsplitI f ⟨Qm u v, (hQ u u.2 v v.2).1⟩ hf).2
    have : mulI h (rep u) (rep v) = ⟨f + Qm u v * 2 ^ k, hb⟩ := mulI_eq h (PM.symm hpm)
    apply Fin.ext
    change (mulI h (rep u) (rep v)).val / 2 ^ k = Qm u v
    rw [this]
    change (f + Qm u v * 2 ^ k) / 2 ^ k = Qm u v
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hf, Nat.zero_add]
  · have e : π (oneI k l) = ⟨0, Nat.two_pow_pos l⟩ := Fin.ext (Nat.zero_div _)
    rw [e]
    exact h0
  · obtain ⟨gens, hg, C, hC, hb⟩ := hbound X hX
    refine ⟨gens, hg, C, fun c hc hcg hcf => hC c hc (fun g hgg => ?_) (fun hf => ?_), hb⟩
    · exact ((mulI_spec h c (rep g)).symm.trans (hcg g hgg ▸ mulI_spec h (rep g) c))
    · have := (mulI_spec h c c).symm
      rw [hcf hf, hw1] at this
      exact this

end CFSG.KS.Asc82Syl

end
