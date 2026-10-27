module

public import Certificates.Data.Kernel.SporCov.BaseReg
public import CFSG.Certificates.Kernel.SporCov.BaseKit
public import CFSG.Certificates.Kernel.SporCov.F2Reg

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.KC.Loop CFSG.Sporadic.Th

theorem strictN_eqR (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eqR (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

variable {G : Type} [Group G]

@[expose] noncomputable def fG (a b : G) (Rg : List (List ℕ)) : ℕ → ℕ → G
  | 0 => fP a b
  | i + 1 => fun c => if c < 4 then fP a b c else wE (fG a b Rg i) (nthW Rg (c - 4))

theorem fG_lt (a b : G) (Rg : List (List ℕ)) : ∀ (i : ℕ) {c : ℕ}, c < 4 → fG a b Rg i c = fP a b c
  | 0, _, _ => rfl
  | i + 1, c, hc => if_pos hc

theorem wE_congr {f g : ℕ → G} : ∀ {w : List ℕ}, (∀ d ∈ w, f d = g d) → wE f w = wE g w
  | [], _ => rfl
  | d :: w, h => by
    rw [wE_cons, wE_cons, h d List.mem_cons_self,
      wE_congr fun d' hd' => h d' (List.mem_cons_of_mem _ hd')]

theorem lt_of_chW_letRL {j : ℕ} {w : List ℕ} (h : chW (letRL j) w = true) :
    ∀ d ∈ w, d < 4 + j := fun d hd => (letRL_iff j d).1 (chW_mem h d hd)

theorem fG_succ (a b : G) {Rg : List (List ℕ)} :
    ∀ (i : ℕ), (∀ j < i, chW (letRL j) (nthW Rg j) = true) →
      ∀ c, c < 4 + i → fG a b Rg (i + 1) c = fG a b Rg i c
  | 0, _, c, hc => by rw [fG_lt a b Rg 1 (by omega), fG_lt a b Rg 0 (by omega)]
  | i + 1, hR, c, hc => by
    by_cases h4 : c < 4
    · rw [fG_lt a b Rg _ h4, fG_lt a b Rg _ h4]
    · change (if c < 4 then fP a b c else wE (fG a b Rg (i + 1)) (nthW Rg (c - 4))) =
        (if c < 4 then fP a b c else wE (fG a b Rg i) (nthW Rg (c - 4)))
      rw [if_neg h4, if_neg h4]
      have hw := lt_of_chW_letRL (hR (c - 4) (by omega))
      exact wE_congr fun d hd => fG_succ a b i (fun j hj => hR j (by omega)) d
        (by have := hw d hd; omega)

theorem fG_stable (a b : G) {Rg : List (List ℕ)} {n : ℕ}
    (hR : ∀ j < n, chW (letRL j) (nthW Rg j) = true) {k : ℕ} (hk : k ≤ n) {c : ℕ}
    (hc : c < 4 + k) : fG a b Rg n c = fG a b Rg k c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← add_assoc, fG_succ a b (k + d) (fun j hj => hR j (by omega)) c (by omega)]
    exact ih fun j hj => hR j (by omega)

theorem fG_reg (a b : G) {Rg : List (List ℕ)} {n : ℕ}
    (hR : ∀ j < n, chW (letRL j) (nthW Rg j) = true) {i : ℕ} (hi : i < n) :
    fG a b Rg n (4 + i) = wE (fG a b Rg n) (nthW Rg i) := by
  rw [fG_stable a b hR (k := i + 1) hi (by omega)]
  change (if 4 + i < 4 then fP a b (4 + i) else wE (fG a b Rg i) (nthW Rg (4 + i - 4))) = _
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  exact (wE_congr fun d hd => fG_stable a b hR hi.le
    (lt_of_chW_letRL (hR i hi) d hd)).symm

variable {N : ℕ} [MulAction G (Fin N)]

theorem imF_eq {F : ℕ → ℕ → ℕ} {h : ℕ → G} (hF : ∀ c x, x < N → F c x = idx N (h c) x) :
    ∀ (w : List ℕ) {x : ℕ}, x < N → imF F w x = idx N (wE h w) x
  | [], x, _ => by
    change x = _
    rw [wE_nil, idx_one]
  | c :: w, x, hx => by
    change strictN (F c x) (imF F w) = _
    rw [strictN_eqR, hF c x hx, imF_eq hF w (idx_lt _ hx), wE_cons, idx_mul]

section Kit

variable {a b : G} {fA fAi fB fBi : ℕ → ℕ} (hA : ∀ x < N, fA x = idx N a x)
  (hAi : ∀ x < N, fAi x = idx N a⁻¹ x) (hB : ∀ x < N, fB x = idx N b x)
  (hBi : ∀ x < N, fBi x = idx N b⁻¹ x)
include hA hAi hB hBi

theorem gLB_eq (Rg : List (List ℕ)) :
    ∀ (i c x : ℕ), x < N → gLB fA fAi fB fBi Rg i c x = idx N (fG a b Rg i c) x
  | 0, c, x, hx => letB_eq hA hAi hB hBi c hx
  | i + 1, c, x, hx => by
    change Bool.rec (motive := fun _ => ℕ) (imF (gLB fA fAi fB fBi Rg i) (nthW Rg (c - 4)) x)
      (letB fA fAi fB fBi c x) (Nat.blt c 4) = _
    by_cases h4 : c < 4
    · have e : Nat.blt c 4 = true := by rw [Nat.blt_eq]; exact h4
      rw [e, fG_lt a b Rg _ h4]
      exact letB_eq hA hAi hB hBi c hx
    · have e : Nat.blt c 4 = false := by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h4
      rw [e]
      change _ = idx N (if c < 4 then fP a b c else wE (fG a b Rg i) (nthW Rg (c - 4))) x
      rw [if_neg h4]
      exact imF_eq (fun c' x' hx' => gLB_eq Rg i c' x' hx') _ hx

variable {lg : ℕ → ℕ} {tb : ℕ → ℕ → ℕ} {Rg : List (List ℕ)} {n m : ℕ}

omit hA hAi hB hBi in
theorem glB_of_lt {s : ℕ} (hs : s < N) : glB N lg s = s := by
  unfold glB
  rw [(by rw [Nat.blt_eq]; exact hs : Nat.blt s N = true)]

omit hA hAi hB hBi in
theorem glB_of_ge {s : ℕ} (hs : N ≤ s) : glB N lg s = lg (s - N) := by
  unfold glB
  rw [(by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega : Nat.blt s N = false)]
  rfl

def VB (N m s : ℕ) : Prop := s < N ∨ (N ≤ s ∧ s - N < m)

theorem stB_spec (hlg : ∀ j < m, lg j < N) {i : ℕ} (hin : i ≤ n)
    (hR : ∀ j < n, chW (letRL j) (nthW Rg j) = true)
    (hT : ∀ i' < i, ∀ j < m, tb i' j < m ∧ lg (tb i' j) = idx N (fG a b Rg n (4 + i')) (lg j))
    {c s : ℕ} (hc : c < 4 + i) (hs : VB N m s) :
    VB N m (stB N fA fAi fB fBi lg tb Rg n c s) ∧
      glB N lg (stB N fA fAi fB fBi lg tb Rg n c s) = idx N (fG a b Rg n c) (glB N lg s) := by
  have hd : glB N lg s < N := by
    rcases hs with hs | ⟨h1, h2⟩
    · rw [glB_of_lt hs]
      exact hs
    · rw [glB_of_ge h1]
      exact hlg _ h2
  unfold stB
  by_cases h4 : c < 4
  · rw [(by rw [Nat.blt_eq]; exact h4 : Nat.blt c 4 = true)]
    change VB N m (letB fA fAi fB fBi c (glB N lg s)) ∧ glB N lg (letB fA fAi fB fBi c (glB N lg s)) = _
    rw [letB_eq hA hAi hB hBi c hd, fG_lt a b Rg n h4]
    exact ⟨Or.inl (idx_lt _ hd), glB_of_lt (idx_lt _ hd)⟩
  · rw [(by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h4 : Nat.blt c 4 = false)]
    by_cases hN : s < N
    · rw [(by rw [Nat.blt_eq]; exact hN : Nat.blt s N = true)]
      change VB N m (gLB fA fAi fB fBi Rg n c s) ∧ glB N lg (gLB fA fAi fB fBi Rg n c s) = _
      rw [gLB_eq hA hAi hB hBi Rg n c s hN, glB_of_lt hN]
      exact ⟨Or.inl (idx_lt _ hN), glB_of_lt (idx_lt _ hN)⟩
    · rw [(by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hN : Nat.blt s N = false)]
      have hloc : s - N < m := by
        rcases hs with hs | ⟨_, h2⟩
        · exact absurd hs hN
        · exact h2
      obtain ⟨ht, he⟩ := hT (c - 4) (by omega) (s - N) hloc
      change VB N m (N + tb (c - 4) (s - N)) ∧ glB N lg (N + tb (c - 4) (s - N)) = _
      rw [glB_of_ge (Nat.le_add_right N _), Nat.add_sub_cancel_left, he,
        (by omega : 4 + (c - 4) = c), glB_of_ge (by omega)]
      exact ⟨Or.inr ⟨Nat.le_add_right N _, by rw [Nat.add_sub_cancel_left]; exact ht⟩, rfl⟩

theorem imBR_spec (hlg : ∀ j < m, lg j < N) {i : ℕ} (hin : i ≤ n)
    (hR : ∀ j < n, chW (letRL j) (nthW Rg j) = true)
    (hT : ∀ i' < i, ∀ j < m, tb i' j < m ∧ lg (tb i' j) = idx N (fG a b Rg n (4 + i')) (lg j)) :
    ∀ (w : List ℕ) {s : ℕ}, chW (letRL i) w = true → VB N m s →
      VB N m (imBR N fA fAi fB fBi lg tb Rg n w s) ∧
        glB N lg (imBR N fA fAi fB fBi lg tb Rg n w s) = idx N (wE (fG a b Rg n) w) (glB N lg s)
  | [], s, _, hs => by
    change VB N m s ∧ glB N lg s = _
    rw [wE_nil, idx_one]
    exact ⟨hs, rfl⟩
  | c :: w, s, hw, hs => by
    rw [chW_cons, Bool.and_eq_true] at hw
    change VB N m (strictN (stB N fA fAi fB fBi lg tb Rg n c s)
        (imBR N fA fAi fB fBi lg tb Rg n w)) ∧
      glB N lg (strictN (stB N fA fAi fB fBi lg tb Rg n c s)
        (imBR N fA fAi fB fBi lg tb Rg n w)) = _
    rw [strictN_eqR]
    obtain ⟨v1, e1⟩ := stB_spec hA hAi hB hBi hlg hin hR hT ((letRL_iff i c).1 hw.1) hs
    obtain ⟨v2, e2⟩ := imBR_spec hlg hin hR hT w hw.2 v1
    refine ⟨v2, ?_⟩
    rw [e2, e1, wE_cons, idx_mul]

theorem tabs_ok (hlg : ∀ j < m, lg j < N)
    (hreg : ∀ i < n, regB N fA fAi fB fBi lg tb Rg n m i = true) :
    ∀ i ≤ n, ∀ i' < i, ∀ j < m, tb i' j < m ∧
      lg (tb i' j) = idx N (fG a b Rg n (4 + i')) (lg j) := by
  have hR : ∀ j < n, chW (letRL j) (nthW Rg j) = true := fun j hj => by
    have h := hreg j hj
    unfold regB at h
    rw [Bool.and_eq_true] at h
    exact h.1
  intro i
  induction i with
  | zero => intro _ i' hi'; exact absurd hi' (Nat.not_lt_zero _)
  | succ i ih =>
    intro hi i' hi' j hj
    have hT := ih (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
    · exact hT i' hi' j hj
    have h := hreg i' (by omega)
    unfold regB at h
    rw [Bool.and_eq_true, allLt_iff] at h
    have hj' := h.2 j hj
    rw [strictB_eqR] at hj'
    change Bool.rec (motive := fun _ => Bool) false (Nat.beq (glB N lg (imBR N fA fAi fB fBi lg tb
      Rg n (nthW Rg i') (N + j))) (lg (tb i' j))) (Nat.blt (tb i' j) m) = true at hj'
    cases hb : Nat.blt (tb i' j) m
    · rw [hb] at hj'
      exact absurd hj' Bool.false_ne_true
    · rw [hb] at hj'
      have e := Nat.eq_of_beq_eq_true hj'
      obtain ⟨-, e2⟩ := imBR_spec hA hAi hB hBi hlg (by omega) hR hT (nthW Rg i') h.1
        (Or.inr ⟨Nat.le_add_right N j, by rw [Nat.add_sub_cancel_left]; exact hj⟩)
      rw [e2, glB_of_ge (Nat.le_add_right N j), Nat.add_sub_cancel_left,
        ← fG_reg a b hR (by omega)] at e
      exact ⟨Nat.le_of_ble_eq_true hb, e.symm⟩

end Kit

theorem kitB_sound {a b : G} {fA fAi fB fBi : ℕ → ℕ} (hA : ∀ x < N, fA x = idx N a x)
    (hAi : ∀ x < N, fAi x = idx N a⁻¹ x) (hB : ∀ x < N, fB x = idx N b x)
    (hBi : ∀ x < N, fBi x = idx N b⁻¹ x) {lg : ℕ → ℕ} {tb : ℕ → ℕ → ℕ} {Rg : List (List ℕ)}
    {n m : ℕ} {bs : List ℕ} (hsep : ∀ g : G, (∀ j ∈ bs, idx N g (lg j) = lg j) → g = 1)
    {k : (List ℕ → List ℕ → Bool) → (List ℕ → ℕ) → Bool}
    (h : kitB N fA fAi fB fBi lg tb Rg n m bs k = true) :
    ∃ (E : List ℕ → List ℕ → Bool) (K : List ℕ → ℕ) (f : ℕ → G), k E K = true ∧
      Model (letRL n) E (wE f) ∧
      (∀ u, chW (letRL n) u = true → wE f u = 1 → E u [] = true) ∧
      (∀ u v, chW (letRL n) u = true → chW (letRL n) v = true → wE f u = wE f v → K u = K v) ∧
      ∀ c < 4, f c = fP a b c := by
  unfold kitB at h
  simp only [Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨hlg', hbs⟩, hreg⟩, hk⟩ := h
  have hlg : ∀ j < m, lg j < N := fun j hj => Nat.le_of_ble_eq_true (hlg' j hj)
  have hbm : ∀ j ∈ bs, j < m := fun j hj => Nat.le_of_ble_eq_true (chW_mem hbs j hj)
  have hR : ∀ j < n, chW (letRL j) (nthW Rg j) = true := fun j hj => by
    have h := hreg j hj
    unfold regB at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have hT := tabs_ok hA hAi hB hBi hlg hreg n le_rfl
  set f := fG a b Rg n
  have key : ∀ u, chW (letRL n) u = true → ∀ j ∈ bs,
      glB N lg (imBR N fA fAi fB fBi lg tb Rg n u (N + j)) = idx N (wE f u) (lg j) := by
    intro u hu j hj
    have v : VB N m (N + j) := Or.inr ⟨Nat.le_add_right N j, by
      rw [Nat.add_sub_cancel_left]; exact hbm j hj⟩
    rw [(imBR_spec hA hAi hB hBi hlg le_rfl hR hT u hu v).2, glB_of_ge (Nat.le_add_right N j),
      Nat.add_sub_cancel_left]
  have eqS : ∀ u v, chW (letRL n) u = true → chW (letRL n) v = true →
      ∀ bs' : List ℕ, (∀ j ∈ bs', j ∈ bs) →
      (eqBR N fA fAi fB fBi lg tb Rg n bs' u v = true ↔ ∀ j ∈ bs', idx N (wE f u) (lg j) =
        idx N (wE f v) (lg j)) := by
    intro u v hu hv bs' hsub
    induction bs' with
    | nil => simp [eqBR]
    | cons j bs' ih =>
      change Bool.rec (motive := fun _ => Bool) false (eqBR N fA fAi fB fBi lg tb Rg n bs' u v)
        (Nat.beq (glB N lg (imBR N fA fAi fB fBi lg tb Rg n u (N + j)))
          (glB N lg (imBR N fA fAi fB fBi lg tb Rg n v (N + j)))) = true ↔ _
      have hj := hsub j List.mem_cons_self
      rw [key u hu j hj, key v hv j hj, List.forall_mem_cons,
        ← ih fun j' hj' => hsub j' (List.mem_cons_of_mem _ hj')]
      cases hb : Nat.beq (idx N (wE f u) (lg j)) (idx N (wE f v) (lg j))
      · have hne : idx N (wE f u) (lg j) ≠ idx N (wE f v) (lg j) := fun e => by
          rw [e, Nat.beq_refl] at hb
          exact Bool.false_ne_true hb.symm
        simp [hne]
      · simp [Nat.eq_of_beq_eq_true hb]
  refine ⟨_, _, f, hk, Model.of_wE _ fun u v hu hv he => ?_, fun u hu h1 => ?_,
    fun u v hu hv he => ?_, fun c hc => fG_lt a b Rg n hc⟩
  · have hp := (eqS u v hu hv bs fun j hj => hj).1 he
    have h1 : (wE f v)⁻¹ * wE f u = 1 := hsep _ fun j hj => by
      rw [idx_mul, hp j hj, idx_inv_idx]
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  · refine (eqS u [] hu (chW_nil _) bs fun j hj => hj).2 fun j _ => ?_
    rw [h1, wE_nil]
  · have : ∀ bs' : List ℕ, (∀ j ∈ bs', j ∈ bs) →
        keyBR N fA fAi fB fBi lg tb Rg n bs' u = keyBR N fA fAi fB fBi lg tb Rg n bs' v := by
      intro bs' hsub
      induction bs' with
      | nil => rfl
      | cons j bs' ih =>
        change Nat.add (glB N lg (imBR N fA fAi fB fBi lg tb Rg n u (N + j)))
            (Nat.mul N (keyBR N fA fAi fB fBi lg tb Rg n bs' u)) =
          Nat.add (glB N lg (imBR N fA fAi fB fBi lg tb Rg n v (N + j)))
            (Nat.mul N (keyBR N fA fAi fB fBi lg tb Rg n bs' v))
        have hj := hsub j List.mem_cons_self
        rw [key u hu j hj, key v hv j hj, he,
          ih fun j' hj' => hsub j' (List.mem_cons_of_mem _ hj')]
    exact this bs fun j hj => hj

end CFSG.KD.SporCov

end
