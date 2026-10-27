module

public import CFSG.Certificates.Kernel.LocalQTTab2KSound
public import Certificates.Data.Kernel.LocalQT.Core

public section

namespace CFSG.KC.LQT.PHSnd

open CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl

private theorem spanLt_cons_lt {x y : ℕ} (h : y < x) (ys acc : List ℕ)
    (k : List ℕ → List ℕ → List ℕ) :
    spanLt x (y :: ys) k acc = spanLt x ys k (y :: acc) := by
  have hb : Nat.blt y x = true := Eq.mpr Nat.blt_eq h
  change Bool.rec (motive := fun _ => List ℕ) (k (List.reverse acc) (List.cons y ys))
    (spanLt x ys k (List.cons y acc)) (Nat.blt y x) = _
  rw [hb]

private theorem spanLt_cons_ge {x y : ℕ} (h : ¬ y < x) (ys acc : List ℕ)
    (k : List ℕ → List ℕ → List ℕ) :
    spanLt x (y :: ys) k acc = k acc.reverse (y :: ys) := by
  have hb : Nat.blt y x = false := by
    cases hb' : Nat.blt y x
    · rfl
    · exact absurd (Eq.mp Nat.blt_eq hb') h
  change Bool.rec (motive := fun _ => List ℕ) (k (List.reverse acc) (List.cons y ys))
    (spanLt x ys k (List.cons y acc)) (Nat.blt y x) = _
  rw [hb]

private theorem spanLt_spec (x : ℕ) (k : List ℕ → List ℕ → List ℕ) : ∀ (ys acc : List ℕ),
    ∃ p r, spanLt x ys k acc = k (acc.reverse ++ p) r ∧ ys = p ++ r ∧ (∀ y ∈ p, y < x) ∧
      ∀ z r', r = z :: r' → x ≤ z
  | [], acc => by
    refine ⟨[], [], ?_, rfl, by simp, fun z r' h => nomatch h⟩
    change k (List.reverse acc) [] = _
    rw [List.append_nil]
  | y :: ys, acc => by
    by_cases h : y < x
    · obtain ⟨p, r, e, hys, hp, hr⟩ := spanLt_spec x k ys (y :: acc)
      refine ⟨y :: p, r, ?_, by rw [hys, List.cons_append], ?_, hr⟩
      · rw [spanLt_cons_lt h, e]
        simp
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact h
        · exact hp z hz
    · refine ⟨[], y :: ys, ?_, rfl, by simp, ?_⟩
      · rw [spanLt_cons_ge h, List.append_nil]
      · intro z r' hzr
        obtain ⟨rfl, -⟩ := List.cons.inj hzr
        exact Nat.not_lt.1 h

private theorem mergeK_cons (x : ℕ) (xs ys : List ℕ) :
    mergeK (x :: xs) ys = spanLt x ys (fun p r => List.append p (List.cons x (mergeK xs r))) [] :=
  rfl

private theorem mergeK_sorted : ∀ (xs ys : List ℕ), xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) →
    (mergeK xs ys).Pairwise (· ≤ ·)
  | [], _, _, hy => hy
  | x :: xs, ys, hx, hy => by
    obtain ⟨p, r, e, hys, hp, hr⟩ :=
      spanLt_spec x (fun p r => List.append p (List.cons x (mergeK xs r))) ys []
    rw [mergeK_cons, e]
    change (p ++ x :: mergeK xs r).Pairwise (· ≤ ·)
    have hys' : (p ++ r).Pairwise (· ≤ ·) := by rw [← hys]; exact hy
    obtain ⟨hpp, hrr, -⟩ := List.pairwise_append.1 hys'
    obtain ⟨hxs1, hxs2⟩ := List.pairwise_cons.1 hx
    have hm : (mergeK xs r).Pairwise (· ≤ ·) := mergeK_sorted xs r hxs2 hrr
    have hge : ∀ b ∈ mergeK xs r, x ≤ b := by
      intro b hb
      rcases List.mem_append.1 ((mergeK_permT xs r).subset hb) with hb | hb
      · exact hxs1 b hb
      · cases r with
        | nil => simp at hb
        | cons z r' =>
          have hz : x ≤ z := hr z r' rfl
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hz
          · exact hz.trans ((List.pairwise_cons.1 hrr).1 b hb)
    refine List.pairwise_append.2 ⟨hpp, List.pairwise_cons.2 ⟨hge, hm⟩, fun a ha b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact (hp a ha).le
    · exact (hp a ha).le.trans (hge b hb)

private theorem passGoT_sorted : ∀ (rs : List (List ℕ)) (o : Option (List ℕ)),
    (∀ r ∈ rs, r.Pairwise (· ≤ ·)) → (∀ a ∈ o, a.Pairwise (· ≤ ·)) →
    ∀ r ∈ passGoT rs o, r.Pairwise (· ≤ ·)
  | [], none, _, _ => by
    change ∀ r ∈ ([] : List (List ℕ)), r.Pairwise (· ≤ ·)
    intro r hr
    simp at hr
  | [], some a, _, ha => by
    change ∀ r ∈ ([a] : List (List ℕ)), r.Pairwise (· ≤ ·)
    intro r hr
    rw [List.mem_singleton.1 hr]
    exact ha a rfl
  | r :: rs, none, hrs, _ => by
    change ∀ r' ∈ passGoT rs (some r), r'.Pairwise (· ≤ ·)
    refine passGoT_sorted rs (some r) (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))
      (fun a ha => ?_)
    have hra : r = a := Option.some.inj ha
    rw [← hra]
    exact hrs r (List.mem_cons.2 (Or.inl rfl))
  | r :: rs, some a, hrs, ha => by
    change ∀ r' ∈ List.cons (mergeK a r) (passGoT rs none), r'.Pairwise (· ≤ ·)
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact mergeK_sorted a r (ha a rfl) (hrs r (List.mem_cons.2 (Or.inl rfl)))
    · exact passGoT_sorted rs none (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))
        (fun a ha => by simp at ha) r' hr'

private theorem passGoT_length : ∀ rs : List (List ℕ),
    (∀ a, (passGoT rs (some a)).length = (rs.length + 2) / 2) ∧
      (passGoT rs none).length = (rs.length + 1) / 2
  | [] => ⟨fun _ => rfl, rfl⟩
  | r :: rs => by
    obtain ⟨h1, h2⟩ := passGoT_length rs
    refine ⟨fun a => ?_, ?_⟩
    · change (passGoT rs none).length + 1 = (rs.length + 1 + 2) / 2
      omega
    · change (passGoT rs (some r)).length = (rs.length + 1 + 1) / 2
      have := h1 r
      omega

private theorem pass_inv {n : ℕ} (m : ℕ) (R : List (List ℕ)) (hs : ∀ r ∈ R, r.Pairwise (· ≤ ·))
    (hl : R.length * 2 ^ m < n + 2 ^ m) :
    (∀ r ∈ passK R, r.Pairwise (· ≤ ·)) ∧ (passK R).length * 2 ^ (m + 1) < n + 2 ^ (m + 1) := by
  refine ⟨passGoT_sorted R none hs (fun _ h => by simp at h), ?_⟩
  have h1 : (passK R).length = (R.length + 1) / 2 := (passGoT_length R).2
  rw [h1, Nat.pow_succ]
  generalize 2 ^ m = P at hl ⊢
  generalize hq : (R.length + 1) / 2 = q
  have h2 : 2 * q ≤ R.length + 1 := by omega
  calc q * (P * 2) = 2 * q * P := by rw [Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm q 2]
    _ ≤ (R.length + 1) * P := Nat.mul_le_mul_right P h2
    _ = R.length * P + P := by rw [Nat.add_mul, Nat.one_mul]
    _ < n + P + P := by omega
    _ = n + P * 2 := by omega

private theorem flatten_sorted {R : List (List ℕ)} (hs : ∀ r ∈ R, r.Pairwise (· ≤ ·))
    (hl : R.length ≤ 1) : R.flatten.Pairwise (· ≤ ·) := by
  match R, hs, hl with
  | [], _, _ => simp
  | [r], hs, _ =>
    rw [List.flatten_singleton]
    exact hs r (List.mem_singleton.2 rfl)
  | _ :: _ :: _, _, hl => exact absurd hl (by simp only [List.length_cons]; omega)

theorem sortN_sorted {l : List ℕ} (hl : l.length ≤ 2 ^ 17) :
    (sortN l).Pairwise (· ≤ ·) := by
  have key : ∀ m, (∀ r ∈ Nat.rec (motive := fun _ => List (List ℕ)) (List.map (fun x => [x]) l)
        (fun _ ih => passK ih) m, r.Pairwise (· ≤ ·)) ∧
      (Nat.rec (motive := fun _ => List (List ℕ)) (List.map (fun x => [x]) l)
        (fun _ ih => passK ih) m).length * 2 ^ m < l.length + 2 ^ m := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun r hr => ?_, ?_⟩
      · change r ∈ List.map (fun x => [x]) l at hr
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
        exact List.pairwise_singleton _ _
      · change (List.map (fun x => [x]) l).length * 2 ^ 0 < l.length + 2 ^ 0
        rw [List.length_map]
        omega
    | succ m ih => exact pass_inv m _ ih.1 ih.2
  obtain ⟨h1, h2⟩ := key 17
  exact flatten_sorted h1 (by omega)

end CFSG.KC.LQT.PHSnd

end
