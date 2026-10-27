module

public import Certificates.Data.Kernel.LocalQT.Core
public import CFSG.Certificates.Kernel.LocalQTTab2KSound

public section

namespace CFSG.KC.LQT.M24Snd

open CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl

private theorem aux_suba_spanLt_spec (x : ℕ) (k : List ℕ → List ℕ → List ℕ) :
    ∀ (ys acc : List ℕ), ys.Pairwise (· ≤ ·) →
      ∃ p q r : List ℕ, spanLt x ys k acc = k p r ∧ p = acc.reverse ++ q ∧ ys = q ++ r ∧
        (∀ z ∈ q, z < x) ∧ (∀ z ∈ r, x ≤ z)
  | [], acc, _ => ⟨acc.reverse, [], [], rfl, (List.append_nil _).symm, rfl, by simp, by simp⟩
  | y :: ys', acc, h => by
    have hy : ∀ z ∈ ys', y ≤ z := (List.pairwise_cons.mp h).1
    have hs : ys'.Pairwise (· ≤ ·) := (List.pairwise_cons.mp h).2
    obtain ⟨p, q, r, e, hp, hqr, hq, hr⟩ := aux_suba_spanLt_spec x k ys' (y :: acc) hs
    change ∃ p q r : List ℕ, Bool.rec (motive := fun _ => List ℕ) (k acc.reverse (List.cons y ys'))
      (spanLt x ys' k (List.cons y acc)) (Nat.blt y x) = k p r ∧ p = acc.reverse ++ q ∧
        List.cons y ys' = q ++ r ∧ (∀ z ∈ q, z < x) ∧ (∀ z ∈ r, x ≤ z)
    cases hb : Nat.blt y x
    · have hyx : ¬ y < x := by
        intro h
        have h' : Nat.blt y x = true := by simpa [Nat.blt_eq] using h
        rw [hb] at h'
        simp at h'
      refine ⟨acc.reverse, [], List.cons y ys', rfl, (List.append_nil _).symm, rfl, by simp, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact not_lt.mp hyx
      · exact le_trans (not_lt.mp hyx) (hy z hz)
    · have hyx : y < x := by simpa [Nat.blt_eq] using hb
      refine ⟨p, List.cons y q, r, e, ?_, by simp [hqr], ?_, hr⟩
      · rw [hp]
        simp [List.reverse_cons]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hyx
        · exact hq z hz

private theorem aux_suba_mergeK_sorted : ∀ (xs ys : List ℕ),
    xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) → (mergeK xs ys).Pairwise (· ≤ ·)
  | [], _, _, hy => hy
  | x :: xs, ys, hx, hy => by
    obtain ⟨p, q, r, e, hp, hqr, hq, hr⟩ := aux_suba_spanLt_spec x
      (fun p r => List.append p (List.cons x (mergeK xs r))) ys [] hy
    have hpq : p = q := hp
    have hxs : xs.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hx).2
    have hxge : ∀ z ∈ xs, x ≤ z := (List.pairwise_cons.mp hx).1
    rw [hqr] at hy
    have hqs : q.Pairwise (· ≤ ·) := (List.pairwise_append.mp hy).1
    have hrs : r.Pairwise (· ≤ ·) := (List.pairwise_append.mp hy).2.1
    have hM : (mergeK xs r).Pairwise (· ≤ ·) := aux_suba_mergeK_sorted xs r hxs hrs
    have hMge : ∀ b ∈ mergeK xs r, x ≤ b := by
      intro b hb
      rcases List.mem_append.mp ((mergeK_permT xs r).subset hb) with h | h
      · exact hxge b h
      · exact hr b h
    have hfin : (p ++ List.cons x (mergeK xs r)).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨(by rw [hpq]; exact hqs), List.pairwise_cons.mpr ⟨hMge, hM⟩, ?_⟩
      intro a ha b hb
      have ha' : a < x := by
        rw [hpq] at ha
        exact hq a ha
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_of_lt ha'
      · exact le_trans (le_of_lt ha') (hMge b hb)
    change (spanLt x ys (fun p r => List.append p (List.cons x (mergeK xs r))) []).Pairwise _
    rw [e]
    exact hfin

private theorem aux_suba_passGoT_length : ∀ (rs : List (List ℕ)),
    (passGoT rs none).length = (rs.length + 1) / 2 ∧
      ∀ a : List ℕ, (passGoT rs (some a)).length = (rs.length + 2) / 2
  | [] => ⟨rfl, fun _ => rfl⟩
  | r :: rs => by
    obtain ⟨h1, h2⟩ := aux_suba_passGoT_length rs
    constructor
    · change (passGoT rs (some r)).length = (rs.length + 1 + 1) / 2
      exact (h2 r).trans (by omega)
    · intro a
      change (mergeK a r :: passGoT rs none).length = (rs.length + 1 + 2) / 2
      rw [List.length_cons, h1]
      omega

private theorem aux_suba_passGoT_sorted : ∀ (rs : List (List ℕ)),
    (∀ r ∈ rs, r.Pairwise (· ≤ ·)) →
      (∀ s ∈ passGoT rs none, s.Pairwise (· ≤ ·)) ∧
        ∀ a : List ℕ, a.Pairwise (· ≤ ·) → ∀ s ∈ passGoT rs (some a), s.Pairwise (· ≤ ·)
  | [], _ => by
    refine ⟨fun s hs => ?_, fun a ha s hs => ?_⟩
    · change s ∈ ([] : List (List ℕ)) at hs
      simp at hs
    · change s ∈ [a] at hs
      rw [List.mem_singleton] at hs
      rw [hs]
      exact ha
  | r :: rs, h => by
    have hr : r.Pairwise (· ≤ ·) := h r (by simp)
    obtain ⟨h1, h2⟩ := aux_suba_passGoT_sorted rs (fun r' hr' => h r' (by simp [hr']))
    refine ⟨fun s hs => ?_, fun a ha s hs => ?_⟩
    · change s ∈ passGoT rs (some r) at hs
      exact h2 r hr s hs
    · change s ∈ mergeK a r :: passGoT rs none at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact aux_suba_mergeK_sorted a r ha hr
      · exact h1 s hs

private theorem aux_suba_flatten_sorted : ∀ (X : List (List ℕ)),
    (∀ r ∈ X, r.Pairwise (· ≤ ·)) → X.length ≤ 1 → (X.flatten).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | [r], h, _ => by simpa using h r (by simp)
  | _ :: _ :: _, _, hn => by
    simp only [List.length_cons] at hn
    omega

private theorem aux_suba_runs (L : List ℕ) (R : ℕ → List (List ℕ))
    (h0 : R 0 = L.map (fun x => [x])) (hs : ∀ i, R (i + 1) = passK (R i)) :
    ∀ i, (∀ r ∈ R i, r.Pairwise (· ≤ ·)) ∧ (R i).length * 2 ^ i < L.length + 2 ^ i := by
  intro i
  induction i with
  | zero =>
    refine ⟨fun r hr => ?_, ?_⟩
    · rw [h0] at hr
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      exact List.pairwise_singleton _ _
    · rw [h0, List.length_map]
      norm_num
  | succ i ih =>
    have hlen : (passK (R i)).length = ((R i).length + 1) / 2 :=
      (aux_suba_passGoT_length (R i)).1
    rw [hs i, hlen, pow_succ]
    refine ⟨(aux_suba_passGoT_sorted (R i) ih.1).1, ?_⟩
    have h1 : ((R i).length + 1) / 2 * 2 ≤ (R i).length + 1 := Nat.div_mul_le_self _ _
    have h2 : ((R i).length + 1) / 2 * 2 * 2 ^ i ≤ ((R i).length + 1) * 2 ^ i :=
      Nat.mul_le_mul_right _ h1
    nlinarith [ih.2, h2]

private theorem aux_suba_main (l : List ℕ) (hl : l.length ≤ 131072) (R : ℕ → List (List ℕ))
    (h0 : R 0 = l.map (fun x => [x])) (hs : ∀ i, R (i + 1) = passK (R i)) :
    (List.flatten (R 17)).Pairwise (· ≤ ·) := by
  obtain ⟨hsort, hlen⟩ := aux_suba_runs l R h0 hs 17
  rw [show (2 : ℕ) ^ 17 = 131072 by norm_num] at hlen
  exact aux_suba_flatten_sorted (R 17) hsort (by omega)

theorem mergeK_sorted {xs ys : List ℕ} (hx : xs.Pairwise (· ≤ ·)) (hy : ys.Pairwise (· ≤ ·)) :
    (mergeK xs ys).Pairwise (· ≤ ·) :=
  aux_suba_mergeK_sorted xs ys hx hy

theorem passK_length (rs : List (List ℕ)) : (passK rs).length = (rs.length + 1) / 2 :=
  (aux_suba_passGoT_length rs).1

theorem passK_sorted (rs : List (List ℕ)) (h : ∀ r ∈ rs, r.Pairwise (· ≤ ·)) :
    ∀ r ∈ passK rs, r.Pairwise (· ≤ ·) :=
  (aux_suba_passGoT_sorted rs h).1

theorem sortN_sorted (l : List ℕ) (hl : l.length ≤ 131072) : (sortN l).Pairwise (· ≤ ·) :=
  aux_suba_main l hl (fun i => Nat.rec (motive := fun _ => List (List ℕ))
    (List.map (fun x => [x]) l) (fun _ ih => passK ih) i) rfl (fun i => rfl)

end CFSG.KC.LQT.M24Snd

end
