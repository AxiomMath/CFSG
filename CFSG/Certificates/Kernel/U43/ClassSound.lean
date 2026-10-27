module

public import Certificates.Data.Kernel.U43.Class
public import CFSG.Certificates.Kernel.U43.FastSound

public section

namespace CFSG.KC.U43

open CFSG.KC.Loop CFSG.KD.U43 CFSG.RankThree.PartTwo.Sec4.Item434RemU43 CFSG.KC.G2Three

theorem build_parF {X G : ℕ → ℕ} {K : ℕ} {gens : List (List ℕ)}
    (hg : ∀ s < K, DatF (gens.getD s one4) (G s)) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)) (i : ℕ), acc.size = i + 1 →
      (∀ t < i + 1, DatF (acc.getD t one4) (X t)) → parF X G K par i = true →
      (par.foldl (fun acc ps => acc.push (mul4 (acc.getD ps.1 one4) (gens.getD ps.2 one4)))
          acc).size = i + 1 + par.length ∧
        ∀ t < i + 1 + par.length,
          DatF ((par.foldl (fun acc ps => acc.push (mul4 (acc.getD ps.1 one4)
            (gens.getD ps.2 one4))) acc).getD t one4) (X t)
  | [], acc, i, hs, hd, _ => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hs, hd⟩
  | ps :: par, acc, i, hs, hd, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (parF X G K par (i + 1))
        (Nat.ble ps.1 i && Nat.blt ps.2 K && Nat.beq (X (i + 1)) (MF (X ps.1) (G ps.2))) =
        true := h
    obtain ⟨h1, h2⟩ := bAnd_g2 h'
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h1
    obtain ⟨⟨hp, hsK⟩, hx⟩ := h1
    have hnew : DatF (mul4 (acc.getD ps.1 one4) (gens.getD ps.2 one4)) (X (i + 1)) := by
      rw [hx]
      exact mulDF (hd _ (by omega)) (hg _ hsK)
    have ih := build_parF hg par
      (acc.push (mul4 (acc.getD ps.1 one4) (gens.getD ps.2 one4))) (i + 1)
      (by rw [Array.size_push, hs]) (fun t ht => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · rw [getD_push_lt one4 (by rw [hs]; exact ht)]
          exact hd t ht
        · rw [ht, ← hs, getD_push_eq]
          rw [hs]
          exact hnew) h2
    rw [List.foldl_cons, List.length_cons]
    exact ⟨by rw [ih.1]; omega, fun t ht => ih.2 t (by omega)⟩

theorem orbGens_conjF {A GA GB : ℕ → ℕ} (hA : lettersF A = true)
    (hga : ∀ s < 2, GA s = wordF A [s]) (hgb : ∀ s < 2, GB s = wordF A (invWord [s]))
    {s : ℕ} (hs : s < 2) {x : List ℕ} {X : ℕ} (hx : DatF x X) :
    DatF (conjStep (orbGens.getD s (wordPair [])) x) (conjF GA GB s X) := by
  have e : orbGens.getD s (wordPair []) = wordPair [s] := by
    interval_cases s <;> rfl
  rw [e, conjF, hga s hs, hgb s hs]
  exact conjDF hA [s] hx

theorem orbit_par {X GA GB : ℕ → ℕ} {x₀ : List ℕ}
    (hg : ∀ s < 2, ∀ {x : List ℕ} {Y : ℕ}, DatF x Y →
      DatF (conjStep (orbGens.getD s (wordPair [])) x) (conjF GA GB s Y)) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)) (i : ℕ), acc.size = i + 1 →
      (∀ t < i + 1, DatF (acc.getD t x₀) (X t)) →
      (∀ j < par.length, (par.getD j (0, 0)).1 ≤ i + j ∧ (par.getD j (0, 0)).2 < 2 ∧
        X (i + j + 1) = conjF GA GB (par.getD j (0, 0)).2 (X (par.getD j (0, 0)).1)) →
      (par.foldl (fun acc ps =>
          acc.push (conjStep (orbGens.getD ps.2 (wordPair [])) (acc.getD ps.1 x₀))) acc).size =
          i + 1 + par.length ∧
        ∀ t < i + 1 + par.length,
          DatF ((par.foldl (fun acc ps =>
            acc.push (conjStep (orbGens.getD ps.2 (wordPair [])) (acc.getD ps.1 x₀))) acc).getD
              t x₀) (X t)
  | [], acc, i, hs, hd, _ => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hs, hd⟩
  | ps :: par, acc, i, hs, hd, h => by
    obtain ⟨hp, hsK, hx⟩ := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at hp hsK hx
    have hnew : DatF (conjStep (orbGens.getD ps.2 (wordPair [])) (acc.getD ps.1 x₀))
        (X (i + 1)) := by
      rw [hx]
      exact hg _ hsK (hd _ (by omega))
    have ih := orbit_par hg par
      (acc.push (conjStep (orbGens.getD ps.2 (wordPair [])) (acc.getD ps.1 x₀))) (i + 1)
      (by rw [Array.size_push, hs]) (fun t ht => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · rw [getD_push_lt x₀ (by rw [hs]; exact ht)]
          exact hd t ht
        · rw [ht, ← hs, getD_push_eq]
          rw [hs]
          exact hnew) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        simp only [List.getD_cons_succ] at this
        have e : i + 1 + j = i + (j + 1) := by omega
        rw [e]
        exact this)
    rw [List.foldl_cons, List.length_cons]
    exact ⟨by rw [ih.1]; omega, fun t ht => ih.2 t (by omega)⟩

theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem stepF_spec {X GA GB PP : ℕ → ℕ} {n h s c p x : ℕ} {k : ℕ → Bool}
    (hst : stepF X GA GB PP n h s c p x k = true) :
    h < c ∧ p ≤ c ∧ p < n ∧ X p = conjF GA GB s x ∧
      (p = c → PP (c - 1) = 2 * h + s ∧ k (c + 1) = true) ∧ (p ≠ c → k c = true) := by
  unfold stepF at hst
  obtain ⟨h1, h2⟩ := bAnd_g2 hst
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h1
  obtain ⟨⟨⟨a, b⟩, c'⟩, d⟩ := h1
  refine ⟨a, b, c', d, fun hpc => ?_, fun hpc => ?_⟩
  · have hb : Nat.beq p c = true := Nat.beq_eq.mpr hpc
    rw [hb] at h2
    obtain ⟨e1, e2⟩ := bAnd_g2 h2
    rw [Nat.beq_eq, Nat.pred_eq_sub_one] at e1
    exact ⟨e1, e2⟩
  · have hb : Nat.beq p c = false := by
      cases hq : Nat.beq p c
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hq) hpc
    rw [hb] at h2
    exact h2

theorem ostep_at {X GA GB WH PP : ℕ → ℕ} {n lo m hi : ℕ}
    (hc : ostepF X GA GB WH PP n lo m hi = true) (hm : m ≤ 64 * hi) :
    ∀ j < m, stepF X GA GB PP n (lo + j) 0 (wC (WH (lo + j))) (wP (WH (lo + j)) 0) (X (lo + j))
      (fun c1 => stepF X GA GB PP n (lo + j) 1 c1 (wP (WH (lo + j)) 1) (X (lo + j))
        fun c2 => Nat.beq (wC (WH (lo + j + 1))) c2) = true := by
  intro j hj
  have := allBelow_g2 hc hm j hj
  simp only [letB_eq] at this
  exact this

end CFSG.KC.U43

end
