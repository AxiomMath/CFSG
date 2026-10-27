module

public import CFSG.Certificates.Kernel.Co1PPathSound
public import Certificates.Data.Kernel.Co1PPathM

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TreeK

theorem pin_prefix {act : Nat → Nat → Nat} {ng root : Nat} {rs : List (Nat × Nat)} {T R : Nat → Nat}
    {M : Nat} (hM : M ≤ rs.length + 1) (hw : (treePts act ng root rs).2 = true)
    (hr : recsEqK R rs 0 = true) (hp : ∀ i < M, pinAt act root T R i = true) :
    ∀ i < M, T i = walkAt act ng root rs i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | j
    · have h0 : Nat.beq (T 0) root = true := hp 0 hi
      rw [walkAt_zero hw]
      exact Nat.eq_of_beq_eq_true h0
    · have h1 : Nat.beq (T (j + 1)) (act (Nat.mod (R j) 8) (T (Nat.div (R j) 8))) = true :=
        hp (j + 1) hi
      have hj : j < rs.length := by omega
      obtain ⟨hpj, -, he⟩ := walkAt_succ hw hj
      have hrj := recsEqK_sound rs 0 hr j hj
      rw [Nat.zero_add] at hrj
      rw [hrj] at hpj he
      rw [he, Nat.eq_of_beq_eq_true h1]
      change act (R j % 8) (T (R j / 8)) = act (R j % 8) (walkAt act ng root rs (R j / 8))
      rw [ih (R j / 8) (by simp only at hpj; omega) (by simp only at hpj; omega)]

theorem pathM_sound {act : Nat → Nat → Nat} {T R H : Nat → Nat} {M N : Nat}
    (hT : ∀ i < M, T i = H i)
    (hHs : ∀ i, 0 < i → i < N → H i = act (labK R i) (H (parK R i))) :
    ∀ d i, i < N → (pathM act T M R d i).2 = true → (pathM act T M R d i).1 = H i
  | 0, i, _, h => by
    have h' : Nat.blt i M = true := h
    exact hT i (lt_of_blt' h')
  | d + 1, i, hi, h => by
    by_cases hm : i < M
    · have hb : Nat.blt i M = true := by rw [Nat.blt_eq]; exact hm
      have e : pathM act T M R (d + 1) i = Prod.mk (T i) true := by
        change Bool.rec (motive := fun _ => Nat × Bool) _ _ (Nat.blt i M) = _
        rw [hb]
      rw [e]
      exact hT i hm
    · have hb : Nat.blt i M = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; exact hm
      have e : pathM act T M R (d + 1) i = Prod.rec (motive := fun _ => Nat × Bool)
          (fun v ok => Prod.mk (act (labK R i) v) (CFSG.KLie.CT.andB ok (Nat.blt (parK R i) i)))
          (pathM act T M R d (parK R i)) := by
        change Bool.rec (motive := fun _ => Nat × Bool) _ _ (Nat.blt i M) = _
        rw [hb]
        rfl
      rw [e] at h ⊢
      rcases hq : pathM act T M R d (parK R i) with ⟨v, ok⟩
      rw [hq] at h
      obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
      have hp := lt_of_blt' h2
      have hv : v = H (parK R i) := by
        have h3 := pathM_sound hT hHs d (parK R i) (by omega) (by rw [hq]; exact h1)
        rw [hq] at h3
        exact h3
      have hi0 : 0 < i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · exact absurd (h0 ▸ hp) (Nat.not_lt_zero _)
        · exact h0
      change act (labK R i) v = H i
      rw [hv, hHs i hi0 hi]

theorem ptM_sound {GK GiK : List Nat} {ng R0 M : Nat} {rs : List (Nat × Nat)} {R TH THi : Nat → Nat}
    (hM : M ≤ rs.length + 1)
    (hh : (treePts (hsAct GK) ng oneK rs).2 = true) (hhi : (treePts (hisAct GiK) ng oneK rs).2 = true)
    (hr : recsEqK R rs 0 = true) (hp : ∀ i < M, pinAt (hsAct GK) oneK TH R i = true)
    (hpi : ∀ i < M, pinAt (hisAct GiK) oneK THi R i = true) {d i : Nat} (hi : i < rs.length + 1)
    (h : (ptM GK GiK TH THi M R R0 d i).2 = true) :
    (ptM GK GiK TH THi M R R0 d i).1 = mulWK (mulWK (walkAt (hsAct GK) ng oneK rs i) R0)
      (walkAt (hisAct GiK) ng oneK rs i) := by
  unfold ptM at h ⊢
  rcases ha : pathM (hsAct GK) TH M R d i with ⟨a, oka⟩
  rcases hb : pathM (hisAct GiK) THi M R d i with ⟨b, okb⟩
  rw [ha, hb] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  have ea : a = walkAt (hsAct GK) ng oneK rs i := by
    have h3 := pathM_sound (pin_prefix hM hh hr hp) (walk_rec hh hr) d i hi (by rw [ha]; exact h1)
    rw [ha] at h3
    exact h3
  have eb : b = walkAt (hisAct GiK) ng oneK rs i := by
    have h3 := pathM_sound (pin_prefix hM hhi hr hpi) (walk_rec hhi hr) d i hi (by rw [hb]; exact h2)
    rw [hb] at h3
    exact h3
  change mulWK (mulWK a R0) b = _
  rw [ea, eb]

end CFSG.KC.Co1P

end
