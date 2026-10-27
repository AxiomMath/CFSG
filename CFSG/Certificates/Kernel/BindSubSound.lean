module

public import CFSG.Certificates.Kernel.LceSTabSound

public section

namespace CFSG.Certificates.BindSub

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates.LCE

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem wLet_eq' (W i : ℕ) : wLet W i = W / 2 ^ (8 * i) % 2 ^ 8 := by
  change W >>> (8 * i) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

noncomputable def mv (M W q : ℕ) : ℕ := 2 * mget M (wLet W q / 2) + wLet W q % 2

theorem mapW_succ (M W n : ℕ) : mapW M W (n + 1) = mapW M W n ||| (mv M W n <<< (8 * n)) := by
  have e1 : Nat.shiftRight (wLet W n) 1 = wLet W n / 2 := by
    change wLet W n >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have e2 : Nat.land (wLet W n) 1 = wLet W n % 2 := Nat.and_one_is_mod _
  change Nat.lor (mapW M W n) (Nat.shiftLeft (Nat.add (Nat.mul 2 (mget M (Nat.shiftRight (wLet W n) 1)))
    (Nat.land (wLet W n) 1)) (Nat.mul 8 n)) = _
  unfold mv
  rw [e1, e2]
  rfl

theorem wLet_mapW (M W : ℕ) : ∀ n, (∀ q < n, mv M W q < 256) →
    mapW M W n < 2 ^ (8 * n) ∧ ∀ i < n, wLet (mapW M W n) i = mv M W i
  | 0, _ => ⟨Nat.two_pow_pos _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, hv => by
    obtain ⟨hlt, hget⟩ := wLet_mapW M W n fun q hq => hv q (by omega)
    have hvn := hv n (by omega)
    have hsum : mapW M W n ||| (mv M W n <<< (8 * n)) = 2 ^ (8 * n) * mv M W n + mapW M W n := by
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hlt]
      by_cases hj : j < 8 * n
      · rw [ite_eq_left hj, Nat.mul_comm, Nat.testBit_mul_two_pow, decide_eq_false (by omega)]
        simp
      · rw [ite_eq_right hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega)
          (by omega))), Nat.mul_comm, Nat.testBit_mul_two_pow, decide_eq_true (by omega)]
        simp
    rw [mapW_succ, hsum]
    refine ⟨?_, fun i hi => ?_⟩
    · have : 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 := by rw [Nat.mul_succ, Nat.pow_add]
      rw [this]
      have := Nat.mul_le_mul_left (2 ^ (8 * n)) (Nat.succ_le_of_lt hvn)
      rw [Nat.mul_succ] at this
      omega
    · rw [wLet_eq']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have e1 : 2 ^ (8 * n) = 2 ^ (8 * i) * 2 ^ (8 * (n - i)) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        have e2 : 2 ^ (8 * (n - i)) = 2 ^ 8 * 2 ^ (8 * (n - i - 1)) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        rw [← hget i hi, wLet_eq', e1, Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_left _ _
          (Nat.two_pow_pos _), e2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
        exact Nat.mod_eq_of_lt hvn

theorem subRel_sound {G : Type*} [Group G] (pg cg : ℕ → G) {M P C nG : ℕ} (h : subRel M P C = true)
    (hnG : nG ≤ 127) (_hP : wWord P < 2 ^ (8 * wLen P))
    (hlet : ∀ q < wLen P, wLet (wWord P) q < 2 * nG)
    (hM : ∀ g < nG, mget M g < 255 → mget M g < 127 ∧ cg (mget M g) = pg g) :
    bval cg (wWord C) (wLen C) = bval pg (wWord P) (wLen P) := by
  obtain ⟨hmap, h2⟩ := andB_true h
  obtain ⟨hlen, hword⟩ := andB_true h2
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hword' := Nat.eq_of_beq_eq_true hword
  have hm : ∀ q < wLen P, mget M (wLet (wWord P) q / 2) < 255 := by
    have key : ∀ n, mapOK M (wWord P) n = true → ∀ q < n, mget M (wLet (wWord P) q / 2) < 255 := by
      intro n
      induction n with
      | zero => intro _ q hq; omega
      | succ n ih =>
        intro hn q hq
        obtain ⟨h1, h2⟩ := andB_true hn
        rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
        · exact ih h1 q hq
        · have := Nat.blt_eq.mp h2
          have e1 : Nat.shiftRight (wLet (wWord P) q) 1 = wLet (wWord P) q / 2 := by
            change wLet (wWord P) q >>> 1 = _
            rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
          rwa [e1] at this
    exact key _ hmap
  have hg : ∀ q < wLen P, wLet (wWord P) q / 2 < nG := fun q hq => by
    have := hlet q hq
    omega
  have hv : ∀ q < wLen P, mv M (wWord P) q < 256 := by
    intro q hq
    have := (hM _ (hg q hq) (hm q hq)).1
    unfold mv
    omega
  obtain ⟨-, hget⟩ := wLet_mapW M (wWord P) (wLen P) hv
  rw [hlen', hword']
  unfold bval
  congr 1
  apply List.map_congr_left
  intro q hq
  have hq' := List.mem_range.1 hq
  rw [hget q hq']
  obtain ⟨m1, m2⟩ := hM _ (hg q hq') (hm q hq')
  have hl := hlet q hq'
  unfold mv letV
  have n1 : 2 * mget M (wLet (wWord P) q / 2) + wLet (wWord P) q % 2 ≠ 255 := by omega
  have n2 : wLet (wWord P) q ≠ 255 := by omega
  have d1 : (2 * mget M (wLet (wWord P) q / 2) + wLet (wWord P) q % 2) / 2 =
      mget M (wLet (wWord P) q / 2) := by omega
  have p1 : (2 * mget M (wLet (wWord P) q / 2) + wLet (wWord P) q % 2) % 2 = wLet (wWord P) q % 2 := by
    omega
  simp only [n1, n2, d1, p1, m2, ↓reduceIte]

end CFSG.Certificates.BindSub

end
