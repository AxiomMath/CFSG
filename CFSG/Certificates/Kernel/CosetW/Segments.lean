module

public import Certificates.Data.Kernel.CosetW.EnumW

public section

namespace CFSG.CosetTable

theorem felschW_zero (P : Params) (fuel c : Nat) (s : StW) : felschW P fuel 0 c s = s := rfl

theorem felschW_succ (P : Params) (fuel n c : Nat) (s : StW) :
    felschW P fuel (n + 1) c s =
      if c < s.next && !s.overflow then felschW P fuel n (c + 1) (fillRowW P fuel c P.L s)
      else s := rfl

theorem felschW_stop (P : Params) (fuel : Nat) {c : Nat} {s : StW}
    (h : (decide (c < s.next) && !s.overflow) = false) : ∀ n, felschW P fuel n c s = s
  | 0 => rfl
  | n + 1 => by rw [felschW_succ, h]; rfl

theorem felschW_add (P : Params) (fuel : Nat) : ∀ (a b c : Nat) (s : StW),
    felschW P fuel (a + b) c s = felschW P fuel b (c + a) (felschW P fuel a c s)
  | 0, b, c, s => by rw [Nat.zero_add, Nat.add_zero, felschW_zero]
  | a + 1, b, c, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega, felschW_succ, felschW_succ]
    by_cases hc : (decide (c < s.next) && !s.overflow) = true
    · rw [if_pos hc, if_pos hc, felschW_add P fuel a b (c + 1), show c + 1 + a = c + (a + 1) by omega]
    · have hc' : (decide (c < s.next) && !s.overflow) = false := by simpa using hc
      rw [if_neg hc, if_neg hc]
      have h2 : (decide (c + (a + 1) < s.next) && !s.overflow) = false := by
        cases hov : s.overflow
        · simp only [hov, Bool.not_false, Bool.and_true, decide_eq_false_iff_not] at hc' ⊢
          omega
        · simp
      rw [felschW_stop P fuel h2]

theorem felschW_seg {P : Params} {fuel : Nat} {a c : Nat} {s s' : StW} (b : Nat)
    (h : felschW P fuel a c s = s') :
    felschW P fuel (a + b) c s = felschW P fuel b (c + a) s' := by
  rw [felschW_add, h]

@[expose] def StW.eqB (x y : StW) : Bool :=
  x.tab.n == y.tab.n && x.tab.t == y.tab.t && x.fwd.n == y.fwd.n && x.fwd.t == y.fwd.t &&
    x.par.n == y.par.n && x.par.t == y.par.t && x.next == y.next && x.ded == y.ded &&
    x.queue == y.queue && x.qi == y.qi && x.overflow == y.overflow

theorem StW.eq_of_eqB : ∀ {x y : StW}, x.eqB y = true → x = y
  | ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, _, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, _, _⟩, h => by
    simp only [StW.eqB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
    subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rfl

@[expose] def checkFromW (P : Params) (fuel r c : Nat) (s : StW) (n : Nat) : Bool :=
  let t := felschW P fuel r c s
  !t.overflow && t.completeW P.L && t.liveCountW == n

theorem checkW_of_felschW {P : Params} {cap n r c : Nat} {s : StW} (hs : P.subs = [])
    (h : felschW P (64 * (cap + 1) * (P.L + 1)) (cap + 1) 1 (StW.init P.L cap) =
      felschW P (64 * (cap + 1) * (P.L + 1)) r c s)
    (hc : checkFromW P (64 * (cap + 1) * (P.L + 1)) r c s n = true) : checkW P cap n = true := by
  unfold checkW enumerateW
  rw [hs]
  unfold checkFromW at hc
  dsimp only at hc ⊢
  rw [show fillSubsW P (64 * (cap + 1) * (P.L + 1)) [] (StW.init P.L cap) = StW.init P.L cap
    from rfl, h]
  exact hc

end CFSG.CosetTable
