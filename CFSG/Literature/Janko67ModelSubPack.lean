module

public import CFSG.RankThree.GF2n.Parrott.PSp43Pack45

public section

namespace CFSG.Literature.Janko67.Pack

open Equiv CFSG.KC.Enum CFSG.KS.PK CFSG.Permutation.FinPack64
  CFSG.RankThree.GF2n.Parrott CFSG.RankThree.GF2n.Parrott.Pack45
open CFSG.KS.PCnt (pkw)

@[expose] noncomputable def outK (b0 b2 b3 : ℕ) : ℕ :=
  mulW 45 cU (mulW 45 (mulW 45 (selK b0 cOne cT) (selK b2 cOne (mulW 45 cA1 cA2)))
    (selK b3 cOne (mulW 45 cB1 cB2)))

theorem pk_out (p : Fin 4 → Fin 2) :
    pkw 6 (u * (t ^ (p 0 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) * (beta1 * beta2) ^ (p 3 : ℕ))) =
      outK (p 0) (p 2) (p 3) :=
  pk_mul h45 pk_u (pk_mul h45 (pk_mul h45 (pk_pow pk_one pk_t _)
    (pk_pow pk_one (pk_mul h45 pk_a1 pk_a2) _)) (pk_pow pk_one (pk_mul h45 pk_b1 pk_b2) _))

@[expose] noncomputable def chkOut : Bool :=
  all2 fun b0 => all2 fun b1 => all2 fun b2 => all2 fun b3 => all2 fun b4 =>
    strictB (mulW 45 cU (q0K b0 b1 b2 b3 b4)) fun W =>
      Bool.rec (motive := fun _ => Bool) true
        (any2 fun c0 => any2 fun c1 => any2 fun c2 => any2 fun c3 =>
          Nat.beq W (s0K c0 c1 c2 c3))
        (Nat.beq (mulW 45 W W) cOne)

theorem chkOut_eq : chkOut = true := by decide +kernel

theorem out_sound (p : Fin 5 → Fin 2) (h : u * q0w p * (u * q0w p) = 1) :
    ∃ q : Fin 4 → Fin 2, s0w q = u * q0w p := by
  have h0 := all2_spec (all2_spec (all2_spec (all2_spec (all2_spec chkOut_eq (p 0).isLt)
    (p 1).isLt) (p 2).isLt) (p 3).isLt) (p 4).isLt
  simp only [strictB_eq] at h0
  have hW := pk_mul h45 pk_u (pk_q0 p)
  have hsq : mulW 45 (mulW 45 cU (q0K (p 0) (p 1) (p 2) (p 3) (p 4)))
      (mulW 45 cU (q0K (p 0) (p 1) (p 2) (p 3) (p 4))) = cOne := by
    rw [← pk_mul h45 hW hW, h, pk_one]
  rw [hsq, Nat.beq_refl] at h0
  obtain ⟨c0, hc0, h1⟩ := any2_spec (brec_true (a := true) h0)
  obtain ⟨c1, hc1, h2⟩ := any2_spec h1
  obtain ⟨c2, hc2, h3⟩ := any2_spec h2
  obtain ⟨c3, hc3, h4⟩ := any2_spec h3
  exact ⟨![⟨c0, hc0⟩, ⟨c1, hc1⟩, ⟨c2, hc2⟩, ⟨c3, hc3⟩],
    eq_of_pk h45 (pk_s0 _) hW (Nat.eq_of_beq_eq_true h4).symm⟩

@[expose] noncomputable def chkS0Out : Bool :=
  all2 fun b0 => all2 fun b2 => all2 fun b3 => Nat.beq (s0K b0 1 b2 b3) (outK b0 b2 b3)

theorem chkS0Out_eq : chkS0Out = true := by decide +kernel

theorem s0_eq_out (p : Fin 4 → Fin 2) (hp : p 1 = 1) :
    s0w p = u * (t ^ (p 0 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) * (beta1 * beta2) ^ (p 3 : ℕ)) := by
  have h := all2_spec (all2_spec (all2_spec chkS0Out_eq (p 0).isLt) (p 2).isLt) (p 3).isLt
  have hs := pk_s0 p
  have e1 : ((p 1 : Fin 2) : ℕ) = 1 := by rw [hp]; rfl
  rw [e1] at hs
  exact eq_of_pk h45 hs (pk_out p) (Nat.eq_of_beq_eq_true h)

@[expose] noncomputable def chkS0Q0 : Bool :=
  all2 fun b0 => all2 fun b2 => all2 fun b3 =>
    strictB (s0K b0 0 b2 b3) fun S =>
      any2 fun c0 => any2 fun c1 => any2 fun c2 => any2 fun c3 => any2 fun c4 =>
        Nat.beq S (q0K c0 c1 c2 c3 c4)

theorem chkS0Q0_eq : chkS0Q0 = true := by decide +kernel

theorem s0_mem_q0 (p : Fin 4 → Fin 2) (hp : p 1 = 0) : ∃ q : Fin 5 → Fin 2, q0w q = s0w p := by
  have h := all2_spec (all2_spec (all2_spec chkS0Q0_eq (p 0).isLt) (p 2).isLt) (p 3).isLt
  simp only [strictB_eq] at h
  have hs := pk_s0 p
  have e1 : ((p 1 : Fin 2) : ℕ) = 0 := by rw [hp]; rfl
  rw [e1] at hs
  obtain ⟨c0, hc0, h1⟩ := any2_spec h
  obtain ⟨c1, hc1, h2⟩ := any2_spec h1
  obtain ⟨c2, hc2, h3⟩ := any2_spec h2
  obtain ⟨c3, hc3, h4⟩ := any2_spec h3
  obtain ⟨c4, hc4, h5⟩ := any2_spec h4
  exact ⟨![⟨c0, hc0⟩, ⟨c1, hc1⟩, ⟨c2, hc2⟩, ⟨c3, hc3⟩, ⟨c4, hc4⟩],
    eq_of_pk h45 (pk_q0 _) hs (Nat.eq_of_beq_eq_true h5).symm⟩

@[expose] noncomputable def chkOutConj : Bool :=
  all2 fun b0 => all2 fun b2 => all2 fun b3 =>
    strictB (outK b0 b2 b3) fun O =>
      any2 fun c0 => any2 fun c1 =>
        strictB (mulW 45 (selK c0 cOne cB1) (selK c1 cOne cA1)) fun G =>
          Bool.rec (motive := fun _ => Bool) (Nat.beq (mulW 45 G O) (mulW 45 (mulW 45 cU cT) G))
            true (Nat.beq (mulW 45 G O) (mulW 45 cU G))

theorem chkOutConj_eq : chkOutConj = true := by decide +kernel

theorem out_conj (p : Fin 4 → Fin 2) :
    ∃ i j : Fin 2,
      (beta1 ^ (i : ℕ) * alpha1 ^ (j : ℕ)) *
          (u * (t ^ (p 0 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) * (beta1 * beta2) ^ (p 3 : ℕ))) *
          (beta1 ^ (i : ℕ) * alpha1 ^ (j : ℕ))⁻¹ = u ∨
      (beta1 ^ (i : ℕ) * alpha1 ^ (j : ℕ)) *
          (u * (t ^ (p 0 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) * (beta1 * beta2) ^ (p 3 : ℕ))) *
          (beta1 ^ (i : ℕ) * alpha1 ^ (j : ℕ))⁻¹ = u * t := by
  have h := all2_spec (all2_spec (all2_spec chkOutConj_eq (p 0).isLt) (p 2).isLt) (p 3).isLt
  simp only [strictB_eq] at h
  obtain ⟨c0, hc0, h1⟩ := any2_spec h
  obtain ⟨c1, hc1, h2⟩ := any2_spec h1
  have hg := pk_mul h45 (pk_pow pk_one pk_b1 ⟨c0, hc0⟩) (pk_pow pk_one pk_a1 ⟨c1, hc1⟩)
  refine ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩, ?_⟩
  rcases brec_or h2 with h3 | h3
  · exact Or.inl (conj_of h45 hg (pk_out p) pk_u (Nat.eq_of_beq_eq_true h3))
  · exact Or.inr (conj_of h45 hg (pk_out p) (pk_mul h45 pk_u pk_t) (Nat.eq_of_beq_eq_true h3))

end CFSG.Literature.Janko67.Pack
