module

public import Certificates.Data.Kernel.G2Three.Q16
public import CFSG.Certificates.Kernel.G2Three.Tables
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLiePosG2Check

public section

namespace CFSG.KC.G2Three

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U
  CFSG.KD.G2Three CFSG.CGT.PushingUpLit.SolKNA

theorem strictB_eq77002 (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem q16Free_of_K (hc : consts3OK 14 5 196 LO RM CI ONE UP = true)
    (hone : pk one14 = ONE) {es : Array (List ℕ)} {X : ℕ → ℕ} {n : ℕ}
    (hn : n ≤ 64) (hsz : es.size = n)
    (hX : ∀ t < n, canon14 (es.getD t []) = true ∧ pk (es.getD t []) = X t)
    (h : q16K X n = true) : q16Free es = true := by
  rw [q16K] at h
  have hall := allBelow_g2 h hn
  unfold q16Free allCheck
  rw [List.all_eq_true]
  intro t ht
  rw [List.mem_range, hsz] at ht
  obtain ⟨hxc, hxp⟩ := hX t ht
  have s2 := mulE hc ⟨hxc, hxp⟩ ⟨hxc, hxp⟩
  have s4 := mulE hc s2 s2
  have s8 := mulE hc s4 s4
  have hk : q16AtK X n (X t) = true := hall t ht
  simp only [q16AtK, strictB_eq77002] at hk
  simp only [q16FreeAt, sq14, bne]
  rw [beq_pk s4.1 canon14_one14, beq_pk s8.1 canon14_one14, s4.2, s8.2, hone]
  simp only [Bool.or_eq_true] at hk ⊢
  rcases hk with (h1 | h1) | h1
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h1)
  · right
    rw [q16PairK] at h1
    have hp := allBelow_g2 h1 hn
    unfold allCheck
    rw [List.all_eq_true]
    intro u hu
    rw [List.mem_range, hsz] at hu
    obtain ⟨hyc, hyp⟩ := hX u hu
    have sy := mulE hc ⟨hyc, hyp⟩ ⟨hyc, hyp⟩
    have sxy := mulE hc (mulE hc ⟨hxc, hxp⟩ ⟨hyc, hyp⟩) ⟨hxc, hxp⟩
    have hq := hp u hu
    dsimp only at hq ⊢
    rw [beq_pk sy.1 s4.1, beq_pk sxy.1 hyc, sy.2, s4.2, sxy.2, hyp]
    exact hq

end CFSG.KC.G2Three

end
