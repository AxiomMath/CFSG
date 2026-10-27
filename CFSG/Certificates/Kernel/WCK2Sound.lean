module

public import Certificates.Data.Kernel.WCK2
public import CFSG.Certificates.Kernel.WCKSound

public section

namespace CFSG.KC.WCK

open CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.KC.S97RYK CFSG.Sporadic.Th.Native
  CFSG.CGT.Timmesfeld75.WCCheck CFSG.LargeExtraspecial.S11.PairCheck

theorem distF_spec (f : Nat → Nat) : ∀ (L : List Nat) (acc : Nat), distF f L acc = true →
    L.Pairwise (fun x y => f x ≠ f y) ∧ ∀ x ∈ L, acc.testBit (f x) = false
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, acc, h => by
    change (!bitK acc (f x) && distF f L (Nat.lor acc (Nat.shiftLeft 1 (f x)))) = true at h
    rw [Bool.and_eq_true, Bool.not_eq_true', bitK_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hn, hb⟩ := distF_spec f L _ h2
    have hbit : ∀ y ∈ L, acc.testBit (f y) = false ∧ f x ≠ f y := by
      intro y hy
      have h3 := hb y hy
      change (acc ||| 1 <<< f x).testBit (f y) = false at h3
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at h3
      refine ⟨h3.1, fun e => ?_⟩
      have h4 := h3.2
      rw [← e, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at h4
      exact Bool.noConfusion h4
    refine ⟨List.pairwise_cons.2 ⟨fun y hy => (hbit y hy).2, hn⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h1
    · exact (hbit y hy).1

theorem injK_of_K2 {n x : Nat} (h : injK2 n x = true) : injK n x = true := by
  have hp := (distF_spec (imgW 5 x) (List.range n) 0 h).1
  unfold injK
  refine List.all_eq_true.2 fun i hi => List.all_eq_true.2 fun j hj => ?_
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
  by_cases e : i = j
  · exact Or.inl e
  · refine Or.inr ?_
    have : Std.Symm fun a b => imgW 5 x a ≠ imgW 5 x b := ⟨fun _ _ h' => Ne.symm h'⟩
    have hne : imgW 5 x i ≠ imgW 5 x j := hp.forall hi hj e
    cases hb : Nat.beq (imgW 5 x i) (imgW 5 x j)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne

theorem chkP_spec (W P : Nat) : ∀ (L : List Nat) (j₀ : Nat), chkP W P L j₀ = true →
    ∀ j (hj : j < L.length), imgW W P (j₀ + j) = L[j]
  | [], _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | x :: L, j₀, h, j, hj => by
    change (Nat.beq (imgW W P j₀) x && chkP W P L (Nat.succ j₀)) = true at h
    rw [Bool.and_eq_true] at h
    rcases j with _ | j
    · rw [Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h.1
    · have e : j₀ + (j + 1) = Nat.succ j₀ + j := by omega
      rw [e]
      exact chkP_spec W P L _ h.2 j (by simpa using hj)

theorem mem_of_memP {b : List Nat} {W SPk TI : Nat} {SP : List Nat} (hc : chkP W SPk SP 0 = true)
    {y : Nat} (h : memP b W SP.length SPk TI y = true) : y ∈ SP := by
  unfold memP at h
  rw [strictK_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hj : imgW 11 TI (keyK b y) < SP.length := Nat.le_of_ble_eq_true h1
  have e := chkP_spec W SPk SP 0 hc _ hj
  rw [Nat.zero_add, Nat.eq_of_beq_eq_true h2] at e
  rw [e]
  exact List.getElem_mem hj

theorem baseK2_of_K3 {D : Data} {b : List Nat} {idP : Nat}
    {pcP pciP SP SiP cwP cwiP clP : List Nat} {zP SPk TI : Nat}
    (hc : chkP (Nat.mul 5 D.n) SPk SP 0 = true)
    (h : baseK3 D b idP pcP pciP SP SiP cwP cwiP clP zP SP.length SPk TI = true) :
    baseK2 D b idP pcP pciP SP SiP cwP cwiP clP zP = true := by
  have hm : ∀ y, memP b (Nat.mul 5 D.n) SP.length SPk TI y = true → memK SP y = true :=
    fun y hy => (memK_iff SP y).2 (mem_of_memP hc hy)
  unfold baseK3 at h
  unfold baseK2
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩
  · exact List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun s hs =>
      hm _ (List.all_eq_true.1 (List.all_eq_true.1 h2 x hx) s hs)
  · exact List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun s hs =>
      hm _ (List.all_eq_true.1 (List.all_eq_true.1 h3 x hx) s hs)
  · exact List.all_eq_true.2 fun x hx => injK_of_K2 (List.all_eq_true.1 h4 x hx)

theorem wcCheck_of_K2 {D : Data} {b : List Nat} (hg : ∀ l, validT D.n (D.gens l) = true)
    (h : wcCheckK2 D b = true) : wcCheck D = true := by
  unfold wcCheckK2 at h
  simp only [strictK_eq, forceL_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h32, ⟨hc, hb⟩, hv⟩ := h
  rw [wcCheck_eq, Bool.and_eq_true]
  refine ⟨baseCheck_of_K h32 hg (baseK_of_K2 (baseK2_of_K3 hc hb)), ?_⟩
  rw [List.all_eq_true] at hv ⊢
  intro J hJ
  obtain ⟨p, hp, hpv⟩ := List.any_eq_true.1 (hv J hJ)
  rw [Bool.and_eq_true] at hpv
  exact List.any_eq_true.2
    ⟨p, hp, by rw [Bool.and_eq_true]; exact ⟨hpv.1, verdictOK_of_K h32 hg hpv.2⟩⟩

end CFSG.KC.WCK

end
