module

public import Certificates.Data.Kernel.WCK
public import CFSG.Certificates.Kernel.S97RYKSound

public section

namespace CFSG.KC.WCK

open CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.KC.S97RYK CFSG.Sporadic.Th.Native
  CFSG.CGT.Timmesfeld75.WCCheck CFSG.LargeExtraspecial.S11.PairCheck

theorem wcCheck_eq (D : Data) : wcCheck D = (baseCheck D &&
    (allMasks D.cls.length).all fun J => D.verdicts.any fun p => p.1 == J && verdictOK D J p.2) :=
  rfl

theorem verdictOK_of_K {D : Data} (h32 : D.n < 32) (hg : ∀ l, validT D.n (D.gens l) = true)
    {J : List Bool} {v : Verdict}
    (h : verdictK D (encK D.n (idT D.n)) (D.pc.map (wK D)) J v = true) :
    verdictOK D J v = true := by
  have hI : validT D.n (idT D.n) = true := validT_idT (by omega)
  cases v with
  | small => exact h
  | notClosed i j =>
    unfold verdictK at h
    simp only [verdictOK]
    rw [memU_eq h32 hg J (validT_compT (el_valid h32 hg i) (el_valid h32 hg j)),
      encK_compT h32 (el_valid h32 hg j), encK_el h32 hg, encK_el h32 hg]
    exact h
  | bad t y g =>
    unfold verdictK at h
    simp only [verdictOK]
    have hgv := wT_valid h32 hg g
    have hgi := wT_valid h32 hg (invWord g)
    have hyv := el_valid h32 hg y
    have htv := el_valid h32 hg t
    rw [beq_encK h32 htv hI, commT_encK h32 hgv htv,
      memU_eq h32 hg J (validT_conjT hgv hyv hgi), encK_conjT h32 hyv hgi,
      encK_wT h32 hg g, encK_wT h32 hg (invWord g), encK_el h32 hg t, encK_el h32 hg y]
    exact h
  | good d =>
    unfold verdictK at h
    simp only [verdictOK]
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨⟨h1, h2⟩, (all_congr' fun q _ => ?_).trans h3⟩
    rcases q with ⟨w, _ | ⟨⟨i, c⟩, rest⟩⟩
    · rfl
    · have hw := wT_valid h32 hg w
      have hwi := wT_valid h32 hg (invWord w)
      have hz := el_valid h32 hg D.zIdx
      dsimp only
      rw [beq_encK h32 (validT_conjT hw hz hwi) (el_valid h32 hg i), encK_conjT h32 hz hwi,
        encK_wT h32 hg w, encK_wT h32 hg (invWord w), encK_el h32 hg D.zIdx, encK_el h32 hg i]

theorem bitK_eq (acc k : Nat) : bitK acc k = acc.testBit k := by
  have h1 : Nat.land (Nat.shiftRight acc k) 1 = acc / 2 ^ k % 2 := by
    change (acc >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitK
  rw [h1, Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem distK_spec (b : List Nat) : ∀ (L : List Nat) (acc : Nat), distK b L acc = true →
    (L.map (keyK b)).Nodup ∧ ∀ x ∈ L, acc.testBit (keyK b x) = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, acc, h => by
    change (!bitK acc (keyK b x) && distK b L (Nat.lor acc (Nat.shiftLeft 1 (keyK b x)))) = true
      at h
    rw [Bool.and_eq_true, Bool.not_eq_true', bitK_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hn, hb⟩ := distK_spec b L _ h2
    have hbit : ∀ y ∈ L, acc.testBit (keyK b y) = false ∧ keyK b y ≠ keyK b x := by
      intro y hy
      have h3 := hb y hy
      change (acc ||| 1 <<< keyK b x).testBit (keyK b y) = false at h3
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at h3
      refine ⟨h3.1, fun e => ?_⟩
      have h4 := h3.2
      rw [e, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at h4
      exact Bool.noConfusion h4
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hn⟩
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      exact (hbit y hy).2 e
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · exact (hbit y hy).1

theorem baseK_of_K2 {D : Data} {b : List Nat} {idP : Nat}
    {pcP pciP SP SiP cwP cwiP clP : List Nat} {zP : Nat}
    (h : baseK2 D b idP pcP pciP SP SiP cwP cwiP clP zP = true) :
    baseK D idP pcP pciP SP SiP cwP cwiP clP zP = true := by
  unfold baseK2 at h
  unfold baseK
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, ?_⟩, h12⟩, h13⟩, h14⟩
  · exact decide_eq_true ((distK_spec b SP 0 h1).1.of_map _)
  · refine List.all_eq_true.2 fun x hx => ?_
    have hx' := List.all_eq_true.1 h11 x hx
    simp only [Bool.or_eq_true] at hx' ⊢
    tauto

end CFSG.KC.WCK

end
