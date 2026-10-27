module

public import Certificates.Data.Kernel.Co2Census
public import CFSG.Certificates.Kernel.Co2J.Sound

public section

namespace CFSG.KC.Co2TInv

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2J CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KC.M1F2
  CFSG.KLie.CT

@[expose] def letL : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, w => (w &&& 7) :: letL n (w >>> 3)

theorem letL_lt : ∀ n w, wLets n w = true → ∀ a ∈ letL n w, a < 5
  | 0, _, _, a, ha => absurd ha List.not_mem_nil
  | n + 1, w, h, a, ha => by
    have h' : andK (Nat.blt (Nat.land w 7) 5) (wLets n (Nat.shiftRight w 3)) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 ha with e | e
    · rw [e]
      exact blt_iff.1 h'.1
    · exact letL_lt n _ h'.2 a e

theorem wProd_letL (G : Nat → Nat) : ∀ n w acc,
    MatP 22 (Co2J.wProd G n w acc) = MatP 22 acc * ((letL n w).map fun a => MatP 22 (G a)).prod
  | 0, _, acc => by simp [letL, Co2J.wProd]
  | n + 1, w, acc => by
    change MatP 22 (strictN (mulV acc (G (Nat.land w 7))) fun a =>
      Co2J.wProd G n (Nat.shiftRight w 3) a) = _
    rw [strictN_eq', wProd_letL G n, MatP_mulV]
    simp only [letL, List.map_cons, List.prod_cons, mul_assoc]
    rfl

theorem wProdR_letL (MK : Nat → Nat) : ∀ n w acc,
    MatP 10 (wProdR MK n w acc) =
      ((letL n w).reverse.map fun a => MatP 10 (MK a)).prod * MatP 10 acc
  | 0, _, acc => by simp [letL, wProdR]
  | n + 1, w, acc => by
    change MatP 10 (strictN (mulT (MK (Nat.land w 7)) acc) fun a =>
      wProdR MK n (Nat.shiftRight w 3) a) = _
    rw [strictN_eq', wProdR_letL MK n, MatP_mulT]
    simp only [letL, List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rfl

theorem lift_sound {G MK PE JE CL LW LN LT SC : Nat → Nat} {NR : Nat}
    (h : liftAllK G MK PE JE CL LW LN LT SC NR = true) : ∀ s < NR,
    CL s < 256 ∧ SC s < 1024 ∧ MatP 22 (LT s) ∈ genMon G ∧
      (∃ l : List Nat, (∀ a ∈ l, a < 5) ∧
        MatP 22 (LT s) = (l.map fun a => MatP 22 (G a)).prod ∧
        MatP 10 (PE (CL s)) = (l.reverse.map fun a => MatP 10 (MK a)).prod) ∧
      MatP 22 (LT s) * MatP 22 (LT s) = MatP 22 (JE (SC s)) := by
  intro s hs
  have h' := allK_spec h s hs
  unfold liftK at h'
  simp only [andK_eq, Bool.and_eq_true] at h'
  obtain ⟨hc, hw, hr, hsc, hsq⟩ := h'
  have hw' := hw
  unfold Co2J.wordK at hw'
  rw [andK_eq, Bool.and_eq_true] at hw'
  refine ⟨blt_iff.1 hc, blt_iff.1 hsc, word_sound hw, ⟨letL (LN s) (LW s),
    letL_lt _ _ hw'.1, ?_, ?_⟩, ?_⟩
  · rw [← Nat.eq_of_beq_eq_true hw'.2, wProd_letL, MatP_IDP, one_mul]
  · rw [← Nat.eq_of_beq_eq_true hr, wProdR_letL, MatP_IDT, mul_one]
  · rw [← MatP_mulV, Nat.eq_of_beq_eq_true hsq]

theorem scan_sound {PE CL SC RR RN SW : Nat → Nat} {NR : Nat}
    (h : scanAllK PE CL SC RR RN SW NR = true) : ∀ s < NR, ∀ v < 1024,
    addP (PE (CL s)) v = SC s →
      ∃ k < RN s, ∃ w < 1024, v = Nat.xor (repAt (RR s) k) (addP (PE (CL s)) w) := by
  intro s hs v hv hc
  have h' := allK_spec h s hs
  unfold scanK at h'
  simp only [letB_eq] at h'
  have h'' := allK_spec h' v hv
  unfold scanV at h''
  have hb : Nat.beq (addP (PE (CL s)) v) (SC s) = true := by
    rw [hc]
    exact Nat.beq_refl _
  rw [implK_eq, if_pos hb] at h''
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h''
  refine ⟨_, blt_iff.1 h''.1, _, ?_, Nat.eq_of_beq_eq_true h''.2⟩
  have hr : Nat.land (Nat.shiftRight (SW s) (Nat.mul 14 v)) 16383 < 2 ^ 14 :=
    Nat.and_lt_two_pow _ (by decide : 16383 < 2 ^ 14)
  change Nat.land (Nat.shiftRight (SW s) (Nat.mul 14 v)) 16383 >>> 4 < 1024
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem fus_sound {PE INV CL FU : Nat → Nat} {NR NI : Nat} (h : fusCK PE INV CL FU NR NI = true) :
    ∀ q < NI, ∃ u < 256, ∃ s < NR,
      MatP 10 (PE u) * MatP 10 (PE (INV q)) = MatP 10 (PE (CL s)) * MatP 10 (PE u) := by
  intro q hq
  have h' := allK_spec h q hq
  unfold fusV at h'
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h'
  refine ⟨Nat.land (FU q) 255, Nat.and_lt_two_pow _ (by decide : 255 < 2 ^ 8), _,
    blt_iff.1 h'.1, ?_⟩
  rw [← MatP_mulT, ← MatP_mulT, Nat.eq_of_beq_eq_true h'.2]

theorem jorb_sound {PE JR JO : Nat → Nat} {NJ : Nat} (h : jorbK PE JR JO NJ = true) :
    (∀ j < NJ, JR j < 1024) ∧
      ∀ v, 1 ≤ v → v < 1024 → ∃ u < 256, ∃ j < NJ, vmF 10 (PE u) (JR j) = v := by
  unfold jorbK at h
  rw [andK_eq, Bool.and_eq_true] at h
  refine ⟨fun j hj => blt_iff.1 (allK_spec h.1 j hj), fun v hv1 hv => ?_⟩
  have h' := rangeK_spec (lo := 1) (n := 1023) h.2 (v - 1) (by omega)
  have e : 1 + (v - 1) = v := by omega
  rw [e] at h'
  unfold jorbV at h'
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h'
  exact ⟨Nat.land (JO v) 255, Nat.and_lt_two_pow _ (by decide : 255 < 2 ^ 8), _, blt_iff.1 h'.1,
    Nat.eq_of_beq_eq_true h'.2⟩

theorem lookV_spec {CF : Nat → Nat → Nat} {NC : Nat → Nat} {X r : Nat}
    (h : lookV CF NC X r = true) : ∃ c < 10, ∃ i < NC c, elemAt (CF c) i = X := by
  unfold lookV at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  exact ⟨_, blt_iff.1 h.1, _, blt_iff.1 h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem look_sound {CF : Nat → Nat → Nat} {NC JE LT RR RN LK : Nat → Nat} {NR : Nat}
    (h : lookAllK CF NC JE LT RR RN LK NR = true) : ∀ s < NR, ∀ k < RN s,
    ∃ c < 10, ∃ i < NC c,
      MatP 22 (elemAt (CF c) i) = MatP 22 (JE (repAt (RR s) k)) * MatP 22 (LT s) := by
  intro s hs k hk
  have h' := allK_spec h s hs
  unfold lookK at h'
  simp only [letB_eq] at h'
  obtain ⟨c, hc, i, hi, e⟩ := lookV_spec (allK_spec h' k hk)
  exact ⟨c, hc, i, hi, by rw [e, MatP_mulV]⟩

theorem lookJ_sound {CF : Nat → Nat → Nat} {NC JE JR JK : Nat → Nat} {NJ : Nat}
    (h : lookJK CF NC JE JR JK NJ = true) : ∀ j < NJ,
    ∃ c < 10, ∃ i < NC c, MatP 22 (elemAt (CF c) i) = MatP 22 (JE (JR j)) := by
  intro j hj
  obtain ⟨c, hc, i, hi, e⟩ := lookV_spec (allK_spec h j hj)
  exact ⟨c, hc, i, hi, by rw [e]⟩

end CFSG.KC.Co2TInv

end
