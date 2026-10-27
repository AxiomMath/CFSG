module

public import CFSG.Certificates.Kernel.Co2Census.Sound
public import CFSG.Certificates.Kernel.Co2J.Glue

public section

namespace CFSG.KC.Co2TInv

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2J CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KC.M1F2
  CFSG.KLie.CT

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem conj_trans {g h a b c : M22} (hg : g * a = b * g) (hh : h * b = c * h) :
    h * g * a = c * (h * g) := by
  rw [mul_assoc, hg, ← mul_assoc, hh, mul_assoc]

theorem xor_cancel {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e := congrArg (fun n => n.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at e
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

section Glue

variable {G GJ JE JS JW JL MK PE PM PS INV : Nat → Nat} {PT : Nat → Nat → Nat}
  {CL LW LN LT SC RR RN SW FU JR JO JK LK : Nat → Nat} {CF : Nat → Nat → Nat} {NC : Nat → Nat}
  {NR NJ NI : Nat}

local notation "jm" => bitProd (fun i => MatP 22 (GJ i)) 10

theorem acts_word (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)
    (hco : coordAllK G GJ JE MK = true) : ∀ l : List ℕ, (∀ a ∈ l, a < 5) →
    ∃ P, MatP 10 P = (l.reverse.map fun a => MatP 10 (MK a)).prod ∧
      ActsP jm (l.map fun a => MatP 22 (G a)).prod P
  | [], _ => ⟨IDT, by simp [MatP_IDT], by simpa using acts_one (GJ := GJ)⟩
  | a :: l, h => by
    obtain ⟨P, hP, hA⟩ := acts_word hgen henum hco l fun b hb => h b (by simp [hb])
    refine ⟨mulT P (MK a), ?_, ?_⟩
    · rw [MatP_mulT, hP]
      simp
    · rw [List.map_cons, List.prod_cons]
      exact acts_mul hA (acts_gen hgen henum hco (h a (by simp)))

theorem acts_inv (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)
    (hco : coordAllK G GJ JE MK = true) (hpow : ∀ x ∈ genMon G, x ^ 32 = 1) {t : M22}
    (ht : t ∈ genMon G) {P : ℕ} (hP : ActsP jm t P) :
    ∃ Q, ActsP jm (t ^ 31) Q ∧ MatP 10 P * MatP 10 Q = 1 ∧ MatP 10 Q * MatP 10 P = 1 := by
  obtain ⟨Q, -, hQ⟩ := acts_all hgen henum hco _ ((genMon G).pow_mem ht 31)
  have e1 : t ^ 31 * t = 1 := by
    rw [← pow_succ]
    exact hpow t ht
  have e2 : t * t ^ 31 = 1 := by
    rw [← pow_succ']
    exact hpow t ht
  have a1 := acts_mul hP hQ
  have a2 := acts_mul hQ hP
  rw [e1] at a1
  rw [e2] at a2
  refine ⟨Q, hQ, ?_, ?_⟩
  · rw [← MatP_mulT, ← MatP_IDT]
    exact acts_unique henum (one_pow 32) a1 acts_one
  · rw [← MatP_mulT, ← MatP_IDT]
    exact acts_unique henum (one_pow 32) a2 acts_one

theorem mem_jm (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)
    (hin : jInTK G GJ JW JL = true) (hco : coordAllK G GJ JE MK = true)
    (hpow : ∀ x ∈ genMon G, x ^ 32 = 1) (hR : TreeI PE PM PS PT MK)
    (hc : Nat.card (genMon G) ≤ 2 ^ 18) {t : M22} (ht : t ∈ genMon G) {P : ℕ}
    (hP : ActsP jm t P) (h1 : MatP 10 P = 1) : ∃ v < 1024, jm v = t := by
  have h' := acts_congr (h1.trans MatP_IDT.symm) hP
  have hm : t ∈ centJ G GJ := ⟨ht, fun v hv => by rw [h' v hv, vmF_IDT hv]⟩
  rw [(small_of_card hgen henum hin hco hpow hR hc).2] at hm
  obtain ⟨v, hv, e⟩ := (jm_bij hgen henum).2.2 hm
  exact ⟨v, hv, e⟩

theorem conj_J (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)
    (hco : coordAllK G GJ JE MK = true) (hR : TreeI PE PM PS PT MK)
    (hjo : jorbK PE JR JO NJ = true) (hlj : lookJK CF NC JE JR JK NJ = true) {v : ℕ}
    (hv1 : 1 ≤ v) (hv : v < 1024) :
    ∃ c < 10, ∃ i < NC c, ∃ g ∈ genMon G, g * MatP 22 (elemAt (CF c) i) = jm v * g := by
  obtain ⟨hJR, horb⟩ := jorb_sound hjo
  obtain ⟨u, hu, j, hj, e⟩ := horb v hv1 hv
  obtain ⟨c, hc, i, hi, he⟩ := lookJ_sound hlj j hj
  obtain ⟨P, hP, t, ht, hA⟩ := acts_surj hgen henum hco _ (treeI_mem hR u hu).2
  refine ⟨c, hc, i, hi, t, ht, ?_⟩
  rw [he, ((jEnum_sound henum).1 _ (hJR j hj)).2, hA _ (hJR j hj), vmF_congr hP, e]

theorem coset_eq (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)
    (hin : jInTK G GJ JW JL = true) (hco : coordAllK G GJ JE MK = true)
    (hpow : ∀ x ∈ genMon G, x ^ 32 = 1) (hR : TreeI PE PM PS PT MK)
    (hc : Nat.card (genMon G) ≤ 2 ^ 18) (hl : liftAllK G MK PE JE CL LW LN LT SC NR = true)
    {s : ℕ} (hsN : s < NR) {y : M22} (hy : y ∈ genMon G) (hsq : y * y = 1) {P : ℕ}
    (hP : ActsP jm y P) (hPS : MatP 10 P = MatP 10 (PE (CL s))) :
    ActsP jm (MatP 22 (LT s)) (PE (CL s)) ∧
      ∃ w < 1024, addP (PE (CL s)) w = SC s ∧ y = jm w * MatP 22 (LT s) := by
  obtain ⟨-, hSC, hLm, ⟨l, hl5, hLl, hPl⟩, hLsq⟩ := lift_sound hl s hsN
  obtain ⟨Q0, hQ0, hA0⟩ := acts_word hgen henum hco l hl5
  have hL : ActsP jm (MatP 22 (LT s)) (PE (CL s)) := by
    rw [hLl]
    exact acts_congr (hQ0.trans hPl.symm) hA0
  obtain ⟨Q, hQ, -, hQL⟩ := acts_inv hgen henum hco hpow hLm hL
  obtain ⟨w, hw, ew⟩ := mem_jm hgen henum hin hco hpow hR hc
    ((genMon G).mul_mem hy ((genMon G).pow_mem hLm 31)) (acts_mul hQ hP)
    (by rw [MatP_mulT, hPS, hQL])
  have e32 : MatP 22 (LT s) ^ 31 * MatP 22 (LT s) = 1 := by
    rw [← pow_succ]
    exact hpow _ hLm
  have hyw : y = jm w * MatP 22 (LT s) := by rw [ew, mul_assoc, e32, mul_one]
  refine ⟨hL, w, hw, ?_, hyw⟩
  have hsc : MatP 22 (LT s) * MatP 22 (LT s) = jm (SC s) := by
    rw [hLsq, ((jEnum_sound henum).1 _ hSC).2]
  have e2 : jm ((w ^^^ vmF 10 (PE (CL s)) w) ^^^ SC s) = jm 0 :=
    calc jm ((w ^^^ vmF 10 (PE (CL s)) w) ^^^ SC s)
        = jm w * (jm (vmF 10 (PE (CL s)) w) * MatP 22 (LT s)) * MatP 22 (LT s) := by
          rw [jm_xor hgen henum, jm_xor hgen henum, ← hsc]
          simp only [mul_assoc]
      _ = jm w * (MatP 22 (LT s) * jm w) * MatP 22 (LT s) := by rw [← hL w hw]
      _ = y * y := by
          rw [hyw]
          simp only [mul_assoc]
      _ = 1 := hsq
      _ = jm 0 := (bitProd_zero _ 10).symm
  have hlt : (w ^^^ vmF 10 (PE (CL s)) w) ^^^ SC s < 1024 :=
    Nat.xor_lt_two_pow (n := 10) (Nat.xor_lt_two_pow (n := 10) hw (vmF_lt' _ _)) hSC
  have e3 := (jm_bij hgen henum).2.1 hlt (by norm_num : (0 : ℕ) < 1024) e2
  change vmF 10 (PE (CL s)) w ^^^ w = SC s
  rw [Nat.xor_comm]
  exact xor_cancel e3

theorem conj_coset (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)
    (hin : jInTK G GJ JW JL = true) (hs : scanAllK PE CL SC RR RN SW NR = true)
    (hk : lookAllK CF NC JE LT RR RN LK NR = true) {s : ℕ} (hsN : s < NR)
    (hL : ActsP jm (MatP 22 (LT s)) (PE (CL s))) {w : ℕ} (hw : w < 1024)
    (hwc : addP (PE (CL s)) w = SC s) :
    ∃ c < 10, ∃ i < NC c, ∃ g ∈ genMon G,
      g * MatP 22 (elemAt (CF c) i) = jm w * MatP 22 (LT s) * g := by
  obtain ⟨k, hkR, w', hw', e⟩ := scan_sound hs s hsN w hw hwc
  obtain ⟨c, hc, i, hi, he⟩ := look_sound hk s hsN k hkR
  have hRk : repAt (RR s) k < 1024 := Nat.and_lt_two_pow _ (by decide : 1023 < 2 ^ 10)
  refine ⟨c, hc, i, hi, jm w', genJ_le hin ((jm_bij hgen henum).1 hw'), ?_⟩
  have e' : w = repAt (RR s) k ^^^ (vmF 10 (PE (CL s)) w' ^^^ w') := e
  have hx : w' ^^^ repAt (RR s) k = w ^^^ vmF 10 (PE (CL s)) w' := by
    rw [e']
    apply Nat.eq_of_testBit_eq
    intro b
    simp only [Nat.testBit_xor]
    cases w'.testBit b <;> cases (repAt (RR s) k).testBit b <;>
      cases (vmF 10 (PE (CL s)) w').testBit b <;> rfl
  have e1 : MatP 22 (LT s) * jm w' = jm (vmF 10 (PE (CL s)) w') * MatP 22 (LT s) := hL w' hw'
  rw [he, ((jEnum_sound henum).1 _ hRk).2]
  calc jm w' * (jm (repAt (RR s) k) * MatP 22 (LT s))
      = jm (w' ^^^ repAt (RR s) k) * MatP 22 (LT s) := by rw [jm_xor hgen henum, mul_assoc]
    _ = jm (w ^^^ vmF 10 (PE (CL s)) w') * MatP 22 (LT s) := by rw [hx]
    _ = jm w * MatP 22 (LT s) * jm w' := by rw [jm_xor hgen henum, mul_assoc, ← e1, ← mul_assoc]

theorem census_T (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)
    (hin : jInTK G GJ JW JL = true) (hco : coordAllK G GJ JE MK = true)
    (hpow : ∀ x ∈ genMon G, x ^ 32 = 1) (hR : TreeI PE PM PS PT MK)
    (hI : invAllK PE INV NI = true) (hl : liftAllK G MK PE JE CL LW LN LT SC NR = true)
    (hs : scanAllK PE CL SC RR RN SW NR = true) (hf : fusCK PE INV CL FU NR NI = true)
    (hjo : jorbK PE JR JO NJ = true) (hk : lookAllK CF NC JE LT RR RN LK NR = true)
    (hlj : lookJK CF NC JE JR JK NJ = true) (hc : Nat.card (genMon G) ≤ 2 ^ 18) {x : M22}
    (hx : x ∈ genMon G) (hsq : x * x = 1) (h1 : x ≠ 1) :
    ∃ c < 10, ∃ i < NC c, ∃ g ∈ genMon G, g * MatP 22 (elemAt (CF c) i) = x * g := by
  obtain ⟨hgT, -⟩ := small_of_card hgen henum hin hco hpow hR hc
  obtain ⟨Px, hPxT, hAx⟩ := acts_all hgen henum hco x hx
  by_cases hX : MatP 10 Px = 1
  · obtain ⟨v, hv, rfl⟩ := mem_jm hgen henum hin hco hpow hR hc hx hAx hX
    have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.2 fun h0 => h1 (by rw [h0]; exact bitProd_zero _ 10)
    exact conj_J hgen henum hco hR hjo hlj hv1 hv
  · obtain ⟨s0, hs0, e0⟩ := treeI_surj hR hgT _ hPxT
    have hXsq : MatP 10 Px * MatP 10 Px = 1 := by
      have a := acts_mul hAx hAx
      rw [hsq] at a
      rw [← MatP_mulT, ← MatP_IDT]
      exact acts_unique henum (one_pow 32) a acts_one
    obtain ⟨q, hq, eq⟩ := (invAll_sound hR hI).2 s0 hs0 (by rw [e0]; exact hXsq)
      (by rw [e0]; exact hX)
    obtain ⟨u, hu, s, hsN, ef⟩ := fus_sound hf q hq
    rw [eq, e0] at ef
    obtain ⟨Pt, hPt, t, ht, hAt⟩ := acts_surj hgen henum hco _ (treeI_mem hR u hu).2
    obtain ⟨Q, -, hPQ, -⟩ := acts_inv hgen henum hco hpow ht hAt
    rw [hPt] at hPQ
    have e31 : t * t ^ 31 = 1 := by
      rw [← pow_succ']
      exact hpow t ht
    have e31' : t ^ 31 * t = 1 := by
      rw [← pow_succ]
      exact hpow t ht
    have hy : t ^ 31 * x * t ∈ genMon G :=
      (genMon G).mul_mem ((genMon G).mul_mem ((genMon G).pow_mem ht 31) hx) ht
    have hty : t * (t ^ 31 * x * t) = x * t := by rw [← mul_assoc, ← mul_assoc, e31, one_mul]
    have hysq : t ^ 31 * x * t * (t ^ 31 * x * t) = 1 :=
      calc t ^ 31 * x * t * (t ^ 31 * x * t) = t ^ 31 * (x * (t * t ^ 31) * x) * t := by
            simp only [mul_assoc]
        _ = 1 := by rw [e31, mul_one, hsq, mul_one, e31']
    obtain ⟨Py, -, hAy⟩ := acts_all hgen henum hco _ hy
    have hYS : MatP 10 Py = MatP 10 (PE (CL s)) := by
      have a1 := acts_mul hAy hAt
      have a2 := acts_mul hAt hAx
      rw [hty] at a1
      have e := acts_unique henum (hpow _ ((genMon G).mul_mem hx ht)) a1 a2
      rw [MatP_mulT, MatP_mulT, hPt, ef] at e
      calc MatP 10 Py = MatP 10 Py * (MatP 10 (PE u) * MatP 10 Q) := by rw [hPQ, mul_one]
        _ = MatP 10 (PE (CL s)) * MatP 10 (PE u) * MatP 10 Q := by rw [← mul_assoc, e]
        _ = MatP 10 (PE (CL s)) := by rw [mul_assoc, hPQ, mul_one]
    obtain ⟨hL, w, hw, hwc, hyw⟩ := coset_eq hgen henum hin hco hpow hR hc hl hsN hy hysq hAy hYS
    obtain ⟨c, hc10, i, hi, g, hg, eg⟩ := conj_coset hgen henum hin hs hk hsN hL hw hwc
    refine ⟨c, hc10, i, hi, t * g, (genMon G).mul_mem ht hg, ?_⟩
    rw [← hyw] at eg
    exact conj_trans eg hty

end Glue

end CFSG.KC.Co2TInv

end
