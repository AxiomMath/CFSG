module

public import CFSG.Certificates.Kernel.GMS78RuPSound
import CFSG.Certificates.Kernel.GMS78RuP.Codes

public section

namespace CFSG.KC.GMS.SM

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS
  CFSG.GMS78RuSP

private theorem sMul_code {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8}
    {ε : Bool} {GT : List (List Nat)} {DPR : List Nat} {LIN DM DO : Nat}
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO) (p q : Pt) (hp : p.1 < 256) (hq : q.1 < 256) :
    sMulK GT DPR LIN DM DO (P117.pCode p) (P117.pCode q) =
        P117.pCode (Gen.sMulFG gA dA dct ε p q) ∧ (Gen.sMulFG gA dA dct ε p q).1 < 256 := by
  obtain ⟨hg, hd, hl, hm, ho, h256⟩ := hT
  obtain ⟨pc, pt, pd⟩ := p
  obtain ⟨qc, qt, qd⟩ := q
  dsimp only at hp hq
  have hpd := pd.isLt
  have hqd := qd.isLt
  have hqt := qt.isLt
  have hi : 256 * pd.val + qc < 2048 := by omega
  obtain ⟨hd1, hd2⟩ := hd _ hi
  have e1 : (256 * pd.val + qc) / 256 = pd.val := by omega
  have e2 : (256 * pd.val + qc) % 256 = qc := by omega
  rw [e1, e2] at hd1 hd2
  have hb := h256 _ hi
  set dp := dA.getD (256 * pd.val + qc) (0, 0) with hdp
  have hj : 256 * pc + dp.1 < 65536 := by omega
  have hgg := hg _ hj
  have e3 : (256 * pc + dp.1) / 256 = pc := by omega
  have e4 : (256 * pc + dp.1) % 256 = dp.1 := by omega
  rw [e3, e4] at hgg
  have hl' := hl pd.val pd.isLt qt.val qt.isLt
  have hm' := hm pd.val pd.isLt qd.val qd.isLt
  have ho' := ho pd.val pd.isLt qd.val qd.isLt
  have f8 : ∀ a : Fin 8, fin8Of a.val = a := fun a => Fin.ext (Nat.mod_eq_of_lt a.isLt)
  rw [f8] at hl' hm' ho'
  rw [f8] at hm' ho'
  have hov : fget DO (8 * pd.val + qd.val) 1 ≤ 1 := Nat.and_le_right
  have hdo : (if (ε && dOvf pd qd) = true then (1 : Fin 8) else 0).val =
      fget DO (8 * pd.val + qd.val) 1 := by
    rw [ho']
    by_cases h : (fget DO (8 * pd.val + qd.val) 1).beq 1 = true
    · rw [if_pos h, Nat.eq_of_beq_eq_true h]
      rfl
    · rw [if_neg h]
      have h1 : fget DO (8 * pd.val + qd.val) 1 ≠ 1 := fun h' => h (by rw [h']; rfl)
      have h0 : fget DO (8 * pd.val + qd.val) 1 = 0 := by omega
      rw [h0]
      rfl
  have hR : P117.pCode (Gen.sMulFG gA dA dct ε (pc, pt, pd) (qc, qt, qd)) =
      (pc ^^^ dp.1) |||
        ((pt.val ^^^ (linApply (dct.getD pd.val linId) qt).val ^^^ dp.2.val ^^^
          (gA.getD (256 * pc + dp.1) 0).val ^^^
          (if (ε && dOvf pd qd) = true then (1 : Fin 8) else 0).val) <<< 8) |||
        ((dMul pd qd).val <<< 11) := by
    simp only [P117.pCode, Gen.sMulFG, P117.fin8_xor_val]
    rfl
  refine ⟨?_, ?_⟩
  · unfold sMulK
    rw [P117.pCode_c hp, P117.pCode_t hp, P117.pCode_d hp, P117.pCode_c hq, P117.pCode_t hq,
      P117.pCode_d hq, hR]
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [← hd1, ← hd2, ← hgg, ← hl', ← hm', ← hdo, Nat.or_assoc]
    rfl
  · change (pc ^^^ dp.1) < 256
    exact Nat.xor_lt_two_pow (n := 8) hp hb

private theorem land1 (x : Nat) : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x

private theorem land3 (x : Nat) : Nat.land x 3 = x % 4 :=
  Nat.and_two_pow_sub_one_eq_mod x 2

private theorem fget3864 (j : Nat) (hj : j < 4) : fget (nat_lit 3864) j 3 = (s0d j).val := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem sLift16_code {p : Nat} (hp : p < 2048) : sLift16 p = P117.pCode (lift16 p) := by
  have hj : p / 512 < 4 := by omega
  have e1 : Nat.shiftRight p 9 = p / 512 := Nat.shiftRight_eq_div_pow p 9
  have e2 : Nat.shiftRight p 8 = p / 256 := P117.shr8 p
  have e3 : Nat.land (p / 256) 1 = (p / 256) % 2 := land1 _
  change Nat.lor (Nat.land p 255) (Nat.lor (Nat.shiftLeft (Nat.mul 4 (Nat.land (Nat.shiftRight p 8) 1)) 8)
    (Nat.shiftLeft (fget (nat_lit 3864) (Nat.shiftRight p 9) 3) 11)) =
      p % 256 ||| (fin8Of (4 * ((p / 256) % 2))).val <<< 8 ||| (s0d (p / 512)).val <<< 11
  rw [e1, e2, e3, fget3864 _ hj, P117.land255, Nat.or_assoc]
  have : (fin8Of (4 * ((p / 256) % 2))).val = 4 * ((p / 256) % 2) := by
    change (4 * ((p / 256) % 2)) % 8 = _
    omega
  rw [this]
  rfl

private theorem sLift17_code {p : Nat} (hp : p < 8192) : sLift17 p = P117.pCode (lift17 p) := by
  have e1 : Nat.shiftRight p 10 = p / 1024 := Nat.shiftRight_eq_div_pow p 10
  have e2 : Nat.shiftRight p 8 = p / 256 := P117.shr8 p
  have e3 : Nat.land (p / 256) 3 = (p / 256) % 4 := land3 _
  have e4 : Nat.land (p / 1024) 7 = p / 1024 := by
    rw [P117.land7]; omega
  change Nat.lor (Nat.land p 255) (Nat.lor (Nat.shiftLeft (Nat.mul 2 (Nat.land (Nat.shiftRight p 8) 3)) 8)
    (Nat.shiftLeft (Nat.land (Nat.shiftRight p 10) 7) 11)) =
      p % 256 ||| (fin8Of (2 * ((p / 256) % 4))).val <<< 8 ||| (fin8Of (p / 1024)).val <<< 11
  rw [e1, e2, e3, e4, P117.land255, Nat.or_assoc]
  have h1 : (fin8Of (2 * ((p / 256) % 4))).val = 2 * ((p / 256) % 4) := by
    change (2 * ((p / 256) % 4)) % 8 = _
    omega
  have h2 : (fin8Of (p / 1024)).val = p / 1024 := by
    change (p / 1024) % 8 = _
    omega
  rw [h1, h2]
  rfl

private theorem sEnc16_code {x : Pt} (hx : x.1 < 256) : sEnc16 (P117.pCode x) = enc16 x := by
  have ht := x.2.1.isLt
  have hd := x.2.2.isLt
  have hc := P117.pCode_eq hx
  change Nat.add (Nat.land (P117.pCode x) 255) (Nat.add (Nat.mul 256
    (Nat.land (Nat.shiftRight (P117.pCode x) 10) 1)) (Nat.mul 512 (Nat.shiftRight (P117.pCode x) 12)))
    = x.1 + 256 * (x.2.1.val / 4) + 512 * (x.2.2.val / 2)
  have e1 : Nat.shiftRight (P117.pCode x) 10 = P117.pCode x / 1024 := Nat.shiftRight_eq_div_pow _ 10
  have e2 : Nat.shiftRight (P117.pCode x) 12 = P117.pCode x / 4096 := Nat.shiftRight_eq_div_pow _ 12
  rw [e1, e2, P117.land255, land1, hc]
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

private theorem sEnc17_code {x : Pt} (hx : x.1 < 256) : sEnc17 (P117.pCode x) = enc17 x := by
  have ht := x.2.1.isLt
  have hd := x.2.2.isLt
  have hc := P117.pCode_eq hx
  change Nat.add (Nat.land (P117.pCode x) 255) (Nat.add (Nat.mul 256
    (Nat.land (Nat.shiftRight (P117.pCode x) 9) 3)) (Nat.mul 1024
    (Nat.land (Nat.shiftRight (P117.pCode x) 11) 7)))
    = x.1 + 256 * (x.2.1.val / 2) + 1024 * x.2.2.val
  have e1 : Nat.shiftRight (P117.pCode x) 9 = P117.pCode x / 512 := Nat.shiftRight_eq_div_pow _ 9
  have e2 : Nat.shiftRight (P117.pCode x) 11 = P117.pCode x / 2048 := P117.shr11 _
  rw [e1, e2, P117.land255, P117.land7, land3, hc]
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem mul16K_eq {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {ε : Bool}
    {GT : List (List Nat)} {DPR : List Nat} {LIN DM DO : Nat}
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO) {p q : Nat} (hp : p < 2048) (hq : q < 2048) :
    mul16K GT DPR LIN DM DO p q = Gen.mul16G gA dA dct ε p q := by
  have h1 : (lift16 p).1 < 256 := by change p % 256 < 256; omega
  have h2 : (lift16 q).1 < 256 := by change q % 256 < 256; omega
  obtain ⟨hc, hl⟩ := sMul_code hT _ _ h1 h2
  unfold mul16K Gen.mul16G
  rw [sLift16_code hp, sLift16_code hq, hc, sEnc16_code hl]

theorem mul16G_lt {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {ε : Bool}
    {GT : List (List Nat)} {DPR : List Nat} {LIN DM DO : Nat}
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO) (p q : Nat) : Gen.mul16G gA dA dct ε p q < 2048 := by
  have h1 : (lift16 p).1 < 256 := by change p % 256 < 256; omega
  have h2 : (lift16 q).1 < 256 := by change q % 256 < 256; omega
  obtain ⟨-, hl⟩ := sMul_code hT _ _ h1 h2
  have ht := (Gen.sMulFG gA dA dct ε (lift16 p) (lift16 q)).2.1.isLt
  have hd := (Gen.sMulFG gA dA dct ε (lift16 p) (lift16 q)).2.2.isLt
  unfold Gen.mul16G enc16 s0dIdx
  omega

theorem mul17K_eq {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {ε : Bool}
    {GT : List (List Nat)} {DPR : List Nat} {LIN DM DO : Nat}
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO) {p q : Nat} (hp : p < 8192) (hq : q < 8192) :
    mul17K GT DPR LIN DM DO p q = Gen.mul17G gA dA dct ε p q := by
  have h1 : (lift17 p).1 < 256 := by change p % 256 < 256; omega
  have h2 : (lift17 q).1 < 256 := by change q % 256 < 256; omega
  obtain ⟨hc, hl⟩ := sMul_code hT _ _ h1 h2
  unfold mul17K Gen.mul17G
  rw [sLift17_code hp, sLift17_code hq, hc, sEnc17_code hl]

theorem mul17G_lt {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {ε : Bool}
    {GT : List (List Nat)} {DPR : List Nat} {LIN DM DO : Nat}
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO) (p q : Nat) : Gen.mul17G gA dA dct ε p q < 8192 := by
  have h1 : (lift17 p).1 < 256 := by change p % 256 < 256; omega
  have h2 : (lift17 q).1 < 256 := by change q % 256 < 256; omega
  obtain ⟨-, hl⟩ := sMul_code hT _ _ h1 h2
  have ht := (Gen.sMulFG gA dA dct ε (lift17 p) (lift17 q)).2.1.isLt
  have hd := (Gen.sMulFG gA dA dct ε (lift17 p) (lift17 q)).2.2.isLt
  unfold Gen.mul17G enc17
  omega

end CFSG.KC.GMS.SM

end
