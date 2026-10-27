module

public import Certificates.Data.Kernel.GMS78RuSCent16
import CFSG.Certificates.Kernel.GMS78RuSC.Basic
import CFSG.Certificates.Kernel.GMS78RuP.Basic

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

private theorem ru16_land255 (x : Nat) : Nat.land x 255 = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa using this

private theorem ru16_land7 (x : Nat) : Nat.land x 7 = x % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 3
  simpa using this

private theorem ru16_land1 (x : Nat) : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x

private theorem ru16_shr (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k :=
  Nat.shiftRight_eq_div_pow x k

private noncomputable def ru16_pd (p : Nat) : Nat := fget (nat_lit 3864) (Nat.shiftRight p 9) 3

private theorem ru16_pd_lt (p : Nat) : ru16_pd p < 8 := SC.fget_lt _ _ 3

private theorem ru16_pd_block {p i : Nat} (h1 : 512 * i ≤ p) (h2 : p < 512 * i + 512) :
    ru16_pd p = fget (nat_lit 3864) i 3 := by
  have e : Nat.shiftRight p 9 = i := by rw [ru16_shr]; omega
  unfold ru16_pd
  rw [e]

private theorem ru16_pack_eq {c T D : Nat} (hc : c < 256) (hT : T < 8) (hD : D < 8) :
    Nat.lor c (Nat.lor (Nat.shiftLeft T 8) (Nat.shiftLeft D 11)) = c + 256 * T + 2048 * D := by
  have e1 : T <<< 8 = T * 256 := Nat.shiftLeft_eq T 8
  have e2 : D <<< 11 = D * 2048 := Nat.shiftLeft_eq D 11
  have h1 : (T <<< 8 ||| c) = T * 256 + c := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega) T, e1]
  have h2 : (D <<< 11 ||| (T * 256 + c)) = D * 2048 + (T * 256 + c) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega) D, e2]
  change c ||| (T <<< 8 ||| D <<< 11) = _
  rw [Nat.or_comm (T <<< 8), ← Nat.or_assoc, Nat.or_comm c, Nat.or_assoc, Nat.or_comm c, h1, h2]
  omega

private theorem ru16_lift_pack (p : Nat) : sLift16 p =
    Nat.land p 255 + 256 * (4 * Nat.land (Nat.shiftRight p 8) 1) + 2048 * ru16_pd p := by
  unfold sLift16
  rw [ru16_pack_eq]
  · rfl
  · simp only [ru16_land255]; omega
  · simp only [ru16_land1, Nat.mul_eq]; omega
  · exact SC.fget_lt _ _ 3

private theorem ru16_dec_c (p : Nat) : Nat.land (sLift16 p) 255 = Nat.land p 255 := by
  rw [ru16_lift_pack]; simp only [ru16_land255, ru16_land1, ru16_shr]; omega

private theorem ru16_dec_t (p : Nat) :
    Nat.land (Nat.shiftRight (sLift16 p) 8) 7 = Nat.mul 4 (Nat.land (Nat.shiftRight p 8) 1) := by
  rw [ru16_lift_pack]
  simp only [ru16_land255, ru16_land1, ru16_land7, ru16_shr, Nat.mul_eq]
  omega

private theorem ru16_dec_d (p : Nat) : Nat.land (Nat.shiftRight (sLift16 p) 11) 7 = ru16_pd p := by
  have := ru16_pd_lt p
  rw [ru16_lift_pack]
  simp only [ru16_land255, ru16_land1, ru16_land7, ru16_shr]
  omega

private theorem ru16_enc_lor {c T D : Nat} (hc : c < 256) (hT : T < 8) (hD : D < 8) :
    sEnc16 (Nat.lor c (Nat.lor (Nat.shiftLeft T 8) (Nat.shiftLeft D 11))) % 256 = c ∧
    sEnc16 (Nat.lor c (Nat.lor (Nat.shiftLeft T 8) (Nat.shiftLeft D 11))) / 512 = D / 2 := by
  rw [ru16_pack_eq hc hT hD]
  unfold sEnc16
  simp only [ru16_land255, ru16_land1, ru16_shr, Nat.add_eq, Nat.mul_eq]
  omega

private theorem ru16_mul16K_fields (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p q : Nat) :
    mul16K GT DPR LIN DM DO p q % 256 = Nat.xor (Nat.land p 255)
      (Nat.land (fget (neGet 0 DPR (ru16_pd p)) (Nat.land q 255) 11) 255) ∧
    mul16K GT DPR LIN DM DO p q / 512 =
      fget DM (Nat.add (Nat.mul 8 (ru16_pd p)) (ru16_pd q)) 3 / 2 := by
  unfold mul16K sMulK
  simp only [ru16_dec_c, ru16_dec_t, ru16_dec_d]
  refine ru16_enc_lor ?_ ?_ ?_
  · exact Nat.xor_lt_two_pow (n := 8) (by rw [ru16_land255]; omega) (by rw [ru16_land255]; omega)
  · have h11 := SC.fget_lt (neGet 0 DPR (ru16_pd p)) (Nat.land q 255) 11
    refine Nat.xor_lt_two_pow (n := 3) (Nat.xor_lt_two_pow (n := 3) (Nat.xor_lt_two_pow (n := 3)
      (Nat.xor_lt_two_pow (n := 3) ?_ (SC.fget_lt _ _ 3)) ?_) (SC.fget_lt _ _ 3)) ?_
    · simp only [ru16_land1, Nat.mul_eq]; omega
    · rw [ru16_shr _ 8]; omega
    · have := SC.fget_lt DO (Nat.add (Nat.mul 8 (ru16_pd p)) (ru16_pd q)) 1
      omega
  · exact SC.fget_lt _ _ 3

private def ru16_CommTests (m : Nat → Nat → Nat) (DPR : List Nat) (DM u : Nat) : Prop :=
  ∀ p, m p u = m u p →
    cDTest16 DM (ru16_pd p) (ru16_pd u) = true ∧
    cCTest (neGet 0 DPR (ru16_pd p)) (neGet 0 DPR (ru16_pd u)) (Nat.land u 255)
      (Nat.land p 255) = true

private theorem ru16_comm_tests (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO p u : Nat)
    (h : mul16K GT DPR LIN DM DO p u = mul16K GT DPR LIN DM DO u p) :
    cDTest16 DM (ru16_pd p) (ru16_pd u) = true ∧
    cCTest (neGet 0 DPR (ru16_pd p)) (neGet 0 DPR (ru16_pd u)) (Nat.land u 255)
      (Nat.land p 255) = true := by
  constructor
  · have := (ru16_mul16K_fields GT DPR LIN DM DO p u).2
    rw [h, (ru16_mul16K_fields GT DPR LIN DM DO u p).2] at this
    unfold cDTest16
    rw [Nat.beq_eq, ru16_shr, ru16_shr]
    omega
  · have := (ru16_mul16K_fields GT DPR LIN DM DO p u).1
    rw [h, (ru16_mul16K_fields GT DPR LIN DM DO u p).1] at this
    unfold cCTest
    rw [Nat.beq_eq]
    exact this.symm

private theorem ru16_sCentT_eq (m : Nat → Nat → Nat) (u base : Nat) (acc : List Nat) :
    ∀ L : List Nat, sCentT m u base L acc =
      (L.map (· + base)).filter (fun p => Nat.beq (m p u) (m u p)) ++ acc
  | [] => rfl
  | pc :: L => by
    change (fun p => Bool.rec (motive := fun _ => List Nat) (sCentT m u base L acc)
      (List.cons p (sCentT m u base L acc)) (Nat.beq (m p u) (m u p))) (Nat.add pc base) = _
    rw [ru16_sCentT_eq m u base acc L, List.map_cons, List.filter_cons]
    simp only [Nat.add_eq]
    cases h : Nat.beq (m (pc + base) u) (m u (pc + base))
    · simp [h]
    · simp [h]

private theorem ru16_blockT (m : Nat → Nat → Nat) (DPR : List Nat) (DM u i j base : Nat)
    (hb : base = 512 * i + 256 * j) (hj : j < 2) (hm : ru16_CommTests m DPR DM u) :
    ((sFilter 256 fun pc => cCTest (neGet 0 DPR (fget (nat_lit 3864) i 3))
        (neGet 0 DPR (fget (nat_lit 3864) (Nat.shiftRight u 9) 3)) (Nat.land u 255) pc).map
        (· + base)).filter (fun p => Nat.beq (m p u) (m u p)) =
      (List.range' base 256).filter (fun p => Nat.beq (m p u) (m u p)) := by
  subst hb
  rw [P117.sFilter_eq, List.range'_eq_map_range, List.filter_map, List.filter_map,
    List.filter_filter]
  have e : (fun x => 512 * i + 256 * j + x) = (fun x => x + (512 * i + 256 * j)) := by
    funext x; omega
  rw [e]
  congr 1
  apply List.filter_congr
  intro pc hpc
  rw [List.mem_range] at hpc
  simp only [Function.comp]
  cases hg : Nat.beq (m (pc + (512 * i + 256 * j)) u) (m u (pc + (512 * i + 256 * j)))
  · simp
  · have h := (hm _ (Nat.eq_of_beq_eq_true hg)).2
    have e1 : ru16_pd (pc + (512 * i + 256 * j)) = fget (nat_lit 3864) i 3 :=
      ru16_pd_block (by omega) (by omega)
    have e2 : Nat.land (pc + (512 * i + 256 * j)) 255 = pc := by
      rw [ru16_land255]; omega
    rw [e1, e2] at h
    have hu : ru16_pd u = fget (nat_lit 3864) (Nat.shiftRight u 9) 3 := rfl
    rw [hu] at h
    simp only [h, hg, Bool.and_self]

private theorem ru16_sCentE16_eq (m : Nat → Nat → Nat) (DPR : List Nat) (DM u i : Nat)
    (acc : List Nat) (hm : ru16_CommTests m DPR DM u) :
    sCentE16 m DPR DM u i acc =
      (List.range' (512 * i) 512).filter (fun p => Nat.beq (m p u) (m u p)) ++ acc := by
  unfold sCentE16
  dsimp only
  cases hD : cDTest16 DM (fget (nat_lit 3864) i 3) (fget (nat_lit 3864) (Nat.shiftRight u 9) 3)
  · symm
    rw [List.filter_eq_nil_iff.2, List.nil_append]
    intro p hp
    rw [List.mem_range'_1] at hp
    have e1 : ru16_pd p = fget (nat_lit 3864) i 3 := ru16_pd_block (by omega) (by omega)
    cases hg : Nat.beq (m p u) (m u p)
    · simp
    · have h := (hm p (Nat.eq_of_beq_eq_true hg)).1
      have hu : ru16_pd u = fget (nat_lit 3864) (Nat.shiftRight u 9) 3 := rfl
      rw [e1, hu, hD] at h
      exact absurd h (by simp)
  · dsimp only
    simp only [Nat.mul_eq, Nat.add_eq]
    simp only [ru16_sCentT_eq]
    rw [ru16_blockT m DPR DM u i 0 (512 * i) (by omega) (by omega) hm,
      ru16_blockT m DPR DM u i 1 (512 * i + 256) (by omega) (by omega) hm]
    have h1 : List.range' (512 * i) 256 ++ List.range' (512 * i + 256) 256 =
        List.range' (512 * i) (256 + 256) := List.range'_append_1
    simp only [Nat.reduceAdd] at h1
    rw [← h1]
    simp only [List.filter_append, List.append_assoc]

private theorem ru16_sCent16_eq (m : Nat → Nat → Nat) (DPR : List Nat) (DM u : Nat)
    (hm : ru16_CommTests m DPR DM u) :
    sCent16 m DPR DM u = (List.range 2048).filter (fun p => Nat.beq (m p u) (m u p)) := by
  have e : List.range 2048 = List.range' (512 * 0) 512 ++ (List.range' (512 * 1) 512 ++
      (List.range' (512 * 2) 512 ++ List.range' (512 * 3) 512)) := by
    have h1 : List.range' 0 512 ++ List.range' (0 + 512) 1536 = List.range' 0 (512 + 1536) :=
      List.range'_append_1
    have h2 : List.range' 512 512 ++ List.range' (512 + 512) 1024 = List.range' 512 (512 + 1024) :=
      List.range'_append_1
    have h3 : List.range' 1024 512 ++ List.range' (1024 + 512) 512 = List.range' 1024 (512 + 512) :=
      List.range'_append_1
    simp only [Nat.reduceAdd] at h1 h2 h3
    rw [List.range_eq_range']
    simp only [Nat.reduceMul]
    rw [h3, h2, h1]
  rw [e]
  show sCentE16 m DPR DM u 0 (sCentE16 m DPR DM u 1 (sCentE16 m DPR DM u 2
    (sCentE16 m DPR DM u 3 []))) = _
  rw [ru16_sCentE16_eq m DPR DM u 0 _ hm, ru16_sCentE16_eq m DPR DM u 1 _ hm,
    ru16_sCentE16_eq m DPR DM u 2 _ hm, ru16_sCentE16_eq m DPR DM u 3 _ hm]
  simp only [List.filter_append, List.append_nil]

private def ru16_keyV (m : Nat → Nat → Nat) (u p : Nat) : Nat :=
  (fun s => Nat.add 1 (Nat.add
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s u)) 14)
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s 256)) 28))) (m p p)

private theorem ru16_sKey_eq (m : Nat → Nat → Nat) (u : Nat) : ∀ n : Nat,
    sKey m n u =
      (((List.range n).filter (fun p => Nat.beq (m p u) (m u p))).map (ru16_keyV m u)).sum
  | 0 => rfl
  | n + 1 => by
    change strictN (sKey m n u) (fun a => Bool.rec (motive := fun _ => Nat) a
      (Nat.add a (ru16_keyV m u n)) (Nat.beq (m n u) (m u n))) = _
    rw [P117.strictN_eq, ru16_sKey_eq m u n, List.range_succ, List.filter_append]
    cases h : Nat.beq (m n u) (m u n)
    · simp [h]
    · simp [h, Nat.add_comm]

private theorem ru16_sKeyL_eq (m : Nat → Nat → Nat) (u : Nat) : ∀ C : List Nat,
    sKeyL m u C = (C.map (ru16_keyV m u)).sum
  | [] => rfl
  | p :: C => by
    change strictN (sKeyL m u C) (fun a => Nat.add a (ru16_keyV m u p)) = _
    rw [P117.strictN_eq, ru16_sKeyL_eq m u C, List.map_cons, List.sum_cons]
    exact Nat.add_comm _ _

private theorem ru16_sKeyL_filter (m : Nat → Nat → Nat) (u : Nat) :
    sKeyL m u ((List.range 2048).filter (fun p => Nat.beq (m p u) (m u p))) = sKey m 2048 u := by
  rw [ru16_sKeyL_eq, ru16_sKey_eq]

theorem kKey16_sound (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO u k : Nat)
    (h : kKey16 GT DPR LIN DM DO u k = true) :
    Nat.beq (sKey (mul16K GT DPR LIN DM DO) 2048 u) (kKeyPart k) = true := by
  unfold kKey16 at h
  rw [SC.neStrictB_eq, SC.neStrictB_eq] at h
  beta_reduce at h
  have hm : ru16_CommTests (mul16K GT DPR LIN DM DO) DPR DM u := fun p hp =>
    ru16_comm_tests GT DPR LIN DM DO p u hp
  rw [ru16_sCent16_eq _ DPR DM u hm, ru16_sKeyL_filter] at h
  exact h

end CFSG.KC.GMS

end
