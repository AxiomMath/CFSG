module

public import Certificates.Data.Kernel.Spor.ONLineKW
public import CFSG.Certificates.Kernel.Spor.ONKWSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option exponentiation.threshold 600

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

theorem enc_add : ∀ (n : Nat) (f g : Nat → Nat),
    Nat.add (encF n f) (encF n g) = encF n (fun i => Nat.add (f i) (g i))
  | 0, f, g => by
    rw [enc_congr 0 f (fun _ => 0) (fun i hi => absurd hi (Nat.not_lt_zero i)),
      enc_congr 0 g (fun _ => 0) (fun i hi => absurd hi (Nat.not_lt_zero i)),
      enc_congr 0 (fun i => Nat.add (f i) (g i)) (fun _ => 0) (fun i hi => absurd hi (Nat.not_lt_zero i)),
      enc_zero]
  | n + 1, f, g => by
    rw [enc_top, enc_top, enc_top, ← enc_add n f g]
    simp only [Nat.add_eq]
    rw [Nat.mul_add]
    omega

theorem mask_lt : mask 256 < 2 ^ 256 := by
  rw [PackFld.mask_eq]
  exact Nat.sub_lt (Nat.two_pow_pos 256) Nat.one_pos

theorem sum_lt {a : Nat} (ha : a ≤ mask 256) : Nat.add a (mask 256) < 2 ^ 512 := by
  have h1 : 2 * 2 ^ 256 ≤ 2 ^ 512 := by
    rw [← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 := mask_lt
  rw [Nat.add_eq]
  generalize mask 256 = M at *
  generalize 2 ^ 256 = P at *
  generalize 2 ^ 512 = Q at *
  omega

theorem nz_half {x : Nat} (hx : x < 2 ^ 256) :
    Nat.land (Nat.shiftRight (Nat.add x (mask 256)) 256) 1 = if x = 0 then 0 else 1 := by
  rw [PackFld.mask_eq, PackFld.shr_eq, Nat.add_eq]
  have hP : 0 < 2 ^ 256 := Nat.two_pow_pos 256
  by_cases h : x = 0
  · subst h
    rw [Nat.zero_add, Nat.div_eq_of_lt (Nat.sub_lt hP Nat.one_pos), if_pos rfl]
    rfl
  · have e : (x + (2 ^ 256 - 1)) / 2 ^ 256 = 1 := by
      apply Nat.div_eq_of_lt_le
      · generalize 2 ^ 256 = P at *
        omega
      · generalize 2 ^ 256 = P at *
        omega
    rw [e, if_neg h]
    rfl

noncomputable def nzF (x : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight (Nat.add (Nat.land x (mask 256)) (mask 256)) 256) 1)
    (Nat.land (Nat.shiftRight (Nat.add (Nat.land (Nat.shiftRight x 256) (mask 256)) (mask 256)) 256) 1)

theorem lo_part (x : Nat) : Nat.land x (mask 256) = x % 2 ^ 256 := by
  rw [PackFld.mask_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x 256

theorem nzF_spec {x : Nat} (hx : x < 2 ^ 512) : (nzF x = 0 → x = 0) ∧ (nzF x = 0 ∨ nzF x = 1) := by
  have hlo : Nat.land x (mask 256) < 2 ^ 256 := by
    rw [lo_part]
    exact Nat.mod_lt _ (Nat.two_pow_pos 256)
  have hhi : Nat.land (Nat.shiftRight x 256) (mask 256) < 2 ^ 256 := by
    rw [lo_part]
    exact Nat.mod_lt _ (Nat.two_pow_pos 256)
  unfold nzF
  rw [nz_half hlo, nz_half hhi]
  have hdiv : x / 2 ^ 256 < 2 ^ 256 :=
    Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hx)
  have ex : x = 2 ^ 256 * (x / 2 ^ 256) + x % 2 ^ 256 := (Nat.div_add_mod x _).symm
  rw [lo_part, lo_part, PackFld.shr_eq, Nat.mod_eq_of_lt hdiv]
  by_cases h1 : x % 2 ^ 256 = 0 <;> by_cases h2 : x / 2 ^ 256 = 0 <;> simp only [h1, h2, if_true,
    if_false] <;> refine ⟨fun h => ?_, by decide⟩
  · rw [ex, h1, h2]
  all_goals exact absurd h (by decide)

theorem nzF_lt (x : Nat) : nzF x < 2 ^ 512 := by
  unfold nzF
  apply Nat.lt_of_le_of_lt _ (Nat.one_lt_two_pow (by omega : 512 ≠ 0))
  have a : ∀ y : Nat, Nat.land y 1 ≤ 1 := fun y => Nat.and_le_right
  have b : ∀ y z : Nat, y ≤ 1 → z ≤ 1 → Nat.lor y z ≤ 1 := by
    intro y z hy hz
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hy with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hz with rfl | rfl <;> decide
  exact b _ _ (a _) (a _)

theorem nzW_enc {n : Nat} {f : Nat → Nat} (hf : Bd n f) :
    nzW (encF n (fun _ => 1)) (encF n (fun _ => mask 256)) (encF n f) = encF n (fun i => nzF (f i)) := by
  have bM : Bd n (fun _ => mask 256) := fun _ _ => lt512_of_lt256 mask_lt
  have b1 : Bd n (fun _ => 1) := fun _ _ => Nat.one_lt_two_pow (by omega)
  have h1 : (1 : Nat) < 2 ^ (512 - 256) := Nat.one_lt_two_pow (by omega)
  have hsel : ∀ g : Nat → Nat, Bd n g → Nat.land (Nat.shiftRight (encF n g) 256) (encF n (fun _ => 1)) =
      encF n (fun i => Nat.land (Nat.shiftRight (g i) 256) 1) := by
    intro g hg
    have := enc_sel h1 n g hg
    simpa only [Nat.land_eq, Nat.shiftRight_eq'] using this
  have hhi : Nat.land (Nat.shiftRight (encF n f) 256) (encF n (fun _ => mask 256)) =
      encF n (fun i => Nat.land (Nat.shiftRight (f i) 256) (mask 256)) := by
    have := enc_sel lo_eq.2 n f hf
    simpa only [Nat.land_eq, Nat.shiftRight_eq'] using this
  have hsum : ∀ g : Nat → Nat, Bd n g → Bd n (fun i => Nat.add (Nat.land (g i) (mask 256)) (mask 256)) :=
    fun g _ i _ => sum_lt Nat.and_le_right
  have bs : ∀ y : Nat, Nat.land y 1 < 2 ^ 512 := fun y =>
    Nat.lt_of_le_of_lt Nat.and_le_right (Nat.one_lt_two_pow (by omega))
  unfold nzW
  rw [enc_and hf bM, enc_add n _ _, hsel _ (hsum f hf), hhi, enc_add n _ _,
    hsel (fun i => Nat.add (Nat.land (Nat.shiftRight (f i) 256) (mask 256)) (mask 256))
      (fun i _ => sum_lt Nat.and_le_right), enc_or (fun i _ => bs _) (fun i _ => bs _)]
  rfl

theorem eq_of_xor_zero {a b : Nat} (h : Nat.xor a b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  have := congrArg (fun z => Nat.testBit z k) h
  simp only [hop_xor, Nat.zero_testBit] at this
  revert this
  cases a.testBit k <;> cases b.testBit k <;> decide

theorem pmW_spec {n : Nat} {zp zm yp ym : Nat → Nat} (hzp : Bd n zp) (hzm : Bd n zm) (hyp : Bd n yp)
    (hym : Bd n ym)
    (h : pmW (encF n (fun _ => 1)) (encF n (fun _ => mask 256)) (encF n zp) (encF n zm) (encF n yp)
      (encF n ym) = true) :
    ∀ i < n, (yp i = zp i ∧ ym i = zm i) ∨ (yp i = zm i ∧ ym i = zp i) := by
  unfold pmW at h
  rw [enc_xor hyp hzp, enc_xor hym hzm, enc_or (hyp.xor hzp) (hym.xor hzm), enc_xor hyp hzm,
    enc_xor hym hzp, enc_or (hyp.xor hzm) (hym.xor hzp), nzW_enc ((hyp.xor hzp).or (hym.xor hzm)),
    nzW_enc ((hyp.xor hzm).or (hym.xor hzp)), enc_and (fun i _ => nzF_lt _) (fun i _ => nzF_lt _)] at h
  have e := enc_inj n _ _ (by intro i _; exact Nat.lt_of_le_of_lt Nat.and_le_right (nzF_lt _))
    (by intro _ _; exact Nat.two_pow_pos 512) ((Nat.eq_of_beq_eq_true h).trans (enc_zero n).symm)
  intro i hi
  have ei : Nat.land (nzF (Nat.lor (Nat.xor (yp i) (zp i)) (Nat.xor (ym i) (zm i))))
      (nzF (Nat.lor (Nat.xor (yp i) (zm i)) (Nat.xor (ym i) (zp i)))) = 0 := e i hi
  have s1 := nzF_spec (((hyp.xor hzp).or (hym.xor hzm)) i hi)
  have s2 := nzF_spec (((hyp.xor hzm).or (hym.xor hzp)) i hi)
  have split : ∀ {a b c d : Nat}, Nat.lor (Nat.xor a b) (Nat.xor c d) = 0 → a = b ∧ c = d := by
    intro a b c d hz
    have := Nat.or_eq_zero_iff.1 hz
    exact ⟨eq_of_xor_zero this.1, eq_of_xor_zero this.2⟩
  rcases s1.2 with z1 | z1
  · exact Or.inl (split (s1.1 z1))
  · rcases s2.2 with z2 | z2
    · exact Or.inr (split (s2.1 z2))
    · rw [z1, z2] at ei
      exact absurd ei (by decide)

theorem wmvLT_spec {n : Nat} {xp xm : Nat → Nat} {fin : Nat → Nat → Bool} (hxp : Bd n xp)
    (hxm : Bd n xm) (hd : ∀ i < n, xp i &&& xm i = 0) :
    ∀ (L : List Nat) (j : Nat) (ap am : Nat → Nat), Bd n ap → Bd n am →
      wmvLT (encF n (fun _ => 1)) (encF n xp) (encF n xm) fin L j (encF n ap) (encF n am) = true →
      ∃ gp gm : Nat → Nat, Bd n gp ∧ Bd n gm ∧ fin (encF n gp) (encF n gm) = true ∧
        ∀ i < n, mvL L (xp i >>> j) (xm i >>> j) (ap i) (am i) = vmk (gp i) (gm i)
  | [], j, ap, am, hap, ham, h => ⟨ap, am, hap, ham, h, fun _ _ => rfl⟩
  | c :: L, j, ap, am, hap, ham, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (strictB (vP c) fun cp => strictB (vM c) fun cm =>
        strictB (selW (encF n xp) (encF n (fun _ => 1)) j) fun sp =>
        strictB (selW (encF n xm) (encF n (fun _ => 1)) j) fun sm =>
        strictB (Nat.lor (Nat.mul sp cp) (Nat.mul sm cm)) fun tp =>
        strictB (Nat.lor (Nat.mul sp cm) (Nat.mul sm cp)) fun tm =>
        strictB (addP (encF n ap) (encF n am) tp tm) fun ap' =>
        strictB (addM (encF n ap) (encF n am) tp tm) fun am' =>
          wmvLT (encF n (fun _ => 1)) (encF n xp) (encF n xm) fin L (Nat.succ j) ap' am')
      (Nat.blt j 512)) (Nat.blt c (Nat.shiftLeft 1 512)) = true at h
    obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hj, h⟩ := (bAnd_iff _ _).1 h
    have hc : c < 2 ^ 512 := by
      have := Nat.blt_eq.mp hc
      rwa [PackFld.shl_eq, Nat.one_mul] at this
    have hj : j < 512 := Nat.blt_eq.mp hj
    simp only [PackFld.strictB_eqP] at h
    have h1 : (1 : Nat) < 2 ^ (512 - j) := Nat.one_lt_two_pow (by omega)
    have esp : selW (encF n xp) (encF n (fun _ => 1)) j = encF n (fun i => Nat.land (xp i >>> j) 1) :=
      enc_sel h1 n xp hxp
    have esm : selW (encF n xm) (encF n (fun _ => 1)) j = encF n (fun i => Nat.land (xm i >>> j) 1) :=
      enc_sel h1 n xm hxm
    rw [esp, esm] at h
    have hcp : vP c < 2 ^ 512 := lt512_of_lt256 (vP_lt c)
    have hcm : vM c < 2 ^ 512 := lt512_of_lt256 (vM_lt hc)
    have b1 : Bd n (fun i => Nat.land (xp i >>> j) 1 * vP c) := fun i _ => sel_mul_lt _ _ hcp
    have b2 : Bd n (fun i => Nat.land (xm i >>> j) 1 * vM c) := fun i _ => sel_mul_lt _ _ hcm
    have b3 : Bd n (fun i => Nat.land (xp i >>> j) 1 * vM c) := fun i _ => sel_mul_lt _ _ hcm
    have b4 : Bd n (fun i => Nat.land (xm i >>> j) 1 * vP c) := fun i _ => sel_mul_lt _ _ hcp
    have etp : Nat.lor (Nat.mul (encF n (fun i => Nat.land (xp i >>> j) 1)) (vP c))
        (Nat.mul (encF n (fun i => Nat.land (xm i >>> j) 1)) (vM c)) =
        encF n (fun i => Nat.lor (Nat.land (xp i >>> j) 1 * vP c) (Nat.land (xm i >>> j) 1 * vM c)) := by
      rw [Nat.mul_eq, Nat.mul_eq, enc_mul, enc_mul, enc_or b1 b2]
    have etm : Nat.lor (Nat.mul (encF n (fun i => Nat.land (xp i >>> j) 1)) (vM c))
        (Nat.mul (encF n (fun i => Nat.land (xm i >>> j) 1)) (vP c)) =
        encF n (fun i => Nat.lor (Nat.land (xp i >>> j) 1 * vM c) (Nat.land (xm i >>> j) 1 * vP c)) := by
      rw [Nat.mul_eq, Nat.mul_eq, enc_mul, enc_mul, enc_or b3 b4]
    rw [etp, etm, enc_addP hap ham (b1.or b2) (b3.or b4), enc_addM hap ham (b1.or b2) (b3.or b4)] at h
    obtain ⟨gp, gm, hgp, hgm, hfin, hmv⟩ := wmvLT_spec hxp hxm hd L (Nat.succ j) _ _
      (hap.addP ham (b1.or b2) (b3.or b4)) (hap.addM ham (b1.or b2) (b3.or b4)) h
    refine ⟨gp, gm, hgp, hgm, hfin, fun i hi => ?_⟩
    rw [mvL_cons, step_field (hd i hi)]
    exact hmv i hi

theorem pmEq_self (Z : Nat) : pmEq Z Z = true := by
  unfold pmEq
  rw [Nat.beq_refl]

theorem pmEq_neg (Z : Nat) : pmEq Z (vneg Z) = true := by
  unfold pmEq
  cases Nat.beq Z (vneg Z)
  · exact Nat.beq_refl _
  · rfl

theorem finL_spec {LA LB : List Nat} {cnt : Nat} {fK fA fB : Nat → Nat} (hK : Bd cnt fK)
    (hA : Bd cnt fA) (hB : Bd cnt fB) (hc : ∀ i < cnt, canon (fK i) = true)
    (h : finL LA LB cnt (encF cnt fK) (encF cnt fA) (encF cnt fB) = true) :
    ∀ i < cnt, pmEq (fA i) (mv LA (fK i)) = true ∧ pmEq (fB i) (mv LB (fK i)) = true := by
  unfold finL at h
  simp only [PackFld.strictB_eqP, rep_eq] at h
  have hP : ∀ {f : Nat → Nat}, Bd cnt f →
      Nat.land (encF cnt f) (encF cnt (fun _ => mask 256)) = encF cnt (fun i => vP (f i)) := by
    intro f hf
    have := enc_sel lo_eq.1 cnt f hf
    rw [Nat.shiftRight_zero] at this
    change (encF cnt f &&& encF cnt (fun _ => mask 256)) = _
    rw [this]
    simp only [Nat.shiftRight_zero]
    rfl
  have hM : ∀ {f : Nat → Nat}, Bd cnt f →
      Nat.land (Nat.shiftRight (encF cnt f) 256) (encF cnt (fun _ => mask 256)) =
        encF cnt (fun i => vM (f i)) := by
    intro f hf
    have := enc_sel lo_eq.2 cnt f hf
    change (encF cnt f >>> 256) &&& encF cnt (fun _ => mask 256) = _
    rw [this]
    exact enc_congr cnt _ _ fun i hi => field_hi (hf i hi)
  rw [hP hK, hM hK, hP hA, hM hA, hP hB, hM hB] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have bP : ∀ {f : Nat → Nat}, Bd cnt (fun i => vP (f i)) := fun _ _ => lt512_of_lt256 (vP_lt _)
  have bM : ∀ {f : Nat → Nat}, Bd cnt f → Bd cnt (fun i => vM (f i)) :=
    fun hf i hi => lt512_of_lt256 (vM_lt (hf i hi))
  have hd : ∀ i < cnt, vP (fK i) &&& vM (fK i) = 0 := fun i hi => (canon_bits (hc i hi)).1
  have b0 : Bd cnt (fun _ => 0) := fun _ _ => Nat.two_pow_pos 512
  obtain ⟨ap, am, hap, ham, fA', sA⟩ :=
    wmvLT_spec bP (bM hK) hd LA 0 _ _ b0 b0 (by rw [enc_zero]; exact h1)
  obtain ⟨bp, bm, hbp, hbm, fB', sB⟩ :=
    wmvLT_spec bP (bM hK) hd LB 0 _ _ b0 b0 (by rw [enc_zero]; exact h2)
  have pA := pmW_spec bP (bM hA) hap ham fA'
  have pB := pmW_spec bP (bM hB) hbp hbm fB'
  intro i hi
  have e : ∀ L, mv L (fK i) = mvL L (vP (fK i) >>> 0) (vM (fK i) >>> 0) 0 0 := by
    intro L
    simp only [mv, PackFld.strictN_eqP, Nat.shiftRight_zero]
  have fin1 : ∀ {Z yp ym : Nat}, (yp = vP Z ∧ ym = vM Z) ∨ (yp = vM Z ∧ ym = vP Z) →
      pmEq Z (vmk yp ym) = true := by
    intro Z yp ym hz
    rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [vmk_vP_vM]
      exact pmEq_self Z
    · exact pmEq_neg Z
  rw [e, e, sA i hi, sB i hi]
  exact ⟨fin1 (pA i hi), fin1 (pB i hi)⟩

theorem lineRangeW_imp {KL LP : Nat → Nat} {LA LB : List Nat} {AL BL : Nat → Nat} {n lo cnt : Nat}
    (h : lineRangeW KL LP LA LB AL BL n lo cnt = true) : lineRange KL LP LA LB AL BL n lo cnt = true := by
  obtain ⟨hl, hp⟩ := (bAnd_iff _ _).1 h
  have hl := allBlk_spec hl
  obtain ⟨h1, h2⟩ := ptsW_spec cnt 0 0 0 hp
  simp only [Nat.mul_zero, Nat.add_zero] at h2
  have hf := finL_spec (fun i _ => key_lt KL _) (fun i _ => key_lt KL _) (fun i _ => key_lt KL _)
    (fun i hi => (h1 i hi).1) h2
  refine allBlk_of fun l hl' => ?_
  obtain ⟨hc, ha, hb⟩ := h1 l hl'
  obtain ⟨eA, eB⟩ := hf l hl'
  have hle : lead1 (key KL (lo + l)) (tab LP (lo + l)) = true := hl l hl'
  unfold lineAt
  simp only [PackFld.strictB_eqP, Nat.add_eq]
  rw [hc, hle, Nat.blt_eq.mpr ha, Nat.blt_eq.mpr hb, eA, eB]

end CFSG.KS.ONW

end
