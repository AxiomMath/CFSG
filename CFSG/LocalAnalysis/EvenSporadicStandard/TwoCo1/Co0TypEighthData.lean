module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypPow
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import Certificates.Certificate24532

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.B.TwoA.Census

theorem bvec_pow_two_apply (n : ℕ) (i : Fin 24) :
    bvec 24 (2 ^ n) i = if n = (i : ℕ) then 1 else 0 := by
  simp [bvec_apply, Nat.testBit_two_pow]

theorem bvec_sigRec {a : Array ℕ} (ha : PermArr a = true) (w : ℕ) :
    ∀ n, n ≤ 24 → ∀ i : Fin 24, bvec 24 (sigRec a w n) i =
      if (i : ℕ) < n then bvec 24 w (arrFun a i) else 0
  | 0, _, i => by simp [sigRec, bvec_zero]
  | n + 1, hn, i => by
    have ih := bvec_sigRec ha w n (by omega) i
    have hv : bvec 24 w (arrFun a i) = if w.testBit a[(i : ℕ)]! then 1 else 0 := by
      rw [bvec_apply, arrFun_val ha i]
    have hb : bvec 24 (if w.testBit a[n]! then 2 ^ n else 0) i =
        if (n = (i : ℕ)) ∧ w.testBit a[n]! = true then 1 else 0 := by
      by_cases h2 : n = (i : ℕ)
      · subst h2
        by_cases h1 : w.testBit a[(i : ℕ)]! = true
        · simp [h1, bvec_pow_two_apply]
        · simp [h1, bvec_zero]
      · by_cases h1 : w.testBit a[n]! = true
        · simp [h1, bvec_pow_two_apply, h2]
        · simp [h1, bvec_zero]
    rw [sigRec, bvec_xor, Pi.add_apply, ih, hb]
    by_cases hlt : (i : ℕ) < n
    · have h1 : (i : ℕ) < n + 1 := by omega
      have h2 : ¬ (n = (i : ℕ)) := by omega
      simp [hlt, h1, h2]
    · by_cases heq : (i : ℕ) = n
      · subst heq
        simp [hv]
      · have h1 : ¬ (i : ℕ) < n + 1 := by omega
        have h2 : ¬ (n = (i : ℕ)) := fun h => heq h.symm
        simp [hlt, h1, h2]

theorem bvec_sigN {a : Array ℕ} (ha : PermArr a = true) (w : ℕ) :
    bvec 24 (sigN a w) = bvec 24 w ∘ arrFun a := by
  funext i
  rw [sigN, bvec_sigRec ha w 24 le_rfl i]
  simp [i.2]

theorem bvec_powSumN {a : Array ℕ} (ha : PermArr a = true) (w k : ℕ) :
    bvec 24 (powSumN a w k) = ∑ j ∈ Finset.range k, bvec 24 w ∘ (arrFun a)^[j] := by
  induction k with
  | zero => simp [powSumN, bvec_zero]
  | succ k ih =>
    rw [powSumN, bvec_xor, bvec_sigN ha, ih, Finset.sum_range_succ']
    funext i
    simp [Finset.sum_apply, Function.iterate_succ, add_comm]

theorem coe_permC_symm (q : AutPerm) (b : C) :
    ((permC q).symm b : Fin 24 → ZMod 2) = (b : Fin 24 → ZMod 2) ∘ ⇑(q : Equiv.Perm (Fin 24)) := by
  funext i
  simp [permC, permWord]

theorem coe_powSumC (p : AutPerm) (b : C) (k : ℕ) :
    ((powSumC p b k : C) : Fin 24 → ZMod 2) =
      ∑ j ∈ Finset.range k, (b : Fin 24 → ZMod 2) ∘ (⇑(p : Equiv.Perm (Fin 24)))^[j] := by
  rw [powSumC, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coe_permC_symm, Subgroup.coe_pow, Equiv.Perm.coe_pow]

theorem popc_add (k m : ℕ) : ∀ a, popc (k + m) a = popc k a + popc m (a / 2 ^ k) := by
  induction k with
  | zero => intro a; simp [popc]
  | succ k ih =>
    intro a
    rw [show k + 1 + m = (k + m) + 1 by omega, popc, ih, popc, pow_succ',
      ← Nat.div_div_eq_div_mul]
    omega

theorem popc_mod (k : ℕ) : ∀ a, popc k (a % 2 ^ k) = popc k a := by
  induction k with
  | zero => intro a; simp [popc]
  | succ k ih =>
    intro a
    rw [popc, popc, pow_succ', Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _),
      Nat.mod_mul_right_div_self, ih]

theorem popTab_getElem {i : ℕ} (hi : i < 4096) : popTab[i]! = popc 12 i := by
  simp [popTab, getElem!_pos, hi]

theorem pop24_eq (x : ℕ) : pop24 x = popc 24 x := by
  have h1 : popc 24 x = popc 12 x + popc 12 (x / 2 ^ 12) := popc_add 12 12 x
  have h2 := popc_mod 12 x
  have h3 := popc_mod 12 (x / 4096)
  rw [h1, pop24, popTab_getElem (Nat.mod_lt _ (by norm_num)),
    popTab_getElem (Nat.mod_lt _ (by norm_num))]
  norm_num at h2 h3 ⊢
  omega

theorem eighthPermOK_weight {a : Array ℕ} (ha : PermArr a = true) (h : eighthPermOK a = true)
    {w : Fin 24 → ZMod 2} (hw : w ∈ C) :
    hammingNorm (∑ j ∈ Finset.range 8, w ∘ (arrFun a)^[j]) = 0 ∨
      hammingNorm (∑ j ∈ Finset.range 8, w ∘ (arrFun a)^[j]) = 16 := by
  have hbad : eighthWeightBad a = 0 := by
    simp only [eighthPermOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  have hsum := sum_comb_bvec 24 (fun x => badWt (hammingNorm x))
    (fun i => (eighthImgs a).getD i 0) 12 0
  have hrhs : treeSumN (fun x => (fun x => badWt (hammingNorm x)) (bvec 24 x))
      (fun i => (eighthImgs a).getD i 0) 12 0 = 0 := by
    simpa only [eighthWeightBad, hammingNorm_bvec, pop24_eq] using hbad
  rw [hrhs] at hsum
  have hμ := (Finset.sum_eq_zero_iff.1 hsum) (fun i : Fin 12 => ψ w i) (Finset.mem_univ _)
  have hword : ∑ j ∈ Finset.range 8, w ∘ (arrFun a)^[j] =
      bvec 24 0 + ∑ i : Fin 12, (ψ w i) • bvec 24 ((eighthImgs a).getD i 0) := by
    let Tl : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
      ∑ j ∈ Finset.range 8, LinearMap.funLeft (ZMod 2) (ZMod 2) ((arrFun a)^[j])
    have hTl : ∀ x, Tl x = ∑ j ∈ Finset.range 8, x ∘ (arrFun a)^[j] := by
      intro x
      simp only [Tl, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun _ _ => rfl
    rw [← hTl]
    conv_lhs => rw [eq_comb_of_mem_C hw]
    rw [map_sum, bvec_zero, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hTl, B_eq_bvec, ← bvec_powSumN ha]
    simp [eighthImgs, List.getD_eq_getElem?_getD]
  rw [hword]
  by_contra hcon
  simp only [badWt, hcon, ↓reduceIte] at hμ
  exact one_ne_zero hμ

theorem eighthPermOK_pow {a : Array ℕ} (ha : PermArr a = true) (h : eighthPermOK a = true) :
    decode a ^ 8 = 1 := by
  have h1 : amul (amul (amul a a) (amul a a)) (amul (amul a a) (amul a a)) = idArr := by
    simp only [eighthPermOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  have h2 := congrArg decode h1
  have ha2 := PermArr_amul ha ha
  have ha4 := PermArr_amul ha2 ha2
  rw [decode_idArr, decode_amul ha4 ha4, decode_amul ha2 ha2, decode_amul ha ha] at h2
  rw [← h2]
  simp [pow_succ, mul_assoc]

theorem eighth_key (b : C)
    (p : AutPerm) (hp : (p : Equiv.Perm (Fin 24)) ∈ sylowSub) :
    p ^ 8 = 1 ∧ (hammingNorm (powSumC p b 8 : Fin 24 → ZMod 2) = 0 ∨
      hammingNorm (powSumC p b 8 : Fin 24 → ZMod 2) = 16) := by
  obtain ⟨i, hi, hpi⟩ := (sylowSub_facts.2 _).1 hp
  have hcheck := Certificates.certificate24532
  have hok : eighthPermOK sylowCert.pts[i]! = true := by
    simp only [eighthCheck, List.all_eq_true, List.mem_range] at hcheck
    exact hcheck i hi
  have ha : PermArr sylowCert.pts[i]! = true := certOK_perm sylowCert_ok hi
  have hdec : decode sylowCert.pts[i]! = (p : Equiv.Perm (Fin 24)) := hpi
  refine ⟨Subtype.ext ?_, ?_⟩
  · have := eighthPermOK_pow ha hok
    rw [hdec] at this
    exact this
  · rw [coe_powSumC]
    have := eighthPermOK_weight ha hok (w := (b : Fin 24 → ZMod 2)) b.2
    rwa [← coe_decode ha, hdec] at this

theorem gO_mul_PO_pow_eight (b : C)
    (p : AutPerm) (hp : (p : Equiv.Perm (Fin 24)) ∈ sylowSub) :
    ∃ e : C, (gO b * PO p) ^ 8 = gO e ∧
      (hammingNorm (e : Fin 24 → ZMod 2) = 0 ∨ hammingNorm (e : Fin 24 → ZMod 2) = 16) := by
  obtain ⟨h1, h2⟩ := eighth_key b p hp
  exact ⟨powSumC p b 8, by rw [gO_mul_PO_pow, h1, PO_one, mul_one], h2⟩

end CFSG.EvenSporadicStandard.TwoCo1
