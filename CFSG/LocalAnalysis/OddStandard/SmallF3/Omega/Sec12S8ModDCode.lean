module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDBase
public import CFSG.HardMathSupport.RichardWeiss.Proving.AltFiveGeneration
public import Certificates.Data.S8DFin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.S8DFin CFSG.HardMathSupport.RichardWeiss.Proving

private theorem s8d_zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide +kernel

private theorem s8d_add_self (v : EvW × EvW) : v + v = 0 := by
  obtain ⟨a, b⟩ := v
  refine Prod.ext (Subtype.ext (funext fun i => ?_)) (Subtype.ext (funext fun i => ?_))
  · exact s8d_zmod2_add_self (a.1 i)
  · exact s8d_zmod2_add_self (b.1 i)

private instance s8dDecIsEvenVec : DecidablePred (IsEvenVec (n := 5)) := fun v => by
  unfold IsEvenVec
  infer_instance

private instance s8dFintypeEvW : Fintype EvW :=
  inferInstanceAs (Fintype {v : Fin 5 → ZMod 2 // IsEvenVec v})

@[expose] def s8dW (j : Fin 5) : EvW := ⟨wvec j, wvec_even j⟩

@[expose] def s8dBas : Fin 8 → EvW × EvW :=
  ![(s8dW 0, 0), (s8dW 1, 0), (s8dW 2, 0), (s8dW 3, 0), (0, s8dW 0), (0, s8dW 1), (0, s8dW 2),
    (0, s8dW 3)]

@[expose] def s8dDec (n : ℕ) : EvW × EvW := ∑ k : Fin 8, if n.testBit k then s8dBas k else 0

@[expose] def s8dCol (m : M8) : Fin 8 → ℕ := ![m.c0, m.c1, m.c2, m.c3, m.c4, m.c5, m.c6, m.c7]

theorem s8dDec_xor (m n : ℕ) : s8dDec (m ^^^ n) = s8dDec m + s8dDec n := by
  unfold s8dDec
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases hm : m.testBit k <;> cases hn : n.testBit k <;> simp_all [s8d_add_self]

theorem s8dDec_zero : s8dDec 0 = 0 := by
  simp [s8dDec]

theorem s8dDec_bas (k : Fin 8) : s8dDec (2 ^ (k : ℕ)) = s8dBas k := by
  revert k
  decide +kernel

theorem s8dAp_dec (f : S8A) (n : ℕ) :
    s8dAp f (s8dDec n) = ∑ k : Fin 8, if n.testBit k then s8dAp f (s8dBas k) else 0 := by
  unfold s8dDec
  let F : EvW × EvW →+ EvW × EvW :=
    { toFun := s8dAp f, map_zero' := s8dAp_zero f, map_add' := s8dAp_add f }
  change F (∑ k : Fin 8, if n.testBit k then s8dBas k else 0) =
    ∑ k : Fin 8, if n.testBit k then s8dAp f (s8dBas k) else 0
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [apply_ite F, map_zero]
  rfl

private theorem s8dDec_eq_zero : ∀ t < 256, s8dDec t = 0 → t = 0 := by
  decide +kernel

theorem s8dDec_inj {m n : ℕ} (hm : m < 256) (hn : n < 256) (h : s8dDec m = s8dDec n) : m = n := by
  have hxor : s8dDec (m ^^^ n) = 0 := by
    rw [s8dDec_xor, h, s8d_add_self]
  have hlt : m ^^^ n < 256 := by
    have hm' : m < 2 ^ 8 := by
      rw [show (2 : ℕ) ^ 8 = 256 from by norm_num]
      exact hm
    have hn' : n < 2 ^ 8 := by
      rw [show (2 : ℕ) ^ 8 = 256 from by norm_num]
      exact hn
    have h := Nat.xor_lt_two_pow hm' hn'
    rwa [show (2 : ℕ) ^ 8 = 256 from by norm_num] at h
  have h0 : m ^^^ n = 0 := s8dDec_eq_zero (m ^^^ n) hlt hxor
  apply Nat.eq_of_testBit_eq
  intro i
  have hzi : (m ^^^ n).testBit i = false := by simp [h0]
  rw [Nat.testBit_xor] at hzi
  revert hzi
  cases m.testBit i <;> cases n.testBit i <;> simp_all

theorem s8dDec_surj (p : EvW × EvW) : ∃ n < 256, s8dDec n = p := by
  have hcardEv : Fintype.card EvW = 16 := by decide +kernel
  have hcard : Fintype.card (EvW × EvW) = 256 := by
    rw [Fintype.card_prod, hcardEv]
  have hinj : Function.Injective (fun n : Fin 256 => s8dDec (n : ℕ)) := by
    intro a b hab
    exact Fin.ext (s8dDec_inj a.2 b.2 hab)
  have he : Fin 256 ≃ EvW × EvW :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin]; exact hcard.symm)
  have hsurj : Function.Surjective (fun n : Fin 256 => s8dDec (n : ℕ)) :=
    (Finite.injective_iff_surjective_of_equiv he).mp hinj
  obtain ⟨n, hn⟩ := hsurj p
  exact ⟨(n : ℕ), n.2, hn⟩

theorem s8d_ext8 {f g : S8A} (h : ∀ k : Fin 8, s8dAp f (s8dBas k) = s8dAp g (s8dBas k)) :
    f = g := by
  refine s8d_ext fun p => ?_
  obtain ⟨n, _, rfl⟩ := s8dDec_surj p
  rw [s8dAp_dec, s8dAp_dec]
  exact Finset.sum_congr rfl fun k _ => by rw [h k]

private theorem s8dDec_ap_sum (m : M8) (n : ℕ) :
    s8dDec (m.ap n) = ∑ k : Fin 8, if n.testBit k then s8dDec (s8dCol m k) else 0 := by
  rw [Fin.sum_univ_eight]
  unfold M8.ap
  rw [s8dDec_xor, s8dDec_xor, s8dDec_xor, s8dDec_xor, s8dDec_xor, s8dDec_xor, s8dDec_xor]
  rw [apply_ite s8dDec, apply_ite s8dDec, apply_ite s8dDec, apply_ite s8dDec,
    apply_ite s8dDec, apply_ite s8dDec, apply_ite s8dDec, apply_ite s8dDec]
  simp [s8dCol, s8dDec_zero]

theorem s8dDec_ap {f : EvW × EvW → EvW × EvW} (hf : ∀ p q, f (p + q) = f p + f q) {m : M8}
    (hm : ∀ k : Fin 8, f (s8dBas k) = s8dDec (s8dCol m k)) (n : ℕ) :
    f (s8dDec n) = s8dDec (m.ap n) := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero, s8d_add_self] at h
    exact h
  let F : EvW × EvW →+ EvW × EvW := { toFun := f, map_zero' := h0, map_add' := hf }
  have hF : ∀ p, F p = f p := fun _ => rfl
  have hL : F (s8dDec n) = ∑ k : Fin 8, if n.testBit k then s8dDec (s8dCol m k) else 0 := by
    conv_lhs => rw [s8dDec]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [apply_ite F, map_zero, hF, hm k]
  rw [← hF (s8dDec n), hL, s8dDec_ap_sum]

private theorem s8d_xor8_lt (g : Fin 8 → ℕ) (h : ∀ k, g k < 256) :
    g 0 ^^^ g 1 ^^^ g 2 ^^^ g 3 ^^^ g 4 ^^^ g 5 ^^^ g 6 ^^^ g 7 < 256 := by
  have h' : ∀ k, g k < 2 ^ 8 := by
    intro k
    rw [show (2 : ℕ) ^ 8 = 256 from by norm_num]
    exact h k
  have h1 : g 0 ^^^ g 1 < 2 ^ 8 := Nat.xor_lt_two_pow (h' 0) (h' 1)
  have h2 : g 0 ^^^ g 1 ^^^ g 2 < 2 ^ 8 := Nat.xor_lt_two_pow h1 (h' 2)
  have h3 : g 0 ^^^ g 1 ^^^ g 2 ^^^ g 3 < 2 ^ 8 := Nat.xor_lt_two_pow h2 (h' 3)
  have h4 : g 0 ^^^ g 1 ^^^ g 2 ^^^ g 3 ^^^ g 4 < 2 ^ 8 := Nat.xor_lt_two_pow h3 (h' 4)
  have h5 : g 0 ^^^ g 1 ^^^ g 2 ^^^ g 3 ^^^ g 4 ^^^ g 5 < 2 ^ 8 :=
    Nat.xor_lt_two_pow h4 (h' 5)
  have h6 : g 0 ^^^ g 1 ^^^ g 2 ^^^ g 3 ^^^ g 4 ^^^ g 5 ^^^ g 6 < 2 ^ 8 :=
    Nat.xor_lt_two_pow h5 (h' 6)
  have h7 := Nat.xor_lt_two_pow h6 (h' 7)
  rwa [show (2 : ℕ) ^ 8 = 256 from by norm_num] at h7

theorem s8d_ap_lt {m : M8} (hm : ∀ k : Fin 8, s8dCol m k < 256) (n : ℕ) : m.ap n < 256 := by
  unfold M8.ap
  refine s8d_xor8_lt (fun k : Fin 8 => if n.testBit k then s8dCol m k else 0) ?_
  intro k
  split_ifs with hk
  · exact hm k
  · norm_num

theorem s8d_cmul_lt {n : ℕ} (hn : n < 256) : cmul n < 256 := by
  revert n
  decide +kernel

theorem s8d_cM_ap {n : ℕ} (hn : n < 256) : cM.ap n = cmul n := by
  revert n
  decide +kernel

private theorem s8dDec_cM_bas :
    ∀ k : Fin 8, s8dAp (s8dDiag (finRotate 5)) (s8dBas k) = s8dDec (s8dCol cM k) := by
  decide +kernel

theorem s8dDec_cM (n : ℕ) : s8dAp (s8dDiag (finRotate 5)) (s8dDec n) = s8dDec (cM.ap n) :=
  s8dDec_ap (f := fun p => s8dAp (s8dDiag (finRotate 5)) p)
    (fun p q => s8dAp_add _ p q) s8dDec_cM_bas n

private theorem s8dDec_rV_bas :
    ∀ k : Fin 8, s8dAp (s8dDiag altFiveVPerm) (s8dBas k) = s8dDec (s8dCol rV k) := by
  decide +kernel

theorem s8dDec_rV (n : ℕ) : s8dAp (s8dDiag altFiveVPerm) (s8dDec n) = s8dDec (rV.ap n) :=
  s8dDec_ap (f := fun p => s8dAp (s8dDiag altFiveVPerm) p)
    (fun p q => s8dAp_add _ p q) s8dDec_rV_bas n

private theorem s8dAp_inv_add (f : S8A) (p q : EvW × EvW) :
    s8dAp f⁻¹ (p + q) = s8dAp f⁻¹ p + s8dAp f⁻¹ q := by
  have h1 : s8dAp f (s8dAp f⁻¹ p + s8dAp f⁻¹ q) = p + q := by
    rw [s8dAp_add, s8dAp_ap_inv, s8dAp_ap_inv]
  calc s8dAp f⁻¹ (p + q) = s8dAp f⁻¹ (s8dAp f (s8dAp f⁻¹ p + s8dAp f⁻¹ q)) := by
        rw [h1]
    _ = s8dAp f⁻¹ p + s8dAp f⁻¹ q := s8dAp_inv_ap f _

private theorem s8dDec_rVi_bas :
    ∀ k : Fin 8, s8dAp (s8dDiag altFiveVPerm)⁻¹ (s8dBas k) = s8dDec (s8dCol rVi k) := by
  rw [← map_inv s8dDiag altFiveVPerm]
  decide +kernel

theorem s8dDec_rVi (n : ℕ) : s8dAp (s8dDiag altFiveVPerm)⁻¹ (s8dDec n) = s8dDec (rVi.ap n) :=
  s8dDec_ap (f := fun p => s8dAp (s8dDiag altFiveVPerm)⁻¹ p)
    (fun p q => s8dAp_inv_add _ p q) s8dDec_rVi_bas n

theorem s8dDec_iter {f : S8A} {m : M8} (hf : ∀ n, s8dAp f (s8dDec n) = s8dDec (m.ap n))
    (k n : ℕ) : s8dAp (f ^ k) (s8dDec n) = s8dDec (m.iter k n) := by
  induction k with
  | zero => rw [pow_zero, s8dAp_one]; rfl
  | succ k ih =>
      rw [pow_succ', s8dAp_mul, ih, hf]
      rfl

end CFSG.OddStandard.SmallF3.Omega
