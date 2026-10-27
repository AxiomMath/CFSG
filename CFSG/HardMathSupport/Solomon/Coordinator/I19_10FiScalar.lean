module

public import CFSG.RankThree.Native.Fi22FiveCentralizers
public import Certificates.Certificate13522

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] noncomputable def fi22ScalarPerm : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22FiveCGenArrs 3)[1]! * permOfArr 3510 (fi22FiveCGenArrs 3)[2]! *
    (permOfArr 3510 (fi22FiveCGenArrs 4)[1]! * permOfArr 3510 (fi22FiveCGenArrs 4)[2]!)

theorem rep_cgen_nat {i k : ℕ} (hi : i < 6) (hk : k < 4) :
    Rep 3510 (fi22FiveCGenArrs i)[k]! (permOfArr 3510 (fi22FiveCGenArrs i)[k]!) :=
  rep_cgen ⟨i, hi⟩ hk

theorem cgen_mem_P_nat
    {i k : ℕ} (hi : i < 6) (hk1 : 1 ≤ k) (hk : k < 3) :
    permOfArr 3510 (fi22FiveCGenArrs i)[k]! ∈ fi22P :=
  cgen_mem_P ⟨i, hi⟩ hk1 hk

theorem rep_fi22ScalarArr :
    Rep 3510 fi22ScalarArr fi22ScalarPerm := by
  rw [fi22ScalarArr, fi22ScalarPerm]
  exact rep_compA (rep_compA (rep_cgen_nat (i := 3) (k := 1) (by norm_num) (by norm_num))
      (rep_cgen_nat (i := 3) (k := 2) (by norm_num) (by norm_num)))
    (rep_compA (rep_cgen_nat (i := 4) (k := 1) (by norm_num) (by norm_num))
      (rep_cgen_nat (i := 4) (k := 2) (by norm_num) (by norm_num)))

theorem fi22ScalarPerm_mem_P :
    fi22ScalarPerm ∈ fi22P :=
  mul_mem (mul_mem (cgen_mem_P_nat (i := 3) (k := 1) (by norm_num) le_rfl (by norm_num))
      (cgen_mem_P_nat (i := 3) (k := 2) (by norm_num) (by norm_num) (by norm_num)))
    (mul_mem (cgen_mem_P_nat (i := 4) (k := 1) (by norm_num) le_rfl (by norm_num))
      (cgen_mem_P_nat (i := 4) (k := 2) (by norm_num) (by norm_num) (by norm_num)))

theorem fi22FiveQGenArrs_zero : fi22FiveQGenArrs[0]! = fi22FiveQ1Arr := by
  simp [fi22FiveQGenArrs]

theorem fi22FiveQGenArrs_one : fi22FiveQGenArrs[1]! = fi22FiveQ2Arr := by
  simp [fi22FiveQGenArrs]

theorem fi22FiveQGenArrs_size : fi22FiveQGenArrs.size = 2 := by
  simp [fi22FiveQGenArrs]

theorem fi22ScalarPerm_conj_gen
    {x : Equiv.Perm (Fin 3510)} (hx : x ∈ permsA 3510 fi22FiveQGenArrs) :
    fi22ScalarPerm * x * fi22ScalarPerm⁻¹ = x ^ 2 := by
  obtain ⟨k, hk, hkx⟩ := hx
  have hx' : permOfArr 3510 fi22FiveQGenArrs[k]! = x := hkx
  subst hx'
  have hk2 : k < 2 := fi22FiveQGenArrs_size ▸ hk
  have hq := rep_qgen hk
  have hc := Certificates.certificate13522
  simp only [fi22ScalarCheck, Bool.and_eq_true] at hc
  have key : fi22ScalarPerm * permOfArr 3510 fi22FiveQGenArrs[k]! =
      permOfArr 3510 fi22FiveQGenArrs[k]! ^ 2 * fi22ScalarPerm := by
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · rw [fi22FiveQGenArrs_zero] at hq ⊢
      exact (eqA_iff (rep_compA rep_fi22ScalarArr hq)
        (rep_compA (rep_powA hq 2) rep_fi22ScalarArr)).1 hc.1
    · rw [fi22FiveQGenArrs_one] at hq ⊢
      exact (eqA_iff (rep_compA rep_fi22ScalarArr hq)
        (rep_compA (rep_powA hq 2) rep_fi22ScalarArr)).1 hc.2
  rw [key, mul_inv_cancel_right]

theorem fi22FiveQ_comm {a b : Equiv.Perm (Fin 3510)}
    (ha : a ∈ fi22FiveQ) (hb : b ∈ fi22FiveQ) : a * b = b * a :=
  congrArg Subtype.val (fi22FiveQ_isElementaryAbelian.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem fi22ScalarPerm_conj
    {q : Equiv.Perm (Fin 3510)} (hq : q ∈ fi22FiveQ) :
    fi22ScalarPerm * q * fi22ScalarPerm⁻¹ = q ^ 2 := by
  have key : q ∈ fi22FiveQ ∧ fi22ScalarPerm * q * fi22ScalarPerm⁻¹ = q ^ 2 := by
    rw [fi22FiveQ] at hq
    induction hq using Subgroup.closure_induction with
    | mem x hx => exact ⟨Subgroup.subset_closure hx, fi22ScalarPerm_conj_gen hx⟩
    | one => exact ⟨one_mem _, by simp⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨mul_mem ihx.1 ihy.1, ?_⟩
      calc fi22ScalarPerm * (x * y) * fi22ScalarPerm⁻¹
          = (fi22ScalarPerm * x * fi22ScalarPerm⁻¹) * (fi22ScalarPerm * y * fi22ScalarPerm⁻¹) := by
            group
        _ = x ^ 2 * y ^ 2 := by rw [ihx.2, ihy.2]
        _ = (x * y) ^ 2 := (Commute.mul_pow (fi22FiveQ_comm ihx.1 ihy.1) 2).symm
    | inv x _ ih =>
      refine ⟨inv_mem ih.1, ?_⟩
      calc fi22ScalarPerm * x⁻¹ * fi22ScalarPerm⁻¹ = (fi22ScalarPerm * x * fi22ScalarPerm⁻¹)⁻¹ := by
            group
        _ = x⁻¹ ^ 2 := by rw [ih.2, inv_pow]
  exact key.2

theorem fi22P_sylow_five_scalar :
    ∃ S : Sylow 5 fi22P,
      (∀ a ∈ (S : Subgroup fi22P), ∀ b ∈ (S : Subgroup fi22P), a * b = b * a) ∧
      (∀ a ∈ (S : Subgroup fi22P), a ^ 5 = 1) ∧
      ∃ g : fi22P, ∀ s ∈ (S : Subgroup fi22P), g * s * g⁻¹ = s ^ 2 := by
  obtain ⟨S, hS⟩ := fi22FiveQ_sylow
  have hmem : ∀ s : fi22P, s ∈ (S : Subgroup fi22P) → (s : Equiv.Perm (Fin 3510)) ∈ fi22FiveQ :=
    fun s hs => by
      rw [hS, Subgroup.mem_subgroupOf] at hs
      exact hs
  refine ⟨S, fun a ha b hb => Subtype.ext (fi22FiveQ_comm (hmem a ha) (hmem b hb)),
    fun a ha => Subtype.ext ?_, ⟨fi22ScalarPerm, fi22ScalarPerm_mem_P⟩, fun s hs => Subtype.ext ?_⟩
  · rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := fi22FiveQ) _ (hmem a ha)
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact fi22ScalarPerm_conj (hmem s hs)

end CFSG.HardMathSupport.Solomon.Coordinator
