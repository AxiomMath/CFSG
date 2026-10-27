module

public import CFSG.Fischer.Polar.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClassBraidInputs
public import Certificates.Certificate3180
public import Certificates.Certificate3181
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open CFSG.Fischer CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native
open CFSG.Sporadic.Schreier

theorem braidOK_tvTabs :
    braidOK tvTabs = true :=
  Certificates.certificate3181.1

theorem tvP_apply_eq_or
    (m m' : Fin 693) : tvP m m' = m' ∨ tvP m m' = tvP m' m := by
  have h := allIn_eq_true.1 (allIn_eq_true.1 braidOK_tvTabs m.val (Nat.zero_le _) m.2) m'.val
    (Nat.zero_le _) m'.2
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rw [rep_tvP m m'.val m'.2, rep_tvP m' m.val m.2, idx_of_lt _ m'.2, idx_of_lt _ m.2] at h
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem orderOf_tvP_mul_tvP
    (m m' : Fin 693) :
    orderOf (tvP m * tvP m') ∈ ({1, 2, 3} : Set ℕ) := by
  rcases tvP_apply_eq_or m m' with h | h
  · have hc : tvP m * tvP m' = tvP m' * tvP m :=
      (tvP_comm_iff_perp m m').2 (tvP_apply_eq_self_iff.1 h)
    have h2 : (tvP m * tvP m') ^ 2 = 1 := by
      calc (tvP m * tvP m') ^ 2 = tvP m * (tvP m' * tvP m) * tvP m' := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = tvP m * tvP m * (tvP m' * tvP m') := by rw [← hc]; group
        _ = 1 := by rw [tvP_mul_self, tvP_mul_self, one_mul]
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h1 | h1 <;>
      simp [h1]
  · have hb : tvP m * tvP m' * tvP m = tvP m' * tvP m * tvP m' := by
      rw [tvP_conj, tvP_conj, h]
    have h3 : (tvP m * tvP m') ^ 3 = 1 := by
      calc (tvP m * tvP m') ^ 3 = tvP m * tvP m' * tvP m * (tvP m' * tvP m * tvP m') := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = tvP m' * tvP m * (tvP m' * tvP m') * tvP m * tvP m' := by rw [hb]; group
        _ = tvP m' * (tvP m * tvP m) * tvP m' := by rw [tvP_mul_self]; group
        _ = 1 := by rw [tvP_mul_self, mul_one, tvP_mul_self]
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h1 | h1 <;>
      simp [h1]

theorem toTable_j1 :
    toTable j1 = tvTabs[(0 : Fin 693).val]! :=
  Certificates.certificate3181.2

theorem j1_eq_tvP_zero :
    j1 = tvP 0 :=
  rep_unique (rep_toTable (by norm_num) j1) (toTable_j1 ▸ rep_tvP 0)

theorem conj_j1_eq
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) : g * j1 * g⁻¹ = tvP (g 0) := by
  rw [j1_eq_tvP_zero]
  exact (isPolarAut_of_mem hg).mul_tvP_mul_inv 0

theorem exists_conj_j1
    (m : Fin 693) :
    ∃ g ∈ T46, g * j1 * g⁻¹ = tvP m := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T46 (0 : Fin 693) m
  exact ⟨g, g.2, by rw [conj_j1_eq g.2]; exact congrArg tvP hg⟩

end CFSG.EvenSmallLie.UnitarySix.Hunt
