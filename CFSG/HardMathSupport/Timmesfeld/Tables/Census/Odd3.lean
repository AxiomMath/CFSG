module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Matrix CFSG.Open CFSG.SectionRank.ClassicalEven CFSG.QuasithinUnique.Vol2Native.EvenWit

variable {K : Type} [Field K]

theorem cycGL_conj_torusDiag (d : Fin 3 → Kˣ) :
    cycGL K * torusDiag d * (cycGL K)⁻¹ = torusDiag ![d 2, d 0, d 1] := by
  refine Units.ext ?_
  show cycMat K * (torusDiag d : Matrix (Fin 3) (Fin 3) K) * (cycMat K)ᵀ =
    (torusDiag ![d 2, d 0, d 1] : Matrix (Fin 3) (Fin 3) K)
  rw [coe_torusDiag, coe_torusDiag]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal, cycMat, Fin.sum_univ_three]

theorem cycGL_pow_three (K : Type) [Field K] : (cycGL K) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  show cycMat K ^ 3 = 1
  rw [pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycGL_ne_scalar {c : Kˣ} : cycGL K ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  intro h
  have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 0) h
  simp [coe_cycGL, cycMat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1

theorem threeTwoWitness_statedProj_klein_cyc [Finite K] (hK : (-1 : K) ≠ 1)
    {H : Subgroup (GL (Fin 3) K)}
    (h1 : torusDiag ![1, -1, -1] ∈ H) (h2 : torusDiag ![-1, 1, -1] ∈ H) (hc : cycGL K ∈ H) :
    ThreeTwoWitness (StatedProj H) := by
  let N : Subgroup H := (StatedScalars (Fin 3) K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  let u1 : Fin 3 → Kˣ := ![1, -1, -1]
  let u2 : Fin 3 → Kˣ := ![-1, 1, -1]
  let a : H := ⟨torusDiag u1, h1⟩
  let b : H := ⟨torusDiag u2, h2⟩
  let c : H := ⟨cycGL K, hc⟩
  have hK' : (-1 : Kˣ) ≠ 1 := fun h => hK (by simpa using congrArg (fun u : Kˣ => (u : K)) h)
  have hmem : ∀ g : H, π g = 1 →
      ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) u = (g : GL (Fin 3) K) := by
    intro g hg
    have := (QuotientGroup.eq_one_iff g).1 hg
    exact this
  have haa : a * a = 1 := by
    refine Subtype.ext ?_
    show torusDiag u1 * torusDiag u1 = 1
    rw [← map_mul, ← map_one (torusDiag (ι := Fin 3) (K := K))]
    congr 1
    funext i
    fin_cases i <;> simp [u1]
  have hbb : b * b = 1 := by
    refine Subtype.ext ?_
    show torusDiag u2 * torusDiag u2 = 1
    rw [← map_mul, ← map_one (torusDiag (ι := Fin 3) (K := K))]
    congr 1
    funext i
    fin_cases i <;> simp [u2]
  have hab : a * b = b * a := Subtype.ext ((Commute.all u1 u2).map torusDiag).eq
  have hc3 : c ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact cycGL_pow_three K)
  have hca : c * a * c⁻¹ = b := by
    refine Subtype.ext ?_
    show cycGL K * torusDiag u1 * (cycGL K)⁻¹ = torusDiag u2
    rw [cycGL_conj_torusDiag]
    congr 1
  have hcb : c * b * c⁻¹ = a * b := by
    refine Subtype.ext ?_
    show cycGL K * torusDiag u2 * (cycGL K)⁻¹ = torusDiag u1 * torusDiag u2
    rw [cycGL_conj_torusDiag, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [u1, u2]
  refine ThreeTwoWitness.of_klein (π a) (π b) (π c) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, haa, map_one]
  · rw [← map_mul, hbb, map_one]
  · rw [← map_mul, ← map_mul, hab]
  · intro h
    obtain ⟨u, hu⟩ := hmem a h
    have h3 : torusDiag (fun _ => u) = torusDiag u1 := by
      rw [← scalar_eq_torusDiag]
      exact hu
    have h4 := torusDiag_injective h3
    have e0 := congrFun h4 0
    have e1 := congrFun h4 1
    simp only [u1] at e0 e1
    exact hK' (by simpa using e1.symm.trans e0)
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hc3, map_one]
    · intro h
      obtain ⟨u, hu⟩ := hmem c h
      exact cycGL_ne_scalar (c := u) hu.symm
  · rw [← map_inv, ← map_mul, ← map_mul, hca]
  · rw [← map_inv, ← map_mul, ← map_mul, hcb, map_mul]

theorem threeTwoWitness_psl_three_odd [Finite K] (hK : (-1 : K) ≠ 1) :
    ThreeTwoWitness (StatedProj (StatedSL 3 K)) :=
  threeTwoWitness_statedProj_klein_cyc hK
    (torusDiag_mem_SL (by simp [Fin.prod_univ_three]))
    (torusDiag_mem_SL (by simp [Fin.prod_univ_three])) (cycGL_mem_SL K)

theorem threeTwoWitness_psu_three_odd [Finite K] {q : ℕ} (hq : q ≠ 0) (hqo : Odd q)
    (hK : (-1 : K) ≠ 1) : ThreeTwoWitness (StatedProj (StatedSU 3 q K)) := by
  have hev : Even (q + 1) := hqo.add_one
  refine threeTwoWitness_statedProj_klein_cyc hK
    (torusDiag_mem_SU hq (by simp [Fin.prod_univ_three]) ?_)
    (torusDiag_mem_SU hq (by simp [Fin.prod_univ_three]) ?_) (cycGL_mem_SU K hq)
  · funext i
    fin_cases i <;> simp [hev.neg_one_pow]
  · funext i
    fin_cases i <;> simp [hev.neg_one_pow]

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
