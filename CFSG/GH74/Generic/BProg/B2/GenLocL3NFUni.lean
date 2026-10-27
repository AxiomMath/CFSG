module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NFAux
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial Matrix

namespace GenLocL3NFUni

open GenLocL3NFAux

variable {K : Type} [Field K] [Finite K]

theorem good_of_graph_field_data {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hfe : Even f) (hK2 : ringChar K ≠ 2) {φ : K ≃+* K} (hφφ : φ * φ = 1)
    (hφpow : ∀ x, φ x = x ^ p ^ (f / 2))
    {D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hτD : LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K ∈ D)
    (hshape : ∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K)) :
    ∃ C : GL (Fin 3) K, ∀ x ∈ D, OkC C x := by
  classical
  set e := f / 2 with he
  have hfe2 : f = 2 * e := by obtain ⟨k, hk⟩ := hfe; omega
  have hU : UnitaryFieldData p e K := ⟨hp, by omega, by rw [hK, hfe2]⟩
  have hbar : ∀ x, hU.bar x = φ x := fun x => by rw [UnitaryFieldData.bar_apply, hφpow]
  have hfun : (⇑hU.bar : K → K) = ⇑φ := funext hbar
  have hpq : 2 ∣ p ^ e + 1 := by
    have : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    exact even_iff_two_dvd.1 this.add_one
  obtain ⟨hcomm, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  obtain ⟨E, ρ, hρsq, hρc, hρD, hρin, hρcomm⟩ := exists_lift_inner hK2 hD
  have hρuni : ∀ e' : E, (((ρ e' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map hU.bar)ᵀ *
      ((ρ e' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    intro e'
    have hcm := hcomm _ (hρD e') _ hτD
    rw [← hρc e'] at hcm
    have h1 := unitary_of_comm_tau (φ := φ) (ρ e') (hρsq e') hcm
    rw [hfun, h1]
    simpa using congrArg Units.val (hρsq e')
  have hmemU : ∀ e' : E, (ρ e' : GL (Fin 3) K) ∈ UnitaryHigher.primeFormUnitary hU
      (RankThree.PartOne.KCUnitaryModel.idGram K 3) := by
    intro e'
    rw [UnitaryHigher.mem_primeFormUnitary]
    simpa [RankThree.PartOne.KCUnitaryModel.idGram] using hρuni e'
  let U := UnitaryHigher.primeFormUnitary hU (RankThree.PartOne.KCUnitaryModel.idGram K 3)
  let G : Subgroup U := ρ.range.comap U.subtype
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro x ⟨e1, he1⟩ y ⟨e2, he2⟩
    apply Subtype.ext
    show (x : GL (Fin 3) K) * y = y * x
    have h1 : ρ e1 = (x : GL (Fin 3) K) := he1
    have h2 : ρ e2 = (y : GL (Fin 3) K) := he2
    rw [← h1, ← h2]
    exact hρcomm e1 e2
  have hGpow : ∀ x ∈ G, x ^ 2 = 1 := by
    rintro x ⟨e1, he1⟩
    apply Subtype.ext
    have h1 : ρ e1 = (x : GL (Fin 3) K) := he1
    show (x : GL (Fin 3) K) ^ 2 = 1
    rw [sq, ← h1]
    exact hρsq e1
  obtain ⟨P, hP⟩ := RankThree.PartOne.KFU.exists_unitary_conj_diag hU Nat.prime_two hpq G hGcomm hGpow
  set C : GL (Fin 3) K := (P : GL (Fin 3) K) with hC
  have hCd : ∀ e' : E, ((C⁻¹ * ρ e' * C : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro e'
    have := hP ⟨ρ e', hmemU e'⟩ ⟨e', rfl⟩
    simpa using this
  have hCuni : ((C : Matrix (Fin 3) (Fin 3) K).map φ)ᵀ * (C : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h1 := (UnitaryHigher.mem_primeFormUnitary).1 P.2
    rw [hfun] at h1
    simpa [RankThree.PartOne.KCUnitaryModel.idGram] using h1
  have hτC : (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) * LinearFlag.conjAut 3 K C =
      LinearFlag.conjAut 3 K C * (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) := by
    calc _ = LinearFlag.fieldAut 3 K φ * (LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K C) := by
          rw [mul_assoc]
      _ = LinearFlag.fieldAut 3 K φ * (LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose C) *
          LinearFlag.dualAut 3 K) := by rw [LinearFlag.dualAut_mul_conjAut]
      _ = (LinearFlag.fieldAut 3 K φ * LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose C)) *
          LinearFlag.dualAut 3 K := by rw [mul_assoc]
      _ = (LinearFlag.conjAut 3 K (GeneralLinearGroup.map (φ : K →+* K)
            (GeneralLinearGroup.inverseTranspose C)) * LinearFlag.fieldAut 3 K φ) *
          LinearFlag.dualAut 3 K := by rw [LinearFlag.fieldAut_mul_conjAut]
      _ = _ := by rw [map_inverseTranspose_eq_of_unitary C hCuni, mul_assoc]
  have hτok : OkC C (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) :=
    okC_of_comm hτC (mul_mem (fieldAut_mem_frameStab φ) dualAut_mem_frameStab)
  have hok1 : ∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) → OkC C x := by
    intro x hx hxA
    obtain ⟨e', he'⟩ := hρin x hx hxA
    rw [he', ← hρc e']
    exact okC_conjAut C _ (hCd e')
  refine ⟨C, fun x hx => ?_⟩
  rcases hshape x hx with ⟨A, rfl⟩ | ⟨A, rfl⟩
  · exact hok1 _ hx ⟨A, rfl⟩
  · have hff : LinearFlag.fieldAut 3 K φ * LinearFlag.fieldAut 3 K φ = 1 := by
      rw [← map_mul, hφφ, map_one]
    have hδδ : LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K = 1 :=
      (LinearFlag.standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
    have hxτ : LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K *
        (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) = LinearFlag.conjAut 3 K A := by
      calc _ = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ *
            (LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K φ) * LinearFlag.dualAut 3 K := by
            simp only [mul_assoc]
        _ = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ *
            (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) * LinearFlag.dualAut 3 K := by
            rw [LinearFlag.dualAut_mul_fieldAut]
        _ = LinearFlag.conjAut 3 K A * (LinearFlag.fieldAut 3 K φ * LinearFlag.fieldAut 3 K φ) *
            (LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K) := by simp only [mul_assoc]
        _ = LinearFlag.conjAut 3 K A := by rw [hff, hδδ, mul_one, mul_one]
    have hxD := mul_mem hx hτD
    rw [hxτ] at hxD
    have hok := hok1 _ hxD ⟨A, rfl⟩
    have e2 : LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K =
        (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K *
          (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K)) *
          (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K)⁻¹ := by group
    rw [e2, hxτ]
    exact hok.mul hτok.inv

end GenLocL3NFUni

end CFSG.GH74.Generic.BProg.B2
