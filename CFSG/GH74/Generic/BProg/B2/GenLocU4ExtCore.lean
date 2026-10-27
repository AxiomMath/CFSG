module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBlock
public import CFSG.GH74.Generic.BProg.B2.GenLocU3Blk
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame
public import CFSG.GH74.Generic.BProg.B2.GenLocU4SuCore

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel

namespace GenLocU4ExtCore

variable {K : Type} [Field K]

theorem five_le_of_mod_four {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) : 5 ≤ p ^ f := by
  have hne : p ^ f ≠ 1 := by
    intro h1
    rw [h1] at hK
    have : Nat.card K = 1 := by simpa using hK
    exact (not_subsingleton K) (Nat.card_eq_one_iff_unique.1 this).1
  omega

theorem mem_primeFormUnitary_of {p f : ℕ} (h : UnitaryFieldData p f K) {n : ℕ} {x : GL (Fin n) K}
    (hx : ((x : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin n) (Fin n) K) = 1) :
    x ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  rw [GenLocU4ExtFrame.map_bar_eq h]; exact hx

theorem unitary_of_mem {p f : ℕ} (h : UnitaryFieldData p f K) {n : ℕ} {x : GL (Fin n) K}
    (hx : x ∈ primeFormUnitary h (idGram K n)) :
    ((x : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin n) (Fin n) K) = 1 := by
  have := (mem_primeFormUnitary (h := h)).1 hx
  simp only [idGram, Units.val_one, Matrix.mul_one] at this
  rw [GenLocU4ExtFrame.map_bar_eq h] at this
  exact this

theorem cent_transport (P : GL (Fin 4) K) (u g z : GL (Fin 4) K) (hz : z = P * u * P⁻¹)
    (hug : u * g = g * u) : P * g * P⁻¹ * z = z * (P * g * P⁻¹) := by
  rw [hz]
  calc P * g * P⁻¹ * (P * u * P⁻¹) = P * (g * u) * P⁻¹ := by group
    _ = P * (u * g) * P⁻¹ := by rw [hug]
    _ = P * u * P⁻¹ * (P * g * P⁻¹) := by group

theorem conj_facts {p f : ℕ} (h : UnitaryFieldData p f K) (P x y : GL (Fin 4) K)
    (hPU : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1)
    (hy2 : (y * y : GL (Fin 4) K) = -1) (hxy : x * y = y * x)
    (hxP : (x : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![-1, -1, 1, 1]) :
    (((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
        ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 ∧
      ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![-1, -1, 1, 1] =
        Matrix.diagonal ![-1, -1, 1, 1] * ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have hPm := mem_primeFormUnitary_of h hPU
  have hym := mem_primeFormUnitary_of h hyU
  refine ⟨unitary_of_mem h (mul_mem (mul_mem (inv_mem hPm) hym) hPm), ?_, ?_⟩
  · rw [← Units.val_mul, show (P⁻¹ * y * P) * (P⁻¹ * y * P) = P⁻¹ * (y * y) * P by group, hy2]
    simp only [Units.val_mul, Units.val_neg, Units.val_one]
    rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Units.inv_mul]
  · have hPi : ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 :=
      Units.inv_mul P
    have hDm : Matrix.diagonal ![-1, -1, 1, 1] =
        ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
          (P : Matrix (Fin 4) (Fin 4) K) := by
      rw [Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, hPi, Matrix.one_mul]
    have hxy' : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
        (y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) := by
      simpa [Units.val_mul] using congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hxy
    simp only [Units.val_mul]
    calc ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) *
          (P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![-1, -1, 1, 1]
        = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) *
            ((P : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![-1, -1, 1, 1]) := by
          rw [Matrix.mul_assoc _ (P : Matrix (Fin 4) (Fin 4) K)]
      _ = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((y : Matrix (Fin 4) (Fin 4) K) *
            (x : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) := by
          rw [← hxP]; simp only [Matrix.mul_assoc]
      _ = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) *
            (y : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) := by rw [hxy']
      _ = Matrix.diagonal ![-1, -1, 1, 1] * (((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (y : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K)) := by
          rw [hDm]
          have hPP : (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
            Units.mul_inv P
          calc ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((x : Matrix (Fin 4) (Fin 4) K) *
                (y : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K)
              = ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) *
                  ((P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
                    (y : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) := by
                rw [hPP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]


theorem eq_top_of_centralizers_ext_aux {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (x y : GL (Fin 4) K)
    (hx2 : x * x = 1) (hy2 : (y * y : GL (Fin 4) K) = -1) (hxy : x * y = y * x)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx : (x : Matrix (Fin 4) (Fin 4) K).trace = 0)
    (hX : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * x = x * g → g ∈ Γ)
    (hY : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * y = y * g → g ∈ Γ)
    (hXY : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * (x * y) = (x * y) * g → g ∈ Γ) :
    Γ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  obtain ⟨P, hPU, hxP⟩ := GenLocU4ExtFrame.exists_frame hp hp2 hK x hxU hx2 hx
  have hPm := mem_primeFormUnitary_of h hPU
  obtain ⟨hU', hsq', hD'⟩ := conj_facts h P x y hPU hyU hy2 hxy hxP
  obtain ⟨A, A', hA, hA', hphi⟩ := GenLocU4ExtBlock.exists_phiU hq h2
    ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) hU' hsq' hD'
  have hcore := GenLocU4Su.su4_core hK hp2 (five_le_of_mod_four hK hq) A A' hA hA'
  let Φ : Su K p f 4 ≃* ↥(StatedSU 4 (p ^ f) K) :=
    (GenLocU3Blk.suEquiv h 4).trans (KFU.conjSU h ⟨P, hPm⟩)
  have hΦ : ∀ g : Su K p f 4, ((Φ g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) =
      P * (g : GL (Fin 4) K) * P⁻¹ := fun g => rfl
  have hPi : ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.inv_mul P
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    Units.mul_inv P
  have hxeq : x = P * ((GenLocU4Su.xU K p f : Su K p f 4) : GL (Fin 4) K) * P⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul]
    change _ = _ * suMat (GenLocU4Su.xU K p f) * _
    rw [GenLocU4ExtBlock.suMat_xU, ← hxP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hyeq : y = P * ((GenLocU4Su.phiU K p f (A, A') : Su K p f 4) : GL (Fin 4) K) * P⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul]
    change _ = _ * suMat (GenLocU4Su.phiU K p f (A, A')) * _
    rw [hphi]
    simp only [Units.val_mul]
    calc (y : Matrix (Fin 4) (Fin 4) K) = ((P : Matrix (Fin 4) (Fin 4) K) *
          ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * (y : Matrix (Fin 4) (Fin 4) K) *
          ((P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
          rw [hPP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hxyeq : x * y = P * (((GenLocU4Su.xU K p f *
      GenLocU4Su.phiU K p f (A, A') : Su K p f 4)) : GL (Fin 4) K) * P⁻¹ := by
    rw [Subgroup.coe_mul, hxeq, hyeq]
    group
  have hcomap : Γ.comap Φ.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← hcore]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      refine hX (Φ g) ?_
      rw [hΦ]
      exact cent_transport P _ _ x hxeq (congrArg Subtype.val hg.symm)
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      refine hY (Φ g) ?_
      rw [hΦ]
      exact cent_transport P _ _ y hyeq (congrArg Subtype.val hg.symm)
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      refine hXY (Φ g) ?_
      rw [hΦ]
      exact cent_transport P _ _ (x * y) hxyeq (congrArg Subtype.val hg.symm)
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨g, rfl⟩ := Φ.surjective z
  exact Subgroup.mem_comap.1 (hcomap ▸ Subgroup.mem_top g)

end GenLocU4ExtCore
end CFSG.GH74.Generic.BProg.B2
