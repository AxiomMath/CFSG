module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2Core
public import CFSG.GH74.Generic.BProg.B2.GenLocU4QAsm

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Assembly.LowTwoRank Subgroup Matrix CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open GenLocU4Basic GenLocU4Out GenLocU4Eich

namespace GenLocU4Q2

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem su4Q2Stmt_holds : GenLocU4Q.Su4Q2Stmt K p f := by
  intro hp hp2 hK hq Γ x y hx2 hy2 hxy hxU hyU hxΓ hyΓ
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_sq hK
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hxx : (x : Matrix (Fin 4) (Fin 4) K) * x = -1 := by
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hx2
    simpa using this
  have hyy : (y : Matrix (Fin 4) (Fin 4) K) * y = -1 := by
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hy2
    simpa using this
  obtain ⟨U, hU, hxU', hyU'⟩ := exists_q2_frame hp hp2 hK hq hxU hyU hxx hyy hxy
  have hU' : ((U : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * U = 1 := hU
  let UG : GL (Fin 4) K := ⟨U, (U.map (· ^ (p ^ f)))ᵀ, mul_eq_one_comm.1 hU', hU'⟩
  have hUG : (UG : Matrix (Fin 4) (Fin 4) K) = U := rfl
  have hUGi : ((UG⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (U.map (· ^ (p ^ f)))ᵀ := rfl
  let P : ↥(primeFormUnitary h (idGram K 4)) := ⟨UG, GenLocU4Gen.mem_primeFormUnitary_of_raw h hU'⟩
  let φ : MulAut ↥(StatedSU 4 (p ^ f) K) := GenLocDiagU.conjSUHom h 4 P
  have hφ : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM (φ g) = U * gM g * (U.map (· ^ (p ^ f)))ᵀ := fun g => rfl
  have hUUs : U * (U.map (· ^ (p ^ f)))ᵀ = 1 := mul_eq_one_comm.1 hU'
  have hxe : (x : Matrix (Fin 4) (Fin 4) K) = U * xi * (U.map (· ^ (p ^ f)))ᵀ := by
    calc (x : Matrix (Fin 4) (Fin 4) K) = x * (U * (U.map (· ^ (p ^ f)))ᵀ) := by rw [hUUs, Matrix.mul_one]
      _ = (x * U) * (U.map (· ^ (p ^ f)))ᵀ := by rw [Matrix.mul_assoc]
      _ = U * xi * (U.map (· ^ (p ^ f)))ᵀ := by rw [hxU']
  have hye : (y : Matrix (Fin 4) (Fin 4) K) = U * q2Y * (U.map (· ^ (p ^ f)))ᵀ := by
    calc (y : Matrix (Fin 4) (Fin 4) K) = y * (U * (U.map (· ^ (p ^ f)))ᵀ) := by rw [hUUs, Matrix.mul_one]
      _ = (y * U) * (U.map (· ^ (p ^ f)))ᵀ := by rw [Matrix.mul_assoc]
      _ = U * q2Y * (U.map (· ^ (p ^ f)))ᵀ := by rw [hyU']
  let Γ' : Subgroup ↥(StatedSU 4 (p ^ f) K) := Γ.comap φ.toMonoidHom
  have hx' : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM g * xi = xi * gM g → g ∈ Γ' := by
    intro g hg
    show φ g ∈ Γ
    apply hxΓ
    apply Units.ext
    show gM (φ g) * (x : Matrix (Fin 4) (Fin 4) K) = (x : Matrix (Fin 4) (Fin 4) K) * gM (φ g)
    rw [hφ, hxe]
    calc U * gM g * (U.map (· ^ (p ^ f)))ᵀ * (U * xi * (U.map (· ^ (p ^ f)))ᵀ)
        = U * (gM g * ((U.map (· ^ (p ^ f)))ᵀ * U) * xi) * (U.map (· ^ (p ^ f)))ᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (xi * ((U.map (· ^ (p ^ f)))ᵀ * U) * gM g) * (U.map (· ^ (p ^ f)))ᵀ := by
          rw [hU', Matrix.mul_one, Matrix.mul_one, hg]
      _ = U * xi * (U.map (· ^ (p ^ f)))ᵀ * (U * gM g * (U.map (· ^ (p ^ f)))ᵀ) := by simp only [Matrix.mul_assoc]
  have hy' : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM g * q2Y = q2Y * gM g → g ∈ Γ' := by
    intro g hg
    show φ g ∈ Γ
    apply hyΓ
    apply Units.ext
    show gM (φ g) * (y : Matrix (Fin 4) (Fin 4) K) = (y : Matrix (Fin 4) (Fin 4) K) * gM (φ g)
    rw [hφ, hye]
    calc U * gM g * (U.map (· ^ (p ^ f)))ᵀ * (U * q2Y * (U.map (· ^ (p ^ f)))ᵀ)
        = U * (gM g * ((U.map (· ^ (p ^ f)))ᵀ * U) * q2Y) * (U.map (· ^ (p ^ f)))ᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (q2Y * ((U.map (· ^ (p ^ f)))ᵀ * U) * gM g) * (U.map (· ^ (p ^ f)))ᵀ := by
          rw [hU', Matrix.mul_one, Matrix.mul_one, hg]
      _ = U * q2Y * (U.map (· ^ (p ^ f)))ᵀ * (U * gM g * (U.map (· ^ (p ^ f)))ᵀ) := by simp only [Matrix.mul_assoc]
  have htop : Γ' = ⊤ := q2_core hp hp2 hK hq Γ' hx' hy'
  rw [eq_top_iff]
  intro g _
  obtain ⟨g₀, rfl⟩ := φ.surjective g
  have hg₀ : g₀ ∈ Γ' := by rw [htop]; trivial
  exact hg₀

end GenLocU4Q2

end CFSG.GH74.Generic.BProg.B2
