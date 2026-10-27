module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddMat
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.Open CFSG.LieType.BorelTits

section Elements

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem one_le_prime_pow (p f : ℕ) [Fact p.Prime] : 1 ≤ p ^ f :=
  Nat.one_le_pow _ _ (Fact.out : p.Prime).pos

omit [Fact p.Prime] [CharP F p] in
theorem pow_card_sq_eq (hF : Nat.card F = (p ^ f) ^ 2) (x : F) : x ^ ((p ^ f) ^ 2) = x := by
  have := Fintype.ofFinite F
  rw [← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] noncomputable def tSU (hF : Nat.card F = (p ^ f) ^ 2) :
    Fˣ →* SU (unitaryInvolution F p f) 3 :=
  (tGLHom (p ^ f)).codRestrict _ fun μ =>
    tGL_mem_SU (unitaryInvolution F p f) (one_le_prime_pow p f)
      (unitaryInvolution_apply F p f) (pow_card_sq_eq hF) μ

@[expose] noncomputable def sSU : SU (unitaryInvolution F p f) 3 :=
  ⟨swapGL, swapGL_mem_SU _⟩

theorem coe_tSU (hF : Nat.card F = (p ^ f) ^ 2) (μ : Fˣ) :
    ((tSU hF μ : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) = tGL (p ^ f) μ := rfl

theorem tSU_injective (hF : Nat.card F = (p ^ f) ^ 2) : Function.Injective (tSU hF) := by
  intro μ ν h
  exact tGLHom_injective (p ^ f) (congrArg Subtype.val h)

theorem sSU_mul_self : (sSU : SU (unitaryInvolution F p f) 3) * sSU = 1 :=
  Subtype.ext (Units.ext sMat_mul_self)

theorem sSU_inv : (sSU : SU (unitaryInvolution F p f) 3)⁻¹ = sSU :=
  inv_eq_of_mul_eq_one_right sSU_mul_self

theorem sSU_mul_tSU (hF : Nat.card F = (p ^ f) ^ 2) (μ : Fˣ) :
    (sSU : SU (unitaryInvolution F p f) 3) * tSU hF μ = tSU hF (μ ^ (p ^ f))⁻¹ * sSU :=
  Subtype.ext (Units.ext (sMat_mul_tMat (one_le_prime_pow p f) (pow_card_sq_eq hF) μ))

theorem sSU_conj_tSU (hF : Nat.card F = (p ^ f) ^ 2) (μ : Fˣ) :
    (sSU : SU (unitaryInvolution F p f) 3) * tSU hF μ * sSU⁻¹ = tSU hF (μ ^ (p ^ f))⁻¹ := by
  rw [sSU_mul_tSU, mul_assoc, mul_inv_cancel, mul_one]

theorem sSU_not_mem_range (hF : Nat.card F = (p ^ f) ^ 2) :
    (sSU : SU (unitaryInvolution F p f) 3) ∉ (tSU hF).range := by
  rintro ⟨μ, hμ⟩
  have := congrArg (fun g : SU (unitaryInvolution F p f) 3 =>
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) hμ
  simp [coe_tSU, coe_tGL, tMat, sSU, swapGL, sMat] at this

theorem card_range_tSU (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card (tSU hF).range = (p ^ f) ^ 2 - 1 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (tSU_injective hF)).toEquiv, Nat.card_units, hF]

end Elements

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
