module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

@[expose] def preGL (W : Subgroup (projectiveSL 4 F)) : Subgroup (GL (Fin 4) F) :=
  (W.comap (proj 4 F)).map SpecialLinearGroup.toGL

@[expose] def IsPElt (p : ℕ) (W : Subgroup (projectiveSL 4 F)) (x : GL (Fin 4) F) : Prop :=
  x ∈ preGL W ∧ ∃ n : ℕ, x ^ p ^ n = 1

@[expose] def fixSp (p : ℕ) (W : Subgroup (projectiveSL 4 F)) : Submodule F (Fin 4 → F) where
  carrier := {v | ∀ x, IsPElt p W x → (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v = v}
  zero_mem' := fun x _ => mulVec_zero _
  add_mem' := fun ha hb x hx => by rw [mulVec_add, ha x hx, hb x hx]
  smul_mem' := fun c v hv x hx => by rw [mulVec_smul, hv x hx]

@[expose] def comSp (p : ℕ) (W : Subgroup (projectiveSL 4 F)) : Submodule F (Fin 4 → F) :=
  Submodule.span F {w | ∃ x v, IsPElt p W x ∧ w = (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v - v}

variable {p : ℕ} {W : Subgroup (projectiveSL 4 F)}

theorem isPElt_conj {A : GL (Fin 4) F}
    (hA : A ∈ normalizer ((preGL W : Subgroup (GL (Fin 4) F)) : Set _))
    {x : GL (Fin 4) F} (hx : IsPElt p W x) : IsPElt p W (A * x * A⁻¹) := by
  obtain ⟨hxW, n, hn⟩ := hx
  exact ⟨(Subgroup.mem_normalizer_iff.mp hA x).mp hxW, n, by rw [conj_pow, hn]; group⟩

theorem mulVec_mem_fixSp {A : GL (Fin 4) F}
    (hA : A ∈ normalizer ((preGL W : Subgroup (GL (Fin 4) F)) : Set _))
    {v : Fin 4 → F} (hv : v ∈ fixSp p W) :
    (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ fixSp p W := by
  intro x hx
  have h1 := hv _ (isPElt_conj (inv_mem hA) hx)
  rw [inv_inv] at h1
  have e : (x : Matrix (Fin 4) (Fin 4) F) * (A : Matrix _ _ F) =
      (A : Matrix _ _ F) * ((A⁻¹ * x * A : GL (Fin 4) F) : Matrix _ _ F) := by
    rw [← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [mulVec_mulVec, e, ← mulVec_mulVec, h1]

theorem mulVec_mem_comSp {A : GL (Fin 4) F}
    (hA : A ∈ normalizer ((preGL W : Subgroup (GL (Fin 4) F)) : Set _))
    {v : Fin 4 → F} (hv : v ∈ comSp p W) :
    (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ comSp p W := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, u, hx, rfl⟩ := hw
    refine Submodule.subset_span ⟨A * x * A⁻¹, (A : Matrix _ _ F) *ᵥ u, isPElt_conj hA hx, ?_⟩
    rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel_right]
  | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ c ha

theorem dot_fixSp_comSp {A : GL (Fin 4) F}
    (hA : ∀ x, IsPElt p W x → ∃ y, IsPElt p W y ∧ (y : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) * ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    {c d : Fin 4 → F} (hc : c ∈ fixSp p W) (hd : d ∈ comSp p W) :
    (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ c) ⬝ᵥ d = 0 := by
  induction hd using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, v, hx, rfl⟩ := hw
    obtain ⟨y, hy, hye⟩ := hA x hx
    have h1 := hc y hy
    rw [hye] at h1
    set w := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ c with hw
    have hAA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *ᵥ w = w := by
      have := congrArg (fun u => ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ u) h1
      simp only [mulVec_mulVec, ← Matrix.mul_assoc, hAA, Matrix.one_mul] at this
      rw [hw, mulVec_mulVec]
      exact this
    have hxx : (x : Matrix (Fin 4) (Fin 4) F)ᵀ *
        ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]
    have h3 : (x : Matrix (Fin 4) (Fin 4) F)ᵀ *ᵥ w = w := by
      conv_lhs => rw [← h2, mulVec_mulVec, hxx, one_mulVec]
    rw [dotProduct_sub, dotProduct_mulVec, ← mulVec_transpose, h3, sub_self]
  | zero => exact dotProduct_zero _
  | add a b _ _ ha hb => rw [dotProduct_add, ha, hb, add_zero]
  | smul r a _ ha => rw [dotProduct_smul, ha, smul_zero]

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
