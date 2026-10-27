module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TL4MF163Mat
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG CFSG.ClassicalInvolution

theorem congr_conjNormal_of_mem {X P : Type} [Group X] [Group P] {N : Subgroup X} [N.Normal]
    (E : ↥N ≃* P) {n : X} (hn : n ∈ N) :
    MulAut.congr E (MulAut.conjNormal n) = MulAut.conj (E ⟨n, hn⟩) := by
  ext y
  obtain ⟨m, rfl⟩ := E.surjective y
  change E (MulAut.conjNormal n (E.symm (E m))) = E ⟨n, hn⟩ * E m * (E ⟨n, hn⟩)⁻¹
  rw [MulEquiv.symm_apply_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem congr_conjNormal_fix {X P : Type} [Group X] [Group P] {N : Subgroup X} [N.Normal]
    (E : ↥N ≃* P) {x n : X} (hn : n ∈ N) (hxn : x * n = n * x) :
    MulAut.congr E (MulAut.conjNormal x) (E ⟨n, hn⟩) = E ⟨n, hn⟩ := by
  change E (MulAut.conjNormal x (E.symm (E ⟨n, hn⟩))) = E ⟨n, hn⟩
  rw [MulEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, hxn, mul_inv_cancel_right]

theorem fix_of_comm_conj {P : Type} [Group P] (hZ : ∀ y : P, (∀ w, w * y = y * w) → y = 1)
    {b : MulAut P} {y : P} (hb : b * MulAut.conj y = MulAut.conj y * b) : b y = y := by
  have h1 : ∀ w, b y * w * (b y)⁻¹ = y * w * y⁻¹ := by
    intro w
    have := congrArg (fun φ : MulAut P => φ (b.symm w)) hb
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at this
    exact this
  have h2 : y⁻¹ * b y = 1 := hZ _ fun w => by
    have := h1 w
    calc w * (y⁻¹ * b y) = y⁻¹ * (y * w * y⁻¹) * b y := by group
      _ = y⁻¹ * (b y * w * (b y)⁻¹) * b y := by rw [this]
      _ = y⁻¹ * b y * w := by group
  calc b y = y * (y⁻¹ * b y) := by group
    _ = y := by rw [h2, mul_one]

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
