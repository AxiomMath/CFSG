module

public import CFSG.HardMathSupport.U4FF.ClassLocWeight
public import CFSG.HardMathSupport.U4FF.ClassLocHw

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups

@[expose] def lowOf : FK → ℕ
  | .N => 3
  | .W => 5
  | .S => 0

theorem lowOf_lt (K : FK) : lowOf K < K.dim := by cases K <;> decide

@[expose] def lowIdx (fs : List FK) : AmbIdx fs := fun f => ⟨lowOf (fs.get f), lowOf_lt _⟩

section Low

variable {k : Type*} [Field k]

@[expose] def Efun (g : SL(4, k)) : k :=
  (g : Matrix (Fin 4) (Fin 4) k) 3 0 *
    ((g : Matrix (Fin 4) (Fin 4) k) 2 0 * (g : Matrix (Fin 4) (Fin 4) k) 3 1 -
      (g : Matrix (Fin 4) (Fin 4) k) 2 1 * (g : Matrix (Fin 4) (Fin 4) k) 3 0) *
    ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) 3 0

theorem amb_entry_low_hw (g : SL(4, k)) :
    ambRep k (fsOf true true true) g ((ambEq (fsOf true true true)).symm
        (ambEq (fsOf true true true) (lowIdx (fsOf true true true))))
      ((ambEq (fsOf true true true)).symm (ambEq (fsOf true true true) (hwIdx (fsOf true true true)))) =
      Efun g := by
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ambRep_apply, kronDep_apply]
  show ∏ f : Fin 3, _ = _
  rw [Fin.prod_univ_three]
  show repN k g 3 0 * repW k g 5 0 * repS k g 0 3 = _
  rw [repN_apply, repW_apply, repS_apply]
  rfl

variable [CharP k 2]

theorem lam_locMat_y (hρ : LocValid1 true true true) (g : SL(4, k)) :
    ((locSpec true true true hρ).Bk k *ᵥ ((locSpec true true true hρ).locMat k g *ᵥ
      yloc true true true hρ k)) (ambEq (fsOf true true true) (lowIdx (fsOf true true true))) =
      Efun g := by
  set S := locSpec true true true hρ with hS
  have hz : S.z = 0 := by
    funext x
    show bitF (locData true true true).z (x : ℕ) = 0
    exact bitF_zero _
  have hzk : S.zk k = 0 := by
    funext x
    show f2 k (S.z x) = 0
    rw [hz]
    simp
  have hPi := Pi_mulVec_hw true true true hρ
  set vk : Fin (ambDim (fsOf true true true)) → k := fun x => f2 k (hwVec (fsOf true true true) x)
    with hvk
  have hPik : S.Pik k *ᵥ vk = vk := by
    rw [LocSpec.Pik_eq_map, hvk, map_mulVec', hPi]
  have hPik' : S.Pik k = S.Bk k * S.Pmk k := by
    unfold LocSpec.Pik
    rw [hzk]
    simp
  have hy : S.Bk k *ᵥ (S.Pmk k *ᵥ vk) = vk := by
    rw [Matrix.mulVec_mulVec, ← hPik', hPik]
  have hamb : ambRepF k (fsOf true true true) g * S.Bk k = S.Bk k * S.locMat k g := by
    have h := S.amb_B k g
    rw [hzk] at h
    ext x y
    have := congrFun (congrFun h x) y
    simpa [Matrix.vecMulVec_apply] using this
  have hyl : yloc true true true hρ k = S.Pmk k *ᵥ vk := rfl
  calc (S.Bk k *ᵥ (S.locMat k g *ᵥ yloc true true true hρ k))
        (ambEq (fsOf true true true) (lowIdx (fsOf true true true)))
      = ((S.Bk k * S.locMat k g) *ᵥ yloc true true true hρ k)
          (ambEq (fsOf true true true) (lowIdx (fsOf true true true))) := by
        rw [Matrix.mulVec_mulVec]
    _ = ((ambRepF k (fsOf true true true) g * S.Bk k) *ᵥ yloc true true true hρ k)
          (ambEq (fsOf true true true) (lowIdx (fsOf true true true))) := by rw [hamb]
    _ = (ambRepF k (fsOf true true true) g *ᵥ (S.Bk k *ᵥ yloc true true true hρ k))
          (ambEq (fsOf true true true) (lowIdx (fsOf true true true))) := by
        rw [← Matrix.mulVec_mulVec]
    _ = (ambRepF k (fsOf true true true) g *ᵥ vk)
          (ambEq (fsOf true true true) (lowIdx (fsOf true true true))) := by rw [hyl, hy]
    _ = ambRepF k (fsOf true true true) g
          (ambEq (fsOf true true true) (lowIdx (fsOf true true true)))
          (ambEq (fsOf true true true) (hwIdx (fsOf true true true))) := by
        rw [hvk, hwVec_eq_single, Matrix.mulVec_single_one]
        rfl
    _ = Efun g := amb_entry_low_hw g

end Low

end CFSG.HardMathSupport.U4FF
