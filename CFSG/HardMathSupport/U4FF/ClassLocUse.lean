module

public import Certificates.Certificate27980
public import CFSG.HardMathSupport.U4FF.ClassLocHw
public import CFSG.HardMathSupport.U4FF.ClassLocWeight
public import CFSG.HardMathSupport.U4FF.ClassTwist

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups


theorem locValid (a b c : Bool) : LocValid a b c :=
  Certificates.certificate27980 a b c

section Use

variable (a b c : Bool) (k : Type*) [Field k] [CharP k 2]

@[expose] noncomputable def locR :
    SL(4, k) →* Matrix (Fin (locM a b c)) (Fin (locM a b c)) k :=
  (locSpec a b c (locValid a b c).1).locRep k

@[expose] noncomputable def ylocC : Fin (locM a b c) → k := yloc a b c (locValid a b c).1 k

variable {a b c k}

theorem locR_apply (g : SL(4, k)) :
    locR a b c k g = (locSpec a b c (locValid a b c).1).locMat k g := rfl

theorem ylocC_ne_zero : ylocC a b c k ≠ 0 := yloc_ne_zero a b c (locValid a b c).1

theorem locR_upTransv_fix {g : SL(4, k)} (hg : g ∈ upTransv k) :
    locR a b c k g *ᵥ ylocC a b c k = ylocC a b c k := by
  obtain ⟨i, j, hij, hlt, t, rfl⟩ := hg
  exact locMat_upper_fix a b c (locValid a b c).1 hij hlt t

theorem fixed_of_upTransv {m : ℕ} (R : SL(4, k) →* Matrix (Fin m) (Fin m) k) (v : Fin m → k)
    (h : ∀ g ∈ upTransv k, R g *ᵥ v = v) : ∀ g ∈ UpT k, R g *ᵥ v = v := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, ← Matrix.mulVec_mulVec, hy, hx]
  | inv x _ hx =>
    calc R x⁻¹ *ᵥ v = R x⁻¹ *ᵥ (R x *ᵥ v) := by rw [hx]
      _ = v := by rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem locR_upT_fix {g : SL(4, k)} (hg : g ∈ UpT k) :
    locR a b c k g *ᵥ ylocC a b c k = ylocC a b c k :=
  fixed_of_upTransv (locR a b c k) _ (fun _ hg' => locR_upTransv_fix hg') g hg

theorem equiv_of_lowTransv {m₁ m₂ : ℕ} (R₁ : SL(4, k) →* Matrix (Fin m₁) (Fin m₁) k)
    (R₂ : SL(4, k) →* Matrix (Fin m₂) (Fin m₂) k) (P : Matrix (Fin m₁) (Fin m₂) k)
    (h : ∀ g ∈ lowTransv k, P * R₂ g = R₁ g * P) : ∀ g ∈ LowT k, P * R₂ g = R₁ g * P := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]
  | inv x _ hx =>
    have h1 : R₁ x⁻¹ * R₁ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : R₂ x * R₂ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc P * R₂ x⁻¹ = (R₁ x⁻¹ * R₁ x) * P * R₂ x⁻¹ := by rw [h1, Matrix.one_mul]
      _ = R₁ x⁻¹ * (R₁ x * P) * R₂ x⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R₁ x⁻¹ * (P * R₂ x) * R₂ x⁻¹ := by rw [hx]
      _ = R₁ x⁻¹ * P * (R₂ x * R₂ x⁻¹) := by simp only [Matrix.mul_assoc]
      _ = R₁ x⁻¹ * P := by rw [h2, Matrix.mul_one]

theorem locR_diag (D : SL(4, k)) (d : Fin 4 → k)
    (hD : (D : Matrix (Fin 4) (Fin 4) k) = diagonal d) :
    locR a b c k D *ᵥ ylocC a b c k = wtLoc a b c d • ylocC a b c k := by
  have hdet : ∏ i, d i = 1 := by
    have := D.det_coe
    rwa [hD, det_diagonal] at this
  have := LocSpec.locMat_eigen (locSpec a b c (locValid a b c).1)
    (Pi_mulVec_hw a b c (locValid a b c).1) D (∏ f : Fin (fsOf a b c).length,
      hwFac d ((fsOf a b c).get f)) (ambRepF_diag_hw (fsOf a b c) D d hD)
  rw [prod_hwFac a b c d hdet] at this
  exact this

@[expose] noncomputable def picK (a b c : Bool) (k : Type*) [Field k] [CharP k 2] :
    Matrix (Fin (locM a b c)) (Fin (locM true true true)) k := (picMat a b c).map (f2 k)

@[expose] noncomputable def pirK (a b c : Bool) (k : Type*) [Field k] [CharP k 2] :
    Matrix (Fin (locM true true true)) (Fin (locM a b c)) k := (pirMat a b c).map (f2 k)

@[expose] noncomputable def iocK (a b c : Bool) (k : Type*) [Field k] [CharP k 2] :
    Matrix (Fin (locM true true true)) (Fin (locM a b c)) k := (iocMat a b c).map (f2 k)

@[expose] noncomputable def iolK (a b c : Bool) (k : Type*) [Field k] [CharP k 2] :
    Matrix (Fin (locM a b c)) (Fin (locM true true true)) k := (iolMat a b c).map (f2 k)

theorem picK_mul_pirK : picK a b c k * pirK a b c k = 1 := by
  unfold picK pirK
  rw [← Matrix.map_mul, picMat_mul_pirMat a b c (locValid a b c).2.2]
  simp

theorem iolK_mul_iocK : iolK a b c k * iocK a b c k = 1 := by
  unfold iolK iocK
  rw [← Matrix.map_mul, iolMat_mul_iocMat a b c (locValid a b c).2.2]
  simp

theorem picK_ylocC : picK a b c k *ᵥ ylocC true true true k = ylocC a b c k :=
  picMat_mulVec_yloc a b c (locValid a b c).2.2 (locValid a b c).1 (locValid true true true).1

theorem picK_equivTransv {g : SL(4, k)} (hg : g ∈ lowTransv k) :
    picK a b c k * locR true true true k g = locR a b c k g * picK a b c k := by
  obtain ⟨i, j, hij, hji, t, rfl⟩ := hg
  exact pi_equivariant a b c (locValid a b c).1 (locValid a b c).2.2 (locValid true true true).1
    hij hji t

theorem iocK_equivTransv {g : SL(4, k)} (hg : g ∈ lowTransv k) :
    iocK a b c k * locR a b c k g = locR true true true k g * iocK a b c k := by
  obtain ⟨i, j, hij, hji, t, rfl⟩ := hg
  exact iota_equivariant a b c (locValid a b c).1 (locValid a b c).2.2
    (locValid true true true).1 hij hji t

theorem picK_equiv {g : SL(4, k)} (hg : g ∈ LowT k) :
    picK a b c k * locR true true true k g = locR a b c k g * picK a b c k :=
  equiv_of_lowTransv (locR a b c k) (locR true true true k) (picK a b c k)
    (fun _ hg' => picK_equivTransv hg') g hg

theorem iocK_equiv {g : SL(4, k)} (hg : g ∈ LowT k) :
    iocK a b c k * locR a b c k g = locR true true true k g * iocK a b c k :=
  equiv_of_lowTransv (locR true true true k) (locR a b c k) (iocK a b c k)
    (fun _ hg' => iocK_equivTransv hg') g hg

theorem ambRepF_nil (g : SL(4, k)) : ambRepF k ([] : List FK) g = 1 := by
  have h1 : ambDim ([] : List FK) = 1 := Finset.prod_eq_one fun i _ => Fin.elim0 i
  ext x y
  have hxy : x = y := Fin.ext (by have := x.isLt; have := y.isLt; omega)
  subst hxy
  rw [Matrix.one_apply_eq, ambRepF_apply, Matrix.submatrix_apply, ambRep_apply, kronDep_apply]
  exact Finset.prod_eq_one fun i _ => Fin.elim0 i

theorem locR_000 (g : SL(4, k)) : locR false false false k g = 1 := by
  have hamb : ambRepF k (fsOf false false false) g = 1 := ambRepF_nil g
  rw [locR_apply]
  unfold LocSpec.locMat
  rw [hamb, Matrix.one_mul]
  exact LocSpec.Pmk_Bk _ k

instance instNonemptyLocIdx (a b c : Bool) : Nonempty (Fin (locM a b c)) :=
  ⟨⟨0, by cases a <;> cases b <;> cases c <;> decide⟩⟩

end Use

end CFSG.HardMathSupport.U4FF
