module

public import CFSG.ClassicalInvolution.Q3.Q3ZAHeis
public import CFSG.ClassicalInvolution.Q3.Q3ZLiftDict

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3Z
open scoped MatrixGroups

@[expose] noncomputable def uSL : SL(2, F3) := mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])

@[expose] noncomputable def lSL : SL(2, F3) := mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])

@[expose] noncomputable def wSL : SL(2, F3) := mkSL !![0, -1; 1, 0] (by simp [Matrix.det_fin_two])

@[expose] noncomputable def sbU : StatedSp 2 F3 := shortBlock F3 (zero_ne_one : (0 : Fin 2) ≠ 1) uSL

@[expose] noncomputable def sbL : StatedSp 2 F3 := shortBlock F3 (zero_ne_one : (0 : Fin 2) ≠ 1) lSL

@[expose] noncomputable def weyl₁ : StatedSp 2 F3 := longBlock F3 2 1 wSL

section Datum

variable {G : Type} [Group G]

@[expose] def HeisDatum (θ : StatedSp 2 F3 →* G) (z e₀ e₂ f₀ f₂ : G) : Prop :=
  ∃ φ : Heis →* G, φ Heis.center = z ∧ φ (Heis.vec (Pi.single (Sum.inl 0) 1)) = e₀ ∧
    φ (Heis.vec (Pi.single (Sum.inl 1) 1)) = e₂ ∧ φ (Heis.vec (Pi.single (Sum.inr 0) 1)) = f₀ ∧
    φ (Heis.vec (Pi.single (Sum.inr 1) 1)) = f₂ ∧
    ∀ (s : StatedSp 2 F3) (x : Heis), θ s * φ x * (θ s)⁻¹ = φ (heisAct s x)

@[expose] def HeisAt (θA θB θX : StatedSp 2 F3 →* G) : Prop :=
  HeisDatum θX (θA (longBlock F3 2 1 uSL))⁻¹ (θA (weyl₁ * sbU * weyl₁⁻¹))
    (θB (weyl₁ * sbU * weyl₁⁻¹)) (θA sbL)⁻¹ (θB sbU)⁻¹

end Datum

@[expose] noncomputable def iotaHom : StatedSp 2 F3 →* StatedSp 2 F3 :=
  (MulAut.conj (longInv F3 2 0)).toMonoidHom

structure LayerTriple {G : Type} [Group G] (Ω : Set (Subgroup G))
    (θA θB θX : StatedSp 2 F3 →* G) : Prop where
  injA : Function.Injective θA
  injB : Function.Injective θB
  injX : Function.Injective θX
  members : ∃ Kp Kh Kr : Subgroup G, Kp ∈ Ω ∧ Kh ∈ Ω ∧ Kr ∈ Ω ∧
    (planeGroup (stdPlane F3 2 0)).map θA = Kp ∧ (planeGroup (stdPlane F3 2 1)).map θA = Kh ∧
    (planeGroup (stdPlane F3 2 0)).map θB = Kh ∧ (planeGroup (stdPlane F3 2 1)).map θB = Kr ∧
    (planeGroup (stdPlane F3 2 0)).map θX = Kp ∧ (planeGroup (stdPlane F3 2 1)).map θX = Kr ∧
    (∀ a ∈ θA.range, ∀ b ∈ Kr, a * b = b * a) ∧ (∀ a ∈ θB.range, ∀ b ∈ Kp, a * b = b * a) ∧
    (∀ a ∈ θX.range, ∀ b ∈ Kh, a * b = b * a)
  hub : ∀ x : SL(2, F3), θA (longBlock F3 2 1 x) = θB (longBlock F3 2 0 x)
  end_p : ∀ x : SL(2, F3), θX (longBlock F3 2 0 x) = θA (longBlock F3 2 0 x)
  end_r : ∀ x : SL(2, F3), θX (longBlock F3 2 1 x) = θB (longBlock F3 2 1 x)

structure SymTri (G : Type) [Group G] (Ω : Set (Subgroup G)) where
  K₀ : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  Θ₀₁ : StatedSp 2 F3 →* G
  Θ₀₂ : StatedSp 2 F3 →* G
  inj₀₁ : Function.Injective Θ₀₁
  inj₀₂ : Function.Injective Θ₀₂
  mem₀ : K₀ ∈ Ω
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  blk₀₁₀ : (planeGroup (stdPlane F3 2 0)).map Θ₀₁ = K₀
  blk₀₁₁ : (planeGroup (stdPlane F3 2 1)).map Θ₀₁ = K₁
  blk₀₂₀ : (planeGroup (stdPlane F3 2 0)).map Θ₀₂ = K₀
  blk₀₂₁ : (planeGroup (stdPlane F3 2 1)).map Θ₀₂ = K₂
  comm₀₁ : ∀ a ∈ Θ₀₁.range, ∀ b ∈ K₂, a * b = b * a
  comm₀₂ : ∀ a ∈ Θ₀₂.range, ∀ b ∈ K₁, a * b = b * a
  matched : ∀ x : SL(2, F3), Θ₀₂ (longBlock F3 2 0 x) = Θ₀₁ (longBlock F3 2 0 x)

end CFSG.ClassicalInvolution.Q3.Q3ZA
