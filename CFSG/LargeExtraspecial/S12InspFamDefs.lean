module

public import CFSG.LargeExtraspecial.DW2AOutInput
public import CFSG.LargeExtraspecial.S14LitRoot
public import CFSG.LargeExtraspecial.S12Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions

@[expose] def InspNondeg (X : Type) [Group X] (D : Set X) : Prop :=
  ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4

@[expose] def InspFor (P : ∀ (X : Type) [Group X], Set X → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → 5 ≤ S.width → t ∈ S.Lbar g →
    IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t → ¬ S.IsReducible12 →
    P (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

@[expose] def FischerSym (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧ ∃ φ : G ≃* Equiv.Perm (Fin m), ∀ g : G, g ∈ D ↔ (φ g).IsSwap

open CFSG.Open Matrix in
@[expose] def FischerSp (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
    fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)

open CFSG.Open Matrix in
@[expose] def FischerO (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
    (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
    fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)

open CFSG.Open Matrix in
@[expose] def FischerPSU (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ m : ℕ, 4 ≤ m ∧
    fischerCentralQuotientModel D
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)

open CFSG.Open in
@[expose] def FischerF3 (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
    (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
    fischerCentralQuotientModel D
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)

@[expose] def FischerFi (G : Type) [Group G] (D : Set G) : Prop :=
  (Nat.card G = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ∧ Nat.card D = 3510) ∨
    (Nat.card G = 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23 ∧ Nat.card D = 31671) ∨
    (Nat.card G = 2 ^ 22 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 ∧
      Nat.card D = 306936)

theorem s12FischerConclusion_iff (G : Type) [Group G] (D : Set G) :
    S12FischerConclusion G D ↔ FischerSym G D ∨ FischerSp G D ∨ FischerO G D ∨
      FischerPSU G D ∨ FischerF3 G D ∨ FischerFi G D :=
  Iff.rfl

@[expose] def InspPSL : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  InspNondeg X D ∧ ∃ m, 3 ≤ m ∧ LieModel X .PSL m 2 1

@[expose] def InspPSp : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  InspNondeg X D ∧ ∃ m, 3 ≤ m ∧ LieModel X .PSp m 2 1

@[expose] def InspPOmega : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  InspNondeg X D ∧ ∃ m, 4 ≤ m ∧ (LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1)

@[expose] def InspU33 : Prop := InspFor fun (X : Type) [Group X] (_ : Set X) =>
  LieModel X .PSU 3 3 1

@[expose] def InspAlt6 : Prop := InspFor fun (X : Type) [Group X] (_ : Set X) =>
  Nonempty (X ≃* alternatingGroup (Fin 6))

@[expose] def InspJ2 : Prop := InspFor fun (X : Type) [Group X] (_ : Set X) =>
  NativeSporadic.IsSporadic X .J2

@[expose] def InspSym : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerSym X D

@[expose] def InspSpTv : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerSp X D

@[expose] def InspOTv : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerO X D

@[expose] def InspPSU : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerPSU X D

@[expose] def InspF3 : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerF3 X D

@[expose] def InspFi : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerFi X D

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem isNondeg12_iff_inspNondeg {g : G} :
    S.IsNondeg12 g ↔ InspNondeg (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) := by
  constructor
  · rintro ⟨d, hd, e, he, h4⟩
    exact ⟨⟨d, subset_Xbar12 hd⟩, hd, ⟨e, subset_Xbar12 he⟩, he, by
      rw [s12_orderOf_mul_coe]; exact h4⟩
  · rintro ⟨d, hd, e, he, h4⟩
    exact ⟨d, hd, e, he, by rwa [s12_orderOf_mul_coe] at h4⟩

theorem isTransClass34_Ebar12 {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t) :
    DW.IsTransClass34 (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) := by
  have hD := transpositionData_Xbar12 S14.rootInvolutionComponentsInput ht htA hS
  refine ⟨s12_closure_preimage_eq_top hD.gen, ⟨hD.t', hD.mem, fun d => ?_⟩,
    fun d hd => ⟨fun h => hD.ne_one _ hd (by rw [h]; rfl), hD.invol' hd⟩,
    fun d hd e he => by rw [s12_orderOf_mul_coe]; exact hD.ord _ hd _ he,
    fun d hd e he h4 => ?_⟩
  · rw [hD.preimage_eq_isConj]
    rfl
  · rw [s12_orderOf_mul_coe] at h4
    have := hD.sq _ hd _ he h4
    simpa using this

end Setting

end CFSG.LargeExtraspecial
