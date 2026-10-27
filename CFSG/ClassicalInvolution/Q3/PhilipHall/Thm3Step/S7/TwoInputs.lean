module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Ident

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight

section Vocab

@[expose] def E3aShape (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((Even f ∧ CFSG.Blueprint.LieModel (TL4.FStarQuot H) .PSL 2 p f ∧
        (genFittingFStar H).index ≤ 2) ∨
      ((CFSG.Blueprint.LieModel (TL4.FStarQuot H) .PSL 3 p f ∨
          CFSG.Blueprint.LieModel (TL4.FStarQuot H) .PSU 3 p f) ∧ p ^ f ≠ 3 ∧
        (genFittingFStar H).index ∣ 6))

@[expose] def IsE3aGroup (X : Type) [Group X] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((Even f ∧ CFSG.Blueprint.LieModel X .PSL 2 p f) ∨
      ((CFSG.Blueprint.LieModel X .PSL 3 p f ∨ CFSG.Blueprint.LieModel X .PSU 3 p f) ∧ p ^ f ≠ 3))

@[expose] def IsTwinGroup (X : Type) [Group X] : Prop :=
  CFSG.Blueprint.LieModel X .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1

end Vocab

section Lie

@[expose] def IsLieImage3 (X : Type) [Group X] : Prop :=
  ∃ (c : CompData) (_ : c.Valid) (_ : c ≠ CompData.sl23) (φ : c.G →* X),
    Function.Surjective φ ∧ φ.ker ≤ Subgroup.center c.G

end Lie

@[expose] def E3aOneClass : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], classicalInvolutionOddCore Y = ⊥ → NoNormalTwo Y →
    FStarSimple Y → ∀ Φ : Set (Subgroup Y), TypeRHyp Φ →
    ∀ K₁ ∈ Φ, ∀ K₂ ∈ Φ, ∀ z₁ z₂ : Y, IsUniqueInvolution K₁ z₁ → IsUniqueInvolution K₂ z₂ →
      (∃ hz : z₁ ∈ omegaGen (lOrbit (genFittingFStar Y) K₁),
        E3aShape ↥(omegaGen (lOrbit (genFittingFStar Y) K₁)) ∧
        Subgroup.Normal ((K₁.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) K₁))).subgroupOf
          (Subgroup.centralizer
            ({⟨z₁, hz⟩} : Set ↥(omegaGen (lOrbit (genFittingFStar Y) K₁)))))) →
      (∃ hz : z₂ ∈ omegaGen (lOrbit (genFittingFStar Y) K₂),
        E3aShape ↥(omegaGen (lOrbit (genFittingFStar Y) K₂)) ∧
        Subgroup.Normal ((K₂.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) K₂))).subgroupOf
          (Subgroup.centralizer
            ({⟨z₂, hz⟩} : Set ↥(omegaGen (lOrbit (genFittingFStar Y) K₂)))))) →
      K₂ ∈ lOrbit (genFittingFStar Y) K₁

section TwoLie

@[expose] def TwoLieOrbitsSame : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y + 1) →
    classicalInvolutionOddCore Y = ⊥ → NoNormalTwo Y → FStarSimple Y →
    ∀ Φ : Set (Subgroup Y), TypeRHyp Φ →
    ∀ K ∈ Φ, ∀ J ∈ Φ, ∀ zK zJ : Y, IsUniqueInvolution K zK → IsUniqueInvolution J zJ →
      (∃ hz : zK ∈ omegaGen (lOrbit (genFittingFStar Y) K),
        OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) K))
          (K.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) K))) ⟨zK, hz⟩) →
      (∃ hz : zJ ∈ omegaGen (lOrbit (genFittingFStar Y) J),
        OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) J))
          (J.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) J))) ⟨zJ, hz⟩) →
      ¬ CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .G2 0 3 1 →
      J ∈ lOrbit (genFittingFStar Y) K

@[expose] def TwoOrbitOfIdent' : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y + 1) →
    classicalInvolutionOddCore Y = ⊥ → NoNormalTwo Y →
    FStarSimple Y → ∀ Φ : Set (Subgroup Y), TypeRHyp Φ → omegaGen Φ = ⊤ →
    (∀ M ∈ Φ, ∀ z : Y, IsUniqueInvolution M z →
      ∃ hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M),
        OrbitIdent ↥(omegaGen (lOrbit (genFittingFStar Y) M))
          (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩) →
    ∀ K ∈ Φ, ∀ J ∈ Φ, J ∉ lOrbit (genFittingFStar Y) K →
      ¬ CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .G2 0 3 1 →
      TwoOrbitModelS7 Y ∧ Φ = {T : Subgroup Y | Nonempty (↥T ≃* QuaternionGroup 2)}

end TwoLie

section Coinc

@[expose] def CoincTwin : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsTwinGroup X → ¬ IsLieImage3 X ∧ ¬ IsE3aGroup X

end Coinc

@[expose] def SocleOddCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    Subgroup.centralizer (N : Set G) = ⊥ →
    (CFSG.Blueprint.LieModel ↥N .PSL 3 3 1 ∨ CFSG.Blueprint.LieModel ↥N .PSU 3 3 1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic ↥N .M12) →
    ∀ z : G, orderOf z = 2 → classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥

@[expose] def TwinOddCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsTwinGroup X →
    ∀ z : X, orderOf z = 2 → classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥

@[expose] def L33Q8Class : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    Subgroup.centralizer (N : Set G) = ⊥ → CFSG.Blueprint.LieModel ↥N .PSL 3 3 1 →
    ∀ T₁ T₂ : Subgroup G, Nonempty (↥T₁ ≃* QuaternionGroup 2) →
      Nonempty (↥T₂ ≃* QuaternionGroup 2) → T₂ ∈ lOrbit N T₁

@[expose] def U33Q8Classes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    Subgroup.centralizer (N : Set G) = ⊥ → CFSG.Blueprint.LieModel ↥N .PSU 3 3 1 →
    ∀ T₁ T₂ : Subgroup G, Nonempty (↥T₁ ≃* QuaternionGroup 2) →
      Nonempty (↥T₂ ≃* QuaternionGroup 2) → T₂ ∉ lOrbit N T₁ →
      N.index = 2 ∧ ∀ T : Subgroup G, Nonempty (↥T ≃* QuaternionGroup 2) →
        T ∈ lOrbit N T₁ ∨ T ∈ lOrbit N T₂

@[expose] def M12Q8Classes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    Subgroup.centralizer (N : Set G) = ⊥ → CFSG.Blueprint.NativeSporadic.IsSporadic ↥N .M12 →
    (∀ T : Subgroup G, Nonempty (↥T ≃* QuaternionGroup 2) → T ≤ N) ∧
    ∀ T₁ T₂ : Subgroup G, Nonempty (↥T₁ ≃* QuaternionGroup 2) →
      Nonempty (↥T₂ ≃* QuaternionGroup 2) → T₂ ∉ lOrbit N T₁ →
      ∀ T : Subgroup G, Nonempty (↥T ≃* QuaternionGroup 2) → T ∈ lOrbit N T₁ ∨ T ∈ lOrbit N T₂

@[expose] def TwinQ8Class : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsTwinGroup X →
    ∀ T₁ T₂ : Subgroup X, Nonempty (↥T₁ ≃* QuaternionGroup 2) →
      Nonempty (↥T₂ ≃* QuaternionGroup 2) → HypOmegaGen (CoreAssembly.conjClass T₁) →
      HypOmegaGen (CoreAssembly.conjClass T₂) → T₂ ∈ CoreAssembly.conjClass T₁

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
