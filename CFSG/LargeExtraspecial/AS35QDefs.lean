module

public import CFSG.LargeExtraspecial.AS35MMain
public import CFSG.LargeExtraspecial.S12InspFamDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.AS35DFinal
public import CFSG.LargeExtraspecial.AS35MSixEightF
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Co2Smith.GlDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

noncomputable abbrev LbarAsc : Subgroup S.O := closure S.DbarAsc

noncomputable abbrev PbarAsc (g : G) : Subgroup S.O :=
  ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ

noncomputable abbrev EhatAsc : Set (S.LbarAsc ⧸ center S.LbarAsc) :=
  (QuotientGroup.mk' (center S.LbarAsc)) '' (Subtype.val ⁻¹' S.DbarAsc)

structure Asc512Standing : Prop where
  normal : ∀ m ∈ S.Mbar, ∀ x ∈ S.LbarAsc, m * x * m⁻¹ ∈ S.LbarAsc
  conj : ∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, ∃ g ∈ S.LbarAsc, g * a * g⁻¹ = b
  fstar_card :
    Nat.card (CFSG.generalizedFitting (S.Mbar ⊓ centralizer S.DbarAsc : Subgroup S.O)) ≤ 3
  fitting_le_center : CFSG.fittingSubgroup S.LbarAsc ≤ center S.LbarAsc

@[expose] def Asc512Thomas : Prop :=
  S.width = 3 ∧ ∃ X : Subgroup S.O, X ≤ S.Mbar ∧ (∀ m ∈ S.Mbar, ∀ x ∈ X, m * x * m⁻¹ ∈ X) ∧
    IsPGroup 3 X ∧ ∃ t ∈ S.DSet, ∃ ht : t ∈ S.M, ∃ x ∈ X, S.ρ ⟨t, ht⟩ * x ≠ x * S.ρ ⟨t, ht⟩

@[expose] def Asc512Unitary : Prop :=
  4 ≤ S.width ∧ Nonempty (S.LbarAsc ⧸ center S.LbarAsc ≃* CFSG.Open.timmesfeldPSU S.width) ∧
    ∀ g : G, g * S.z * g⁻¹ ∈ S.DSet → S.PbarAsc g ≤ S.LbarAsc

@[expose] def Asc512SpSix : Prop :=
  S.width = 4 ∧ CFSG.Blueprint.LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp 3 2 1

end Setting

namespace S14

@[expose] def AschbacherFiveTwelveCoreStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp →
    (S.width = 4 ∧ Nonempty (S.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2)) ∨
      (S.width = 3 ∧ ∀ g₁ g₂ : G,
        orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) ∨
      S.SixFiveConcl

theorem aschbacherSecFiveSixRest_of_core (h512 : AschbacherFiveTwelveCoreStmt)
    (h681 : AschbacherSixEightOneStmt) (h682 : AschbacherSixEightTwoStmt)
    (h611 : AschbacherSixElevenStmt) : AschbacherSecFiveSixRest := by
  intro G _ _ S ih hn hW hO hsimp hC htop hH h64
  have hS : S.SixHyp := ⟨hn, hW, hO, hsimp, hC, htop, hH, h64⟩
  rcases h512 G S hS with hCo | ⟨-, h3⟩ | h65
  · exact Or.inr hCo
  · exact Or.inl h3
  · left
    have hD := aschbacherSixSixStmt G S hS h65
    have h69' := aschbacherSixNineStmt_of h681 h682 G S ih hS h65
    have h3 : ∀ a ∈ S.BSet, ∀ b ∈ S.BSet, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ) :=
      fun a ha b hb => S.orderOf_mul_mem_of_mem_BSet hS.sixFour h69' hD ha hb
    have hall := h611 G S ih hS h65 (fun g hg => S.BAt_eq_BSet hS.sixFour h69' hg) h3
    intro g₁ g₂
    exact h3 _ (hall g₁) _ (hall g₂)

theorem aschbacherSecFiveSixRest_of_core'
    (h512 : AschbacherFiveTwelveCoreStmt) (hT : SixFiveTransvectionStmt)
    (h67 : AschbacherSixSevenMbarStmt) (h59 : AschbacherFiveNineOneStmt)
    (h592 : AschbacherFiveNineTwoStmt) (hU : AschTwoAutStmt)
    (hcore : AschbacherSixElevenFusionCoreStmt) : AschbacherSecFiveSixRest :=
  aschbacherSecFiveSixRest_of_core h512 (aschbacherSixEightOneStmt_of' hT h67 h59 hU)
    (aschbacherSixEightTwoStmt_of' hT h67 h59 hU)
    (aschbacherSixElevenStmt_of_inputs' hcore h592 hT h67 h59 hU)

@[expose] def Asc512DichotomyStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing ∨ S.Asc512Thomas

@[expose] def Asc512SymStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp →
    ∀ g : G, g * S.z * g⁻¹ ∈ S.DSet → ∀ htM : g * S.z * g⁻¹ ∈ S.M,
      ∀ W : Submodule (ZMod 2) S.Qt,
        (∀ m ∈ S.Mbar, ∀ w ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) →
        W ≤ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) →
        ¬ W ≤ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) →
        ∃ Y : Subgroup S.O, Y ≤ S.PbarAsc g ∧ S.ρ ⟨_, htM⟩ ∈ Y ∧
          ¬ Y ≤ zpowers (S.ρ ⟨_, htM⟩) ∧ Nat.card Y ≤ 2 * Nat.card W ∧
          ∀ c ∈ S.Mbar, c * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * c → ∀ y ∈ Y, c * y * c⁻¹ ∈ Y

@[expose] def Asc512InspFor (P : ∀ (X : Type) [Group X], Set X → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    P (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc → S.Asc512Unitary ∨ S.Asc512SpSix

@[expose] def Asc512ClassifyStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    (InspNondeg _ S.EhatAsc ∧ CFSG.Timmesfeld.Outcome (S.LbarAsc ⧸ center S.LbarAsc)) ∨
      (¬ InspNondeg _ S.EhatAsc ∧
        S12FischerConclusion (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc)

@[expose] def Asc512Co2Branch :
    Prop :=
  CFSG.Sporadic.Co2Smith.SmithG1Input →
    ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
      S.Asc512SpSix → Nonempty (S.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2)

@[expose] def Asc512UnitaryBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    S.Asc512Unitary → S.SixFiveConcl

@[expose] def Asc512FiveTwelveSevenStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp →
    ∀ g : G, g * S.z * g⁻¹ ∈ S.DSet → ∀ htM : g * S.z * g⁻¹ ∈ S.M,
      ∃ x ∈ S.Mbar, (∃ k : ℕ, orderOf x = 3 ^ k) ∧ x * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * x ∧
        ∀ v ∈ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0

@[expose] def Asc512FiveEightStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp →
    ∀ g : G, g * S.z * g⁻¹ ∈ S.DSet → ∀ htM : g * S.z * g⁻¹ ∈ S.M,
      ∀ X : Subgroup S.O, X ≤ S.Mbar → (∀ x ∈ X, x * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * x) →
        (∀ p ∈ S.PbarAsc g, ∀ x ∈ X, p * x * p⁻¹ ∈ X) →
        CFSG.oddCore X ⊔ CFSG.layer X = ⊤ → Nat.card X ≤ 3

@[expose] def Asc512PbarStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp →
    ∀ g : G, g * S.z * g⁻¹ ∈ S.DSet → ∀ htM : g * S.z * g⁻¹ ∈ S.M,
      S.ρ ⟨_, htM⟩ ∈ S.PbarAsc g ∧ CFSG.IsExtraspecialPGroup 2 (S.PbarAsc g) ∧
        Nat.card (S.PbarAsc g) = 2 ^ (2 * S.width - 3) ∧
        (∀ x ∈ S.PbarAsc g, (∀ y ∈ S.PbarAsc g, x * y = y * x) → x = 1 ∨ x = S.ρ ⟨_, htM⟩) ∧
        (∀ c ∈ S.Mbar, c * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * c →
          ∀ x ∈ S.PbarAsc g, c * x * c⁻¹ ∈ S.PbarAsc g) ∧
        (∀ x ∈ S.PbarAsc g, ∀ v ∈ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
        ∀ x ∈ S.PbarAsc g, ∀ v ∈ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
            commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)

open CFSG.Fischer.Classification.Unitary in
@[expose] def SUModuleInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V), q.polarBilin.Nondegenerate → ∀ n : ℕ, 4 ≤ n →
    Module.finrank (ZMod 2) V = 2 * n →
    ∀ (L : Subgroup (V ≃ₗ[ZMod 2] V)) (D : Set (V ≃ₗ[ZMod 2] V)) (hDL : D ⊆ L),
      closure D = L → (∀ d ∈ D, IsTypeA q d 2) → (∀ g ∈ L, ∀ v, q (g v) = q v) →
      (∃ ψ : L ⧸ center L ≃* PG n, ∀ d (hd : d ∈ D),
        ψ (QuotientGroup.mk (⟨d, hDL hd⟩ : L)) ∈ DG n) →
      (∀ W : Submodule (ZMod 2) V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∃ J : V ≃ₗ[ZMod 2] V, (∀ v, J (J v) + J v + v = 0) ∧ (∀ v, q (J v) = q v) ∧
        ∀ g ∈ L, ∀ v, g (J v) = J (g v)

end S14

end CFSG.LargeExtraspecial
