module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
import CFSG.Adapters.RankTwoModelTransports
import CFSG.LieType.CurtisTits.Conclusion
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped commutatorElement

theorem genFittingFStar_eq_of_normal_simple {G : Type*} [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F] (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hC : Subgroup.centralizer (F : Set G) = ⊥) : genFittingFStar G = F :=
  (CFSG.generalizedFitting_eq_componentClassification G).symm.trans
    (CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot F hFnonab hC)

theorem oddLieType_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    CFSG.Blueprint.OddLieType X ↔ CFSG.Blueprint.OddLieType Y := by
  constructor
  · rintro ⟨t, n, p, f, hp, hp2, hadm, hmodel⟩
    exact ⟨t, n, p, f, hp, hp2, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel⟩
  · rintro ⟨t, n, p, f, hp, hp2, hadm, hmodel⟩
    exact ⟨t, n, p, f, hp, hp2, hadm,
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hmodel⟩

theorem isSporadic_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {s : TauCeti.SporadicName} :
    CFSG.Blueprint.NativeSporadic.IsSporadic X s ↔
      CFSG.Blueprint.NativeSporadic.IsSporadic Y s :=
  ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

noncomputable def nativeM11EquivM11 :
    CFSG.Blueprint.NativeSporadic.M11 ≃* CFSG.Open.M11 :=
  (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11).symm.trans
    CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11

theorem nativeM12_eq_classicalInvolutionM12 :
    CFSG.Blueprint.NativeSporadic.M12 = CFSG.Open.classicalInvolutionM12 := rfl

theorem nonempty_mulEquiv_m11_of_isSporadic {X : Type} [Group X]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic X .M11) :
    Nonempty (X ≃* CFSG.Open.M11) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans nativeM11EquivM11⟩

theorem nonempty_mulEquiv_m12_of_isSporadic {X : Type} [Group X]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic X .M12) :
    Nonempty (X ≃* CFSG.Open.classicalInvolutionM12) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (MulEquiv.subgroupCongr nativeM12_eq_classicalInvolutionM12)⟩

theorem orderForm_of_modelsForm_of_finite
    (hOrder : ∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.OddLieType X →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card X ∈ lieOrdersChar p)
    (hModels : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)]
      (_hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
      (z : G) (_hz : orderOf z = 2)
      (J : Subgroup G) (_hzJ : z ∈ J)
      (_hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
      (S : Sylow 2 J)
      (_hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))),
      (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
      (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12))
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨
        Nonempty (F ≃* CFSG.Open.M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨
        Nonempty (F ≃* CFSG.Open.M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) := by
  obtain rfl := genFittingFStar_eq_of_normal_simple F hFnonab hFstar
  obtain ⟨hW, hT⟩ := hModels G hFnonab z hz J hzJ hJ S hS
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases hW h with h | h
    · exact Or.inl (hOrder _ h)
    · exact Or.inr (nonempty_mulEquiv_m11_of_isSporadic h)
  · rcases hT h with h | h | h
    · exact Or.inl (hOrder _ h)
    · exact Or.inr (Or.inl (nonempty_mulEquiv_m11_of_isSporadic h))
    · exact Or.inr (Or.inr (nonempty_mulEquiv_m12_of_isSporadic h))

theorem orderForm_of_modelsForm
    (hOrder : ∀ (X : Type) [Group X], CFSG.Blueprint.OddLieType X →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card X ∈ lieOrdersChar p)
    (hModels : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)]
      (_hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
      (z : G) (_hz : orderOf z = 2)
      (J : Subgroup G) (_hzJ : z ∈ J)
      (_hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
      (S : Sylow 2 J)
      (_hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))),
      (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
      (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12))
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨
        Nonempty (F ≃* CFSG.Open.M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨
        Nonempty (F ≃* CFSG.Open.M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) :=
  orderForm_of_modelsForm_of_finite (fun X _ _ h => hOrder X h) hModels G F hFnonab hFstar z hz J
    hzJ hJ S hS

end CFSG.ClassicalInvolution
