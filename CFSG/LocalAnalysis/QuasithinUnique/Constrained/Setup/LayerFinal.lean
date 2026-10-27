module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ10
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOrig

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Final

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.SectionRank CFSG.Open
open scoped commutatorElement

universe v

section Linear

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [CharP k 2] [Finite V]

theorem minimal_best_offenders_normalize_components {G A : Subgroup (V ≃ₗ[k] V)}
    (hAG : A ≤ Subgroup.normalizer (G : Set (V ≃ₗ[k] V)))
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A) :
    QuadAct (MonoidHom.id (V ≃ₗ[k] V)) A ∧
      ∀ L : Subgroup (V ≃ₗ[k] V), IsComponentIn L G → ∀ a ∈ A, conjSub a L = L :=
  Layer.minimal_best_offenders_normalize_components quadBestOffendersNormalize hAG hAel hAne hoff
    hstrict

theorem component_section {G L A : Subgroup (V ≃ₗ[k] V)} (hL : IsComponentIn L G) (hAG : A ≤ G)
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hcomm : ⁅L, A⁆ ≠ ⊥) : ∃ I : Submodule k V, Layer.ComponentSection L A I :=
  Layer.component_section quadBestOffendersNormalize hL hAG hAel hAne hoff hstrict hcomm

theorem minimal_parabolic_section {H T M E : Subgroup (V ≃ₗ[k] V)}
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) : Layer.ParabolicSection H T :=
  Layer.minimal_parabolic_section quadBestOffendersNormalize hO2 hT hTn hTM hMH hmax hEH hEne hEel
    hEoff

theorem nonsolvable_layer {H T M E : Subgroup (V ≃ₗ[k] V)} (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) :
    Layer.NonsolvableLayer H T M :=
  Layer.nonsolvable_layer quadBestOffendersNormalize hns hO2 hT hTn hTM hMH hmax hEH hEne hEel
    hEoff

theorem actual_component_minimal_parabolic {H T M E : Subgroup (V ≃ₗ[k] V)}
    (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) :
    Layer.ActualComponentTransfer H T M :=
  Layer.actual_component_minimal_parabolic quadBestOffendersNormalize hns hO2 hT hTn hTM hMH hmax
    hEH hEne hEel hEoff

end Linear

section Original

variable {G : Type} [Group G] [Finite G] {S P : Subgroup G} {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W]

theorem original_nonsolvable_action (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    (hobs : PushUpObstruction S P)
    {θ : ↥(conjClosure (omegaOneCenterOf S) P) ≃* Multiplicative W}
    {ρ : ↥P →* (W ≃ₗ[ZMod 2] W)}
    (h : Layer.IsBinModel (reducedAction_of_pushUpObstruction hobs).le_normalizer θ ρ) :
    Layer.OriginalReduced S P ρ ∧ (¬ Group.IsSolvable ↥ρ.range →
      Layer.OriginalLayer S P (conjClosure (omegaOneCenterOf S) P) ρ) :=
  Layer.original_nonsolvable_action quadBestOffendersNormalize hcent hcat hobs h

end Original

end CFSG.QuasithinUnique.Setup.Layer.Final
