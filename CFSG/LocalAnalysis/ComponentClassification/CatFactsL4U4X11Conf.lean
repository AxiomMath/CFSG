module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace X11

@[expose] def KConf (G : Type) [Group G] (N : Subgroup G) : Prop :=
  N.Normal ∧ centralizer (N : Set G) = ⊥ ∧ IsSimpleGroup ↥N ∧
    ∃ (b : G) (K : Subgroup G), orderOf b = 2 ∧ K ≤ N ∧ K ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set G))) ∧
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSp 2 3 1

@[expose] def Conf (G : Type) [Group G] (N : Subgroup G) : Prop :=
  N.Normal ∧ centralizer (N : Set G) = ⊥ ∧ IsSimpleGroup ↥N ∧
    ∃ (a b : G) (J K : Subgroup G), orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧
      J ≤ N ∧ J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) ∧
      Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 3 2 ∧ b ∈ coreActionKernel J ∧
      (∀ R : Subgroup G, R ≤ centralizer ({a} : Set G) ⊓ coreActionKernel J → IsPGroup 2 R →
        Nat.card R ≤ 8) ∧
      K ≤ N ∧ K ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set G))) ∧
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSp 2 3 1

theorem Conf.kConf {G : Type} [Group G] {N : Subgroup G} (h : Conf G N) : KConf G N := by
  obtain ⟨hN, hC, hs, a, b, J, K, -, hb, -, -, -, -, -, -, -, hKN, hKb, hKc, hKm⟩ := h
  exact ⟨hN, hC, hs, b, K, hb, hKN, hKb, hKc, hKm⟩

@[expose] def Outcome {G : Type} [Group G] (N : Subgroup G) : Prop :=
  Blueprint.LieModel ↥N .PSL 4 3 1 ∨ Blueprint.LieModel ↥N .PSU 4 3 1 ∨
    Nonempty (↥N ≃* alternatingGroup (Fin 10))

@[expose] def Recognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), Conf G N → GSRestricted ↥N → Outcome N

end X11

@[expose] def CF81X11CharThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), X11.Conf G N → ∀ f : ℕ,
    ((Blueprint.LieModel ↥N .PSL 4 3 f ∨ Blueprint.LieModel ↥N .PSU 4 3 f ∨
      Blueprint.LieModel ↥N .PSp 2 3 f) → f = 1) ∧
      ¬ Blueprint.LieModel ↥N .POmegaMinus 4 3 f

@[expose] def CF81X11U52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    centralizer (N : Set G) = ⊥ → Blueprint.LieModel ↥N .PSU 5 2 1 → ∀ t : G, orderOf t = 2 →
      Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 82944 ∨
        Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 4608 ∨
        Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 720

@[expose] def CF81X11ON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
    centralizer (N : Set G) = ⊥ → Blueprint.NativeSporadic.IsSporadic ↥N .ONan →
    ∀ t : G, orderOf t = 2 →
      Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 161280 ∨
        Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 175560

end CFSG.ComponentClassification.GSThmB
