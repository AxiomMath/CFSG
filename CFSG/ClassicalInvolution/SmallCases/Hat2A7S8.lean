module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SStd
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Theorem8


structure Std8A7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  stand : Std2A7 Ω K
  noTwins : ∀ K' ∈ twinSet Ω K, K' = K
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hT : T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

@[expose] def A7C27_nbr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → ¬ DEdgeless Ω → ∃ J ∈ omegaNbr Ω K, True

@[expose] def A7C27_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → ∀ z : G,
      IsUniqueInvolution K z → ∀ J ∈ omegaNbr Ω K, ∀ t : G, IsUniqueInvolution J t →
        ∃ (S : Sylow 2 G) (R T W : Subgroup G), Std8A7 Ω K J S R T W z t

@[expose] def A7C27_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8A7 Ω K J S R T W z t →
      ¬ DConnected Ω →
        sigmaNorm Ω K ⊔ (⨆ M ∈ omegaNbr Ω K, ⨆ (s : G) (_ : IsUniqueInvolution M s),
          Subgroup.centralizer ({z * s} : Set G)) = ⊤

@[expose] def A7C27_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8A7 Ω K J S R T W z t →
      ¬ DConnected Ω → Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K

@[expose] def A7C26_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8A7 Ω K J S R T W z t →
      ¬ DConnected Ω → omegaNbrGen Ω K ≠ J ⊔ oddCoreOf (omegaNbrGen Ω K)

theorem a7T8_of_steps (hnbr : A7C27_nbr) (hsetup : A7C27_setup) (h274 : A7C27_4)
    (h278 : A7C27_8) : A7T8 := by
  intro G _ _ _ Ω K hs hedge hnt hdisc
  obtain ⟨J, hJ, -⟩ := hnbr G Ω K hs hedge
  obtain ⟨⟨z, hz⟩, -⟩ := hs.hyp.omega1 K hs.mem
  obtain ⟨⟨t, ht⟩, -⟩ := hs.hyp.omega1 J hJ.1
  obtain ⟨S, R, T, W, hstd⟩ := hsetup G Ω K hs hnt hdisc z hz J hJ t ht
  have h4 := h274 G Ω K J S R T W z t hstd hdisc
  have hle : sigmaNorm Ω K ⊔ (⨆ M ∈ omegaNbr Ω K, ⨆ (s : G) (_ : IsUniqueInvolution M s),
      Subgroup.centralizer ({z * s} : Set G)) ≤ sigmaNorm Ω K := by
    refine sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => ?_)
    obtain ⟨S', R', T', W', hstd'⟩ := hsetup G Ω K hs hnt hdisc z hz M hM s hs'
    exact h278 G Ω K M S' R' T' W' z s hstd' hdisc
  rw [h4] at hle
  have htop : sigmaNorm Ω K = ⊤ := top_le_iff.mp hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.mem hs.trans htop)

end Theorem8

end CFSG.ClassicalInvolution.Hat2A7S
