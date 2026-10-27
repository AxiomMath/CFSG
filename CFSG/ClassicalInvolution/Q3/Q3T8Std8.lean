module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3CLStd
import CFSG.ClassicalInvolution.Asc77.AscT8SetupEng
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def Thm8A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand Ω K → ¬ DEdgeless Ω → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → False
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Std8 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  stand : AscStand Ω K
  noTwins : ∀ K' ∈ twinSet Ω K, K' = K
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hT : T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

theorem AscStand.toCore {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    (h : AscStand Ω K) : Q3CL.T8R.Loc.AscStandCore Ω K :=
  ⟨h.hyp, h.cls, h.aEmpty, h.mem, h.trans⟩

open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc in
theorem Std8.toStd8Core {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) : Std8Core Ω K J S R T W z t :=
  ⟨hs.stand.toCore, hs.noTwins, hs.hz, hs.hJ, hs.ht, hs.hR, hs.hT, hs.hW⟩

@[expose] def C26_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → omegaNbrGen Ω K ≠ J ⊔ oddCoreOf (omegaNbrGen Ω K)

@[expose] def C26_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoS4 Ω W

@[expose] def C26_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoWylD4 Ω W

@[expose] def C27_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → dComp Ω K = dstarComp Ω K

@[expose] def C27_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω →
        sigmaNorm Ω K ⊔ (⨆ M ∈ omegaNbr Ω K, ⨆ (s : G) (_ : IsUniqueInvolution M s),
          Subgroup.centralizer ({z * s} : Set G)) = ⊤

@[expose] def C27_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K

@[expose] def C27_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand Ω K → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → ∀ z : G,
      IsUniqueInvolution K z → ∀ J ∈ omegaNbr Ω K, ∀ t : G, IsUniqueInvolution J t →
        ∃ (S : Sylow 2 G) (R T W : Subgroup G), Std8 Ω K J S R T W z t

@[expose] def C27_nbr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand Ω K → ¬ DEdgeless Ω → ∃ J ∈ omegaNbr Ω K, True

theorem thm8A_of_steps (hnbr : C27_nbr) (hsetup : C27_setup) (h274 : C27_4)
    (h278 : C27_8) : Thm8A := by
  intro G _ _ _ Ω K hs hedge hnt hdisc
  obtain ⟨J, hJ, -⟩ := hnbr G Ω K hs hedge
  obtain ⟨z, hzcl⟩ := hs.modU.classical K hs.mem
  have hz := hzcl.isUniqueInvolution_sl2
  obtain ⟨t, htcl⟩ := hs.modU.classical J hJ.1
  have ht := htcl.isUniqueInvolution_sl2
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
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

theorem c27_nbr_proved : C27_nbr := by
  intro G _ _ _ Ω K hs hedge
  have hΩ : HypOmegaMod Ω := hs.hyp
  exact CFSG.ClassicalInvolution.Asc77.c27_nbrE hΩ.conjInvariant (fun hA hB h => Q3CL.T3.omegaNbr_symm (l6_2) hΩ hA hB h)
    hs.trans hedge

theorem c27_setup_proved : C27_setup := by
  intro G _ _ _ Ω K hs hnt _ z hz J hJ t ht
  have hΩ : HypOmegaMod Ω := hs.hyp
  obtain ⟨S, R, T, W, hR, hT, hW⟩ := CFSG.ClassicalInvolution.Asc77.c27_setupE hs.mem hJ
    (fun hM hR hRM => Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hM hR hRM)
    (fun S => (l6_9_proved G Ω hΩ S).1)
  exact ⟨S, R, T, W,
    { stand := hs, noTwins := hnt, hz := hz, hJ := hJ, ht := ht, hR := hR, hT := hT, hW := hW }⟩
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
