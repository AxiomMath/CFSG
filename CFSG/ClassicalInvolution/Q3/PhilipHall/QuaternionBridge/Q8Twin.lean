module

public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

structure Q8TwinDatum {G : Type*} [Group G] (R : Subgroup G) (S : Sylow 2 R) (t : G) : Prop where
  quat : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
  mem : t ∈ (S : Subgroup R).map R.subtype
  order : orderOf t = 2
  cent : R ≤ Subgroup.centralizer ({t} : Set G)
  twoGroup : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)

theorem TightDatum.toQ8TwinDatum {G : Type*} [Group G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    (h : TightDatum R S t) : Q8TwinDatum R S t :=
  ⟨h.quat, h.mem, h.order, h.cent, h.twoGroup⟩

theorem Q8TwinDatum.toTightDatum {G : Type*} [Group G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    (h : Q8TwinDatum R S t)
    (hn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) : TightDatum R S t :=
  ⟨h.quat, h.mem, h.order, h.cent, hn, h.twoGroup⟩

theorem Q8TwinDatum.sylow_core {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R}
    {t : G} (_h : Q8TwinDatum R S t) :
    IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := by
  have hS : IsSylow2In ((S : Subgroup R).map R.subtype) R := Asc77.isSylow2In_map_subtype R S
  refine ⟨?_, hS.2.1, fun V hVK hV2 hle => hS.2.2 V (hVK.trans (tightCore_le R)) hV2 hle⟩
  intro s hs
  exact Subgroup.subset_closure ⟨hS.1 hs, hS.2.1.to_le (Subgroup.zpowers_le.mpr hs)⟩

theorem Q8TwinDatum.exists_sylow_q8 {G : Type} [Group G] [Finite G] {R : Subgroup G}
    {S : Sylow 2 R} {t : G} (h : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ P : Subgroup G, IsSylow2In P (tightCore R) ∧ Nonempty (↥P ≃* QuaternionGroup 2) :=
  ⟨_, h.sylow_core, ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
    R.subtype_injective).symm.trans hq8.some⟩⟩

theorem iSup_conjClass_eq_iSup {G : Type} [Group G] (K : Subgroup G) :
    (⨆ J ∈ CoreAssembly.conjClass K, J) = ⨆ g : G, conjSub g K := by
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    obtain ⟨g, rfl⟩ := hJ
    exact le_iSup (fun g : G => conjSub g K) g
  · exact iSup_le fun g => le_iSup₂_of_le (conjSub g K) ⟨g, rfl⟩ le_rfl

section Targets


@[expose] def Q8Thm7 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup ↥(genFittingFStar Y) →
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    TightBelow (Nat.card Y) →
    ∀ (Ω : Set (Subgroup Y)) (K : Subgroup Y), HypOmegaGen Ω → K ∈ Ω →
      (∀ J ∈ Ω, ∃ g : Y, conjSub g K = J) → (⨆ J ∈ Ω, J) = ⊤ →
      (∃ P : Subgroup Y, IsSylow2In P K ∧ Nonempty (↥P ≃* QuaternionGroup 2)) →
      AEmpty Ω K → (∃ K' ∈ twinSet Ω K, K' ≠ K) → IsSimpleGroup Y

@[expose] def Q8SimpleGood : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
    CIT3Below (Nat.card Y) → TightBelow (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → GoodThreeElement R t

@[expose] def Q8TwinGood : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup ↥(genFittingFStar Y) →
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    TightBelow (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → GoodThreeElement R t

theorem q8TwinGood_of_parts (h7 : Q8Thm7) (hg : Q8SimpleGood) : Q8TwinGood := by
  intro Y _ _ hF hnab hbelow hbelowT R S t hd hq8 hgen hΩ hA htw
  have hsimple : IsSimpleGroup Y :=
    h7 Y hF hnab hbelow hbelowT _ (tightCore R) hΩ (CoreAssembly.mem_conjClass_self _)
      (fun J hJ => hJ) (by rw [iSup_conjClass_eq_iSup]; exact hgen) (hd.exists_sylow_q8 hq8) hA htw
  obtain ⟨a, b, hab⟩ := hnab
  exact hg Y hsimple ⟨a, b, fun h => hab (Subtype.ext h)⟩ hbelow hbelowT R S t hd hq8 hgen hΩ hA
    htw

@[expose] def Q8SimpleLift : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
    CIT3Below (Nat.card Y) → TightBelow (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → TightHasLift R t

@[expose] def Q8TwinLift : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup ↥(genFittingFStar Y) →
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    TightBelow (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → TightHasLift R t

theorem q8TwinLift_of_parts (h7 : Q8Thm7) (hl : Q8SimpleLift) : Q8TwinLift := by
  intro Y _ _ hF hnab hbelow hbelowT R S t hd hq8 hgen hΩ hA htw
  have hsimple : IsSimpleGroup Y :=
    h7 Y hF hnab hbelow hbelowT _ (tightCore R) hΩ (CoreAssembly.mem_conjClass_self _)
      (fun J hJ => hJ) (by rw [iSup_conjClass_eq_iSup]; exact hgen) (hd.exists_sylow_q8 hq8) hA htw
  obtain ⟨a, b, hab⟩ := hnab
  exact hl Y hsimple ⟨a, b, fun h => hab (Subtype.ext h)⟩ hbelow hbelowT R S t hd hq8 hgen hΩ hA
    htw

end Targets

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
