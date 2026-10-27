module

public import CFSG.ClassicalInvolution.Q3.TL3C11
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

theorem card_centralizer_lt_of_center {G : Type} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) {c : G} (hc1 : c ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({c} : Set G)) < Nat.card G := by
  have hne : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
    intro htop
    apply hc1
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rwa [hZ, Subgroup.mem_bot] at hcZ
  have h3 := Subgroup.card_le_card_group (Subgroup.centralizer ({c} : Set G))
  have h4 : Nat.card ↥(Subgroup.centralizer ({c} : Set G)) ≠ Nat.card G :=
    fun h => hne ((Subgroup.card_eq_iff_eq_top _).mp h)
  omega

section Outcome

variable {Y : Type} [Group Y] [Finite Y]

theorem datumLift_of_IH {n : ℕ} (hT : Thm1RTwinHasLiftBelow n) (hB : TightBelow n)
    (hlt : Nat.card Y < n) {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hd : Q8TwinDatum R S t) (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2))
    (hgen : TightSelfGen R) (hO : TightOddFree Y) (htc : tightCore R = R)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hA : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    (HasTwin R → TightInO2 t ∨ TwinE4 Y ∨ TightHasLift R t) ∧
      (¬ HasTwin R → TightEx Y R S t ∨ TightHasLift R t) := by
  refine ⟨fun htw => hT Y hlt R S t hd hq8 hgen hO hΩ hA htw, fun hno => ?_⟩
  · have hzK : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core hd
    have hsing : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        {tightCore R} := by
      ext K
      constructor
      · intro hK
        by_contra hne
        exact hno ⟨K, hK, hne⟩
      · intro hK
        rw [Set.mem_singleton_iff] at hK
        subst hK
        exact ⟨CoreAssembly.mem_conjClass_self _, t, hzK, hzK⟩
    have hnormal := (twinSet_eq_singleton_iff (Q3B.conjInvariant_conjClass _)
      (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) (CoreAssembly.mem_conjClass_self _) hzK).mp hsing
    rw [htc] at hnormal
    have hdt := hd.toTightDatum hnormal
    rcases hB Y hlt R S t hdt ⟨hq8, hgen, hO⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (tightHasLift_of_good hdt h)

end Outcome

@[expose] def TwinSecHyp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    Q8TwinDatum R S t → tightCore R = R →
    HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
    ∀ u : Y, IsUniqueInvolution J u → u ≠ t →
      HypOmegaGen (CoreAssembly.conjClass (tightCore (secR R u)))

section Main

@[expose] def TwinSecA (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → tightCore R = R →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ u : Y, IsUniqueInvolution J u → u ≠ t →
        ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
          (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
          AEmpty (CoreAssembly.conjClass (tightCore (secR R u))) (tightCore (secR R u)) ∨
            TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
              (⟨⟨t, htu⟩, ht⟩ : secH R u))

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
