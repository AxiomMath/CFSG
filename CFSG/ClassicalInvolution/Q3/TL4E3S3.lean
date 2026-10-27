module

public import CFSG.ClassicalInvolution.Q3.TL4E3Z2
public import CFSG.ClassicalInvolution.Q3.TL4Conn264C
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.Blueprint
open scoped commutatorElement

namespace E3

abbrev orbGen {G : Type} [Group G] (Ω : Set (Subgroup G)) (K J : Subgroup G) : Subgroup G :=
  ⨆ M ∈ orbOf (TC.nbrAdj Ω) K J, M

abbrev OrbQ {G : Type} [Group G] (Ω : Set (Subgroup G)) (K J : Subgroup G) : Type :=
  ↥(orbGen Ω K J) ⧸ classicalInvolutionOddCore ↥(orbGen Ω K J)

end E3

theorem thm1RTwinLiftSetBelow_of_E {n : ℕ} (H : Thm1RTwinLiftSetEBelow n) :
    Thm1RTwinLiftSetBelow n := by
  intro Y _ _ hY R S t hd hq hg hO hΩ hA htw
  rcases H Y hY R S t hd hq hg hO hΩ hA htw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.toSet (Q8Datum.isUniqueInvolution_core hd)))

section Cit3


@[expose] def TightE3S3Pick (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → TightEdgeless (secR R u) →
      (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ∃ L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R),
          L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
            L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)

@[expose] def TightE3S3Sec163 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht)

@[expose] def TightE3S3Cent (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht) →
      ∀ L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R),
        L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
          L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
            ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
              ⁅u * t, y⁆ ∈ oddCoreOf
                (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)

@[expose] def TightE3S3Orbit (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) →
      ∀ L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R),
        L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
          L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
            (∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
              ⁅u * t, y⁆ ∈ oddCoreOf
                (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)) →
      ∀ (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
        tightCore Rd = J → TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t →
          SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (tightCore R)
              (u * t) ∧
            ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t) u

@[expose] def TightE3S3Orth (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht) →
      ∀ L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R),
        L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
          L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
            (∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
              ⁅u * t, y⁆ ∈ oddCoreOf
                (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)) →
      ∀ (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
        tightCore Rd = J → TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t →
          (TwinE4 ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t)) ∨
            SecTwinOmega (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t)) →
            LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) .PSL 3 3 1 ∨
              LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) .PSU 3 3 1

@[expose] def TightE3S3Fin (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      (LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) .PSL 3 3 1 ∨
        LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) .PSU 3 3 1) →
        TightInO2 (E3.secT htu ht)

end Cit3

section Cit3b


theorem tightE3S3F_of_leaves {n : ℕ} (h4 : Thm4RBelow 3 n) (hPick : TightE3S3Pick n)
    (hSec : TightE3S3Sec163 n) (hCent : TightE3S3Cent n) (hOrb : TightE3S3Orbit n)
    (hOrth : TightE3S3Orth n) (hFin : TightE3S3Fin n) : TightE3S3F n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hμ
  by_contra hE2
  have h163 := hSec Y R S t J u hF htu ht Sb hex hedge hμ hE2
  obtain ⟨L, hLπ, hLs, hLn⟩ := hPick Y R S t J u hF hedge hμ
  have hc := hCent Y R S t J u hF htu ht Sb hex hedge hμ hE2 h163 L hLπ hLs hLn
  obtain ⟨g, Sd, S', R', T, W, hgJ, -, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  obtain ⟨hconj, hnO2⟩ :=
    hOrb Y R S t J u hF htu ht hedge hμ hE2 L hLπ hLs hLn hc _ Sd S' R' T W hcore hs
  have hω := hs.secTwinOmega_or_twinE4 h4
    (thm1RTwinLiftSetBelow_of_E (hF.plus.twin rfl)) hconj hnO2
  exact hE2 (hFin Y R S t J u hF htu ht Sb hex
    (hOrth Y R S t J u hF htu ht hedge hμ hE2 h163 L hLπ hLs hLn hc _ Sd S' R' T W hcore hs hω))

end Cit3b

end CFSG.ClassicalInvolution.Q3.TL4
