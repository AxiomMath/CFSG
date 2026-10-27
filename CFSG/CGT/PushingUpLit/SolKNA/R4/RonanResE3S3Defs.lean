module

public import CFSG.ClassicalInvolution.Q3.TL4E3Plus
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


structure E3FrameR (r n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) (J : Subgroup Y) (u : Y) : Prop where
  large : TightLargeHypR r n Y R S t
  conn : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  sep : TC.SepHyp (CoreAssembly.conjClass (tightCore R))
  alpha : TightSepAlpha R t
  maxAdj : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J
  inv : IsUniqueInvolution J u

@[expose] def TightE3S3Sec163R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3FrameR r n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht)

@[expose] def TightSecGenS3R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3FrameR r n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → ¬ TightInO2 (E3.secT htu ht) →
        ∀ s : SecQ R u, E3.secT htu ht * s = s * E3.secT htu ht → s ≠ E3.secT htu ht →
          (∃ g : SecQ R u, s = g * E3.secT htu ht * g⁻¹) →
            Subgroup.centralizer ({E3.secT htu ht} : Set (SecQ R u)) ⊔
              Subgroup.centralizer ({s} : Set (SecQ R u)) = ⊤

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3FrameR.card_secQ_lt (hF : E3FrameR r n R S t J u) : Nat.card (SecQ R u) < n := by
  have hd := hF.large.datum
  have hJnbr := hF.maxAdj.1.2
  obtain ⟨-, hu2, -, -, -, -⟩ := hd.edge_involution hJnbr hF.inv
  obtain ⟨g, hgJ'⟩ := hJnbr.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hgu : g * t * g⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgJ] at h1
    exact h1.eq hF.inv
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hF.inv.ne_one
  have hE2u : ¬ TightInO2 u := hgu ▸ not_tightInO2_conj hF.large.notInO2 g
  have h3 := card_centralizer_lt hu2' hE2u
  have h1 : Nat.card (SecQ R u) ≤ Nat.card ↥(secH R u) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥(secH R u) ≤ Nat.card ↥(Subgroup.centralizer ({u} : Set Y)) :=
    Subgroup.card_le_card_group _
  rw [← hF.large.card]
  omega

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
