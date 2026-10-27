module

public import CFSG.ClassicalInvolution.Q3.TL4SepDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


@[expose] def TightE3LeafR' (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) → TightSepAlpha R t →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
        (Sb : Sylow 2 ↥(secR R u)),
        TightEx (SecQ R u) (secR R u) Sb
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
            (⟨⟨t, htu⟩, ht⟩ : secH R u))

@[expose] def TightE3Z2R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) → TightSepAlpha R t →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
        (Sb : Sylow 2 ↥(secR R u)),
        TightEx (SecQ R u) (secR R u) Sb
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) →
        TightEdgeless (secR R u) →
        (∀ W ∈ WSet (CoreAssembly.conjClass (tightCore (secR R u))),
          MuIsoZ2 (CoreAssembly.conjClass (tightCore (secR R u))) W) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
            (⟨⟨t, htu⟩, ht⟩ : secH R u))

@[expose] def TightE3S3R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) → TightSepAlpha R t →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
        (Sb : Sylow 2 ↥(secR R u)),
        TightEx (SecQ R u) (secR R u) Sb
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) →
        TightEdgeless (secR R u) →
        (∀ W ∈ WSet (CoreAssembly.conjClass (tightCore (secR R u))),
          MuIsoS3 (CoreAssembly.conjClass (tightCore (secR R u))) W) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
            (⟨⟨t, htu⟩, ht⟩ : secH R u))

@[expose] def TightE3E4R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) → TightSepAlpha R t →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
        (Sb : Sylow 2 ↥(secR R u)),
        TightEx (SecQ R u) (secR R u) Sb
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) →
        ¬ TightEdgeless (secR R u) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
            (⟨⟨t, htu⟩, ht⟩ : secH R u))

@[expose] def TightE3LeafR'' (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) → TightSepAlpha R t →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
        (Sb : Sylow 2 ↥(secR R u)),
        TightEx (SecQ R u) (secR R u) Sb
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
            (⟨⟨t, htu⟩, ht⟩ : secH R u)) ∨ TightE4 (SecQ R u)

theorem TightE3LeafR'.toR'' {r n : ℕ} (h : TightE3LeafR' r n) : TightE3LeafR'' r n :=
  fun Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex =>
    Or.inl (h Y R S t hL hcn hsp hα J hJ u hu htu ht Sb hex)

@[expose] def TightE3E4O (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR 3 n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
        TightE4 (SecQ R u) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
            (⟨⟨t, htu⟩, ht⟩ : secH R u))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
