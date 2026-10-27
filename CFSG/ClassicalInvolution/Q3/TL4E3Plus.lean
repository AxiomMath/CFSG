module

public import CFSG.ClassicalInvolution.Q3.TL4E3Split
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

namespace E3

variable {Y : Type} [Group Y] [Finite Y]

noncomputable abbrev secT {R : Subgroup Y} {t u : Y}
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) : SecQ R u :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩

noncomputable abbrev secΩ (R : Subgroup Y) (u : Y) : Set (Subgroup (SecQ R u)) :=
  CoreAssembly.conjClass (tightCore (secR R u))

end E3

section Cit3


structure E3Frame (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) (J : Subgroup Y) (u : Y) : Prop where
  large : TightLargeHypR 3 n Y R S t
  conn : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  sep : TC.SepHyp (CoreAssembly.conjClass (tightCore R))
  alpha : TightSepAlpha R t
  maxAdj : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J
  inv : IsUniqueInvolution J u
  plus : TightBelowRPlus 3 n

@[expose] def TightE3Z2F (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) →
        TightInO2 (E3.secT htu ht)

@[expose] def TightE3S3F (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        TightInO2 (E3.secT htu ht)

@[expose] def TightE3E4F (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      ¬ TightEdgeless (secR R u) → TightInO2 (E3.secT htu ht)

@[expose] def TightE3Z2Step (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → TightE3Z2R 3 n

@[expose] def TightE3S3Step (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → TightE3S3R 3 n

@[expose] def TightE3E4Step (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → TightE3E4R 3 n

theorem tightE3Z2Step_of_F {n : ℕ} (h : TightE3Z2F n) : TightE3Z2Step n :=
  fun hP Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge hmu =>
    h Y R S t J u ⟨hL, hcn, hsp, hα, hJ, hu, hP⟩ htu ht Sb hex hedge hmu

theorem tightE3S3Step_of_F {n : ℕ} (h : TightE3S3F n) : TightE3S3Step n :=
  fun hP Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge hmu =>
    h Y R S t J u ⟨hL, hcn, hsp, hα, hJ, hu, hP⟩ htu ht Sb hex hedge hmu

theorem tightE3E4Step_of_F {n : ℕ} (h : TightE3E4F n) : TightE3E4Step n :=
  fun hP Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge =>
    h Y R S t J u ⟨hL, hcn, hsp, hα, hJ, hu, hP⟩ htu ht Sb hex hedge

theorem tightE3LeafR'_of_steps {n : ℕ} (hZ2 : TightE3Z2Step n) (hS3 : TightE3S3Step n)
    (hE4 : TightE3E4Step n) (hP : TightBelowRPlus 3 n) : TightE3LeafR' 3 n :=
  tightE3LeafR'_of_parts (hZ2 hP) (hS3 hP) (hE4 hP)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
