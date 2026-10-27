module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreRestr
public import CFSG.ClassicalInvolution.Asc77.AscC25J14c
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UTop
public import CFSG.ClassicalInvolution.Uniform.U5Three
public import CFSG.ClassicalInvolution.Asc77.AscC25J1
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Q3.Q3CLApi

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Sect

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25J
open scoped MatrixGroups

structure GenSection {X : Type} [Group X] (Φ : Set (Subgroup X)) : Prop where
  modU : HypOmegaModU (.sl2 3 1) Φ
  hyp : HypOmegaGen Φ
  cls : Q3CL.ClassicalClause Φ
  oddCore : classicalInvolutionOddCore X = ⊥
  gen : omegaGen Φ = ⊤
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}



theorem genSection_layerHull (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (Y : Subgroup G) :
    GenSection (oddQuotientFamily (restrictFamily Ω (layerHull Ω Y))) := by
  set Y₀ := layerHull Ω Y with hY₀
  set N₀ : Subgroup ↥Y₀ := classicalInvolutionOddCore ↥Y₀ with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y₀
  have hΛU : HypOmegaModU (.sl2 3 1) (restrictFamily Ω Y₀) := hypOmegaModU_restrict hΩ Y₀
  have hΛ : HypOmegaGen (restrictFamily Ω Y₀) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛU
  have hΛ'U : HypOmegaModU (.sl2 3 1) (oddQuotientFamily (restrictFamily Ω Y₀)) :=
    hypOmegaModU_oddQuotientFamily hΛU
  have hΛ' : HypOmegaGen (quotFamily (restrictFamily Ω Y₀) N₀) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ'U
  have hΛA : ∀ L ∈ restrictFamily Ω Y₀, AEmpty (restrictFamily Ω Y₀) L := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    exact C25J.aEmpty_restrict_gen (hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ) hLY
      (hA L hL)
  exact
    { modU := hΛ'U
      hyp := hΛ'
      cls := Q3CL.classicalClause_of_modU hΛ'U
      oddCore := CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y₀
      gen := omegaGen_quotFamily_of_gen _ N₀ (omegaGen_restrictFamily_layerHull Y)
      aEmpty := C25J.aEmpty_quotFamily_gen hΛ hΛ' hN₀odd hΛA }

theorem s26_genSection_omegaNbrGen {K : Subgroup G} (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) :
    GenSection (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) := by
  have := genSection_layerHull hΩ hA (omegaNbrGen Ω K)
  rwa [s26_layerHull_omegaNbrGen Ω K] at this

end Layer

section Member


variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

theorem natCard_quot_member (hz : IsClassicalMemberU (.sl2 3 1) L z) :
    Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) = Nat.card SL(2, GaloisField 3 1) := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2Three (by norm_num : (3 : ℕ) ^ 1 = 3)
  rw [Nat.card_congr e.toEquiv, natCard_sl2Three, natCard_sl2_galoisField_three]

theorem natCard_isSylow2In_of_member {Ω : Set (Subgroup Y)} (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    {K P : Subgroup Y} (hK : K ∈ Ω) (hP : IsSylow2In P K) :
    Nat.card P = 2 ^ (Nat.card SL(2, GaloisField 3 1)).factorization 2 := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  rw [natCard_isSylow2In_eq hP, natCard_quot_member hz]

end Member

section Restrict


variable {Y : Type} [Group Y] [Finite Y]

theorem hypOmegaGen_restrict {Ω : Set (Subgroup Y)} (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (X : Subgroup Y) : HypOmegaGen (restrictFamily Ω X) :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (Q3T6.hypOmegaModU_restrict hΩ X)

end Restrict

end CFSG.ClassicalInvolution.Q3.Q3T8.Sect
