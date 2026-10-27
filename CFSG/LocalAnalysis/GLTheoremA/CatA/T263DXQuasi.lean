module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]

section Quasi

variable {J : Subgroup Ω}

private theorem open_of_native {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native G).2 h

private theorem native_of_open {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    CFSG.IsQuasisimple G :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native G).1 h

theorem glaPPrimeCore_le_center_of_dvd (hp : p.Prime) (hJ : IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpJ : p ∣ Nat.card ↥J := hdvd.trans (Subgroup.card_quotient_dvd_card _)
  refine le_center_of_normal_of_isQuasisimple (open_of_native hJ) (GLAPPrimeCore.normal p ↥J)
    fun h => ?_
  have hc : Nat.Coprime p (Nat.card (CFSG.pPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
  rw [show CFSG.pPrimeCore p ↥J = ⊤ from h, Subgroup.card_top] at hc
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hc hpJ

theorem glaPPrimeCoreOf_le_centralizer_of_dvd (hp : p.Prime) (hJ : IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    GLAPPrimeCoreOf p J ≤ J ⊓ Subgroup.centralizer (J : Set Ω) := by
  have hO := glaPPrimeCore_le_center_of_dvd hp hJ hdvd
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 (show x ∈ (GLAPPrimeCore p ↥J).map J.subtype from hx)
  refine ⟨u.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 (hO hu) ⟨g, hg⟩)

theorem isQuasisimple_pQuot_of_dvd (hp : p.Prime) (hJ : IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) : IsQuasisimple (PQuot p J) :=
  native_of_open (CFSG.ComponentClassification.Quasisimple.central_quotient (open_of_native hJ) _
    (glaPPrimeCore_le_center_of_dvd hp hJ hdvd))

theorem nonempty_pSimple_equiv_of_dvd (hp : p.Prime) (hJ : IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    Nonempty (PSimple p J ≃* ↥J ⧸ Subgroup.center ↥J) := by
  have hO := glaPPrimeCore_le_center_of_dvd hp hJ hdvd
  haveI : Group.IsPerfect ↥J := hJ.1
  have hcenter : (Subgroup.center ↥J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) =
      Subgroup.center (PQuot p J) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (QuotientGroup.mk'_surjective _)
      (by simpa only [QuotientGroup.ker_mk'] using hO)
  exact ⟨(QuotientGroup.congr _ _ (MulEquiv.refl _) (by simpa using hcenter)).symm.trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hO)⟩

private theorem glaMarking_const_of_equiv {A B : Type} [Group A] [Group B]
    (hB : commutator B = ⊤) (e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B)
    (Q : CFSG.Assembly.LargeEvenLabel → Prop)
    (h : GLAMarking A (fun lab _ _ _ _ _ => Q lab)) :
    GLAMarking B (fun lab _ _ _ _ _ => Q lab) := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hB, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hq⟩
  exact ⟨hs, hna, e.symm.trans θ, hq⟩

theorem glaMarking_of_pQuot (hp : p.Prime) (hJ : IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) (Q : CFSG.Assembly.LargeEvenLabel → Prop)
    (h : GLAMarking (PQuot p J) (fun lab _ _ _ _ _ => Q lab)) :
    GLAMarking (↥J) (fun lab _ _ _ _ _ => Q lab) := by
  obtain ⟨e⟩ := nonempty_pSimple_equiv_of_dvd hp hJ hdvd
  exact glaMarking_const_of_equiv hJ.1.commutator_eq_top e Q h

theorem glaPComponent_of_isComponentOf_of_dvd (hp : p.Prime) {X : Subgroup Ω}
    (hJ : IsComponentOf J X) (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    GLAPComponent p X J :=
  S12.glaPComponent_of_quasisimple' hp hJ.2.1 hJ.2.2 hdvd

end Quasi

section Transfer

variable {J K : Subgroup Ω}

theorem isChevSimple_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsChevSimple 2 A) :
    IsChevSimple 2 B := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans f⟩⟩

end Transfer

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
