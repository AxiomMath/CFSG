module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Kind
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate19953
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T10
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)
open CFSG.StandardType (markTag markRank markDeg)

private theorem lieModel_of_unTwo {R : Type} [Group R]
    (h : catalogIs R S9.isU5two ∨ catalogIs R S9.isU6two) :
    ∃ r, (r = 4 ∨ r = 5) ∧ CFSG.Blueprint.LieModel R .PSU (r + 1) 2 1 := by
  rcases h with h | h
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
    cases d <;> try exact hP.elim
    rename_i r q
    rcases r with _ | _ | _ | _ | _ | r <;> try exact hP.elim
    have hq : q.card = 2 := hP
    obtain ⟨h1, h1'⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    have hm := CFSG.Models.LieModel.toBlueprint (by decide) (lieModel_twistedA' 4 q hv e)
    rw [h1, h1'] at hm
    exact ⟨4, Or.inl rfl, hm⟩
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
    cases d <;> try exact hP.elim
    rename_i r q
    rcases r with _ | _ | _ | _ | _ | _ | r <;> try exact hP.elim
    have hq : q.card = 2 := hP
    obtain ⟨h1, h1'⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    have hm := CFSG.Models.LieModel.toBlueprint (by decide) (lieModel_twistedA' 5 q hv e)
    rw [h1, h1'] at hm
    exact ⟨5, Or.inr rfl, hm⟩

private theorem label_eq_of_psu {lab : GLALabel} {r : ℕ} (hr : 4 ≤ r)
    (ht : markTag lab = .PSU) (hrk : markRank lab = r + 1) (hf : markDeg lab = 1) :
    lab = ⟨.twA, r, 1⟩ := by
  obtain ⟨t, k, n⟩ := lab
  by_cases h3 : k = 3 <;> by_cases h2 : k = 2 <;> cases t <;>
    simp_all [markTag, markRank, markDeg] <;> omega

private theorem label_eq_of_canon {labK : GLALabel} {r : ℕ} (hr : 4 ≤ r)
    (hn : (canonLabel labK).n = 3 * (canonLabel ⟨.twA, r, 1⟩).n)
    (htag : (canonLabel labK).tag = (canonLabel ⟨.twA, r, 1⟩).tag)
    (hrank : (canonLabel labK).rank = (canonLabel ⟨.twA, r, 1⟩).rank) :
    labK = ⟨.twA, r, 3⟩ := by
  obtain ⟨t, k, n⟩ := labK
  by_cases h3 : k = 3 <;> by_cases h2 : k = 2 <;> cases t <;> simp_all [canonLabel] <;> omega


theorem exists_label_of_fieldOn_unTwo {G : Type} [Group G] [Finite G] {X S : Subgroup G} {b : G}
    (hS : GLAPComponent 3 X S) (hF : FieldOn 3 b S) (hb3 : b ^ 3 = 1) (hI : Ipart 3 S b ≠ ⊥)
    (hty : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU5two ∨
      catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU6two) :
    ∃ labK : GLALabel, FieldKind (PSimple 3 S) labK (indAut 3 S b hF.1) ∧
      (labK = ⟨.twA, 4, 3⟩ ∨ labK = ⟨.twA, 5, 3⟩) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp3 hS
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨labK, -, hnot, hkind⟩ := S265F3.fieldKind_of_fieldOn hp3 (by decide) hq hF
  have hcore := FR.coreSub_of_fieldOn hp3 (by decide) FR.Res.smallDatum_holds
    (FR.Res.twF4Core_holds hp3 (by decide)) hF (FR.exists_perfect_of_ipart hp3 hF.1 hb3 hI)
  rw [FR.fixSub_indAut hF.1] at hcore
  obtain ⟨E, hEC, hE, hna, hperf, -, -⟩ := hcore
  obtain ⟨J₀, hJ₀, hIeq, hTE⟩ := FR.ipart_single hp3 hF.1 hb3 hE hEC hperf hI
  subst hTE
  have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hb3
  have hEc := glaPComponent_chevTransfer hp3 hF.1 hap hJ₀
  obtain ⟨e₁⟩ := nonempty_pSimple_equiv_chevTransfer hp3 hF.1 hap hJ₀
  obtain ⟨e₂⟩ := FR.nonempty_pSimple_equiv_of_simple hp3 hE hna hEc
  haveI := hE
  obtain ⟨u, v, huv⟩ := hna
  have hZE : Subgroup.center ↥(chevTransfer 3 S J₀) = ⊥ := FR.center_eq_bot_of_simple_nonab huv
  have hEtop : commutator ↥(chevTransfer 3 S J₀) = ⊤ := by
    apply Subgroup.map_injective (chevTransfer 3 S J₀).subtype_injective
    rw [map_commutator_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      glaPComponent_perfect hEc]
  have hfix : fixSubgroup (indAut 3 S b hF.1) = fixSubgroup (chevAut 3 S ⟨b, hF.1⟩) := by
    have h : indAut 3 S b hF.1 = (chevAut 3 S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h]
    ext y
    rw [mem_fixSubgroup, mem_fixSubgroup]
    constructor
    · intro hy
      calc chevAut 3 S ⟨b, hF.1⟩ y
          = chevAut 3 S ⟨b, hF.1⟩ ((chevAut 3 S ⟨b, hF.1⟩)⁻¹ y) := by rw [hy]
        _ = y := MulAut.apply_inv_self _ _ _
    · intro hy
      calc (chevAut 3 S ⟨b, hF.1⟩)⁻¹ y
          = (chevAut 3 S ⟨b, hF.1⟩)⁻¹ (chevAut 3 S ⟨b, hF.1⟩ y) := by rw [hy]
        _ = y := MulAut.inv_apply_self _ _ _
  have hEc' : GLAPComponent 3 (fixSubgroup (indAut 3 S b hF.1)) (chevTransfer 3 S J₀) := by
    rw [hfix]
    exact hEc
  have hα3 : indAut 3 S b hF.1 ^ 3 = 1 :=
    chevAut_pow_eq_one 3 S (Subgroup.inv_mem _ hF.1) (by rw [inv_pow, hb3, inv_one])
  rw [hIeq] at hty
  obtain ⟨r, hr, hm⟩ := lieModel_of_unTwo hty
  let eZ : ↥(chevTransfer 3 S J₀) ≃*
      ↥(chevTransfer 3 S J₀) ⧸ Subgroup.center ↥(chevTransfer 3 S J₀) :=
    ((QuotientGroup.quotientMulEquivOfEq hZE).trans QuotientGroup.quotientBot).symm
  obtain ⟨-, labJ, hlabJ, hrawJ⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hEtop
      (CFSG.Blueprint.LieModel.of_mulEquiv ((e₁.trans e₂).trans eZ) hm)
  obtain ⟨_, _, _, _, -, -, -, htJ, hrJ, -, hfJ⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hrawJ
  have hlJ : Y10F.HasLabel ↥(chevTransfer 3 S J₀) (fun l => l = labJ) :=
    ⟨hEtop, labJ, hlabJ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hrawJ⟩
  have h4 : 4 ≤ r := by omega
  obtain rfl := label_eq_of_psu h4 htJ hrJ hfJ
  obtain ⟨hn, htag, hrank⟩ := T158Inn.t158Inn_fldPiece (PSimple 3 S) 3 (indAut 3 S b hF.1)
    (chevTransfer 3 S J₀) labK _ hp3 (by decide) hcen hkind hnot hα3 hlJ hEc'
  have hK := label_eq_of_canon h4 hn htag hrank
  refine ⟨labK, hkind, ?_⟩
  rcases hr with rfl | rfl
  · exact Or.inl hK
  · exact Or.inr hK

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
