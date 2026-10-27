module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.CGT.PushingUpLit.BHS.ThreeNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (commV ffJ fixV IsSylowIn)
open CFSG.Open (pCoreOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.CGT.PushingUpLit.BHS

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem card_eq_three_of_isAlt_three {L : Subgroup (MulAut W)} (hL : IsAlt ↥L 3) :
    Nat.card ↥L = 3 := by
  obtain ⟨e⟩ := hL
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem le_pCoreOf_three_of_isAlt_three {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLsn : (L.subgroupOf Y).IsSubnormal) (hL : IsAlt ↥L 3) :
    L ≤ pCoreOf 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal
    ((CFSG.Open.IsSubnormal.iff_subgroupOf hLY).2 hLsn)
    (IsPGroup.of_card (n := 1) (by rw [card_eq_three_of_isAlt_three hL, pow_one]))

private theorem ffJ_le_normalizer_of_isAlt_three (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact37Hyp Y S L) (hL : IsAlt ↥L 3) :
    ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  unfold GomiFact37Hyp at h
  obtain ⟨-, hSyl, hLY, hLsn, -, hcomm4⟩ := h
  have hLcard := card_eq_three_of_isAlt_three hL
  have hLN : L ≤ pCoreOf 3 Y := le_pCoreOf_three_of_isAlt_three hLY hLsn hL
  have hN3 : IsPGroup 3 (pCoreOf 3 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := MulAut W) 3 Y
  have hYN : Y ≤ Subgroup.normalizer (pCoreOf 3 Y : Set (MulAut W)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 Y
  refine iSup_le fun A => iSup_le fun hA => ?_
  have hAoff : IsOff A := ⟨le_top, hA.2⟩
  have hAN : ∀ a ∈ A, ∀ n ∈ pCoreOf 3 Y, a * n * a⁻¹ ∈ pCoreOf 3 Y := by
    intro a ha n hn
    exact (Subgroup.mem_normalizer_iff.mp (hYN (hSyl.le (hA.1 ha))) n).1 hn
  exact offender_le_normalizer_of_card_three hW hAoff hN3 hAN hLN hLcard (hcomm4 hL)

private theorem ne_bot_inf_fixV_ffJ_of_isAlt_three (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact37Hyp Y S L) (hL : IsAlt ↥L 3) :
    commV L ⊓ fixV (ffJ S) ≠ ⊥ := by
  have hffJN := ffJ_le_normalizer_of_isAlt_three hW h hL
  unfold GomiFact37Hyp at h
  obtain ⟨-, hSyl, -, -, -, hcomm4⟩ := h
  have hffJle : ffJ S ≤ S := iSup_le fun A => iSup_le fun hA => hA.1
  have hffJp : IsPGroup 2 ↥(ffJ S) := hSyl.isPGroup.to_le hffJle
  have hpres : ∀ g ∈ ffJ S, ∀ v ∈ commV L, (g : MulAut W) v ∈ commV L :=
    fun g hg v hv => CFSG.Quasithin.commV_apply_mem_of_mem_normalizer (hffJN hg) hv
  let act : MulAction ↥(ffJ S) ↥(commV L) :=
    { smul := fun g v => ⟨(g : MulAut W) (v : W), hpres g g.2 v v.2⟩
      one_smul := fun v => Subtype.ext (MulAut.one_apply W (v : W))
      mul_smul := fun g h v =>
        Subtype.ext (MulAut.mul_apply W (g : MulAut W) (h : MulAut W) (v : W)) }
  have hfix1 : (1 : ↥(commV L)) ∈ MulAction.fixedPoints ↥(ffJ S) ↥(commV L) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (map_one (g : MulAut W))
  have hpdvd : 2 ∣ Nat.card ↥(commV L) := by
    rw [hcomm4 hL]
    norm_num
  obtain ⟨b, hb, hbne⟩ :=
    hffJp.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥(commV L) hpdvd hfix1
  have hbF : (b : W) ∈ commV L ⊓ fixV (ffJ S) := by
    refine Subgroup.mem_inf.2 ⟨b.2, ?_⟩
    rw [CFSG.Quasithin.mem_fixV]
    intro x hx
    exact congrArg Subtype.val ((MulAction.mem_fixedPoints.1 hb) ⟨x, hx⟩)
  intro hbot
  have hb1 : (b : W) ∈ (⊥ : Subgroup W) := hbot ▸ hbF
  exact hbne (Subtype.ext (by simpa using hb1)).symm

theorem gomiCSP_le_normalizer_of_isAlt_three
    (hW : ∀ w : W, w ^ 2 = 1) {Y S L : Subgroup (MulAut W)} (h : GomiFact37Hyp Y S L)
    (hL : IsAlt ↥L 3) : gomiCSP S L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hFne := ne_bot_inf_fixV_ffJ_of_isAlt_three hW h hL
  unfold GomiFact37Hyp at h
  obtain ⟨-, hSyl, hLY, hLsn, -, hcomm4⟩ := h
  have hLcard := card_eq_three_of_isAlt_three hL
  have hLN : L ≤ pCoreOf 3 Y := le_pCoreOf_three_of_isAlt_three hLY hLsn hL
  have hN3 : IsPGroup 3 (pCoreOf 3 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := MulAut W) 3 Y
  have hYN : Y ≤ Subgroup.normalizer (pCoreOf 3 Y : Set (MulAut W)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 Y
  intro s hs
  by_contra hns
  rw [gomiCSP, Subgroup.mem_inf] at hs
  obtain ⟨hsS, hsfix⟩ := hs
  have hsN : ∀ n ∈ pCoreOf 3 Y, s * n * s⁻¹ ∈ pCoreOf 3 Y := by
    intro n hn
    exact (Subgroup.mem_normalizer_iff.mp (hYN (hSyl.le hsS)) n).1 hn
  set L' : Subgroup (MulAut W) := L.map (MulAut.conj s).toMonoidHom with hL'def
  have hL'le : L' ≤ pCoreOf 3 Y := by
    rw [hL'def]
    exact map_conjHom_le hsN hLN
  have hcL' : Nat.card L' = 3 := by
    rw [hL'def]
    exact (card_map_conjHom L s).trans hLcard
  have hW' : Nat.card (commV L') = 4 := by
    rw [hL'def, CFSG.Quasithin.B19.commV_map_conj,
      Subgroup.card_map_of_injective s.injective, hcomm4 hL]
  have hne : L' ≠ L := by
    intro hEq
    exact hns (map_conjHom_eq_iff_mem_normalizer.1 (hL'def ▸ hEq))
  have hdisj : commV L ⊓ commV L' = ⊥ :=
    (conj_three_commute hW hN3 hLN hL'le hLcard hcL' (hcomm4 hL) hW' (Ne.symm hne)).1
  have hFbot : commV L ⊓ fixV (ffJ S) = ⊥ := by
    have hle : commV L ⊓ fixV (ffJ S) ≤ commV L' := by
      intro f hf
      obtain ⟨hfL, hffix⟩ := Subgroup.mem_inf.1 hf
      have hsf : s • f = f := (mem_fixingSubgroup_iff (MulAut W)).1 hsfix f hf
      have hsf' : (s : MulAut W) f = f := by simpa only [MulAut.smul_def] using hsf
      have hmem : (s : MulAut W) f ∈ commV L' := by
        rw [hL'def, CFSG.Quasithin.B19.commV_map_conj]
        exact Subgroup.mem_map_of_mem s.toMonoidHom hfL
      rwa [hsf'] at hmem
    have hle' : commV L ⊓ fixV (ffJ S) ≤ commV L ⊓ commV L' :=
      le_inf inf_le_left hle
    rw [hdisj] at hle'
    exact bot_unique hle'
  exact hFne hFbot

end CFSG.GroupTheory

end
