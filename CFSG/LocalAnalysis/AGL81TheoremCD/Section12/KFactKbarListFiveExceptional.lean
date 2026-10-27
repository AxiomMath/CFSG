module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveTransport
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
import CFSG.RankThree.PartTwo.Sec4.Item49OddChar
import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusSuzukiModelGeneral
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TitsP3NoElemAbelian
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LieType.Simplicity.TitsModel
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveCore
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

open CFSG.Open CFSG.Blueprint Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4.RonanK429

section Chevalley


theorem false_of_g2_prime {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* S) (hK : ChevalleyExceptionalModel K .G2 p 1)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_g2_simplicity K p 1 hK).2
  obtain ⟨F, instF, instFin, hF, ⟨a⟩⟩ := Sec4.exists_mulEquiv_adjointGroup_G2 hK
  let ψ := (equiv_of_centerQuotient hq e).symm.trans a
  have hFp : Nat.card F = p := by simpa using hF
  have h3 : ¬ 3 ∣ Nat.card F := by
    rw [hFp]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  have hno : NoE27 (Chevalley.adjointGroup Chevalley.Tag.G2 F) := by
    intro D hD
    have h9 := CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2
      F h3 D hD.1
    rw [hD.2] at h9
    norm_num at h9
  have hout := Sec4.Item49OddChar.not_three_dvd_card_outer_of_mulEquiv a.symm
    (Sec4.Item49OddChar.not_three_dvd_card_outer_g2 (by omega) hK)
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Chevalley.Tag.G2) (K := F)
  exact (AutNoE27.of_mulEquiv ψ (autNoE27_of_noE27 hout hZ hno)) E ⟨hE, hc⟩

section Tits


theorem false_of_tits {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) (hK : ReeTitsModel K .Tits 2 1)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  have : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_tits_simplicity K 2 1 hK).2
  let hv : TauCeti.LieTypeIndex.tits.Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    constructor <;> simp
  let T := CFSG.LieType.SeitzGeneration.Cat ⟨.tits, hv⟩
  have hT : ReeTitsModel T .Tits 2 1 :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_tits_of_index hv (MulEquiv.refl T)
  obtain ⟨a⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1 hK
  obtain ⟨b⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv T 2 1 hT
  let ψ : S ≃* T := ((equiv_of_centerQuotient hq e).symm.trans a).trans b.symm
  have hE' := CFSG.SectionRank.isElemAbelian_map hE (MulAut.congr ψ).toMonoidHom
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.titsNoElemAbelian27 hv
    (E.map (MulAut.congr ψ).toMonoidHom) hE'
    (by rw [Subgroup.card_map_of_injective (MulAut.congr ψ).injective, hc])

end Tits

end Chevalley

section Suzuki


theorem false_of_suzuki {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) (hK : SuzukiModel K 2 5)
    {Y V W₁ W₂ W₃ : Subgroup (MulAut S)} {t₁ t₂ t₃ : MulAut S}
    (hcfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hV : V ≤ Y)
    (ht₁ : t₁ ∈ Y) (ht₂ : t₂ ∈ Y) (ht₃ : t₃ ∈ Y) : False := by
  have : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_2b2_simplicity K 2 5 hK).2
  obtain ⟨-, m, hm, F, instF, instFin, hf, hF, ⟨a⟩⟩ := hK
  let ψ := (equiv_of_centerQuotient hq e).symm.trans a
  have hnone := CFSG.LocalAnalysis.GLTheoremA.suzukiModel_no_order_three_general m hm
    (by simpa [hf] using hF)
  have hW₁V : W₁ ≤ V := hcfg.join ▸ le_sup_left.trans le_sup_left
  have hW₁ : Nontrivial W₁ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcfg.card₁]; norm_num)
  have : Nontrivial W₁ := hW₁
  obtain ⟨w, hw1⟩ := exists_ne (1 : W₁)
  let α : MulAut S := w
  have hα : α ∈ W₁ := w.2
  have hd : α ∈ commutator (MulAut S) := by
    have hcomm := hcfg.le_commutator hV ht₁ ht₂ ht₃ (hW₁V hα)
    exact Subgroup.commutator_mono le_top le_top hcomm
  refine hnone ⟨MulAut.congr ψ α, ?_, ?_, ?_⟩
  · exact commutator_le_innAutDerived _ (map_mem_commutator_mulAut (MulAut.congr ψ).toMonoidHom hd)
  · rw [← map_pow, hcfg.elem.2 α (hW₁V hα), map_one]
  · intro h
    exact hw1 (Subtype.ext ((MulAut.congr ψ).injective (h.trans (map_one _).symm)))

end Suzuki

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

end
