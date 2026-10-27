module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Lift
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278S
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Cases
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1RedQuot
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
open scoped MatrixGroups

namespace P614K278

theorem nonempty_equiv_psl34 {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {K : Type}
    [Group K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty (K ≃* PSL(3, GaloisField 2 2)) := by
  obtain ⟨q, hq2, hqe, hd'⟩ := hd
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd'
  subst hd'
  obtain ⟨p, f, hp, hf⟩ := q
  simp only at hq2 hqe
  subst hq2 hqe
  exact ⟨e.trans (@CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 ⟨2, 2, hp, hf⟩ ⟨hp⟩ hv)⟩

theorem isSimpleGroup_of_component {X : Type} [Group X] {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hc : center K = ⊥) : IsSimpleGroup K ∧ ⁅K, K⁆ = K := by
  have hs : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  refine ⟨MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm, ?_⟩
  have h1 : commutator K = ⊤ := hK.2.2.1
  have h2 := congrArg (map K.subtype) h1
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

end P614K278

open P614K278

theorem kFact278L34_of (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hC : ∀ (X : Type) [Group X] [Finite X] (R : Sylow 3 X) (A X₀ K B : Subgroup X),
      D2AlmostSimple 3 X R A X₀ K → B ≤ R → IsElemAbelian 3 B → Nat.card B = 9 →
      (∀ g : X, B.map (MulAut.conj g).toMonoidHom ≠ A) →
      ∃ d : TauCeti.ValidLieTypeIndex, IsL34Index d ∧
        Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    KFact278L34 := by
  intro A _ _ X Q B U Y hK hrk hQ hZ hBQ hB hB9 hUQ hU hU9 hBU hwc hYX hYne hU1 hQ2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hQX, hQp, hQs⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hQ
  have hBX : B ≤ X := hBQ.trans hQX
  have hUX : U ≤ X := hUQ.trans hQX
  have hU9' : Nat.card U = 3 ^ 2 := by rw [hU9]; norm_num
  have hB9' : Nat.card B = 3 ^ 2 := by rw [hB9]; norm_num
  have hOY : rankThreePrimeCore 3 X ≤ Y :=
    P64Free.rankThreePrimeCore_le_of_gammaOne_plane hp hUX hU hU9' hU1
  obtain ⟨Qb, hQb⟩ := P64Asm.XBar.exists_sylow hQp.comap_subtype hQs
  have hred := K1Red.reduced hrk hQX hQp hUQ hU hU9 hYX hYne hU1 hQ2 Qb hQb
  have hKX : CFSG.IsKGroup (P64Asm.XBar 3 X) :=
    CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple (hK.quotient _)
  obtain ⟨Kb, h⟩ := k1Core_almostSimple hKX hred
  have hBpl := P64Asm.XBar.plane hp hQX hQp hBQ hB hB9'
  have hBconj := P64Asm.XBar.not_conj hp hBX hUX (hQp.to_le hBQ) (hQp.to_le hUQ) hBU
  have hBR : (B.subgroupOf X).map (P64Asm.XBar.mk 3 X) ≤ Qb := by rw [hQb]; exact hBpl.1
  have hBc : Nat.card ((B.subgroupOf X).map (P64Asm.XBar.mk 3 X)) = 9 := by
    rw [hBpl.2.2]; norm_num
  obtain ⟨d, hd, ⟨e⟩⟩ := hC _ Qb _ _ Kb _ h hBR hBpl.2.1 hBc hBconj
  have := h.normal
  obtain ⟨hKs, hKp⟩ := isSimpleGroup_of_component h.component h.center_eq_bot
  obtain ⟨K, hKX', hKn, hKp', hKlt, hKmax, hKmap, ⟨eK⟩⟩ := exists_lift hKs hKp h.dvd
  have hUK := h.le_of_l34 hO hd ⟨e⟩
  have hY := h.eq_normalizer_of_l34 hI hd ⟨e⟩ hUK
  refine ⟨K, hKX', hKn, hKp', hKlt, hKmax, ?_, ?_, ?_⟩
  ·
    refine le_sup_of_map_sup_eq_top ?_
    rw [hKmap]
    rcases hI d hd _ Kb h.normal h.centralizer_eq_bot ⟨e⟩ _ h.elem h.card_A hUK
        ((Y.subgroupOf X).map (P64Asm.XBar.mk 3 X) ⊔ Kb) (hY ▸ le_sup_left) with h1 | h1
    · exact absurd (hY ▸ h1 ▸ le_sup_right) h.not_le
    · exact h1
  ·
    obtain ⟨e₀⟩ := nonempty_equiv_psl34 hd e
    exact ⟨eK.trans e₀⟩
  ·
    intro S ⟨hSX, hS2, hBS⟩ hSY
    rw [relIndex_eq_card_map hSX]
    refine card_le_two_of_l34 hO hI h hd e hBR hBpl.2.1 hBc (k1Core_ne_of_conj hBconj)
      (hS2.comap_subtype.map _) (P64Asm.XBar.normalizer_map hBS) ?_
    intro htop
    apply hSY
    refine le_antisymm (sup_le hYX hSX) ?_
    have h1 := le_sup_of_map_sup_eq_top htop
    exact h1.trans (sup_le le_rfl (hOY.trans le_sup_left))

section Holds

theorem kFact278L34_holds : KFact278L34 :=
  kFact278L34_of kFactL34Outer kFactL34Inner fun _ _ _ _ _ _ _ _ h hBR hB hBc hconj =>
    exists_l34 h hBR hB hBc hconj

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
