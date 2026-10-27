module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64iiDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B2Hyp
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiPx
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSNotDelta

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

theorem kFact64iiThree_apply (h : KFact64iiThree) {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    {H S : Subgroup G} (hyp : Hyp P M x z H S) (hΩ : OmegaLe x z H) :
    (∃ K : Subgroup G, PComp 3 ((M ⊓ H) ⊔ rankThreePrimeCore 3 H) H K z) ∧
      ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
        ¬ CFSG.HasNormalPComplement 3 ↥(H ⊓ centralizer ({b} : Set G)) := by
  have hS := hyp.setting
  have hsit := hyp.situation
  have hx := hyp.point
  have hz := hyp.central
  have hopt := hyp.optimal
  have : IsSimpleGroup G := hS.simple
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHtop : H ≠ ⊤ := twoLocal_ne_top hS.nonab H hopt.ext.pair.isTwoLocal
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx.pow_eq_one hx.ne_one
  have hzo : orderOf z = 3 := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hxnz : x ∉ zpowers z := by
    intro hxZ
    have h1 := Subgroup.card_le_of_le
      (sup_le (zpowers_le.2 hxZ) le_rfl : zpowers x ⊔ zpowers z ≤ zpowers z)
    rw [hpl.card_eq, Nat.card_zpowers, hzo] at h1
    norm_num at h1
  have hB3 : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hB3' : IsPGroup 3 ↥((zpowers x ⊔ zpowers z).subgroupOf H) :=
    hB3.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q H := ⟨Q', rfl⟩
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := by
    intro b hb
    have hbH : (⟨b, hBH hb⟩ : H) ∈ (zpowers x ⊔ zpowers z).subgroupOf H := hb
    exact ⟨⟨b, hBH hb⟩, hQ' hbH, rfl⟩
  have hQM : Q ≤ M := hopt.sylow_le Q hQsyl.isPGroup hQsyl.le hBQ
  have hΩQ := hΩ Q hQsyl.le hQsyl.isPGroup hBQ
  have hfr : x ∉ (frattini ↥Q).map Q.subtype := x_not_mem_frattini3 hS hsit hx hQsyl.isPGroup
  have hwc : ∀ g ∈ H, g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z → g * z * g⁻¹ ∈ zpowers z :=
    fun g _ hg => conj_mem_zpowers hS hsit hx hz hg
  have hNZ : normalizer (zpowers z : Set G) ⊓ H ≤ M ⊓ H := fun g hg =>
    ⟨normalizer_zpowers_le_of_largeObstruction_empty hS hsit.mem_sigmaA hsit.isCoreMaxLocal
      hsit.largeObstruction_empty hz.mem hz.centralizes hz.ne_one hz.pow_eq_one hg.1, hg.2⟩
  have hcover : ¬ H ≤ (M ⊓ H) ⊔ rankThreePrimeCore 3 H := fun hle =>
    hopt.ext.pair.not_le (hle.trans (sup_le inf_le_left hyp.core_le))
  exact h G H Q (M ⊓ H) x z hKH hxo hzo hxz hxnz hQsyl hBQ hΩQ
    hfr hwc (le_inf hQM hQsyl.le) inf_le_right hNZ hcover

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B2

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem pieceCompOmegaThree_holds : PieceCompOmegaThree := by
  intro h64 G _ _ P M x z H S hyp hΩ _
  obtain ⟨⟨K, hK⟩, -⟩ := P614B2.kFact64iiThree_apply h64 hyp hΩ
  exact ⟨K, hK.le, hK.normal, fun hKM => hK.not_le (le_sup_of_le_left (le_inf hKM hK.le)),
    hK.mem, hK.rank_one, hK.perfect, hK.lt, hK.maximal⟩

theorem pieceNotDeltaThree_holds : PieceNotDeltaThree := by
  intro h64 G _ _ P M x z H S hyp hΩ hnpc
  obtain ⟨-, b, hbB, hbZ, hbN⟩ := P614B2.kFact64iiThree_apply h64 hyp hΩ
  obtain ⟨g, -, hgconj⟩ := exists_mem_normalizer_conj_zpowers hyp.setting hyp.situation
    hyp.point hyp.central hbB hbZ
  exact hbN (RankFourTheoremC.PEmpty.L6LeavesNS.hasNormalPComplement_inf_centralizer hgconj H hnpc)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
