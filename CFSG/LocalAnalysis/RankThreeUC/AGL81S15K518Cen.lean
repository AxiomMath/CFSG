module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518C
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518Par
import CFSG.LieType.SeitzGeneration.ExcPlanePair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbedding
  CFSG.Open

variable {X : Type} [Group X] [Finite X]

theorem orderOf_ne_of_classical (hG : KFactChevGenCentre) {T T₁ T₂ L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hg : IsGNPair T T₁ T₂)
    (hpar : GNParabolic T T₁ T₂) (hY : GNYComponent T T₁ T₂ Ls) (hL : LiftOf T L Ls)
    (hcl : IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : mN T₁ p ≤ 1) : ∀ c ∈ L ⊓ gnC T, orderOf c ≠ p := by
  intro c hc hco
  obtain ⟨hzZ, hzo⟩ := mk_mem_center_of_mem_inf hX hY.1 hL hp hp2 hc hco
  have hpZ := dvd_card_center_of_mem_inf hX hY.1 hL hp hp2 hc hco
  have hcov : ParabolicCover T T₁ T₂ Ls := fun P hP =>
    hpar Ls hY.1 (isChevTwo_of_classicalTwoOrG2 hcl) P hP
  obtain ⟨l, hl, hlo, hlZ, hlA⟩ := exists_mem_lift_of_dvd_center hG hX hY hL hcl hcov hp hp2 hpZ
  have hCN := gnC_le_normalizer_of_isGNPair hg
  have hlN : l ∈ Subgroup.normalizer (T₁ : Set X) := by
    obtain ⟨n, hn, hnl⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hlA).1
    have hc' : n⁻¹ * l ∈ gnC T := QuotientGroup.eq.1 hnl
    have e : l = n * (n⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem _ hn (hCN hc')
  set ψ := QuotientGroup.mk' (CFSG.pCore 2 X) with hψ
  have hzN : ψ c ∈ (Subgroup.normalizer (T₁ : Set X)).map ψ :=
    ⟨c, hCN (Subgroup.mem_inf.1 hc).2, rfl⟩
  have hyN : ψ l ∈ (Subgroup.normalizer (T₁ : Set X)).map ψ := ⟨l, hlN, rfl⟩
  have hcomm : Commute (ψ c) (ψ l) := by
    obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.1 hzZ
    have h1 := Subgroup.mem_center_iff.1 hz ⟨ψ l, ⟨l, hl, rfl⟩⟩
    rw [← hzc]
    exact (congrArg Subtype.val h1).symm
  have hind : ψ l ∉ Subgroup.zpowers (ψ c) := fun h => hlZ ((Subgroup.zpowers_le.2 hzZ) h)
  have hzp : ψ c ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hyp : ψ l ^ p = 1 := by rw [← hlo]; exact pow_orderOf_eq_one _
  have hE := CFSG.LieType.SeitzGeneration.isElemAbelian_closure_pair (p := p) hcomm hzp hyp
  have hcard := CFSG.LieType.SeitzGeneration.card_closure_pair_sq hp hcomm hzo hlo hind
  have hEA : Subgroup.closure ({ψ c, ψ l} : Set (X ⧸ CFSG.pCore 2 X)) ≤
      (Subgroup.normalizer (T₁ : Set X)).map ψ := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hzN
    · exact hyN
  have h2 := CFSG.SectionRank.le_pRank hp.one_lt hEA hE hcard
  have h3 := two_le_pRank_of_map ψ hp hp2 _ h2
  have hN' : CFSG.Open.pRank p (Subgroup.normalizer (T₁ : Set X)) ≤ 1 := hN
  omega

theorem not_dvd_card_gnC_of_lift (hG : KFactChevGenCentre) (hKSMAlt : KSMAlt)
    {T T₁ T₂ L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hY : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (h₁ : mS T T₁ p Ls = 1) (h₂ : mS T T₂ p Ls = 1) (hN₁ : mN T₁ p = 1) :
    ¬ p ∣ Nat.card (gnC T) := by
  have hLC : ∀ c ∈ L ⊓ gnC T, orderOf c ≠ p := by
    rcases (hg.shape Ls hY).2 with ⟨hcl, -⟩ | ⟨n, hn, e⟩
    · exact orderOf_ne_of_classical hG hX hg.pair hg.parabolic hY hL hcl hp hp2 hN₁.le
    · exact orderOf_ne_of_alt hKSMAlt hX hg.alt7 hY.1 hinv hL hn e hp hp2 h₁ h₂
  have hA : p ∣ Nat.card (gnA T T₁ Ls) := by
    obtain ⟨E, hEA, -, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (gnA T T₁ Ls)
    have h1 : CFSG.Open.pRank p (gnA T T₁ Ls) = 1 := h₁
    rw [h1, pow_one] at hEc
    exact hEc ▸ Subgroup.card_dvd_of_le hEA
  exact not_dvd_card_gnC_of_inf hg.pair hL hp hp2 hA hN₁.le hLC

end CFSG.LocalAnalysis.RankThreeUC.S15
