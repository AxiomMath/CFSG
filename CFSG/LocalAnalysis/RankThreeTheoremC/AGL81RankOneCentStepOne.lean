module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteen
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepZero
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem mul_ne_of_mem_sup {p : ℕ} {y a b : G} (hnc : a * y ≠ y * a)
    (hEb : Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b =
      Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers a) : b * y ≠ y * b := by
  intro hby
  apply hnc
  have hle : Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact pow_mul_comm' y p
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hby
  have ha' : a ∈ Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b := by
    rw [hEb]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha')

theorem kbar_ne_bot_of_not_le (hS : Setting G) (h1014 : AGL81TenFourteenCentCfg G)
    (h10143 : AGL81TenFourteenThreeCfgGen G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    (hKs : IsCaseTwoGroup p ↥K) (hKn : K.Normal) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (hpJ : p ∣ Nat.card (jZero H L)) {W : Subgroup G} {y a z : G} (hWH : W ≤ H ⊓ M)
    (hzW : z ∈ W ⊓ d1PlusCore p H K) (hzo : orderOf z = p) (hzc : ∀ w ∈ W, w * z = z * w)
    (hyl : d1LiftX p H W K = Subgroup.zpowers y) (hyo : orderOf y = p ^ 2) (haW : a ∈ W)
    (hao : orderOf a = p) (haout : a ∉ hyp111Pre p H K ⊔ d1PlusCore p H K)
    (hnc : a * y ≠ y * a) (hZL : ⁅Subgroup.zpowers (y ^ p), L⁆ ≤ pCoreOf 2 L) {b : G}
    (hb : b ∈ Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers a)
    (hbZ : b ∉ Subgroup.zpowers (y ^ p))
    (hC : ¬ Subgroup.centralizer ({b} : Set G) ≤ M) :
    d1KBar p M (Subgroup.centralizer ({b} : Set G)) ≠ ⊥ := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup ↥K := RankOneSylow.isSimpleGroup_of_isCaseTwoGroup hKs
  have hWH' : W ≤ H := hWH.trans inf_le_left
  have hWM : W ≤ M := hWH.trans inf_le_right
  obtain ⟨hbo, hEb, hE', hE'c, hE'W⟩ := elemAbelian_triple hKn hWH' hzW.1 hzW.2 hzo hzc hyl hyo
    haW hao haout hb hbZ
  set E' := Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers z with hE'def
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  have hbE' : b ∈ E' := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hZE' : Subgroup.zpowers (y ^ p) ≤ E' := le_sup_left.trans le_sup_left
  have hE'M : E' ≤ M := hE'W.trans hWM
  have hE'p : IsPGroup p E' := IsPGroup.of_card (n := 3) hE'c
  have hE'C : E' ≤ C := by
    intro e he
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hE'.1.is_comm.comm ⟨b, hbE'⟩ ⟨e, he⟩)).symm
  have hQ : IsAGLQ p M E' :=
    ⟨hE'M, hE'p, Or.inl (by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE' hE'c)⟩
  have hT := h1014 hS p P M H Q K hd b (hE'M hbE') hbo hC ⟨E', hE'C, hQ⟩
  intro hbot
  obtain ⟨B, hE'B, hBCM, hBp, ⟨S, hSB⟩, hB3, -⟩ :=
    exists_sylow_of_elemAbelian hS hd (C := C) le_rfl (le_inf hE'C hE'M) hE'p hE' hE'c
  have hBsylC : CFSG.ABGLocalTools.IsSylowOf p B C := ⟨S, hSB⟩
  have hcyc := hT.cyclic hbot B (hBsylC.of_le hBCM inf_le_left) hB3.ge
  have hbW : b ∈ W := hE'W hbE'
  have hbp : b ^ p = 1 := hbo ▸ pow_orderOf_eq_one b
  have hconj : b * y * b⁻¹ ∈ Subgroup.zpowers y := by
    rw [← hyl]
    exact RankOne.conj_mem_d1LiftX hKn hbW (hWH' hbW) (hyl ▸ Subgroup.mem_zpowers y)
  obtain ⟨hcZ, -⟩ := RankOne.conj_pow_facts hyo hbp hconj
  have hc1 : b * y * b⁻¹ * y⁻¹ ≠ 1 := by
    intro h
    apply mul_ne_of_mem_sup hnc hEb
    calc b * y = (b * y * b⁻¹ * y⁻¹) * y * b := by group
      _ = y * b := by rw [h, one_mul]
  have hLM : L ≤ M := hL.le
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hyM : y ∈ M := hWM (d1LiftX_le p H W K (hyl ▸ Subgroup.mem_zpowers y))
  have hpL : p ∣ Nat.card L :=
    hpJ.trans (Subgroup.card_dvd_of_le ((jZero_le H L).trans inf_le_right))
  have hcL : b ∈ L → b * y * b⁻¹ * y⁻¹ ∈ L := by
    intro hbL
    have : y * b⁻¹ * y⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hML hyM) b⁻¹).mp (L.inv_mem hbL)
    have h := L.mul_mem hbL this
    simpa [mul_assoc] using h
  have hcT : ∀ l ∈ L, (b * y * b⁻¹ * y⁻¹) * l * (b * y * b⁻¹ * y⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
    fun l hl => (Subgroup.commutator_le.mp hZL) _ hcZ l hl
  have hbL := commutator_le_of_cyclic_center hBsylC (hBCM.trans inf_le_right) hcyc
    (hE'B hbE') hbo hLM hML hpL hc1 (hE'B (hZE' hcZ)) hcL hcT
  exact h10143 hS p P M H Q K hd L hL hpL b (hE'M hbE') hbo hC ⟨E', hE'C, hQ⟩ hbL

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
