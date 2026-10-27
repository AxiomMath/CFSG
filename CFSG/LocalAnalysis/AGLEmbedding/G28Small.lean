module

public import CFSG.LocalAnalysis.AGLEmbedding.G28Defs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCenterElt
public import CFSG.LocalAnalysis.AGLEmbedding.G28SmallAux
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section CaseTwo

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G} {z : G}

theorem D1G28Data.small_T (h : D1G28Data P M H R z) :
    Subgroup.zpowers z ⊔ GLBPrimeCore 3 H ≤ M ∧ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H ≤ H ∧
      pCoreOf 2 M ≤ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H ∧
      ∀ B : Subgroup G, B ≤ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H → IsPGroup 3 B →
        Nat.card B ≤ 3 := by
  have h3 := h.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzM : z ∈ M := h3.le_M h.z_mem
  have hzH : z ∈ H := h3.le_H h.z_mem
  have hzle : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.mpr hzH
  have hTH : Subgroup.zpowers z ⊔ GLBPrimeCore 3 H ≤ H := sup_le hzle (glbPrimeCore_le 3 H)
  refine ⟨sup_le (Subgroup.zpowers_le.mpr hzM) h3.primeCore_le, hTH, ?_, fun B hBT hB => ?_⟩
  · exact (h3.twoCore_M_le h3.twoCore_inf).trans ((pCoreOf_le_glbPrimeCore Nat.prime_two
      (by norm_num) H).trans le_sup_right)
  · have := card_le_of_le_sup_glbPrimeCore hzle (hBT.trans hTH) hB hBT
    rwa [Nat.card_zpowers, h.z_order] at this

theorem D1G28Data.mem_Pi (h : D1G28Data P M H R z) (hB3 : StmtBlockThree) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    H ⊓ M ≤ Subgroup.normalizer (((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L : Subgroup G) : Set G) ∧
    ∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧
      (∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ pCoreOf 2 M) ∧ y ∈ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L := by
  have h3 := h.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  refine ⟨(le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
    Subgroup.inf_normalizer_le_normalizer_inf, ?_⟩
  obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hl, hlQ⟩ := hB3 h3 hL
  have hyK : y ∈ H ⊓ M := hKeq ▸ ⟨hL.le hyL, hyS⟩
  have hyE : y ∈ blockClosure M (H ⊓ M) L :=
    Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
      (Subgroup.mem_iSup_of_mem (H ⊓ M).one_mem ⟨y, hyL, by simp⟩))
  exact ⟨y, hyL, hy3, ⟨l, hl, hlQ⟩, hyK, hyE⟩

theorem D1G28Data.barM_conj_eq (h : D1G28Data P M H R z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hPi : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H)
    {k : G} (hk : k ∈ H ⊓ M) : barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L := by
  obtain ⟨hTM, -, hQT, hT3⟩ := h.small_T
  obtain ⟨hN, y, hyL, hy3, hyl, hyPi⟩ := h.mem_Pi hB3 hL
  have hky : k * y * k⁻¹ ∈ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L :=
    (Subgroup.mem_normalizer_iff.mp (hN hk) y).mp hyPi
  exact barM_conj_eq_of_small hL.toIsTwoPrimeComponent hyL hy3 hyl hk.2 hTM hQT (hPi hyPi)
    (hPi hky) hT3

theorem D1G28Data.le_normalizer_block (h : D1G28Data P M H R z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hPi : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H) :
    R ≤ Subgroup.normalizer (L : Set G) := by
  have h3 := h.ph3
  refine hL.toIsTwoPrimeComponent.le_normalizer ?_ h3.le_M
  rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
  have hrK : r ∈ H ⊓ M := h3.le_inf (Subgroup.mem_subgroupOf.mp hr)
  have heq := h.barM_conj_eq hB3 hL hPi hrK
  rw [barM_map_conj hrM] at heq
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem D1G28Data.inf_blockCentralizer_eq_bot (h : D1G28Data P M H R z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hPi : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H) :
    R ⊓ blockCentralizer M L = ⊥ := by
  have h3 := h.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTM, -, hQT, hT3⟩ := h.small_T
  obtain ⟨-, y, hyL, hy3, hyl, hyPi⟩ := h.mem_Pi hB3 hL
  have hRL := h.le_normalizer_block hB3 hL hPi
  by_contra hne
  obtain ⟨w, hwC, hwZ, hw1⟩ := exists_mem_inf_centerOf h3.isPGroup_R (inf_le_left :
    R ⊓ blockCentralizer M L ≤ R) (fun r hr => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hr, mem_normalizer_blockCentralizer (h3.le_M hr) (hRL hr)⟩) hne
  have hwz : w ∈ Subgroup.zpowers z := h.center_le hwZ
  have hzw : z ∈ Subgroup.zpowers w := by
    have hle : Subgroup.zpowers w ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hwz
    have hcz : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, h.z_order]
    have hcw : Nat.card (Subgroup.zpowers w) ≠ 1 := by
      rw [Nat.card_zpowers]
      exact fun h1 => hw1 (orderOf_eq_one_iff.mp h1)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcz] at hdvd
    have hc3 : Nat.card (Subgroup.zpowers w) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact absurd h1 hcw
      · exact h1
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hc3])
    exact heq ▸ Subgroup.mem_zpowers z
  have hzC : z ∈ blockCentralizer M L := (Subgroup.zpowers_le.mpr hwC.2) hzw
  have hzM : z ∈ M := h3.le_M h.z_mem
  have hzCb := (mem_blockCentralizer_iff ⟨z, hzM⟩).mp hzC
  have hz3 : IsPGroup 3 (Subgroup.zpowers z) := isPGroup_zpowers_of_pow_prime_pow_eq_one
    (n := 1) (by rw [pow_one, ← h.z_order]; exact pow_orderOf_eq_one z)
  have hzb1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ≠ 1 := by
    intro h1
    have hzQ := coe_mem_pCoreOf_two_of_mk_eq_one _ h1
    have := eq_one_of_mem_pCoreOf_two Nat.prime_three (by norm_num) h3.isPGroup_R h.z_mem hzQ
    have hzo := h.z_order
    rw [this, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  exact false_of_mem_centralizer_of_small hL.toIsTwoPrimeComponent hyL hy3 hyl hzM hz3 hzCb hzb1
    hTM hQT (hPi hyPi) (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) hT3

end CaseTwo

end CFSG.AGLEmbedding
