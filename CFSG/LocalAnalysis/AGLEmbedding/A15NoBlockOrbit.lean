module

public import CFSG.LocalAnalysis.AGLEmbedding.A15NoBlockOrbitAux
import CFSG.LocalAnalysis.AGLEmbedding.A15OddCore
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section A15

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G} {c : Fin 3 → G}
  {σ τ : G}

theorem D1A15Data.exists_not_le_centralizer (h : D1A15Data P M H R c σ τ)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hUR : U ≤ barM M R) (hU : U ≠ ⊥) :
    ∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
      ¬ U ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  by_contra hcon
  push Not at hcon
  refine hU (eq_bot_iff.mpr fun x hx => ?_)
  obtain ⟨⟨r, hrM⟩, hr, rfl⟩ := hUR hx
  have hr1 := h.eq_one_of_forall_mem_centralizer h84 hD2 (Subgroup.mem_subgroupOf.mp hr)
    fun Lb hLb => hcon Lb hLb hx
  subst hr1
  exact Subgroup.mem_bot.mpr (map_one _)

end A15

theorem stmtA15NoBlockOrbit_of (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hα : KFactThreeOrFiveDvd) (hS : CatalogOuterSolvable) : StmtA15NoBlockOrbit := by
  intro G _ _ P M H R c σ τ h hall
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Rb := barM M R with hRbdef
  have hbad : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      ¬ Rb ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ∃ L : Subgroup G, IsTwoPrimeComponent M L ∧ barM M L = Lb ∧ L ≤ H ⊓ M ∧
        ¬ L ≤ GLBPrimeCore 5 H := by
    intro Lb hLb hRC
    obtain ⟨L, hL2, rfl, hL⟩ := h3.exists_weakSBlock_or_le_inf hLb
    rcases hL with hw | hLK
    · exact (hRC (h.barM_le_centralizer_block hB3 hb h84 h86 hD2 hα hS hw (hall L hw))).elim
    · refine ⟨L, hL2, rfl, hLK, fun hLN => hRC (h.barM_le_centralizer_of_coprime hB3 hα hS hLb ?_)⟩
      have hdvd : Nat.card (barM M L) ∣ Nat.card L := by
        have := Subgroup.card_map_dvd (L.subgroupOf M) mk
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
      exact Nat.Coprime.coprime_dvd_right (hdvd.trans (Subgroup.card_dvd_of_le hLN))
        (glbPrimeCore_coprime 5 H)
  have hstep : ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), U ≤ Rb →
      ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      ¬ Rb ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.card U ≤ 5 * Nat.card
        (U ⊓ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
    intro U hUR Lb hLb hRC
    obtain ⟨L, hL2, rfl, hLK, hLN⟩ := hbad Lb hLb hRC
    have h1 := h.relIndex_centralizer_dvd_five hB3 hα hS hL2 hLK hLN hUR
    have h2 := Subgroup.relIndex_mul_card
      (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) U
    rw [inf_comm] at h2
    rw [← h2]
    exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) h1)
  have hne : ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), 1 < Nat.card U → U ≠ ⊥ := by
    rintro U hU rfl
    rw [Subgroup.card_bot] at hU
    exact lt_irrefl _ hU
  have hRcard : Nat.card Rb = 5 ^ 3 := h.card_barM
  obtain ⟨L1, hL1, hR1⟩ :=
    h.exists_not_le_centralizer h84 hD2 le_rfl (hne Rb (by rw [hRcard]; norm_num))
  have hU1c : 25 ≤ Nat.card
      (Rb ⊓ Subgroup.centralizer (L1 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
    have := hstep Rb le_rfl L1 hL1 hR1
    rw [hRcard] at this
    omega
  obtain ⟨L2, hL2, hU1C⟩ := h.exists_not_le_centralizer h84 hD2 inf_le_left
    (hne (Rb ⊓ Subgroup.centralizer (L1 : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (by omega))
  have hR2 : ¬ Rb ≤ Subgroup.centralizer (L2 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun hle => hU1C (inf_le_left.trans hle)
  have hU2c : 5 ≤ Nat.card (Rb ⊓ Subgroup.centralizer (L1 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
      Subgroup.centralizer (L2 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
    have := hstep (Rb ⊓ Subgroup.centralizer (L1 : Set (↥M ⧸ CFSG.pCore 2 ↥M))) inf_le_left L2
      hL2 hR2
    omega
  obtain ⟨L3, hL3, hU2C⟩ := h.exists_not_le_centralizer h84 hD2
    (inf_le_left.trans inf_le_left)
    (hne (Rb ⊓ Subgroup.centralizer (L1 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
      Subgroup.centralizer (L2 : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (by omega))
  have hR3 : ¬ Rb ≤ Subgroup.centralizer (L3 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun hle => hU2C ((inf_le_left.trans inf_le_left).trans hle)
  have h12 : L1 ≠ L2 := fun he => hU1C (he ▸ inf_le_right)
  have h13 : L1 ≠ L3 := fun he => hU2C (he ▸ inf_le_left.trans inf_le_right)
  have h23 : L2 ≠ L3 := fun he => hU2C (he ▸ inf_le_right)
  obtain ⟨L0, hL0⟩ := h3.exists_weakSBlock h84 hD2
  have hR0 : Rb ≤ Subgroup.centralizer (barM M L0 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h.barM_le_centralizer_block hB3 hb h84 h86 hD2 hα hS hL0 (hall L0 hL0)
  have h01 : barM M L0 ≠ L1 := fun he => hR1 (he ▸ hR0)
  have h02 : barM M L0 ≠ L2 := fun he => hR2 (he ▸ hR0)
  have h03 : barM M L0 ≠ L3 := fun he => hR3 (he ▸ hR0)
  set s : Set (Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := {barM M L0, L1, L2, L3} with hs
  have hmoved : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      ¬ Rb ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ∃ y ∈ barM M (H ⊓ M), y ∈ Lb ∧ IsPGroup 3 (Subgroup.zpowers y) ∧
        ∃ l ∈ Lb, y * l ≠ l * y := by
    intro Lb hLb hRC
    obtain ⟨L, hL2, rfl, hLK, hLN⟩ := hbad Lb hLb hRC
    have h60 := h.card_center_quotient_eq hL2 hLK hLN
    obtain ⟨y, hyL, hy3, l, hlL, hyl⟩ :=
      exists_qElement_not_central Nat.prime_three (h60 ▸ (by norm_num : 3 ∣ 60))
    exact ⟨y, barM_mono hLK hyL, hyL, hy3, l, hlL, hyl⟩
  have hdata : ∀ x : ↥s, IsComponentOf (x : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ⊤ ∧
      ∃ y ∈ barM M (H ⊓ M), y ∈ (x : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        IsPGroup 3 (Subgroup.zpowers y) ∧
        ∃ l ∈ (x : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)), y * l ≠ l * y := by
    rintro ⟨Lb, hLb⟩
    rcases hLb with rfl | rfl | rfl | rfl
    · refine ⟨hL0.component, ?_⟩
      obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hl, hlQ⟩ := hB3 h3 hL0
      have hyM : y ∈ M := hL0.le hyL
      have hlM : l ∈ M := hL0.le hl
      refine ⟨mk ⟨y, hyM⟩, Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr (hKeq.ge ⟨hyM, hyS⟩)),
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL), ?_, mk ⟨l, hlM⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl), fun he => hlQ ?_⟩
      · obtain ⟨k, hk⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
        have hk' : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        refine isPGroup_zpowers_of_pow_eq_one (k := k) ?_
        have : (⟨y, hyM⟩ : M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk')
        rw [← map_pow, this, map_one]
      · have h1 : mk (⟨y, hyM⟩ * ⟨l, hlM⟩ * (⟨y, hyM⟩)⁻¹ * (⟨l, hlM⟩)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, he]
          group
        simpa using coe_mem_pCoreOf_two_of_mk_eq_one _ h1
    · exact ⟨hL1, hmoved _ hL1 hR1⟩
    · exact ⟨hL2, hmoved _ hL2 hR2⟩
    · exact ⟨hL3, hmoved _ hL3 hR3⟩
  choose hcomp y hyK hyL hy3 hyZ using hdata
  have h4 := stmtComponentRank Nat.prime_three (fun x : ↥s => (x : Subgroup _)) hcomp
    Subtype.val_injective (barM M (H ⊓ M)) y hyK hyL hy3 hyZ
  have hcard : Nat.card ↥s = 4 := by
    rw [Nat.card_coe_set_eq, hs, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair h23]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h12, h13⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h01, h02, h03⟩
  rw [hcard] at h4
  have h5 := h4.trans (stmtBarPRankLift Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)
  have h6 := h.pRank_three_le
  omega

end CFSG.AGLEmbedding
