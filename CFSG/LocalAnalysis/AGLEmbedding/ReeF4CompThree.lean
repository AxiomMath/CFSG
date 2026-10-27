module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Comp

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R X : Subgroup G}

theorem D1ReeF4Data.exists_three_element (h : D1ReeF4Data P M H R X) (hB3 : StmtBlockThree)
    (hα : KFactThreeOrFiveDvd) {L : Subgroup G} (hL2 : IsTwoPrimeComponent M L)
    (hcase : IsWeakSBlock M (pCoreOf 2 H) L ∨ L ≤ H ⊓ M) :
    ∃ y ∈ barM M L, y ∈ barM M (H ⊓ M) ∧ IsPGroup 3 (Subgroup.zpowers y) ∧
      ∃ l ∈ barM M L, y * l ≠ l * y := by
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  rcases hcase with hLw | hLK
  · obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hl, hlQ⟩ := hB3 h3 hLw
    have hyM : y ∈ M := hL2.le hyL
    have hyK : y ∈ H ⊓ M := hKeq ▸ ⟨hyM, hyS⟩
    refine ⟨mk ⟨y, hyM⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyK), ?_,
      mk ⟨l, hL2.le hl⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl), ?_⟩
    · obtain ⟨k, hk⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
      have hk' : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine isPGroup_zpowers_of_pow_prime_pow_eq_one (n := k) ?_
      have : (⟨y, hyM⟩ : M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [← map_pow, this, map_one]
    · intro hc
      apply hlQ
      have h2 : mk (⟨y, hyM⟩ * ⟨l, hL2.le hl⟩ * ⟨y, hyM⟩⁻¹ * ⟨l, hL2.le hl⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      exact coe_mem_pCoreOf_two_of_mk_eq_one _ h2
  ·
    have hLb : IsComponentOf (barM M L) ⊤ := hL2.component
    have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
    have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
      (catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient _
    have hLcat := hcat.isCatalogGroup_center_quotient hLb
    have hLN := h.perfect_le L hLK hL2.perfect
    have h5L : ¬ 5 ∣ Nat.card (barM M L) := by
      have hcop : Nat.Coprime 5 (Nat.card (barM M L)) :=
        Nat.Coprime.coprime_dvd_right ((card_barM_dvd hL2.le).trans
          (Subgroup.card_dvd_of_le hLN)) (glbPrimeCore_coprime 5 H)
      intro hd
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop hd) (by norm_num)
    have hsimple : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hLb.2.2.2
    have h3d : 3 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
      rcases hα _ hsimple (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
        _ hLb.2.2) hLcat with h3 | h5
      · exact h3
      · exact absurd (h5.trans (Subgroup.card_quotient_dvd_card _)) h5L
    obtain ⟨y, hyL, hy3, l, hl, hyl⟩ := exists_qElement_not_central Nat.prime_three h3d
    exact ⟨y, hyL, Subgroup.map_mono (Subgroup.comap_mono hLK) hyL, hy3, l, hl, hyl⟩

end Comp

end CFSG.AGLEmbedding
