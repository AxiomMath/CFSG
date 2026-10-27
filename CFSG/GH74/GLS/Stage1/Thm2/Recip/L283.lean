module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_commute {x y : G} (h : Commute x y) : y ∈ centralizer ({x} : Set G) :=
  mem_centralizer_singleton_iff.mpr h.symm

omit [Finite G] in
theorem IsIntrinsic.mem_cSec {t : G} {K : Subgroup G} (h : IsIntrinsic t K) : t ∈ cSec K := by
  refine ⟨le_normalizer h.2.2, TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer h.2.2),
    fun k hk => ?_⟩
  have : ⁅k, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (h.comm_of_mem hk)
  rw [this]
  exact one_mem _

theorem x_mem_cSec_of_fAut (hBal : IG_balance_fAut) {x y : G} {L J : Subgroup G}
    (cfg : RecipCfg G x y L J) (h : InducesFAut y L) : x ∈ cSec J := by
  rcases hBal G cfg.simple x y cfg.hx cfg.hy cfg.comm L cfg.hL h with h1 | ⟨K, hK, hxK⟩
  · exact O22_le_cSec cfg.hJ.1 h1
  · by_cases hKJ : K = J
    · have hxJ : x ∈ J := hKJ ▸ hxK
      have : x = y := cfg.hJ.eq_of_involution cfg.hy hxJ cfg.hx
      rw [this]
      exact cfg.hJ.mem_cSec
    · exact le_cSec_of_ne hK cfg.hJ.1 hKJ hxK

theorem RecipCfg.symm {x y : G} {L J : Subgroup G} (cfg : RecipCfg G x y L J) :
    RecipCfg G y x J L :=
  ⟨cfg.simple, cfg.hy, cfg.hx, cfg.comm.symm, cfg.hJ, cfg.hL⟩

theorem lemma_28_3 (hBal : IG_balance_fAut) :
    ∀ (G : Type) [Group G] [Finite G] (x y : G) (L J : Subgroup G), RecipCfg G x y L J →
      (InducesFAut x J ∨ InducesFAut y L) →
        y ∈ cSec L ∧ x ∈ cSec J ∧
        (x ∈ normalizer (J : Set G) → y ∈ normalizer (L : Set G)) ∧
        (x ∈ normalizer (J : Set G) → ∀ a ∈ J, IsPGroup 2 (zpowers a) → a ∉ zpowers y →
          Commute a x → a ∈ normalizer (L : Set G)) := by
  intro G _ _ x y L J cfg hf
  have hsym := cfg.symm
  have key : x ∈ cSec J ∧ y ∈ cSec L := by
    rcases hf with hfx | hfy
    · have hy' : y ∈ cSec L := x_mem_cSec_of_fAut hBal hsym hfx
      exact ⟨x_mem_cSec_of_fAut hBal cfg
        (inducesFAut_of_mem_cSec cfg.simple cfg.hx cfg.hL.1 cfg.hL.2.1 hy'), hy'⟩
    · have hx' : x ∈ cSec J := x_mem_cSec_of_fAut hBal cfg hfy
      exact ⟨hx', x_mem_cSec_of_fAut hBal hsym
        (inducesFAut_of_mem_cSec cfg.simple cfg.hy cfg.hJ.1 cfg.hJ.2.1 hx')⟩
  refine ⟨key.2, key.1, fun _ => key.2.1, fun _ a haJ ha2 _ hax => ?_⟩
  obtain ⟨Λ, -, -, -, -, hΛW, h2el, -⟩ := TwoThin.pumpup_cover (x := y) (y := x) cfg.hx cfg.hJ.1
    (key.1 : x ∈ centralizerSection J (pPrimeCoreOf 2 J))
  have haC : a ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hax
  have hpow : ∃ n : ℕ, a ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := ha2 ⟨a, mem_zpowers a⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have haΛ : a ∈ Λ := h2el a ⟨haJ, haC⟩ hpow
  have hΛL := le_pLayerOf_of_isPCompIn_inf (s := y) (t := x) cfg.hy
    (mem_centralizer_of_commute cfg.comm) hΛW
  exact pLayerOf_le_normalizer cfg.hL.1 (hΛL haΛ)

end CFSG.GH74.GLS.Stage1.Thm2.Recip
