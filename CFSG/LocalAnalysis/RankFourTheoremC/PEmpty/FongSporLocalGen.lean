module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem mem_normalizer_zpowers_of_commute {x t : G} (h : x * t = t * x) :
    x ∈ normalizer (zpowers t : Set G) := by
  have hc : Commute x t := h
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [(hc.zpow_right k).mul_inv_cancel]
    exact hy
  · intro hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hxk : Commute x (t ^ k) := hc.zpow_right k
    have h2 : x⁻¹ * t ^ k * x = t ^ k := by
      have := hxk.inv_left.mul_inv_cancel
      simpa using this
    calc t ^ k = x⁻¹ * t ^ k * x := h2.symm
      _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [← hk]
      _ = y := by group

variable [Finite G]

theorem mem_of_centralizes_involution {z : G} {K : Subgroup G}
    (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K)
    {t m : G} (ht2 : t * t = 1) (ht1 : t ≠ 1) (hzt : z * t = t * z) (hmt : m * t = t * m) :
    m ∈ K := by
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hU : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]; norm_num
  have htK : t ∈ K := hN (mem_normalizer_zpowers_of_commute (x := t) (t := z) hzt.symm)
  have hUK : zpowers t ⊓ K ≠ ⊥ := by
    intro hbot
    have : t ∈ zpowers t ⊓ K := ⟨mem_zpowers t, htK⟩
    rw [hbot] at this
    exact ht1 (Subgroup.mem_bot.mp this)
  exact hcl (zpowers t) hU (mem_normalizer_zpowers_of_commute hzt) hUK
    (mem_normalizer_zpowers_of_commute hmt)

theorem closure_le_of_gen {z : G} {K : Subgroup G}
    (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K)
    {ns ms : Set G} (hns : ∀ n ∈ ns, n ∈ normalizer (zpowers z : Set G))
    (hms : ∀ m ∈ ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z * t = t * z ∧ m * t = t * m) :
    closure (ns ∪ ms) ≤ K := by
  rw [closure_le]
  intro g hg
  rcases hg with hg | hg
  · exact hN (hns g hg)
  · obtain ⟨t, h2, h1, hzt, hmt⟩ := hms g hg
    exact mem_of_centralizes_involution hN hcl h2 h1 hzt hmt

theorem eq_top_of_gen {z : G} {K : Subgroup G}
    (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K)
    {ns ms : Set G} (hns : ∀ n ∈ ns, n ∈ normalizer (zpowers z : Set G))
    (hms : ∀ m ∈ ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z * t = t * z ∧ m * t = t * m)
    (hgen : closure (ns ∪ ms) = ⊤) : K = ⊤ :=
  top_le_iff.mp (hgen ▸ closure_le_of_gen hN hcl hns hms)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
