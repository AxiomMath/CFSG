module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mul_self_eq_of_orderOf_four {t : G} {K : Subgroup G} (h : IsIntrinsic t K)
    (ht : orderOf t = 2) {w : G} (hw : w ∈ K) (hw4 : orderOf w = 4) : w * w = t := by
  have h1 : orderOf (w * w) = 2 := by
    rw [← pow_two, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hw4]
    norm_num
  exact h.eq_of_involution ht (mul_mem hw hw) h1

theorem fusion_first (h44 : II4_44) (hAut : II4_Aut) (hG : IsKProperSimple G) {x s : G}
    {L S : Subgroup G} (hx : orderOf x = 2) (hL : IsIntrinsic x L) (hs : orderOf s = 2)
    (hsN : s ∈ normalizer (L : Set G)) (hnf : ¬ InducesFAut s L) (hS : IsSylow2In S L)
    (hSs : ∀ a ∈ S, s * a * s⁻¹ ∈ S) :
    ∃ c ∈ S, c ∈ normalizer ((closure ({s, x} : Set G) : Subgroup G) : Set G) ∧
      c⁻¹ * s * c = s * x := by
  have hx1 := mul_self_eq_one_of_orderOf_eq_two hx
  have hs1 := mul_self_eq_one_of_orderOf_eq_two hs
  have hsC : s ∈ centralizer ({x} : Set G) := hL.normalizer_le_centralizer hx hsN
  have hsx : s * x = x * s := mem_centralizer_singleton_iff.mp hsC
  have hscs : s ∉ cSec L := fun h => hnf (inducesFAut_of_mem_cSec hG hx hL.1 hL.2.1 h)
  have hφ1 : phi L s hsN ≠ 1 := fun h => hscs ((phi_eq_one_iff L hsN).mp h)
  have hQ := h44 G hG x hx L hL.1 hL.2.1
  have hφ2 := phi_mul_self L hsN hs1
  obtain ⟨wb, hwbP, hwbo, hwbφ⟩ := (((hAut (Hat L) hQ).2.2 (phi L s hsN) hφ2).1 hφ1 (hatImg L S)
    (isSylow2In_hatImg hS) (fun p hp => phi_mem_hatImg hsN hSs hp))
  obtain ⟨a, haS, rfl⟩ := mem_hatImg.mp hwbP
  have hSL : S ≤ L := hS.1
  have hSp : IsPGroup 2 ↥S := hS.2.1
  have ha4 : orderOf (a : G) = 4 := by
    have := orderOf_hatMk hSL hSp haS
    rw [← this]
    exact hwbo
  have haL : (a : G) ∈ L := a.2
  have hww : (a : G) * a = x := mul_self_eq_of_orderOf_four hL hx haL ha4
  have hinv : s * (a : G) * s⁻¹ = (a : G)⁻¹ := by
    apply eq_of_hatMk_eq hSL hSp (hSs _ haS) (inv_mem haS)
    rw [← phi_mk L hsN a, hwbφ, ← map_inv]
    rfl
  have hax : (a : G) * x = x * a := hL.comm_of_mem haL
  obtain ⟨hn, he⟩ := fusion_of_inverted hs1 hx1 hsx hax hww hinv
  exact ⟨a, haS, hn, he⟩

theorem lemma_28_4 (h44 : II4_44) (hAut : II4_Aut) :
    ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (x : G), orderOf x = 2 →
      ∀ L : Subgroup G, IsIntrinsic x L → ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
        ¬ InducesFAut s L →
        (∀ S : Subgroup G, IsSylow2In S L → (∀ a ∈ S, s * a * s⁻¹ ∈ S) →
          ∃ c ∈ S, c ∈ normalizer ((closure ({s, x} : Set G) : Subgroup G) : Set G) ∧
            c⁻¹ * s * c = s * x) ∧
        (∀ H : Subgroup G, IsIntrinsic s H → x ∈ normalizer (H : Set G) → ¬ InducesFAut x H →
          ∃ g : G, g⁻¹ * x * g = s ∧ g⁻¹ * s * g = x) := by
  intro G _ _ hG x hx L hL s hs hsN hnf
  refine ⟨fun S hS hSs => fusion_first h44 hAut hG hx hL hs hsN hnf hS hSs, ?_⟩
  intro H hH hxH hnfx
  have hx1 := mul_self_eq_one_of_orderOf_eq_two hx
  have hs1 := mul_self_eq_one_of_orderOf_eq_two hs
  have hsC : s ∈ centralizer ({x} : Set G) := hL.normalizer_le_centralizer hx hsN
  have hsx : s * x = x * s := mem_centralizer_singleton_iff.mp hsC
  obtain ⟨S, hS, hSn⟩ := exists_invariant_sylow (isPGroup_zpowers_of_mul_self_eq_one hs1)
    (zpowers_le.mpr hsN)
  obtain ⟨S', hS', hSn'⟩ := exists_invariant_sylow (isPGroup_zpowers_of_mul_self_eq_one hx1)
    (zpowers_le.mpr hxH)
  have hSs : ∀ a ∈ S, s * a * s⁻¹ ∈ S := fun a ha =>
    (mem_normalizer_iff.mp (hSn (mem_zpowers s)) a).mp ha
  have hS's' : ∀ a ∈ S', x * a * x⁻¹ ∈ S' := fun a ha =>
    (mem_normalizer_iff.mp (hSn' (mem_zpowers x)) a).mp ha
  obtain ⟨c, hcS, -, hc⟩ := fusion_first h44 hAut hG hx hL hs hsN hnf hS hSs
  obtain ⟨c', hcS', -, hc'⟩ := fusion_first h44 hAut hG hs hH hx hxH hnfx hS' hS's'
  have h1x : c⁻¹ * x * c = x := by
    have h := hL.comm_of_mem (hS.1 hcS)
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = c⁻¹ * (c * x) := by rw [← h]
      _ = x := by group
  have h2s : c'⁻¹ * s * c' = s := by
    have h := hH.comm_of_mem (hS'.1 hcS')
    calc c'⁻¹ * s * c' = c'⁻¹ * (s * c') := by group
      _ = c'⁻¹ * (c' * s) := by rw [← h]
      _ = s := by group
  exact swap_of_two_fusions hx1 hsx h1x hc h2s hc' hs1

end CFSG.GH74.GLS.Stage1.Thm2.Recip
