module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_sup_oddCoreIn_eq {L S : Subgroup G} (hS : IsPGroup 2 S)
    (hSL : S ≤ coreActionKernel L) : (L ⊓ centralizer (S : Set G)) ⊔ oddCoreIn L = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (sup_le inf_le_left (map_subtype_le _)) fun l hl => ?_
  set A := normalizer (L : Set G) with hA
  have hLA : L ≤ A := le_normalizer
  have hSA : S ≤ A := fun x hx => (hSL hx).1
  set N := (oddCoreIn L).subgroupOf A with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn a => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h1 := map_conj_oddCoreIn (D := L) a.2
    rw [← h1]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hNodd : ¬ 2 ∣ Nat.card N := by
    have h1 : Nat.card N ∣ Nat.card (oddCoreIn L) := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    intro h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_oddCoreIn L) (h2.trans h1)
  set Q := S.subgroupOf A with hQ
  have hQ2 : IsPGroup 2 Q := hS.comap_subtype
  have : Fact (IsPGroup 2 Q) := ⟨hQ2⟩
  set x : ↥A := ⟨l, hLA hl⟩ with hx
  have hxc : QuotientGroup.mk' N x ∈ centralizer ((Q.map (QuotientGroup.mk' N) : Subgroup _) :
      Set (↥A ⧸ N)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have h1 := (hSL (mem_subgroupOf.mp hq)).2 l hl
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [mem_subgroupOf]
    have h2 : (((q * x)⁻¹ * (x * q) : ↥A) : G) = l⁻¹ * (q : G)⁻¹ * l * q := by
      simp only [hx, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact h1
  have hcop : Nat.Coprime 2 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hNodd
  rw [CFSG.centralizer_map_quotient_eq_map_centralizer 2 Q N hNn hcop] at hxc
  obtain ⟨c, hc, hcx⟩ := hxc
  have hco : c⁻¹ * x ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
    exact hcx
  have hcS : (c : G) ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have := (mem_centralizer_iff.mp hc) ⟨s, hSA hs⟩ (mem_subgroupOf.mpr hs)
    exact congrArg Subtype.val this
  have hcoL : ((c⁻¹ * x : ↥A) : G) ∈ oddCoreIn L := mem_subgroupOf.mp hco
  have hcL : (c : G) ∈ L := by
    have h1 : (c : G) = l * ((c⁻¹ * x : ↥A) : G)⁻¹ := by simp [hx]
    rw [h1]
    exact mul_mem hl (inv_mem (map_subtype_le _ hcoL))
  have hl' : l = (c : G) * ((c⁻¹ * x : ↥A) : G) := by simp [hx]
  rw [hl']
  exact mul_mem (mem_sup_left ⟨hcL, hcS⟩) (mem_sup_right hcoL)

end CFSG.ComponentClassification.Sol76
