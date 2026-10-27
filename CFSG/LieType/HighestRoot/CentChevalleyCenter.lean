module

public import CFSG.LieType.Chevalley.OddSignRootComponent

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}

theorem rootReflection_ne_one
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : rootReflection β ≠ 1 := by
  intro h
  have h1 := rootReflection_smul_self hβ
  rw [h, one_smul] at h1
  refine hβ.ne_zero (funext fun k => ?_)
  have h2 := congrFun h1 k
  simp only [Pi.neg_apply] at h2
  simp only [Pi.zero_apply]
  omega

theorem mem_componentBorel_of_commute
    {v : (Fin τ.rank → ℤ) → WeylGroup τ}
    {j : (Fin τ.rank → ℤ) → Fin τ.rank}
    (hvj : ∀ β ∈ simpleRoots (componentRoots χ i),
      v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
    {x : ModGL τ K} (hxS : x ∈ componentRootSpan K χ i)
    (hxB : ∀ b ∈ componentBorel K χ i, b * x = x * b) : x ∈ componentBorel K χ i := by
  have hΨ := isRootComponent_componentRoots i
  have hmem : x ∈ (componentRootSpan K χ i : Set (ModGL τ K)) := hxS
  rw [coe_componentRootSpan_eq_iUnion hvj] at hmem
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨w, hw, hxw⟩ := hmem
  obtain ⟨b₁, hb₁, g, hg, b₂, hb₂, hx⟩ := mem_componentCell.1 hxw
  by_cases hw1 : w = 1
  · subst hw1
    have ht := inv_mul_mem_componentTorus hvj one_mem_componentLifts hg
    rw [inv_one, one_mul] at ht
    rw [← hx]
    exact mul_mem (mul_mem hb₁ (componentTorus_le_componentBorel ht)) hb₂
  exfalso
  obtain ⟨β, hβ, hneg⟩ := exists_smul_mem_negRoots hΨ (inv_mem hw) (inv_ne_one.2 hw1)
  have hlen := (componentLength_rootReflection_mul_of_neg hΨ hβ hw hneg).1
  have hx' : x ∈ componentCell K χ i v j (rootReflection β) * componentCell K χ i v j w := by
    rw [componentCell_mul_of_length_eq_sub_one hvj hβ hw hlen]
    exact Or.inr hxw
  obtain ⟨d, hd, d', hd', hdd'⟩ := Set.mem_mul.1 hx'
  obtain ⟨b₃, hb₃, g', hg', b₄, hb₄, hd'e⟩ := mem_componentCell.1 hd'
  have ht := inv_mul_mem_componentTorus hvj hg hg'
  have hc : b₃ * b₁⁻¹ ∈ componentBorel K χ i := mul_mem hb₃ (inv_mem hb₁)
  have hr : b₂⁻¹ * (g⁻¹ * g') * b₄ ∈ componentBorel K χ i :=
    mul_mem (mul_mem (inv_mem hb₂) (componentTorus_le_componentBorel ht)) hb₄
  have hd'x : d' = x * (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄)) := by
    have hg_eq : g = b₁⁻¹ * x * b₂⁻¹ := by rw [← hx]; group
    calc d' = b₃ * g * (g⁻¹ * g') * b₄ := by rw [← hd'e]; group
      _ = b₃ * b₁⁻¹ * x * (b₂⁻¹ * (g⁻¹ * g') * b₄) := by rw [hg_eq]; group
      _ = x * (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄)) := by rw [hxB _ hc]; group
  have hb := mul_mem hc hr
  have hd_eq : d = (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄))⁻¹ := by
    have e : x = d * (x * (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄))) := by rw [← hd'x, hdd']
    have hcb := hxB _ (inv_mem hb)
    calc d = d * (x * (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄))) *
          (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄))⁻¹ * x⁻¹ := by group
      _ = x * (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄))⁻¹ * x⁻¹ := by rw [← e]
      _ = (b₃ * b₁⁻¹ * (b₂⁻¹ * (g⁻¹ * g') * b₄))⁻¹ := by rw [← hcb]; group
  have hd1 : d ∈ componentCell K χ i v j 1 :=
    mem_componentCell.2 ⟨d, hd_eq ▸ inv_mem hb, 1, one_mem_componentLifts, 1, one_mem _,
      by rw [mul_one, mul_one]⟩
  exact Set.disjoint_left.1
    (disjoint_componentCell (rootReflection_ne_one (simpleRoots_isRoot hβ)).symm) hd1 hd

theorem coe_mem_componentTorus_of_mem_center
    {x : componentRootSpan K χ i}
    (hx : x ∈ Subgroup.center (componentRootSpan K χ i)) :
    (x : ModGL τ K) ∈ componentTorus K χ i := by
  obtain ⟨v, j, hvj⟩ := exists_componentWeylChoice χ i
  have hΨ := isRootComponent_componentRoots i
  have hcomm : ∀ g ∈ componentRootSpan K χ i, g * (x : ModGL τ K) = x * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨g, hg⟩)
  have hxB : (x : ModGL τ K) ∈ componentBorel K χ i :=
    mem_componentBorel_of_commute hvj x.2 fun b hb =>
      hcomm b (componentBorel_le_componentRootSpan hb)
  obtain ⟨w₀, hw₀, himg⟩ := exists_longest hΨ
  obtain ⟨g₀, hg₀N, hg₀w⟩ := exists_mem_componentMonomial_mapsRootLines (K := K) hvj hw₀
  have hg₀S : g₀ ∈ componentRootSpan K χ i := componentMonomial_le_componentRootSpan hvj hg₀N
  have hg₀M : g₀ ∈ monomialSubgroup τ K := componentMonomial_le_monomialSubgroup K χ i v j hg₀N
  have hnegroot : ∀ α ∈ negRoots (componentRoots χ i), IsRoot τ α ∧ height α < 0 := fun α hα =>
    ⟨hΨ.isRoot α ((mem_negRoots_iff hΨ).1 hα).1, ((mem_negRoots_iff hΨ).1 hα).2⟩
  have hconjU : ∀ u ∈ componentUnipotent K χ i,
      g₀ * u * g₀⁻¹ ∈ rootSpan τ K (negRoots (componentRoots χ i)) := fun u hu => by
    have h := conj_mem_rootSpan_of_mapsRootLines hg₀M hg₀w (S := posRoots (componentRoots χ i))
      (fun α hα => hΨ.isRoot α hα.1) hu
    rwa [himg] at h
  have hxopp : (x : ModGL τ K) ∈ torusGroup τ K ⊔ negUnipotent τ K := by
    have hxB' := hxB
    rw [← SetLike.mem_coe, coe_componentBorel] at hxB'
    obtain ⟨t, ht, u, hu, htu⟩ := hxB'
    have e : (x : ModGL τ K) = (g₀ * t * g₀⁻¹) * (g₀ * u * g₀⁻¹) := by
      calc (x : ModGL τ K) = g₀ * x * g₀⁻¹ := by rw [hcomm g₀ hg₀S]; group
        _ = _ := by rw [← htu]; group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (componentTorus_le_torusGroup K χ i
      (conj_mem_componentTorus hvj hg₀N ht)))
      (Subgroup.mem_sup_right (rootSpan_le_negUnipotent hnegroot (hconjU u hu)))
  obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
  have hH : (x : ModGL τ K) ∈ torusGroup τ K := by
    rw [← (opposite_Borel_intersection τ K w₁ hw₁).2.2.1]
    exact Subgroup.mem_inf.2 ⟨componentBorel_le_borelGroup hxB, hxopp⟩
  exact Subgroup.mem_inf.2 ⟨x.2, hH⟩

end CFSG.LieType.HighestRoot
