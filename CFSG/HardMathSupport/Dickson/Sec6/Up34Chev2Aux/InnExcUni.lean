module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcUniDefs
public import CFSG.LieType.Chevalley.OddSignRootComponent
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Up34Exc


theorem uniEmbed_holds : UniEmbed := by
  intro τ M _ χ i K _ _ ℓ _ _
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  refine ⟨(componentUnipotent K χ i).subgroupOf (componentRootSpan K χ i), ?_, ?_, ?_⟩
  · exact ((CFSG.SignalizerFunctorTheorem.NonLocalExc.isPGroup_posUnipotent ℓ).to_le
      componentUnipotent_le_posUnipotent).comap_subtype
  · have hcl : ∀ α ∈ posRoots (componentRoots χ i), ∀ β ∈ posRoots (componentRoots χ i),
        ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
          a • α + b • β ∈ posRoots (componentRoots χ i) :=
      fun α hα β hβ a b ha hb hr => mem_posRoots_of_nsmul_add hα hβ a b ha hb hr
    have h1 : Nat.card (componentUnipotent K χ i) =
        Nat.card K ^ (posRoots (componentRoots χ i)).ncard :=
      card_rootSpan (fun α hα => isRoot_height_pos_of_mem_posRoots hα) hcl
    rw [← h1]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe componentUnipotent_le_componentRootSpan).toEquiv
  · obtain ⟨v, j, hvj⟩ := exists_componentWeylChoice χ i
    obtain ⟨w₀, hw₀, himg⟩ := exists_longest hΨ
    obtain ⟨g₀, hg₀N, hg₀w⟩ := exists_mem_componentMonomial_mapsRootLines (K := K) hvj hw₀
    have hg₀C : g₀ ∈ componentRootSpan K χ i := componentMonomial_le_componentRootSpan hvj hg₀N
    have hg₀M : g₀ ∈ monomialSubgroup τ K :=
      componentMonomial_le_monomialSubgroup K χ i v j hg₀N
    have hnegroot : ∀ α ∈ negRoots (componentRoots χ i), IsRoot τ α ∧ height α < 0 := fun α hα =>
      ⟨hΨ.isRoot α ((mem_negRoots_iff hΨ).1 hα).1, ((mem_negRoots_iff hΨ).1 hα).2⟩
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxV, hxZ⟩ := Subgroup.mem_inf.1 hx
    have hxU : (x : ModGL τ K) ∈ componentUnipotent K χ i := Subgroup.mem_subgroupOf.1 hxV
    have h1 := conj_mem_rootSpan_of_mapsRootLines hg₀M hg₀w (S := posRoots (componentRoots χ i))
      (fun α hα => hΨ.isRoot α hα.1) hxU
    rw [himg] at h1
    have h2 : g₀ * (x : ModGL τ K) * g₀⁻¹ = x := by
      have h := congrArg (fun y : componentRootSpan K χ i => (y : ModGL τ K))
        (Subgroup.mem_center_iff.1 hxZ ⟨g₀, hg₀C⟩)
      simp only [Subgroup.coe_mul] at h
      rw [h]
      group
    rw [h2] at h1
    have h3 : (x : ModGL τ K) ∈ negUnipotent τ K := rootSpan_le_negUnipotent hnegroot h1
    have h4 : (x : ModGL τ K) ∈ borelGroup τ K :=
      componentBorel_le_borelGroup (componentUnipotent_le_componentBorel hxU)
    have h5 : (x : ModGL τ K) ∈ borelGroup τ K ⊓ negUnipotent τ K :=
      Subgroup.mem_inf.2 ⟨h4, h3⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at h5
    exact Subgroup.mem_bot.2 (Subtype.ext h5)

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
