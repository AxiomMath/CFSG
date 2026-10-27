module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.AtlasMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup Cover CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

section Certificates


theorem fi23SelfCentralizing_of_mult (hmult : Fi23Mult) : Fi23SelfCentralizing := by
  intro G _ _ L K hcov hKL hKq hKcq x hxL hxK l hl
  have hZK : center ↥K = ⊥ := hmult ↥K hKq hKcq
  have hKs : IsSporadic ↥K .Fi23 := isSporadic_of_center_eq_bot hZK hKcq
  obtain ⟨K₀, u₀, hu₀K, ⟨-, hu₂, -⟩, hK₀, hQ⟩ := exists_fiLoc_pair_of_isSporadic_fi23 hKs hKL
  obtain ⟨huL, hbase, -⟩ := fi24in_data hcov hQ
  have hK₀K : K₀ ≤ K := by
    rw [hK₀]
    exact inf_le_left
  have hcomm : ∀ k ∈ bar (K₀.subgroupOf L),
      ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ center ↥L) * k = k * ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ center ↥L) := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := mem_bar.1 hk
    have hk'K : (k' : G) ∈ K := hK₀K (Subgroup.mem_subgroupOf.1 hk')
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (hxK _ hk'K).symm)
  rcases hbase.cent _ hcomm with h1 | h2
  · have hz : (⟨x, hxL⟩ : ↥L) ∈ center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩)
  · exfalso
    have hz : (⟨x, hxL⟩ : ↥L)⁻¹ * ⟨u₀, huL⟩ ∈ center ↥L := QuotientGroup.eq.1 h2
    have hu₀ : ⟨u₀, hu₀K⟩ ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨(k : G), hKL k.2⟩)
      have h4 := hxK (k : G) k.2
      have h5 : (k : G) * (x⁻¹ * u₀) = (x⁻¹ * u₀) * (k : G) := by
        simpa using h3
      apply Subtype.ext
      show (k : G) * u₀ = u₀ * (k : G)
      calc (k : G) * u₀ = (k : G) * (x * (x⁻¹ * u₀)) := by group
        _ = ((k : G) * x) * (x⁻¹ * u₀) := by group
        _ = (x * (k : G)) * (x⁻¹ * u₀) := by rw [h4]
        _ = x * ((k : G) * (x⁻¹ * u₀)) := by group
        _ = x * ((x⁻¹ * u₀) * (k : G)) := by rw [h5]
        _ = u₀ * (k : G) := by group
    rw [hZK, Subgroup.mem_bot] at hu₀
    have hu1 : u₀ = 1 := congrArg Subtype.val hu₀
    rw [hu1, orderOf_one] at hu₂
    omega

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.V3
