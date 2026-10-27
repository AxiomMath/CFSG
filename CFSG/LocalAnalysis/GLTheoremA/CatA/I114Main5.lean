module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Main4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

@[expose] def Eset (x y : Y) : Subgroup Y :=
  Subgroup.zpowers y ⊔ (Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹))

theorem H9_bound [Finite Y] {B K : Subgroup Y} {x : Y} (hB : IsElemAbelian 3 B) (hxB : x ∈ B)
    (hrel : (Subgroup.normalizer (K : Set Y)).relIndex B = 3)
    (hKK₂ : ElemCommute K (cj x K)) (hKK₃ : ElemCommute K (cj (x * x) K))
    (hmax : ∀ F : Subgroup Y, IsElemAbelian 3 F →
      (∃ W : Subgroup Y, W ≠ ⊥ ∧ IsPGroup 2 W ∧ F ≤ Subgroup.normalizer (W : Set Y)) →
      Nat.card F ≤ Nat.card B)
    (hA : ∃ y : ↥K, (∃ z : ↥K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
      ∃ U : Subgroup ↥K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ y ∈ Subgroup.normalizer (U : Set ↥K)) :
    9 ≤ Nat.card (HK K B) := by
  obtain ⟨y₀, ⟨z₀, hz₀⟩, hy₀3, U₀, hU₀ne, hU₀p, hy₀N⟩ := hA
  have hy₀K : (y₀ : Y) ∈ K := y₀.2
  have hy₀nc : ∃ z ∈ K, z * (y₀ : Y) ≠ (y₀ : Y) * z :=
    ⟨z₀.1, z₀.2, fun h => hz₀ (Subtype.ext h)⟩
  have hy₀3' : orderOf (y₀ : Y) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hy₀3
  have hU₀K : U₀.map K.subtype ≤ K := Subgroup.map_subtype_le U₀
  have hU₀ne' : U₀.map K.subtype ≠ ⊥ := by
    intro h
    apply hU₀ne
    rw [eq_bot_iff]
    intro u hu
    have hmem : (u : Y) ∈ U₀.map K.subtype := Subgroup.mem_map_of_mem K.subtype hu
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hmem
  have hU₀p' : IsPGroup 2 ↥(U₀.map K.subtype) := by
    intro w
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.1 w.2
    obtain ⟨n, hn⟩ := hU₀p ⟨u, hu⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hu1 : u ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← huw, ← map_pow, hu1, map_one]
  have hy₀U : cj (y₀ : Y) (U₀.map K.subtype) = U₀.map K.subtype := by
    rw [cj_map_subtype, mem_normalizer_iff_cj.1 hy₀N]
  have hF0 := F0_bound hB hxB hKK₂ hKK₃ hy₀K hy₀3' hy₀nc hU₀K hU₀ne' hU₀p' hy₀U hmax
  have hcardB := card_B_eq hrel
  have hc : 0 < Nat.card (CBK K B) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  rw [hcardB] at hF0
  nlinarith

end CFSG.LocalAnalysis.GLTheoremA.I114
