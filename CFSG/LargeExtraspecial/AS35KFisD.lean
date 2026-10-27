module

public import CFSG.LargeExtraspecial.AS35KBridgeMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

namespace Setting

variable {H : Type} [Group H] [Finite H] (T : Setting H)

omit [Finite H] in
theorem eq_one_or_z_of_conjNormal [T.zGen.Normal] (hC : centralizer (T.zGen : Set H) = ⊥) {c : H}
    (h : (∀ x, MulAut.conjNormal (H := T.zGen) c x = x) ∨
      ∀ x, MulAut.conjNormal (H := T.zGen) c x = T.zL * x * T.zL⁻¹) :
    c = 1 ∨ c = T.z := by
  have hcent : ∀ a : H, (∀ l ∈ T.zGen, a * l * a⁻¹ = l) → a = 1 := by
    intro a ha
    have : a ∈ centralizer (T.zGen : Set H) := mem_centralizer_iff.mpr fun l hl => by
      calc l * a = a * l * a⁻¹ * a := by rw [ha l hl]
        _ = a * l := by group
    rwa [hC, mem_bot] at this
  rcases h with h | h
  · refine Or.inl (hcent c fun l hl => ?_)
    have := congrArg Subtype.val (h ⟨l, hl⟩)
    simpa only [MulAut.conjNormal_apply] using this
  · refine Or.inr ?_
    have h1 := hcent (T.z⁻¹ * c) fun l hl => by
      have h2 : c * l * c⁻¹ = T.z * l * T.z⁻¹ := by
        have := congrArg Subtype.val (h ⟨l, hl⟩)
        simpa [MulAut.conjNormal_apply] using this
      calc T.z⁻¹ * c * l * (T.z⁻¹ * c)⁻¹ = T.z⁻¹ * (c * l * c⁻¹) * T.z := by group
        _ = l := by rw [h2]; group
    calc c = T.z * (T.z⁻¹ * c) := by group
      _ = T.z := by rw [h1, mul_one]

end Setting

end CFSG.LargeExtraspecial
