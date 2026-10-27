module

public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem commuting_disjoint_elementary_product {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime firstRank secondRank : ℕ}
    (First Second : Subgroup Ambient) (hfirst : IsElemAbelian prime First)
    (hsecond : IsElemAbelian prime Second) (hfirstCard : Nat.card First = prime ^ firstRank)
    (hsecondCard : Nat.card Second = prime ^ secondRank)
    (hcommutes : First ≤ Subgroup.centralizer (Second : Set Ambient)) (hdisjoint : Disjoint First Second) :
    ∃ Combined : Subgroup Ambient, First ≤ Combined ∧ Second ≤ Combined ∧
      IsElemAbelian prime Combined ∧ Nat.card Combined = prime ^ (firstRank + secondRank) ∧
      Combined ≤ First ⊔ Second := by
  let : CommGroup First := { (inferInstance : Group First) with mul_comm := @mul_comm' First _ hfirst.1 }
  let : CommGroup Second := { (inferInstance : Group Second) with mul_comm := @mul_comm' Second _ hsecond.1 }
  let productMap := First.subtype.noncommCoprod Second.subtype (by
    intro first second
    exact (Subgroup.mem_centralizer_iff.mp (hcommutes first.property) second.val second.property).symm)
  have hinjective : Function.Injective productMap := by
    apply (MonoidHom.ker_eq_bot_iff productMap).mp
    apply le_antisymm _ bot_le
    intro pair hpair
    have hproduct : pair.1.val * pair.2.val = 1 := hpair
    have hfirstSecond : pair.1.val ∈ Second := by
      rw [mul_eq_one_iff_eq_inv.mp hproduct]
      exact Second.inv_mem pair.2.property
    have hfirstOne : pair.1.val = 1 := Subgroup.mem_bot.mp
      ((disjoint_iff.mp hdisjoint).le ⟨pair.1.property, hfirstSecond⟩)
    have hsecondOne : pair.2.val = 1 := by simpa only [hfirstOne, one_mul] using hproduct
    exact Subgroup.mem_bot.mpr (Prod.ext (Subtype.ext hfirstOne) (Subtype.ext hsecondOne))
  have htopElementary : IsElemAbelian prime (⊤ : Subgroup (First × Second)) := by
    constructor
    · infer_instance
    · intro pair _
      exact Prod.ext (Subtype.ext (hfirst.2 pair.1.val pair.1.property))
        (Subtype.ext (hsecond.2 pair.2.val pair.2.property))
  have hrangeElementary : IsElemAbelian prime productMap.range := by
    rw [MonoidHom.range_eq_map]
    exact elementary_map ⊤ htopElementary productMap
  have hrangeCard : Nat.card productMap.range = prime ^ (firstRank + secondRank) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinjective).toEquiv, Nat.card_prod,
      hfirstCard, hsecondCard, pow_add]
  refine ⟨productMap.range, ?_, ?_, hrangeElementary, hrangeCard, ?_⟩
  · intro element helement
    refine ⟨(⟨element, helement⟩, 1), ?_⟩
    change element * 1 = element
    exact mul_one element
  · intro element helement
    refine ⟨(1, ⟨element, helement⟩), ?_⟩
    change 1 * element = element
    exact one_mul element
  · intro element helement
    obtain ⟨pair, rfl⟩ := helement
    exact Subgroup.mul_mem_sup pair.1.property pair.2.property

end CFSG.LargeEvenClassification.Helpers
