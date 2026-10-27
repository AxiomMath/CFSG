module


public import CFSG.GroupTheory.WielandtProductFinal

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

theorem isSolvable_sup_of_perm_odd_two {G : Type} [Group G] [Finite G] {B U : Subgroup G}
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B)) (hU : IsPGroup 2 U)
    (hBU : (B : Set G) * U = U * B) : Group.IsSolvable ↥(B ⊔ U) := by
  let K : Subgroup G :=
    { carrier := {g | ∃ a ∈ B, ∃ c ∈ U, g = a * c}
      mul_mem' := by
        rintro _ _ ⟨b1, hb1, u1, hu1, rfl⟩ ⟨b2, hb2, u2, hu2, rfl⟩
        have h12 : u1 * b2 ∈ (B : Set G) * U := by
          rw [hBU]; exact ⟨u1, hu1, b2, hb2, rfl⟩
        obtain ⟨b3, hb3, u3, hu3, h3⟩ := h12
        have h3' : u1 * b2 = b3 * u3 := h3.symm
        refine ⟨b1 * b3, B.mul_mem hb1 hb3, u3 * u2, U.mul_mem hu3 hu2, ?_⟩
        calc b1 * u1 * (b2 * u2) = b1 * (u1 * b2) * u2 := by group
          _ = b1 * (b3 * u3) * u2 := by rw [h3']
          _ = b1 * b3 * (u3 * u2) := by group
      one_mem' := ⟨1, B.one_mem, 1, U.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨b, hb, u, hu, rfl⟩
        have h1 : u⁻¹ * b⁻¹ ∈ (B : Set G) * U := by
          rw [hBU]; exact ⟨u⁻¹, U.inv_mem hu, b⁻¹, B.inv_mem hb, rfl⟩
        obtain ⟨b3, hb3, u3, hu3, h3⟩ := h1
        exact ⟨b3, hb3, u3, hu3, by rw [mul_inv_rev, ← h3]⟩ }
  have hK : B ⊔ U = K := by
    apply le_antisymm
    · refine sup_le (fun b hb => ⟨b, hb, 1, U.one_mem, by simp⟩)
        (fun u hu => ⟨1, B.one_mem, u, hu, by simp⟩)
    · rintro g ⟨a, ha, c, hc, rfl⟩
      exact mul_mem ((le_sup_left : B ≤ B ⊔ U) ha) ((le_sup_right : U ≤ B ⊔ U) hc)
  have hsurj : ∀ g : ↥(B ⊔ U), ∃ a ∈ B.subgroupOf (B ⊔ U), ∃ c ∈ U.subgroupOf (B ⊔ U),
      g = a * c := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ K := hK ▸ hg
    obtain ⟨a, ha, c, hc, rfl⟩ := hg'
    refine ⟨⟨a, (le_sup_left : B ≤ B ⊔ U) ha⟩, ?_, ⟨c, (le_sup_right : U ≤ B ⊔ U) hc⟩, ?_, rfl⟩
    · exact (Subgroup.mem_subgroupOf).2 ha
    · exact (Subgroup.mem_subgroupOf).2 hc
  have hA_comm : ∀ x y : ↥(B.subgroupOf (B ⊔ U)), x * y = y * x := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hBab x (Subgroup.mem_subgroupOf.1 hx) y (Subgroup.mem_subgroupOf.1 hy)
  have hA_nil : Group.IsNilpotent ↥(B.subgroupOf (B ⊔ U)) := by
    letI : CommGroup ↥(B.subgroupOf (B ⊔ U)) :=
      { (inferInstance : Group ↥(B.subgroupOf (B ⊔ U))) with
        mul_comm := fun x y => hA_comm x y }
    infer_instance
  have hUsub : IsPGroup 2 (U.subgroupOf (B ⊔ U)) := by
    exact hU.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_right : U ≤ B ⊔ U)).symm
  have hC_nil : Group.IsNilpotent ↥(U.subgroupOf (B ⊔ U)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hUsub.isNilpotent
  have hcardA : Nat.card ↥(B.subgroupOf (B ⊔ U)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : B ≤ B ⊔ U)).toEquiv
  have hcardU : ∃ n : ℕ, Nat.card ↥(U.subgroupOf (B ⊔ U)) = 2 ^ n := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.iff_card).1 hUsub
  obtain ⟨n, hn⟩ := hcardU
  have hcop : Nat.Coprime (Nat.card ↥(B.subgroupOf (B ⊔ U)))
      (Nat.card ↥(U.subgroupOf (B ⊔ U))) := by
    rw [hcardA, hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hBodd)
  exact CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product _ _ hA_nil hC_nil hcop hsurj

end Section5

end CFSG.LocalAnalysis.RankThreeUC
