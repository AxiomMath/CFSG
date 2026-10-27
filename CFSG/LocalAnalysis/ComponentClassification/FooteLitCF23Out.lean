module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.Schreier

theorem isComponent_fixSub {G : Type*} [Group G] {N J : Subgroup G} [N.Normal] {α : G}
    (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    J.subgroupOf N ≤ fixSub (MulAut.conjNormal α : MulAut N) ∧
      IsComponent ((J.subgroupOf N).subgroupOf (fixSub (MulAut.conjNormal α : MulAut N))) := by
  obtain ⟨hq, hs⟩ := hJ
  have hfix : ∀ x : N, x ∈ fixSub (MulAut.conjNormal α : MulAut N) ↔ (x : G) * α = α * x := by
    intro x
    rw [mem_fixSub]
    constructor
    · intro h
      have := congrArg Subtype.val h
      rw [MulAut.conjNormal_apply] at this
      calc (x : G) * α = α * x * α⁻¹ * α := by rw [this]
        _ = α * x := by group
    · intro h
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, ← h, mul_inv_cancel_right]
  have hle : J.subgroupOf N ≤ fixSub (MulAut.conjNormal α : MulAut N) := by
    intro x hx
    rw [hfix]
    exact mem_centralizer_singleton_iff.mp (hJα (mem_subgroupOf.mp hx))
  let f : fixSub (MulAut.conjNormal α : MulAut N) →* centralizer ({α} : Set G) :=
    { toFun := fun x => ⟨((x : N) : G), mem_centralizer_singleton_iff.mpr ((hfix x).1 x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨hle, ?_, ?_⟩
  · have e : ↥((J.subgroupOf N).subgroupOf (fixSub (MulAut.conjNormal α : MulAut N))) ≃*
        ↥(J.subgroupOf (centralizer ({α} : Set G))) :=
      (subgroupOfEquivOfLe hle).trans
        ((subgroupOfEquivOfLe hJN).trans (subgroupOfEquivOfLe hJα).symm)
    exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq
  · have he : (J.subgroupOf N).subgroupOf (fixSub (MulAut.conjNormal α : MulAut N)) =
        (J.subgroupOf (centralizer ({α} : Set G))).comap f := by
      ext x
      simp only [mem_subgroupOf, mem_comap]
      rfl
    rw [he]
    exact hs.comap f

theorem conjNormal_outer {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) {α : G} (hα : orderOf α = 2) (hαN : α ∉ N) :
    (MulAut.conjNormal α : MulAut N) * MulAut.conjNormal α = 1 ∧
      (MulAut.conjNormal α : MulAut N) ∉ OuterAutomorphisms.inner N := by
  refine ⟨?_, fun h => hαN (mem_of_conjNormal_mem_inner hC h)⟩
  rw [← map_mul, ← pow_two, ← hα, pow_orderOf_eq_one, map_one]

theorem small_ord_ne_of_between {n a : ℕ} (h1 : a * (a ^ 2 - 1) < 2 * n)
    (h2 : 2 * n + 2 ≤ (a + 1) * ((a + 1) ^ 2 - 1)) (q : ℕ) : q * (q ^ 2 - 1) / 2 ≠ n := by
  intro h
  have hlo : 2 * n ≤ q * (q ^ 2 - 1) := by omega
  have hhi : q * (q ^ 2 - 1) < 2 * n + 2 := by omega
  rcases Nat.lt_or_ge a q with hq | hq
  · have : (a + 1) * ((a + 1) ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega
  · have : q * (q ^ 2 - 1) ≤ a * (a ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega

theorem not_small_of_card_ne {X : Type} [Group X]
    (hX : Nat.card X = 95040 ∨ Nat.card X = 175560 ∨ Nat.card X = 604800)
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel X .PSL 2 p f) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7))) : False := by
  rcases card_small h with ⟨q, -, -, hq⟩ | h7
  · rcases hX with hX | hX | hX <;> rw [hX] at hq
    · exact small_ord_ne_of_between (a := 57) (by norm_num) (by norm_num) q hq.symm
    · exact small_ord_ne_of_between (a := 70) (by norm_num) (by norm_num) q hq.symm
    · exact small_ord_ne_of_between (a := 106) (by norm_num) (by norm_num) q hq.symm
  · omega

end CFSG.ComponentClassification.GSThmB.CF23I
