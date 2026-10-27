module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models
import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG

theorem UT3_mem_center_iff (x : UT3 F4c) :
    x ∈ Subgroup.center (UT3 F4c) ↔ x.a = 0 ∧ x.b = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have h1 := congrArg UT3.c (h ⟨0, 1, 0⟩)
    have h2 := congrArg UT3.c (h ⟨1, 0, 0⟩)
    simp only [UT3.mul_def] at h1 h2
    refine ⟨?_, ?_⟩
    · linear_combination (-1 : F4c) * h1
    · linear_combination h2
  · rintro ⟨ha, hb⟩ g
    refine UT3.ext ?_ ?_ ?_ <;> simp only [UT3.mul_def, ha, hb] <;> ring

namespace UT3Aux

theorem mem_center_equiv_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (g : G) :
    g ∈ Subgroup.center G ↔ e g ∈ Subgroup.center G' := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h h'
    obtain ⟨k, rfl⟩ := e.surjective h'
    rw [← map_mul, ← map_mul, h k]
  · intro h k
    apply e.injective
    rw [map_mul, map_mul, h (e k)]

end UT3Aux

theorem card_center_UT3 : Nat.card (Subgroup.center (UT3 F4c)) = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => UT3_mem_center_iff x)),
    Nat.card_eq_fintype_card]
  decide

theorem mem_center_of_equiv_UT3_iff {G : Type} [Group G] (e : G ≃* UT3 F4c) (g : G) :
    g ∈ Subgroup.center G ↔ (e g).a = 0 ∧ (e g).b = 0 :=
  (UT3Aux.mem_center_equiv_iff e g).trans (UT3_mem_center_iff (e g))

theorem card_center_of_equiv_UT3 {G : Type} [Group G] (e : G ≃* UT3 F4c) :
    Nat.card (Subgroup.center G) = 4 :=
  (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (UT3Aux.mem_center_equiv_iff e))).trans
    card_center_UT3

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
