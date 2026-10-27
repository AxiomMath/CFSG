module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup CFSG.Assembly.LowTwoRank

theorem exists_elementary_of_commuting {G : Type*} [Group G] [Finite G] {x y z : G}
    (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1) (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy1 : x ≠ y) (hz1 : z ≠ 1) (hzx : z ≠ x)
    (hzy : z ≠ y) (hzxy : z ≠ x * y) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ 4 < Nat.card E := by
  classical
  set S : Set G := {x, y, z} with hS
  have hcomm : S.Pairwise Commute := by
    intro a ha b hb _
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _ | exact hxy | exact hxz | exact hyz | exact hxy.symm
      | exact hxz.symm | exact hyz.symm
  have hCE := Subgroup.isMulCommutative_closure hcomm
  have hcE : ∀ a b : closure S, a * b = b * a := isMulCommutative_iff.mp hCE
  set E := closure S with hE
  have hsq : ∀ g ∈ E, g * g = 1 := by
    intro g hg
    refine closure_induction (fun a ha => ?_) (by rw [one_mul]) (fun a b ha hb iha ihb => ?_)
      (fun a ha iha => ?_) hg
    · simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    · have hab : a * b = b * a := congrArg Subtype.val (hcE ⟨a, ha⟩ ⟨b, hb⟩)
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    · rw [← mul_inv_rev, iha, inv_one]
  have hEl : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hCE
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by rw [Subgroup.coe_pow, sq, hsq a a.2, Subgroup.coe_one]) }
  refine ⟨E, hEl, ?_⟩
  have hxE : x ∈ E := subset_closure (by simp [hS])
  have hyE : y ∈ E := subset_closure (by simp [hS])
  have hzE : z ∈ E := subset_closure (by simp [hS])
  let v : Fin 5 → E := ![1, ⟨x, hxE⟩, ⟨y, hyE⟩, ⟨x * y, E.mul_mem hxE hyE⟩, ⟨z, hzE⟩]
  have hxy' : x * y ≠ 1 := fun h => hxy1 (by
    rw [← mul_one x, ← hy, ← mul_assoc, h, one_mul])
  have hv : Function.Injective v := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      simp [v] at hij' <;>
      first
        | rfl
        | exact absurd hij' hx1 | exact absurd hij'.symm hx1
        | exact absurd hij' hy1 | exact absurd hij'.symm hy1
        | exact absurd hij' hxy1 | exact absurd hij'.symm hxy1
        | exact absurd hij' hz1 | exact absurd hij'.symm hz1
        | exact absurd hij' hzx | exact absurd hij'.symm hzx
        | exact absurd hij' hzy | exact absurd hij'.symm hzy
        | exact absurd hij' hzxy | exact absurd hij'.symm hzxy
        | exact absurd hij' hxy' | exact absurd hij'.symm hxy'
  have h5 := Nat.card_le_card_of_injective v hv
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h5
  omega

theorem not_small_source_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (E : Subgroup Y) [IsElementaryAbelian 2 E] (hE : 4 < Nat.card E) {l : ℕ} (hl : l.Prime)
    (hl2 : l ≠ 2) (hdvd : l ^ 3 ∣ Nat.card Y) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 := by
  have : IsElementaryAbelian 2 (E.map e.symm.toMonoidHom) := IsElementaryAbelian.map _
  have hE' : 4 < Nat.card (E.map e.symm.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.symm.injective]
  refine not_small_source_of_quotient _ hE' hl hl2 ?_
  rwa [Nat.card_congr e.toEquiv]

end CFSG.ComponentClassification.OddSelector
