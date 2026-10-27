module

public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.Asc77.AscT7K5

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Elem

variable {G : Type} [Group G]

theorem comm_gen_of {U Z E : G} (cUZ : U * Z = Z * U) (cUE : U * E = E * U)
    (cZE : Z * E = E * Z) :
    ∀ a ∈ ({U * E, U, Z} : Set G), ∀ b ∈ ({U * E, U, Z} : Set G), a * b = b * a := by
  have c1 : Commute U E := cUE
  have c2 : Commute U Z := cUZ
  have c3 : Commute Z E := cZE
  have c4 : Commute (U * E) U := Commute.mul_left (Commute.refl U) c1.symm
  have c5 : Commute (U * E) Z := Commute.mul_left c2 c3.symm
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (Commute.refl _).eq
  · exact c4.eq
  · exact c5.eq
  · exact c4.symm.eq
  · exact (Commute.refl _).eq
  · exact c2.eq
  · exact c5.symm.eq
  · exact c2.symm.eq
  · exact (Commute.refl _).eq

theorem B_isElemAbelian_of {U Z E : G} (hU : U * U = 1) (hZ : Z * Z = 1) (hE : E * E = 1)
    (cUZ : U * Z = Z * U) (cUE : U * E = E * U) (cZE : Z * E = E * Z) :
    IsElemAbelian 2 (Subgroup.closure ({U * E, U, Z} : Set G)) := by
  have hgen := comm_gen_of cUZ cUE cZE
  have hcomm := T7A.commutes_closure hgen
  have hsq : ∀ a ∈ ({U * E, U, Z} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · calc U * E * (U * E) = U * (E * U) * E := by group
        _ = U * (U * E) * E := by rw [← cUE]
        _ = (U * U) * (E * E) := by group
        _ = 1 := by rw [hU, hE]; group
    · exact hU
    · exact hZ
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq hgen x hx

theorem closure_eq_sup (U Z E : G) :
    Subgroup.closure ({U * E, U, Z} : Set G) =
      Subgroup.closure ({U, Z} : Set G) ⊔ Subgroup.zpowers E := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers E))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · have : E = U⁻¹ * (U * E) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))

theorem B_natCard_of [Finite G] {U Z E : G} (hU : U * U = 1) (hZ : Z * Z = 1) (hE : E * E = 1)
    (hU1 : U ≠ 1) (hZ1 : Z ≠ 1) (hUZ : U ≠ Z) (cUZ : U * Z = Z * U) (cUE : U * E = E * U)
    (cZE : Z * E = E * Z) (hEn : E ∉ Subgroup.closure ({U, Z} : Set G)) :
    Nat.card ↥(Subgroup.closure ({U * E, U, Z} : Set G)) = 8 := by
  have hD := T7A.isElemAbelian2_closure_pair hU hZ hU1 hZ1 hUZ cUZ
  have hE1 : E ≠ 1 := fun h => hEn (h ▸ Subgroup.one_mem _)
  have he2 : orderOf E = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE) hE1
  have hcomm : Commutes (Subgroup.closure ({U, Z} : Set G)) (Subgroup.zpowers E) := by
    have hle : Subgroup.closure ({U, Z} : Set G) ≤ Subgroup.centralizer ({E} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr cUE
      · exact Subgroup.mem_centralizer_singleton_iff.mpr cZE
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x E := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({U, Z} : Set G) ⊓ Subgroup.zpowers E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases T7A.eq_one_or_eq_of_mem_zpowers he2 hx.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact absurd (h1 ▸ hx.1) hEn
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, he2, hD.1, mul_one] at hN
  rw [closure_eq_sup, sup_comm, hN]
  norm_num

theorem mem_normalizer_of_card_eq_eight [Finite G] {W B : Subgroup G}
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {a b c : G} (ha : a ∈ W) (hb : b ∈ W)
    (hc : c ∈ W) (hgen : W ≤ Subgroup.closure ({a, b, c} : Set G)) (hBW : B ≤ W)
    (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) :
    n ∈ Subgroup.normalizer (B : Set G) := by
  have hB2 : ∀ s ∈ B, s * s = 1 := fun s hs => by simpa only [pow_two] using hB.2 s hs
  have key : ∀ m ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ B, m * x * m⁻¹ ∈ B := by
    intro m hm x hx
    refine T7K.mem_of_involution_of_card_eq_eight hcomm ha hb hc hgen hBW hB2 hB8
      ((Subgroup.mem_normalizer_iff.mp hm x).mp (hBW hx)) ?_
    calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
      _ = 1 := by rw [hB2 x hx]; group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  simpa [mul_assoc] using this

end Elem

end CFSG.ClassicalInvolution.Asc77.S24
