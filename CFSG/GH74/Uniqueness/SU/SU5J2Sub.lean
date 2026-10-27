module

public import CFSG.GH74.Uniqueness.SU.SU5Models
public import CFSG.GH74.Uniqueness.SU.SU5Map

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

@[expose] def W : Subgroup J2Syl := subOfPred (fun s => s.right = 1) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)

@[expose] def U : Subgroup J2Syl := subOfPred (fun s => s.right = 1 ∧ s.left.a = 0 ∧ s.left.b = 0)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def A : Subgroup J2Syl := subOfPred (fun s => s.right = 1 ∧ s.left.b = 0)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def B : Subgroup J2Syl := subOfPred (fun s => s.right = 1 ∧ s.left.a = 0)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def Cx : Subgroup J2Syl := subOfPred (fun s => s * x0 = x0 * s)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

instance instDecMemW (s : J2Syl) : Decidable (s ∈ W) := inferInstanceAs (Decidable (s.right = 1))

instance instDecMemU (s : J2Syl) : Decidable (s ∈ U) :=
  inferInstanceAs (Decidable (s.right = 1 ∧ s.left.a = 0 ∧ s.left.b = 0))

instance instDecMemA (s : J2Syl) : Decidable (s ∈ A) :=
  inferInstanceAs (Decidable (s.right = 1 ∧ s.left.b = 0))

instance instDecMemB (s : J2Syl) : Decidable (s ∈ B) :=
  inferInstanceAs (Decidable (s.right = 1 ∧ s.left.a = 0))

instance instDecMemCx (s : J2Syl) : Decidable (s ∈ Cx) :=
  inferInstanceAs (Decidable (s * x0 = x0 * s))

theorem mem_W {s : J2Syl} : s ∈ W ↔ s.right = 1 := Iff.rfl

theorem mem_U {s : J2Syl} : s ∈ U ↔ s.right = 1 ∧ s.left.a = 0 ∧ s.left.b = 0 := Iff.rfl

theorem mem_A {s : J2Syl} : s ∈ A ↔ s.right = 1 ∧ s.left.b = 0 := Iff.rfl

theorem mem_B {s : J2Syl} : s ∈ B ↔ s.right = 1 ∧ s.left.a = 0 := Iff.rfl

theorem mem_Cx {s : J2Syl} : s ∈ Cx ↔ s * x0 = x0 * s := Iff.rfl

theorem card_W : Nat.card W = 64 := by
  unfold W; rw [card_subOfPred]; decide +kernel

theorem card_U : Nat.card U = 4 := by
  unfold U; rw [card_subOfPred]; decide +kernel

theorem card_A : Nat.card A = 16 := by
  unfold A; rw [card_subOfPred]; decide +kernel

theorem card_B : Nat.card B = 16 := by
  unfold B; rw [card_subOfPred]; decide +kernel

theorem card_Cx : Nat.card Cx = 16 := by
  unfold Cx; rw [card_subOfPred]; decide +kernel

theorem x0_sq : x0 * x0 = 1 := by decide +kernel

theorem x0_not_mem_W : x0 ∉ W := by decide +kernel

theorem W_normal : ∀ s r : J2Syl, r ∈ W → s * r * s⁻¹ ∈ W := by decide +kernel

theorem cover : ∀ s : J2Syl, s ∈ W ∨ x0 * s ∈ W := by decide +kernel

theorem z0_mem_U : z0 ∈ U := by decide +kernel

theorem z0_sq : z0 * z0 = 1 := by decide +kernel

theorem z0_ne_one : z0 ≠ 1 := by decide +kernel

theorem center_iff : ∀ s : J2Syl, (∀ t : J2Syl, s * t = t * s) ↔ (s = 1 ∨ s = z0) := by
  decide +kernel

theorem U_le_A : U ≤ A := by
  intro s hs; exact ⟨hs.1, hs.2.2⟩

theorem A_le_W : A ≤ W := fun _ hs => hs.1

theorem B_le_W : B ≤ W := fun _ hs => hs.1

theorem U_le_W : U ≤ W := fun _ hs => hs.1

theorem comm_A : ∀ s t : J2Syl, s ∈ A → t ∈ A → s * t = t * s := by decide +kernel

theorem comm_B : ∀ s t : J2Syl, s ∈ B → t ∈ B → s * t = t * s := by decide +kernel

theorem comm_U : ∀ s t : J2Syl, s ∈ U → t ∈ U → s * t = t * s := by decide +kernel

theorem sq_A : ∀ s : J2Syl, s ∈ A → s * s = 1 := by decide +kernel

theorem sq_B : ∀ s : J2Syl, s ∈ B → s * s = 1 := by decide +kernel

theorem sq_U : ∀ s : J2Syl, s ∈ U → s * s = 1 := by decide +kernel

theorem isE_A : IsE 4 A := by
  refine ⟨isElemAbelian_iff.2 ⟨fun a ha b hb => comm_A a b ha hb, fun a ha => ?_⟩, card_A⟩
  rw [pow_two]; exact sq_A a ha

theorem isE_B : IsE 4 B := by
  refine ⟨isElemAbelian_iff.2 ⟨fun a ha b hb => comm_B a b ha hb, fun a ha => ?_⟩, card_B⟩
  rw [pow_two]; exact sq_B a ha

theorem isE_U : IsE 2 U := by
  refine ⟨isElemAbelian_iff.2 ⟨fun a ha b hb => comm_U a b ha hb, fun a ha => ?_⟩, card_U⟩
  rw [pow_two]; exact sq_U a ha

theorem A_inf_B : A ⊓ B = U := by
  ext s
  simp only [Subgroup.mem_inf, mem_A, mem_B, mem_U]
  tauto

theorem A_ne_B : A ≠ B := by
  intro h
  have h1 : (⟨⟨1, 0, 0⟩, 1⟩ : J2Syl) ∈ A := ⟨rfl, rfl⟩
  rw [h] at h1
  have h10 : (1 : F4c) = 0 := h1.2
  exact absurd h10 (by decide)

theorem prod_AB : ∀ s : J2Syl, s ∈ W →
    ∃ a b : J2Syl, a ∈ A ∧ b ∈ B ∧ a * b = s := by
  intro s hs
  refine ⟨⟨⟨s.left.a, 0, s.left.c + s.left.a * s.left.b⟩, 1⟩, ⟨⟨0, s.left.b, 0⟩, 1⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  revert s
  decide +kernel

theorem A_sup_B : A ⊔ B = W := by
  apply le_antisymm
  · exact sup_le A_le_W B_le_W
  · intro s hs
    obtain ⟨a, b, ha, hb, rfl⟩ := prod_AB s hs
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem inv_W : ∀ s : J2Syl, s ∈ W → s * s = 1 → s ∈ A ∨ s ∈ B := by decide +kernel

theorem cent_A : ∀ a g : J2Syl, a ∈ A → a ∉ B → (g * a = a * g ↔ g ∈ A) := by decide +kernel

theorem cent_B : ∀ b g : J2Syl, b ∈ B → b ∉ A → (g * b = b * g ↔ g ∈ B) := by decide +kernel

theorem conj_A : ∀ s : J2Syl, s ∈ A → x0 * s * x0⁻¹ ∈ B := by decide +kernel

theorem conj_B : ∀ s : J2Syl, s ∈ B → x0 * s * x0⁻¹ ∈ A := by decide +kernel

theorem map_conj_A : A.map (MulAut.conj x0).toMonoidHom = B := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact conj_A s hs
  · intro s hs
    refine ⟨x0 * s * x0⁻¹, conj_B s hs, ?_⟩
    have h1 : x0⁻¹ = x0 := inv_eq_of_mul_eq_one_right x0_sq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h1]
    calc x0 * (x0 * s * x0) * x0 = (x0 * x0) * s * (x0 * x0) := by group
      _ = s := by rw [x0_sq]; group

theorem cert_cent : ∀ s t : J2Syl, s.right ≠ 1 → s * s = 1 → t * s = s * t → t * t = 1 →
    t = 1 ∨ t = s ∨ t = z0 ∨ t = s * z0 := by decide +kernel

theorem card_le_16 (E : Subgroup J2Syl) (hE : Open.IsElemAbelian 2 E) : Nat.card E ≤ 16 := by
  have hE' := isElemAbelian_iff.1 hE
  by_cases hW : E ≤ W
  · have h : ∀ e ∈ E, e ∈ A ∨ e ∈ B := fun e he =>
      inv_W e (hW he) (by rw [← pow_two]; exact hE'.2 e he)
    rcases le_or_le_of_subset_union h with h1 | h1
    · exact (Subgroup.card_le_of_le h1).trans card_A.le
    · exact (Subgroup.card_le_of_le h1).trans card_B.le
  · obtain ⟨s, hsE, hsW⟩ := IsConcreteLE.not_le_iff_exists.1 hW
    have hs2 : s * s = 1 := by rw [← pow_two]; exact hE'.2 s hsE
    have hsub : ∀ t ∈ E, t ∈ ({1, s, z0, s * z0} : Finset J2Syl) := by
      intro t ht
      have h1 : t * s = s * t := hE'.1 t ht s hsE
      have h2 : t * t = 1 := by rw [← pow_two]; exact hE'.2 t ht
      have := cert_cent s t hsW hs2 h1 h2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    calc Nat.card E ≤ ({1, s, z0, s * z0} : Finset J2Syl).card :=
          card_le_card_of_subset_finset hsub
      _ ≤ 4 := Finset.card_le_four
      _ ≤ 16 := by norm_num

theorem le_W_of_card_16 (E : Subgroup J2Syl) (hE : IsE 4 E) : E ≤ W := by
  have hE' := isElemAbelian_iff.1 hE.1
  by_contra hW
  obtain ⟨s, hsE, hsW⟩ := IsConcreteLE.not_le_iff_exists.1 hW
  have hs2 : s * s = 1 := by rw [← pow_two]; exact hE'.2 s hsE
  have hsub : ∀ t ∈ E, t ∈ ({1, s, z0, s * z0} : Finset J2Syl) := by
    intro t ht
    have h1 : t * s = s * t := hE'.1 t ht s hsE
    have h2 : t * t = 1 := by rw [← pow_two]; exact hE'.2 t ht
    have := cert_cent s t hsW hs2 h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h4 : Nat.card E ≤ 4 :=
    (card_le_card_of_subset_finset hsub).trans Finset.card_le_four
  rw [hE.2] at h4
  norm_num at h4

theorem isE4_unique (E : Subgroup J2Syl) (hE : IsE 4 E) : E = A ∨ E = B := by
  have hW := le_W_of_card_16 E hE
  have hE' := isElemAbelian_iff.1 hE.1
  have h : ∀ e ∈ E, e ∈ A ∨ e ∈ B := fun e he =>
    inv_W e (hW he) (by rw [← pow_two]; exact hE'.2 e he)
  rcases le_or_le_of_subset_union h with h1 | h1
  · left; exact Subgroup.eq_of_le_of_card_ge h1 (by rw [card_A, hE.2]; norm_num)
  · right; exact Subgroup.eq_of_le_of_card_ge h1 (by rw [card_B, hE.2]; norm_num)

theorem JE_eq_W : JE (⊤ : Subgroup J2Syl) = W := by
  rw [JE_eq_sup (A := A) (B := B) le_top le_top isE_A isE_B
    (fun F _ hF => (card_le_16 F hF).trans (by norm_num))
    (fun E _ hE => isE4_unique E hE), A_sup_B]

theorem class_four : ∀ n : J2Syl, n * n = 1 → n ≠ 1 →
    ¬ (n.right = 1 ∧ n.left.a = 0 ∧ n.left.b = 0) →
    4 ≤ (Finset.univ.image (fun g : J2Syl => g * n * g⁻¹)).card := by decide +kernel

theorem unique_normal_four (N : Subgroup J2Syl) (hN : N.Normal) (hE : IsE 2 N) : N = U := by
  have hE' := isElemAbelian_iff.1 hE.1
  have hle : N ≤ U := by
    refine normal_le_of_class_four N U hN (by rw [hE.2]; norm_num) ?_
    intro n hn hn1 hnU
    have hn2 : n * n = 1 := by rw [← pow_two]; exact hE'.2 n hn
    exact class_four n hn2 hn1 hnU
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hE.2, card_U]; norm_num)

theorem conj_involutions : ∀ s : J2Syl, s.right ≠ 1 → s * s = 1 → ∃ g : J2Syl, g * x0 * g⁻¹ = s := by
  decide +kernel

theorem Cx_cases : ∀ s : J2Syl, s * x0 = x0 * s → s.right = 1 ∨ (x0 * s).right = 1 := by
  decide +kernel

end J2Syl

end CFSG.GH74.Uniqueness.SU.SU5
