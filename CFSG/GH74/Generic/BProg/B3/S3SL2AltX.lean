module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.Generic.BProg.B3.S3SL2AltX

open Equiv Equiv.Perm Subgroup

def pts (a b : Fin 9) : Finset (Fin 9) := ({a, b} : Finset (Fin 9))ᶜ

theorem mem_pts {a b x : Fin 9} : x ∈ pts a b ↔ x ≠ a ∧ x ≠ b := by
  simp [pts]

theorem card_pts {a b : Fin 9} (hab : a ≠ b) : (pts a b).card = 7 := by
  rw [pts, Finset.card_compl, Finset.card_pair hab]
  simp

def Xs (a b : Fin 9) : Subgroup (alternatingGroup (Fin 9)) :=
  (alternatingGroup.ofSubtype (pts a b)).range

theorem mem_Xs_fix {a b : Fin 9} {x : alternatingGroup (Fin 9)} (hx : x ∈ Xs a b) :
    (x : Perm (Fin 9)) a = a ∧ (x : Perm (Fin 9)) b = b := by
  obtain ⟨k, rfl⟩ := hx
  rw [alternatingGroup.coe_ofSubtype]
  exact ⟨Perm.ofSubtype_apply_of_not_mem _ (by simp [mem_pts]),
    Perm.ofSubtype_apply_of_not_mem _ (by simp [mem_pts])⟩

theorem Xs_of_fix {a b : Fin 9} {g : alternatingGroup (Fin 9)} (hga : (g : Perm (Fin 9)) a = a)
    (hgb : (g : Perm (Fin 9)) b = b) : g ∈ Xs a b := by
  classical
  have h1 : ∀ x, (g : Perm (Fin 9)) x ∈ pts a b ↔ x ∈ pts a b := by
    intro x
    simp only [mem_pts]
    constructor
    · rintro ⟨hxa, hxb⟩
      refine ⟨fun h => hxa ?_, fun h => hxb ?_⟩
      · rw [h, hga]
      · rw [h, hgb]
    · rintro ⟨hxa, hxb⟩
      refine ⟨fun h => hxa ?_, fun h => hxb ?_⟩
      · exact (g : Perm (Fin 9)).injective (h.trans hga.symm)
      · exact (g : Perm (Fin 9)).injective (h.trans hgb.symm)
  have h2 : ∀ x, (g : Perm (Fin 9)) x ≠ x → x ∈ pts a b := by
    intro x hx
    rw [mem_pts]
    exact ⟨fun h => hx (h ▸ hga), fun h => hx (h ▸ hgb)⟩
  have hsign : Perm.sign ((g : Perm (Fin 9)).subtypePerm h1) = 1 := by
    have := Perm.sign_ofSubtype (p := fun x => x ∈ pts a b) ((g : Perm (Fin 9)).subtypePerm h1)
    rw [Perm.ofSubtype_subtypePerm h1 h2] at this
    rw [← this]
    exact (mem_alternatingGroup).1 g.2
  refine ⟨⟨(g : Perm (Fin 9)).subtypePerm h1, (mem_alternatingGroup).2 hsign⟩, ?_⟩
  apply Subtype.ext
  rw [alternatingGroup.coe_ofSubtype]
  exact Perm.ofSubtype_subtypePerm h1 h2


noncomputable def Xs_equiv {a b : Fin 9} : alternatingGroup (pts a b) ≃* Xs a b :=
  MonoidHom.ofInjective alternatingGroup.ofSubtype_injective

theorem natCard_pts {a b : Fin 9} (hab : a ≠ b) : Nat.card (pts a b) = 7 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_pts hab]

theorem Xs_isSimple {a b : Fin 9} (hab : a ≠ b) : IsSimpleGroup (Xs a b) := by
  have : IsSimpleGroup (alternatingGroup (pts a b)) :=
    alternatingGroup.isSimpleGroup (by rw [natCard_pts hab]; norm_num)
  exact (Xs_equiv (a := a) (b := b)).symm.isSimpleGroup

theorem Xs_card {a b : Fin 9} (hab : a ≠ b) : Nat.card (Xs a b) = 2520 := by
  have : Nontrivial (pts a b) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe, card_pts hab]; norm_num
  rw [← Nat.card_congr Xs_equiv.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_coe, card_pts hab]
  decide +kernel

theorem Xs_nonabelian {a b : Fin 9} (hab : a ≠ b) : ∃ x y : Xs a b, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hc : center (Xs a b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hcon y x
  have hz : center (alternatingGroup (pts a b)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [natCard_pts hab]; norm_num)
  have h3 : center (Xs a b) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : Xs_equiv.symm x ∈ center (alternatingGroup (pts a b)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      apply Xs_equiv.injective
      rw [map_mul, map_mul]
      simpa using hx (Xs_equiv g)
    rw [hz, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    simpa using congrArg Xs_equiv hx'
  have h4 : (⊤ : Subgroup (Xs a b)) = ⊥ := hc ▸ h3
  have h5 : Nat.card (Xs a b) = 1 := by
    rw [← Subgroup.card_top, h4, Subgroup.card_bot]
  rw [Xs_card hab] at h5
  omega

theorem Xs_comm_swap {a b : Fin 9} {x : alternatingGroup (Fin 9)} (hx : x ∈ Xs a b) :
    (x : Perm (Fin 9)) * swap a b = swap a b * (x : Perm (Fin 9)) := by
  obtain ⟨h1, h2⟩ := mem_Xs_fix hx
  rw [Equiv.mul_swap_eq_swap_mul, h1, h2]

theorem Xs_normalized {a b : Fin 9} {c : alternatingGroup (Fin 9)}
    (hc : (c : Perm (Fin 9)) * swap a b = swap a b * (c : Perm (Fin 9))) (hab : a ≠ b)
    {x : alternatingGroup (Fin 9)} (hx : x ∈ Xs a b) : c * x * c⁻¹ ∈ Xs a b := by
  have hca : (c : Perm (Fin 9)) a = a ∧ (c : Perm (Fin 9)) b = b ∨
      (c : Perm (Fin 9)) a = b ∧ (c : Perm (Fin 9)) b = a := by
    have h1 := congrArg (fun f : Perm (Fin 9) => f a) hc
    simp only [Perm.mul_apply, Equiv.swap_apply_left] at h1
    by_cases hA : (c : Perm (Fin 9)) a = a
    · left
      refine ⟨hA, ?_⟩
      rw [hA, Equiv.swap_apply_left] at h1
      exact h1
    · by_cases hB : (c : Perm (Fin 9)) a = b
      · right
        refine ⟨hB, ?_⟩
        rw [hB, Equiv.swap_apply_right] at h1
        exact h1
      · exfalso
        rw [Equiv.swap_apply_of_ne_of_ne hA hB] at h1
        exact hab ((c : Perm (Fin 9)).injective h1).symm
  obtain ⟨hx1, hx2⟩ := mem_Xs_fix hx
  have hinv : ∀ y, y = a ∨ y = b → (c : Perm (Fin 9))⁻¹ y = a ∨ (c : Perm (Fin 9))⁻¹ y = b := by
    intro y hy
    rcases hca with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hy with rfl | rfl
      · left; rw [Equiv.Perm.inv_eq_iff_eq]; exact h1.symm
      · right; rw [Equiv.Perm.inv_eq_iff_eq]; exact h2.symm
    · rcases hy with rfl | rfl
      · right; rw [Equiv.Perm.inv_eq_iff_eq]; exact h2.symm
      · left; rw [Equiv.Perm.inv_eq_iff_eq]; exact h1.symm
  have hfix : ∀ y, (y = a ∨ y = b) → (x : Perm (Fin 9)) ((c : Perm (Fin 9))⁻¹ y) = (c : Perm (Fin 9))⁻¹ y := by
    intro y hy
    rcases hinv y hy with h | h
    · rw [h, hx1]
    · rw [h, hx2]
  apply Xs_of_fix
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [hfix a (Or.inl rfl)]
    simp
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [hfix b (Or.inr rfl)]
    simp


end CFSG.GH74.Generic.BProg.B3.S3SL2AltX
