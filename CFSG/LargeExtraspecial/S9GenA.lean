module

public import CFSG.LargeExtraspecial.S5Fus

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def conjL (t : S.O) : Set S.O :=
  {τ | τ ∈ S.Lbar g ∧ ∃ x ∈ S.Mbar, τ = x * t * x⁻¹}

variable (S g) in
@[expose] noncomputable def Fbar (t : S.O) : Subgroup S.O :=
  closure (conjL S g t)

theorem conjL_subset_Lbar {t : S.O} : conjL S g t ⊆ S.Lbar g :=
  fun _ h => h.1

theorem Fbar_le_Lbar {t : S.O} : Fbar S g t ≤ S.Lbar g :=
  (closure_le _).mpr conjL_subset_Lbar

theorem self_mem_conjL {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ conjL S g t :=
  ⟨ht, 1, one_mem _, by group⟩

theorem self_mem_Fbar {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ Fbar S g t :=
  subset_closure (self_mem_conjL ht)

theorem Fbar_le_of_subset {t : S.O} {X : Subgroup S.O} (hX : conjL S g t ⊆ X) :
    Fbar S g t ≤ X :=
  (closure_le _).mpr hX

theorem conj_mem_conjL {t n τ : S.O} (hnM : n ∈ S.Mbar)
    (hnN : n ∈ normalizer (S.Lbar g : Set S.O)) (hτ : τ ∈ conjL S g t) :
    n * τ * n⁻¹ ∈ conjL S g t := by
  obtain ⟨hτL, x, hxM, rfl⟩ := hτ
  refine ⟨(mem_normalizer_iff.mp hnN _).mp hτL, n * x, mul_mem hnM hxM, by group⟩

theorem conj_mem_Fbar {t n f : S.O} (hnM : n ∈ S.Mbar)
    (hnN : n ∈ normalizer (S.Lbar g : Set S.O)) (hf : f ∈ Fbar S g t) :
    n * f * n⁻¹ ∈ Fbar S g t := by
  induction hf using closure_induction with
  | mem x hx => exact subset_closure (conj_mem_conjL hnM hnN hx)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem exists_normalizer_conj_eq (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) {τ : S.O} (hτ : τ ∈ conjL S g t) :
    ∃ n ∈ S.Mbar, n ∈ normalizer (S.Lbar g : Set S.O) ∧ τ = n * t * n⁻¹ := by
  obtain ⟨hτL, x, hxM, rfl⟩ := hτ
  exact S5.exists_mem_normalizer_conj H C hxM (fun l hl => Lbar_comm S H.conj_mem ht hl)
    (fun l hl => Lbar_comm S H.conj_mem hτL hl)

theorem mul_mem_conjL (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t)
    {x y : S.O} (hx : x ∈ conjL S g t) (hy : y ∈ conjL S g t) (hxy : x ≠ y) :
    x * y ∈ conjL S g t := by
  have haQ := H.conj_mem
  obtain ⟨n, hnM, hnN, rfl⟩ := exists_normalizer_conj_eq H C ht hx
  have hnN' : n⁻¹ ∈ normalizer (S.Lbar g : Set S.O) := inv_mem hnN
  have hτ : n⁻¹ * y * n⁻¹⁻¹ ∈ conjL S g t := conj_mem_conjL (inv_mem hnM) hnN' hy
  have hτt : n⁻¹ * y * n⁻¹⁻¹ ≠ t := by
    intro he
    apply hxy
    rw [← he]
    group
  obtain ⟨w, hwM, hw⟩ := hkey _ hτ hτt
  obtain ⟨hyL, x', hx'M, rfl⟩ := hy
  refine ⟨mul_mem hx.1 hyL, n * w * n⁻¹ * x', ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem hnM hwM) (inv_mem hnM)) hx'M
  · rw [Lbar_comm S haQ hx.1 hyL]
    calc x' * t * x'⁻¹ * (n * t * n⁻¹) =
        n * ((n⁻¹ * (x' * t * x'⁻¹) * n⁻¹⁻¹) * t) * n⁻¹ := by group
      _ = n * (w * (n⁻¹ * (x' * t * x'⁻¹) * n⁻¹⁻¹) * w⁻¹) * n⁻¹ := by rw [hw]
      _ = n * w * n⁻¹ * x' * t * (n * w * n⁻¹ * x')⁻¹ := by group

theorem mem_conjL_of_mem_Fbar (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t) {f : S.O}
    (hf : f ∈ Fbar S g t) : f = 1 ∨ f ∈ conjL S g t := by
  have haQ := H.conj_mem
  induction hf using closure_induction with
  | mem x hx => exact Or.inr hx
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | hx
    · rw [one_mul]
      exact hy
    rcases hy with rfl | hy
    · rw [mul_one]
      exact Or.inr hx
    by_cases hxy : x = y
    · subst hxy
      exact Or.inl (mul_self_of_mem_Lbar S haQ hx.1)
    · exact Or.inr (mul_mem_conjL H C ht hkey hx hy hxy)
  | inv x _ hx =>
    rcases hx with rfl | hx
    · exact Or.inl inv_one
    · rw [inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S haQ hx.1)]
      exact Or.inr hx

theorem mem_conjL_of_mem_Fbar_of_ne_one (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g)
    (hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t) {f : S.O}
    (hf : f ∈ Fbar S g t) (hf1 : f ≠ 1) : f ∈ conjL S g t :=
  (mem_conjL_of_mem_Fbar H C ht hkey hf).resolve_left hf1

theorem exists_conj_eq_mul_of_mem_Fbar (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) {Y : Subgroup S.O} (hYM : Y ≤ S.Mbar)
    (hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ Y, y * τ * y⁻¹ = τ * t) {f : S.O}
    (hf : f ∈ Fbar S g t) (hft : f ∉ zpowers t) : ∃ y ∈ Y, y * f * y⁻¹ = f * t := by
  have hkey' : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t := by
    intro τ hτ hτt
    obtain ⟨y, hy, he⟩ := hkey τ hτ hτt
    exact ⟨y, hYM hy, he⟩
  have hf1 : f ≠ 1 := fun h => hft (h ▸ one_mem _)
  have hft' : f ≠ t := fun h => hft (h ▸ mem_zpowers t)
  exact hkey f (mem_conjL_of_mem_Fbar_of_ne_one H C ht hkey' hf hf1) hft'

end CFSG.LargeExtraspecial.S9
