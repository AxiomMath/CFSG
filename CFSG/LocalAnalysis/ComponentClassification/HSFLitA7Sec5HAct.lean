module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HSetup

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Sec8

namespace Sec5H

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem conjSub_eq_of_relIndex_two {H K : Subgroup G} (hHK : H ≤ K) (h2 : H.relIndex K = 2)
    {g : G} (hg : g ∈ K) : conjSub g H = H := by
  have hN : (H.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two h2
  refine conjSub_eq_of_le (conjSub_le_iff.mpr fun h hh => ?_) le_rfl
  have := hN.conj_mem ⟨h, hHK hh⟩ (by rw [mem_subgroupOf]; exact hh) ⟨g, hg⟩
  rw [mem_subgroupOf] at this
  exact this

end Generic

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

section T₂

variable (D : S.Sec5 F T₁)

theorem T₂_le_T₁ : D.T₂ ≤ T₁ := by rw [D.T₂_eq]; exact inf_le_left

theorem conjSub_R {n : X} (hn : n ∈ D.R) : conjSub n D.T₂ = D.T₂ := by
  refine conjSub_eq_of_relIndex_two D.T₂_le ?_ hn
  have h := Subgroup.relIndex_mul_card (H := D.T₂) (K := D.R)
  rw [inf_eq_left.mpr D.T₂_le, D.card_T₂, D.card_R] at h
  omega

end T₂

namespace Setup

variable {D : S.Sec5 F T₁} (C : Setup D)

include C in
theorem card_T₁ : Nat.card T₁ = 128 := by rw [C.h4.card, S.card_T]

include C in
theorem conjSub_T₁ {n : X} (hn : n ∈ T₁) : conjSub n D.T₂ = D.T₂ := by
  refine conjSub_eq_of_relIndex_two (T₂_le_T₁ D) ?_ hn
  have h := Subgroup.relIndex_mul_card (H := D.T₂) (K := T₁)
  rw [inf_eq_left.mpr (T₂_le_T₁ D), D.card_T₂, C.card_T₁] at h
  omega

include C in
theorem z_mem_T₁ : S.z ∈ T₁ := C.h4.le S.z_mem.1

include C in
theorem g_z : D.g * S.z * D.g⁻¹ = S.z := by
  have h := (D.center_T₁ S.z C.z_mem_T₁).mpr (mem_zpowers _)
  rw [← h D.g D.g_mem, mul_inv_cancel_right]

theorem conj_g_mem_Zs {f : X} (hf : f ∈ C.Zs) : D.g * f * D.g⁻¹ ∈ C.Zs := by
  have hgk := D.g_k
  have hgz := C.g_z
  rw [C.mem_Zs] at hf ⊢
  rcases hf with rfl | rfl | rfl | rfl
  · left; group
  · right; left; exact hgz
  · right; right; right; exact hgk
  · right; right; left
    calc D.g * (S.z * F.kF) * D.g⁻¹ = (D.g * S.z * D.g⁻¹) * (D.g * F.kF * D.g⁻¹) := by group
      _ = F.kF := by rw [hgz, hgk, ← mul_assoc, z_mul_z, one_mul]

theorem conjSub_g_Zs : conjSub D.g C.Zs = C.Zs :=
  conjSub_eq_of_le (conjSub_le_iff.mpr fun _ hf => C.conj_g_mem_Zs hf) le_rfl

@[expose] def Acts (n : X) (π : Fin 8 → Fin 8) : Prop :=
  ∀ i : Fin 8, i.val < 6 → conjSub n (C.Fs i) = C.Fs (π i)

theorem Acts.mul {n m : X} {π ρ : Fin 8 → Fin 8} (hn : C.Acts n π) (hm : C.Acts m ρ)
    (hπ : ∀ i : Fin 8, i.val < 6 → (π i).val < 6) : C.Acts (m * n) (ρ ∘ π) := by
  intro i hi
  rw [conjSub_mul, hn i hi, hm _ (hπ i hi), Function.comp_apply]

theorem Acts.inv {n : X} {π : Fin 8 → Fin 8} (hn : C.Acts n π)
    (hπ : ∀ i : Fin 8, i.val < 6 → (π i).val < 6 ∧ π (π i) = i) : C.Acts n⁻¹ π := by
  intro i hi
  have h := hn (π i) (hπ i hi).1
  rw [(hπ i hi).2] at h
  rw [← h, conjSub_inv_conjSub]

theorem acts_w₂ : C.Acts D.w₂ RH.wtau := fun i _ => C.conjSub_w₂ i

theorem exists_conjSub_g {i : Fin 8} (hi : i.val < 6) :
    ∃ j : Fin 8, j.val < 6 ∧ conjSub D.g (C.Fs i) = C.Fs j := by
  have hle : conjSub D.g (C.Fs i) ≤ D.T₂ := by
    rw [← C.conjSub_T₁ D.g_mem]
    exact conjSub_mono _ (C.Fs_le_T₂ hi)
  obtain ⟨j, hj⟩ := C.eq_Fs_of_elem _ (hle.trans D.T₂_le) (fun a ha => by
      have hb := C.sq_of_mem_Fs (mem_conjSub.mp ha)
      calc a * a = D.g * ((D.g⁻¹ * a * D.g) * (D.g⁻¹ * a * D.g)) * D.g⁻¹ := by group
        _ = 1 := by rw [hb, mul_one, mul_inv_cancel])
    (by rw [card_conjSub, C.card_Fs])
  refine ⟨j, ?_, hj⟩
  by_contra hj6
  have h1 : C.Fs j ⊓ D.T₂ = C.Fs j := inf_eq_left.mpr (hj ▸ hle)
  have h2 := C.card_Fs_inf_T₂ (i := j) (by omega)
  rw [h1, C.card_Fs] at h2
  omega

theorem conjSub_g_zero : conjSub D.g (C.Fs 0) = C.Fs 1 := by
  rw [C.Fs_zero, C.Fs_one]; exact D.g_E

theorem conjSub_g_g {i : Fin 8} (hi : i.val < 6) :
    conjSub D.g (conjSub D.g (C.Fs i)) = C.Fs i := by
  rw [← conjSub_mul, ← pow_two]
  exact C.conjSub_T₂ hi D.g_sq_mem

theorem conjSub_g_one : conjSub D.g (C.Fs 1) = C.Fs 0 := by
  rw [← C.conjSub_g_zero, C.conjSub_g_g (by decide)]

@[expose] def σA : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 6, 7]

@[expose] def σB : Fin 8 → Fin 8 := ![1, 0, 5, 4, 3, 2, 6, 7]

theorem g_image {i j : Fin 8} (hi2 : 2 ≤ i.val) (hi : i.val < 6) (hj : j.val < 6)
    (hij : conjSub D.g (C.Fs i) = C.Fs j) :
    2 ≤ j.val ∧ ((i = 2 ∨ i = 4) → (j = 3 ∨ j = 5)) ∧ ((i = 3 ∨ i = 5) → (j = 2 ∨ j = 4)) := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [← C.conjSub_g_one] at hij
    have := C.Fs_injective (conjSub_injective _ hij)
    subst this; simp at hi2
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [← C.conjSub_g_zero] at hij
    have := C.Fs_injective (conjSub_injective _ hij)
    subst this; simp at hi2
  have hj2 : 2 ≤ j.val := by
    by_contra h
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  have hinter : conjSub D.g (C.Fs i ⊓ C.Fs 1) = C.Fs j ⊓ C.Fs 0 := by
    rw [conjSub_inf, hij, C.conjSub_g_one]
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := (C.inter_Z (f := 1))
  obtain ⟨⟨a, ha0, ha2, haZ⟩, ⟨b, hb0, hb4, hbZ⟩, ⟨c, hc1, hc3, hcZ⟩, ⟨d, hd1, hd5, hdZ⟩⟩ :=
    C.inter_big
  refine ⟨hj2, fun hi' => ?_, fun hi' => ?_⟩
  ·
    have hsmall : C.Fs j ⊓ C.Fs 0 ≤ C.Zs := by
      rw [← hinter, ← C.conjSub_g_Zs]
      refine conjSub_mono _ fun f ⟨hf, hf1⟩ => ?_
      rcases hi' with rfl | rfl
      · exact (C.inter_Z (f := f)).1 hf1 hf
      · exact (C.inter_Z (f := f)).2.1 hf1 hf
    by_contra hj'
    have : j = 2 ∨ j = 4 := by omega
    rcases this with rfl | rfl
    · exact haZ (hsmall ⟨ha2, ha0⟩)
    · exact hbZ (hsmall ⟨hb4, hb0⟩)
  ·
    obtain ⟨e, he, heZ⟩ : ∃ e ∈ C.Fs i ⊓ C.Fs 1, e ∉ C.Zs := by
      rcases hi' with rfl | rfl
      · exact ⟨c, ⟨hc3, hc1⟩, hcZ⟩
      · exact ⟨d, ⟨hd5, hd1⟩, hdZ⟩
    have he' : D.g * e * D.g⁻¹ ∈ C.Fs j ⊓ C.Fs 0 := hinter ▸ conj_mem_conjSub he
    have heZ' : D.g * e * D.g⁻¹ ∉ C.Zs := by
      intro h
      have h' : D.g⁻¹ * (D.g * e * D.g⁻¹) * D.g ∈ C.Zs := by
        rw [← mem_conjSub, C.conjSub_g_Zs]; exact h
      apply heZ
      simpa [mul_assoc] using h'
    by_contra hj'
    have : j = 3 ∨ j = 5 := by omega
    rcases this with rfl | rfl
    · exact heZ' ((C.inter_Z (f := _)).2.2.1 he'.2 he'.1)
    · exact heZ' ((C.inter_Z (f := _)).2.2.2 he'.2 he'.1)

theorem g_acts : C.Acts D.g σA ∨ C.Acts D.g σB := by
  obtain ⟨j2, hj2, h2⟩ := C.exists_conjSub_g (i := 2) (by decide)
  obtain ⟨j3, hj3, h3⟩ := C.exists_conjSub_g (i := 3) (by decide)
  obtain ⟨j4, hj4, h4⟩ := C.exists_conjSub_g (i := 4) (by decide)
  obtain ⟨j5, hj5, h5⟩ := C.exists_conjSub_g (i := 5) (by decide)
  obtain ⟨-, k2, -⟩ := C.g_image (by decide) (by decide) hj2 h2
  obtain ⟨-, -, k3⟩ := C.g_image (by decide) (by decide) hj3 h3
  obtain ⟨-, k4, -⟩ := C.g_image (by decide) (by decide) hj4 h4
  obtain ⟨-, -, k5⟩ := C.g_image (by decide) (by decide) hj5 h5
  have k2 := k2 (Or.inl rfl)
  have k3 := k3 (Or.inl rfl)
  have k4 := k4 (Or.inr rfl)
  have k5 := k5 (Or.inr rfl)
  have inv : ∀ {i j : Fin 8}, i.val < 6 → conjSub D.g (C.Fs i) = C.Fs j →
      conjSub D.g (C.Fs j) = C.Fs i := by
    intro i j hi h
    rw [← h, C.conjSub_g_g hi]
  have inj : ∀ {i i' j : Fin 8}, conjSub D.g (C.Fs i) = C.Fs j →
      conjSub D.g (C.Fs i') = C.Fs j → i = i' := by
    intro i i' j h h'
    exact C.Fs_injective (conjSub_injective _ (h.trans h'.symm))
  rcases k2 with rfl | rfl
  ·
    have h3' := inv (by decide) h2
    have hj4 : j4 = 5 := by
      rcases k4 with rfl | rfl
      · exact absurd (inj h4 h2) (by decide)
      · rfl
    subst hj4
    have h5' := inv (by decide) h4
    left
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact C.conjSub_g_zero
    · exact C.conjSub_g_one
    · exact h2
    · exact h3'
    · exact h4
    · exact h5'
  ·
    have h6' := inv (by decide) h2
    have hj4 : j4 = 3 := by
      rcases k4 with rfl | rfl
      · rfl
      · exact absurd (inj h4 h2) (by decide)
    subst hj4
    have h4' := inv (by decide) h4
    right
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact C.conjSub_g_zero
    · exact C.conjSub_g_one
    · exact h2
    · exact h4'
    · exact h4
    · exact h6'

end Setup

end Sec5H

end CFSG.ComponentClassification.HSFLit
