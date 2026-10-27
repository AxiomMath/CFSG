module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs

public section

namespace CFSG.OddStandard.AltStdSmall4.GL62

open scoped Matrix

theorem add_self_eq_zero' (w : Fin 3 → ZMod 2) : w + w = 0 := by
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  funext i
  exact h (w i)

@[expose] def T₁ : Set (Fin 6 → ZMod 2) := Set.range fun w : Fin 3 → ZMod 2 => Fin.append 0 w

@[expose] def T₂ : Set (Fin 6 → ZMod 2) := Set.range fun w : Fin 3 → ZMod 2 => Fin.append w w

@[expose] def img (g : GL (Fin 6) (ZMod 2)) (S : Set (Fin 6 → ZMod 2)) : Set (Fin 6 → ZMod 2) :=
  (fun x => (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x) '' S

theorem img_mul (g h : GL (Fin 6) (ZMod 2)) (S : Set (Fin 6 → ZMod 2)) :
    img (g * h) S = img g (img h S) := by
  simp only [img, Set.image_image, Units.val_mul, Matrix.mulVec_mulVec]

theorem img_one (S : Set (Fin 6 → ZMod 2)) : img 1 S = S := by
  simp [img]

theorem img_inv_img (g : GL (Fin 6) (ZMod 2)) (S : Set (Fin 6 → ZMod 2)) :
    img g⁻¹ (img g S) = S := by
  rw [← img_mul, inv_mul_cancel, img_one]

theorem img_mono (g : GL (Fin 6) (ZMod 2)) {S S' : Set (Fin 6 → ZMod 2)} (h : S ⊆ S') :
    img g S ⊆ img g S' :=
  Set.image_mono h

theorem img_eq_of_invol {g : GL (Fin 6) (ZMod 2)} (hg : g * g = 1) {S S' : Set (Fin 6 → ZMod 2)}
    (h₁ : img g S ⊆ S') (h₂ : img g S' ⊆ S) : img g S = S' := by
  refine Set.Subset.antisymm h₁ ?_
  calc S' = img g (img g S') := by rw [← img_mul, hg, img_one]
    _ ⊆ img g S := img_mono g h₂

theorem img_eq_of_subset {g : GL (Fin 6) (ZMod 2)} {S : Set (Fin 6 → ZMod 2)} (h₁ : img g S ⊆ S)
    (h₂ : img g⁻¹ S ⊆ S) : img g S = S := by
  refine Set.Subset.antisymm h₁ ?_
  calc S = img g (img g⁻¹ S) := by rw [← img_mul, mul_inv_cancel, img_one]
    _ ⊆ img g S := img_mono g h₂

@[expose] def pairStab : Subgroup (GL (Fin 6) (ZMod 2)) where
  carrier := {g | (img g T₁ = T₁ ∧ img g T₂ = T₂) ∨ (img g T₁ = T₂ ∧ img g T₂ = T₁)}
  mul_mem' := by
    rintro g h (⟨hg₁, hg₂⟩ | ⟨hg₁, hg₂⟩) (⟨hh₁, hh₂⟩ | ⟨hh₁, hh₂⟩) <;>
      simp only [Set.mem_setOf_eq, img_mul, hh₁, hh₂, hg₁, hg₂, true_and, and_true, true_or,
        or_true]
  one_mem' := Or.inl ⟨img_one _, img_one _⟩
  inv_mem' := by
    rintro g (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · calc img g⁻¹ T₁ = img g⁻¹ (img g T₁) := by rw [h₁]
          _ = T₁ := img_inv_img g T₁
      · calc img g⁻¹ T₂ = img g⁻¹ (img g T₂) := by rw [h₂]
          _ = T₂ := img_inv_img g T₂
    · refine Or.inr ⟨?_, ?_⟩
      · calc img g⁻¹ T₁ = img g⁻¹ (img g T₂) := by rw [h₂]
          _ = T₂ := img_inv_img g T₂
      · calc img g⁻¹ T₂ = img g⁻¹ (img g T₁) := by rw [h₁]
          _ = T₁ := img_inv_img g T₁

theorem img_dg_T₁ (A : GL (Fin 3) (ZMod 2)) : img (dg A) T₁ ⊆ T₁ := by
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  exact ⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w, by
    dsimp only
    rw [dg_mulVec, Matrix.mulVec_zero]⟩

theorem img_dg_T₂ (A : GL (Fin 3) (ZMod 2)) : img (dg A) T₂ ⊆ T₂ := by
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  exact ⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w, by dsimp only; rw [dg_mulVec]⟩

theorem dg_mem_pairStab (A : GL (Fin 3) (ZMod 2)) : dg A ∈ pairStab :=
  Or.inl ⟨img_eq_of_subset (img_dg_T₁ A) (by rw [← map_inv]; exact img_dg_T₁ A⁻¹),
    img_eq_of_subset (img_dg_T₂ A) (by rw [← map_inv]; exact img_dg_T₂ A⁻¹)⟩

theorem z0_mem_pairStab : z₀ ∈ pairStab := by
  refine Or.inr ⟨img_eq_of_invol z0_mul_self ?_ ?_, img_eq_of_invol z0_mul_self ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, by dsimp only; rw [z0_mulVec, zero_add]⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, by dsimp only; rw [z0_mulVec, add_self_eq_zero']⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, by dsimp only; rw [z0_mulVec, add_self_eq_zero']⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, by dsimp only; rw [z0_mulVec, zero_add]⟩

theorem gW_mul_self : gW * gW = 1 := Units.ext gWMat_mul_self

theorem gW_mulVec_T₁ : ∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
    (gW : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append 0 w = Fin.append w' w' := by
  decide

theorem gW_mulVec_T₂ : ∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
    (gW : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append w w = Fin.append 0 w' := by
  decide

theorem gW_mem_pairStab : gW ∈ pairStab := by
  refine Or.inr ⟨img_eq_of_invol gW_mul_self ?_ ?_, img_eq_of_invol gW_mul_self ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨w', hw'⟩ := gW_mulVec_T₁ w
    exact ⟨w', hw'.symm⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨w', hw'⟩ := gW_mulVec_T₂ w
    exact ⟨w', hw'.symm⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨w', hw'⟩ := gW_mulVec_T₂ w
    exact ⟨w', hw'.symm⟩
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨w', hw'⟩ := gW_mulVec_T₁ w
    exact ⟨w', hw'.symm⟩

theorem B₀_le_pairStab : B₀ ≤ pairStab :=
  sup_le (by rintro _ ⟨A, rfl⟩; exact dg_mem_pairStab A)
    (Subgroup.zpowers_le.2 z0_mem_pairStab)

theorem MW_le_pairStab : MW ≤ pairStab :=
  sup_le B₀_le_pairStab (Subgroup.zpowers_le.2 gW_mem_pairStab)

theorem mulVec_of_mem_pairStab {x : GL (Fin 6) (ZMod 2)} (hx : x ∈ pairStab) :
    ((∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append 0 w = Fin.append 0 w') ∧
      ∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append w w = Fin.append w' w') ∨
    ((∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append 0 w = Fin.append w' w') ∧
      ∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append w w = Fin.append 0 w') := by
  have hT₁ : ∀ w : Fin 3 → ZMod 2, (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append 0 w ∈
      img x T₁ := fun w => ⟨_, ⟨w, rfl⟩, rfl⟩
  have hT₂ : ∀ w : Fin 3 → ZMod 2, (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append w w ∈
      img x T₂ := fun w => ⟨_, ⟨w, rfl⟩, rfl⟩
  rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine Or.inl ⟨fun w => ?_, fun w => ?_⟩
    · obtain ⟨w', hw'⟩ : _ ∈ T₁ := h₁ ▸ hT₁ w
      exact ⟨w', hw'.symm⟩
    · obtain ⟨w', hw'⟩ : _ ∈ T₂ := h₂ ▸ hT₂ w
      exact ⟨w', hw'.symm⟩
  · refine Or.inr ⟨fun w => ?_, fun w => ?_⟩
    · obtain ⟨w', hw'⟩ : _ ∈ T₂ := h₁ ▸ hT₁ w
      exact ⟨w', hw'.symm⟩
    · obtain ⟨w', hw'⟩ : _ ∈ T₁ := h₂ ▸ hT₂ w
      exact ⟨w', hw'.symm⟩

theorem mulVec_of_mem_MW {x : GL (Fin 6) (ZMod 2)} (hx : x ∈ MW) :
    ((∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append 0 w = Fin.append 0 w') ∧
      ∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append w w = Fin.append w' w') ∨
    ((∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append 0 w = Fin.append w' w') ∧
      ∀ w : Fin 3 → ZMod 2, ∃ w' : Fin 3 → ZMod 2,
        (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append w w = Fin.append 0 w') :=
  mulVec_of_mem_pairStab (MW_le_pairStab hx)

@[expose] def cLin : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  appendLin sndLin (fstLin + sndLin)

@[expose] def cInvLin : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  appendLin (fstLin + sndLin) fstLin

theorem cLin_apply (x : Fin 6 → ZMod 2) : cLin x = Fin.append (snd x) (fst x + snd x) := rfl

theorem cInvLin_apply (x : Fin 6 → ZMod 2) : cInvLin x = Fin.append (fst x + snd x) (fst x) := rfl

theorem cLin_cInvLin : cLin ∘ₗ cInvLin = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cLin_apply, cInvLin_apply, fst_append, snd_append, add_comm (fst x),
    add_add_self, LinearMap.id_apply, append_fst_snd]

theorem cInvLin_cLin : cInvLin ∘ₗ cLin = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cLin_apply, cInvLin_apply, fst_append, snd_append, add_comm (snd x),
    add_add_self, LinearMap.id_apply, append_fst_snd]

@[expose] def cGL : GL (Fin 6) (ZMod 2) :=
  ⟨LinearMap.toMatrix' cLin, LinearMap.toMatrix' cInvLin,
    by rw [← LinearMap.toMatrix'_comp, cLin_cInvLin, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, cInvLin_cLin, LinearMap.toMatrix'_id]⟩

theorem cGL_mulVec (v w : Fin 3 → ZMod 2) :
    (cGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w = Fin.append w (v + w) := by
  rw [show (cGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = LinearMap.toMatrix' cLin from rfl,
    LinearMap.toMatrix'_mulVec, cLin_apply, fst_append, snd_append]

theorem cGL_pow_three : cGL ^ 3 = 1 := by
  refine Units.ext ?_
  decide

theorem cGL_ne_one : cGL ≠ 1 := by
  intro h
  have h' := congrArg (fun g : GL (Fin 6) (ZMod 2) => (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  revert h'
  decide

theorem dg_mul_cGL (A : GL (Fin 3) (ZMod 2)) : dg A * cGL = cGL * dg A := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_dg,
    show (cGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = LinearMap.toMatrix' cLin from rfl,
    show dgMat (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) = LinearMap.toMatrix' (dgLin A) from rfl,
    ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, dgLin_apply, cLin_apply, fst_append, snd_append,
    Matrix.mulVec_add]

theorem z0_conj_cGL : z₀ * cGL * z₀⁻¹ = cGL⁻¹ := by
  refine Units.ext ?_
  decide

theorem gS_conj_cGL : gS * cGL * gS⁻¹ = cGL⁻¹ := by
  refine Units.ext ?_
  decide

theorem gG_conj_cGL : gG * cGL * gG⁻¹ = cGL⁻¹ := by
  refine Units.ext ?_
  decide

@[expose] def normC : Subgroup (GL (Fin 6) (ZMod 2)) where
  carrier := {x | x * cGL * x⁻¹ = cGL ∨ x * cGL * x⁻¹ = cGL⁻¹}
  mul_mem' := by
    intro x y hx hy
    have e : x * y * cGL * (x * y)⁻¹ = x * (y * cGL * y⁻¹) * x⁻¹ := by group
    have e' : x * cGL⁻¹ * x⁻¹ = (x * cGL * x⁻¹)⁻¹ := by group
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [e]
    rcases hy with hy | hy <;> rw [hy]
    · exact hx
    · rw [e']
      rcases hx with hx | hx <;> rw [hx]
      · exact Or.inr rfl
      · exact Or.inl (inv_inv _)
  one_mem' := Or.inl (by group)
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases hx with hx | hx
    · refine Or.inl ?_
      calc x⁻¹ * cGL * x⁻¹⁻¹ = x⁻¹ * (x * cGL * x⁻¹) * x⁻¹⁻¹ := by rw [hx]
        _ = cGL := by group
    · refine Or.inr ?_
      calc x⁻¹ * cGL * x⁻¹⁻¹ = x⁻¹ * (x * cGL * x⁻¹)⁻¹ * x⁻¹⁻¹ := by rw [hx, inv_inv cGL]
        _ = cGL⁻¹ := by group

theorem conj_zpow_mem_zpowers {x : GL (Fin 6) (ZMod 2)} (hx : x ∈ normC) (n : ℤ) :
    x * cGL ^ n * x⁻¹ ∈ Subgroup.zpowers cGL := by
  rw [← conj_zpow]
  rcases hx with hx | hx <;> rw [hx]
  · exact Subgroup.zpow_mem_zpowers cGL n
  · rw [inv_zpow']
    exact Subgroup.zpow_mem_zpowers cGL (-n)

theorem normC_le_normalizer :
    normC ≤ Subgroup.normalizer (Subgroup.zpowers cGL : Set (GL (Fin 6) (ZMod 2))) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨n, rfl⟩
    exact conj_zpow_mem_zpowers hx n
  · rintro ⟨n, hn⟩
    dsimp only at hn
    have h' := conj_zpow_mem_zpowers (normC.inv_mem hx) n
    rwa [hn, show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h'

theorem dg_mem_normC (A : GL (Fin 3) (ZMod 2)) : dg A ∈ normC :=
  Or.inl (by rw [dg_mul_cGL, mul_inv_cancel_right])

theorem z0_mem_normC : z₀ ∈ normC := Or.inr z0_conj_cGL

theorem B₀_le_normC : B₀ ≤ normC :=
  sup_le (by rintro _ ⟨A, rfl⟩; exact dg_mem_normC A) (Subgroup.zpowers_le.2 z0_mem_normC)

theorem MS_le_normC : MS ≤ normC :=
  sup_le B₀_le_normC (Subgroup.zpowers_le.2 (Or.inr gS_conj_cGL))

theorem MG_le_normC : MG ≤ normC :=
  sup_le B₀_le_normC (Subgroup.zpowers_le.2 (Or.inr gG_conj_cGL))

theorem MS_le_normalizer :
    MS ≤ Subgroup.normalizer (Subgroup.zpowers cGL : Set (GL (Fin 6) (ZMod 2))) :=
  MS_le_normC.trans normC_le_normalizer

theorem MG_le_normalizer :
    MG ≤ Subgroup.normalizer (Subgroup.zpowers cGL : Set (GL (Fin 6) (ZMod 2))) :=
  MG_le_normC.trans normC_le_normalizer

end CFSG.OddStandard.AltStdSmall4.GL62
