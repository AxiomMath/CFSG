module

public import CFSG.LargeExtraspecial.S12Good
public import CFSG.LargeExtraspecial.DW2ModBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def secRank (g : V ≃ₗ[ZMod 2] V) (A B : Submodule (ZMod 2) V) : ℕ :=
  finrank (ZMod 2) ↥(B.map ((g : V →ₗ[ZMod 2] V) - 1) ⊔ A) - finrank (ZMod 2) A

theorem sub_one_apply (g : V ≃ₗ[ZMod 2] V) (v : V) :
    ((g : V →ₗ[ZMod 2] V) - 1) v = g v - v := by
  simp

variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem secRank_bot_top (g : V ≃ₗ[ZMod 2] V) :
    secRank g ⊥ ⊤ = finrank (ZMod 2) ↥(commSpace g) := by
  rw [secRank, Submodule.map_top, sup_bot_eq, finrank_bot, Nat.sub_zero]

theorem secRank_eq_zero_iff {g : V ≃ₗ[ZMod 2] V} {A B : Submodule (ZMod 2) V} :
    secRank g A B = 0 ↔ ∀ b ∈ B, g b - b ∈ A := by
  rw [secRank, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h b hb
    have heq : B.map ((g : V →ₗ[ZMod 2] V) - 1) ⊔ A = A :=
      (Submodule.eq_of_le_of_finrank_le le_sup_right h).symm
    rw [← sub_one_apply, ← heq]
    exact mem_sup_left (mem_map_of_mem hb)
  · intro h
    refine Submodule.finrank_mono (sup_le ?_ le_rfl)
    rintro _ ⟨b, hb, rfl⟩
    rw [sub_one_apply]
    exact h b hb

theorem secRank_add_le {g : V ≃ₗ[ZMod 2] V} {A B C : Submodule (ZMod 2) V} (hAB : A ≤ B)
    (hBC : B ≤ C) (hgB : ∀ b ∈ B, g b ∈ B) : secRank g A B + secRank g B C ≤ secRank g A C := by
  unfold secRank
  set γ : V →ₗ[ZMod 2] V := (g : V →ₗ[ZMod 2] V) - 1 with hγ
  have hMB : B.map γ ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hγ, sub_one_apply]
    exact sub_mem (hgB b hb) hb
  have hMBC : B.map γ ≤ C.map γ := map_mono hBC
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (C.map γ ⊔ A) B
  have h2 : C.map γ ⊔ A ⊔ B = C.map γ ⊔ B := by rw [sup_assoc, sup_eq_right.mpr hAB]
  have h3 : B.map γ ⊔ A ≤ (C.map γ ⊔ A) ⊓ B :=
    le_inf (sup_le_sup_right hMBC A) (sup_le hMB hAB)
  have h4 := Submodule.finrank_mono h3
  have h5 := Submodule.finrank_mono (le_sup_right : A ≤ B.map γ ⊔ A)
  have h6 := Submodule.finrank_mono (le_sup_right : B ≤ C.map γ ⊔ B)
  have h7 := Submodule.finrank_mono (le_sup_right : A ≤ C.map γ ⊔ A)
  rw [h2] at h1
  omega

variable {Y : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem one_le_secRank {D : Set (V ≃ₗ[ZMod 2] V)} (hgen : Y = Subgroup.closure D)
    (hcl : ∀ d ∈ D, ∀ d' ∈ D, ∃ g ∈ Y, d' = g * d * g⁻¹) {A B : Submodule (ZMod 2) V}
    (hA : IsInv Y A) (hB : IsInv Y B) (hnu : ¬ IsUnip Y A B) {d : V ≃ₗ[ZMod 2] V} (hd : d ∈ D) :
    1 ≤ secRank d A B := by
  by_contra h0
  have h0' : secRank d A B = 0 := by omega
  rw [secRank_eq_zero_iff] at h0'
  have hDY : ∀ t ∈ D, t ∈ Y := fun t ht => hgen ▸ Subgroup.subset_closure ht
  have hall : ∀ t ∈ D, t ∈ secCent A B := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := hcl d hd t ht
    refine mem_secCent_of_isInv hB (hDY _ ht) fun b hb => ?_
    have e : (g * d * g⁻¹) b - b = g (d (g⁻¹ b) - g⁻¹ b) := by
      simp [LinearEquiv.mul_apply, map_sub]
    rw [e]
    exact hA g hg _ (h0' _ (hB.inv_apply_mem hg hb))
  have hle : Y ≤ secCent A B := by
    rw [hgen, Subgroup.closure_le]
    exact hall
  exact hnu (isUnip_of_commSub_le (commSub_le_of_le_secCent hle))

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_bot_of_isUnip (hO2 : S12NoNormalTwo Y) (h : IsUnip Y ⊥ ⊤) : Y = ⊥ :=
  hO2 Y le_rfl (isPGroup_of_isUnip h) fun _ hy => (Subgroup.mem_normalizer_iff).mpr fun _ =>
    ⟨fun hx => Y.mul_mem (Y.mul_mem hy hx) (Y.inv_mem hy), fun hx => by
      have e := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hx) hy
      simpa [mul_assoc] using e⟩

end CFSG.LargeExtraspecial.DW
