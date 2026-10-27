module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Five

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.Quasithin.B42Sp4 (spM fixK mem_fixK)

private theorem b2count_pi_injective {F : Type} [Field F] [CharP F 2] [Fintype F]
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (α : MulAut (StatedSp 2 F))
    (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F))
    (hφ : ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w)) :
    Function.Injective π := by
  intro g h hgh
  have hmat : spM (α g) = spM (α h) := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    obtain ⟨w, rfl⟩ := φ.surjective v
    rw [← hφ g w, ← hφ h w, hgh]
  exact α.injective (Subtype.ext (Units.ext hmat))

theorem card_mul_card_fix_le_of_natural_sp4 {F : Type} [Field F] [CharP F 2] [Fintype F]
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (π : StatedSp 2 F →* (M ≃ₗ[ZMod 2] M)) (α : MulAut (StatedSp 2 F))
    (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F)) (hφ : ∀ g w, φ (π g w) = (spM (α g)).mulVec (φ w))
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hA : ∀ a ∈ A, ∃ x, ∀ w, a w = π x w)
    (h2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} ≤ Nat.card F ^ 5 := by
  have hπinj := b2count_pi_injective π α φ hφ
  have hAle : A ≤ π.range := by
    intro a ha
    obtain ⟨x, hx⟩ := hA a ha
    exact MonoidHom.mem_range.mpr ⟨x, (LinearEquiv.ext hx).symm⟩
  set Γ₀ : Subgroup (StatedSp 2 F) := (A.comap π).map α with hΓdef
  have hΓ : ∀ x ∈ Γ₀, x * x = 1 := by
    intro x hx
    rw [hΓdef] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyA : π y ∈ A := hy
    have hy2 : y * y = 1 := by
      apply hπinj
      rw [map_mul, h2 (π y) hyA, map_one]
    rw [← map_mul, hy2, map_one]
  let CM := {m : M // ∀ a ∈ A, a m = m}
  have hcardA : Nat.card A = Nat.card (A.comap π) := by
    conv_lhs => rw [← Subgroup.map_comap_eq_self hAle]
    exact Subgroup.card_map_of_injective (K := A.comap π) (f := π) hπinj
  have hcardΓ : Nat.card Γ₀ = Nat.card (A.comap π) := by
    rw [hΓdef]
    exact Subgroup.card_map_of_injective
      (K := A.comap π) (f := (α : StatedSp 2 F →* StatedSp 2 F)) α.injective
  have hcardfix : Nat.card CM = Nat.card ↥(fixK Γ₀) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨φ m.1, ?_⟩
        invFun := fun v => ⟨φ.symm v.1, ?_⟩
        left_inv := fun m => Subtype.ext (φ.symm_apply_apply m.1)
        right_inv := fun v => Subtype.ext (φ.apply_symm_apply v.1) }
    · intro γ hγ
      rw [hΓdef] at hγ
      rcases Subgroup.mem_map.mp hγ with ⟨y, hy, rfl⟩
      change (spM (α y)).mulVec (φ m.1) = φ m.1
      rw [← hφ y m.1, m.2 (π y) hy]
    · intro a ha
      obtain ⟨x, hx⟩ := hA a ha
      have haeq : a = π x := LinearEquiv.ext hx
      apply φ.injective
      rw [hx (φ.symm v.1), hφ x (φ.symm v.1), φ.apply_symm_apply]
      exact (mem_fixK.mp v.2) (α x) (by
        rw [hΓdef]
        refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
        show π x ∈ A
        rw [← haeq]
        exact ha)
  have hmain := card_mul_card_fixK_le_pow_five Γ₀ hΓ
  rw [← hcardA.trans hcardΓ.symm, ← hcardfix] at hmain
  exact hmain

end CFSG.LocalAnalysis.RankThreeUC.S15

end
