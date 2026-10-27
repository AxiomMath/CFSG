module

public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Transport

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin

section Reduction

variable {X : Type} [Group X]

theorem conj_inv_conj (h x : X) : MulAut.conj h⁻¹ (MulAut.conj h x) = x := by
  simp [MulAut.conj_apply, mul_assoc]

theorem conj_conj_inv (h x : X) : MulAut.conj h (MulAut.conj h⁻¹ x) = x := by
  simp [MulAut.conj_apply, mul_assoc]

variable [Finite X]

theorem mem_iff_of_map_le {P : Subgroup X} (φ : MulAut X) (h : ∀ p ∈ P, φ p ∈ P) :
    ∀ y, φ y ∈ P ↔ y ∈ P := by
  have hle : P.map φ.toMonoidHom ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp
  have hcard : Nat.card (P.map φ.toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective φ.injective
  have heq : P.map φ.toMonoidHom = P := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  intro y
  refine ⟨fun hy => ?_, h y⟩
  have hy' : φ y ∈ P.map φ.toMonoidHom := by
    rw [heq]
    exact hy
  obtain ⟨y', hy'P, hyy⟩ := hy'
  have : y' = y := φ.injective hyy
  rwa [← this]

theorem mem_normalizer_of_conj_le {F : Subgroup X} {w : X} (h : ∀ f ∈ F, w * f * w⁻¹ ∈ F) :
    w ∈ Subgroup.normalizer (F : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro f
  have := mem_iff_of_map_le (P := F) (MulAut.conj w) h f
  rw [MulAut.conj_apply] at this
  exact this.symm

omit [Finite X] in
theorem mem_conj_iff {P₀ P : Subgroup X} {h : X} (hh : P = P₀.map (MulAut.conj h).toMonoidHom)
    (z : X) : z ∈ P ↔ MulAut.conj h⁻¹ z ∈ P₀ := by
  rw [hh]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have : MulAut.conj h⁻¹ ((MulAut.conj h).toMonoidHom p) = p := conj_inv_conj h p
    rw [this]
    exact hp
  · intro hz
    exact ⟨_, hz, conj_conj_inv h z⟩

theorem fixPointwiseInner_of_sylow {P₀ : Subgroup X} (hP₀ : IsSylowTwoOf P₀ ⊤)
    (h₀ : ∀ α : MulAut X, (∀ y ∈ P₀, α y = y) → α ∈ innerAut X) : FixPointwiseInner X := by
  intro P hP α hα
  obtain ⟨h, -, hh⟩ := hP₀.exists_conj hP
  have hc : (MulAut.conj h : MulAut X) ∈ innerAut X := ⟨h, rfl⟩
  have hα' : (MulAut.conj h)⁻¹ * α * MulAut.conj h ∈ innerAut X := by
    apply h₀
    intro y hy
    have hcy : MulAut.conj h y ∈ P := by
      rw [hh]
      exact Subgroup.mem_map_of_mem _ hy
    show (MulAut.conj h)⁻¹ (α (MulAut.conj h y)) = y
    rw [hα _ hcy]
    exact MulAut.inv_apply_self X (MulAut.conj h) y
  have : α = MulAut.conj h * ((MulAut.conj h)⁻¹ * α * MulAut.conj h) * (MulAut.conj h)⁻¹ := by
    group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hα') (Subgroup.inv_mem _ hc)

theorem four_fixes_of_sylow {P₀ : Subgroup X} (hP₀ : IsSylowTwoOf P₀ ⊤)
    (h₀ : ∀ F : Subgroup X, F ≤ P₀ → IsFourSubgroup F → ∀ φ : MulAut X, (∀ f ∈ F, φ f = f) →
      ∀ y, φ y ∈ P₀ ↔ y ∈ P₀) :
    ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → ∀ F : Subgroup X, F ≤ P → IsFourSubgroup F →
      ∀ φ : MulAut X, (∀ f ∈ F, φ f = f) → ∀ y : X, φ y ∈ P ↔ y ∈ P := by
  intro P hP F hFP hF φ hφ y
  obtain ⟨h, -, hh⟩ := hP₀.exists_conj hP
  have hF' : IsFourSubgroup (F.map (MulAut.conj h⁻¹).toMonoidHom) :=
    isFourSubgroup_map (MulAut.conj h⁻¹) hF
  have hF'le : F.map (MulAut.conj h⁻¹).toMonoidHom ≤ P₀ := by
    rintro _ ⟨f, hf, rfl⟩
    exact (mem_conj_iff hh f).mp (hFP hf)
  have key := h₀ _ hF'le hF' (MulAut.conj h⁻¹ * φ * MulAut.conj h) (by
    rintro _ ⟨f, hf, rfl⟩
    show MulAut.conj h⁻¹ (φ (MulAut.conj h (MulAut.conj h⁻¹ f))) = MulAut.conj h⁻¹ f
    rw [conj_conj_inv, hφ f hf]) (MulAut.conj h⁻¹ y)
  have e : (MulAut.conj h⁻¹ * φ * MulAut.conj h) (MulAut.conj h⁻¹ y) = MulAut.conj h⁻¹ (φ y) := by
    show MulAut.conj h⁻¹ (φ (MulAut.conj h (MulAut.conj h⁻¹ y))) = _
    rw [conj_conj_inv]
  rw [e] at key
  rw [mem_conj_iff hh (φ y), mem_conj_iff hh y]
  exact key

end Reduction

theorem nonempty_mulEquiv_semidihedral {H : Type} [Group H] (a b : H) (ha : a ^ 8 = 1)
    (hb : b ^ 2 = 1) (hab : b * a * b⁻¹ = a ^ 3) (hgen : ∀ x : H, ∃ i j : ℕ, x = a ^ i * b ^ j)
    (hcard : 16 ≤ Nat.card H) : Nonempty (H ≃* SemidihedralGroup 4) := by
  have hab' : b * a * b⁻¹ = a ^ (2 ^ (4 - 2) - 1) := by
    rw [show (2 ^ (4 - 2) - 1 : ℕ) = 3 by norm_num]
    exact hab
  have hrels : ∀ r ∈ semidihedralRels 4, FreeGroup.lift ![a, b] r = 1 := by
    rintro r (rfl | rfl | rfl)
    · simpa using ha
    · simpa using hb
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hab', mul_inv_cancel]
  let φ : SemidihedralGroup 4 →* H := PresentedGroup.toGroup hrels
  have hφ0 : φ (PresentedGroup.of 0) = a := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hφ1 : φ (PresentedGroup.of 1) = b := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨i, j, hx⟩ := hgen x
    refine ⟨PresentedGroup.of 0 ^ i * PresentedGroup.of 1 ^ j, ?_⟩
    rw [map_mul, map_pow, map_pow, hφ0, hφ1, hx]
  have : Finite (SemidihedralGroup 4) := CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  have hle : Nat.card (SemidihedralGroup 4) ≤ Nat.card H := by
    rw [CFSG.Semidihedral.card 4 (by norm_num)]
    exact hcard
  exact ⟨(MulEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hle)).symm⟩

end CFSG.QuasithinUnique.Unc25Small
