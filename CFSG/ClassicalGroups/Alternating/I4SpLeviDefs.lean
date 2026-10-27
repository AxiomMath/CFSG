module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.Alternating.I4SpPlane

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

@[expose] def leviGroup (BN : BilinForm K N) (H : Submodule K N) : Subgroup (Gsp BN) where
  carrier := {g | ∀ x ∈ H, g.app x = x}
  one_mem' := fun x _ => rfl
  mul_mem' := fun {g h} hg hh x hx => by rw [Gsp.app_mul, hh x hx, hg x hx]
  inv_mem' := fun {g} hg x hx => by
    calc g⁻¹.app x = g⁻¹.app (g.app x) := by rw [hg x hx]
      _ = x := Gsp.app_inv_app g x

@[expose] def IsLeviSpace (BN : BilinForm K N) (ℓ H : Submodule K N) : Prop :=
  IsLine BN ℓ ∧ ℓ ≤ H ∧ finrank K H = 4 ∧ ∀ x ∈ H, (∀ y ∈ H, BN x y = 0) → x = 0

@[expose] noncomputable def leviRoot (hBN : BN.IsAlt) (n : N) : Subgroup (Gsp BN) :=
  Subgroup.closure (Set.range (Tsp hBN n))

section Basic

variable [FiniteDimensional K N] {ℓ H : Submodule K N}

omit [FiniteDimensional K N] in
theorem IsLeviSpace.restrict_nondegenerate (hH : IsLeviSpace BN ℓ H) (hBN : BN.IsAlt) :
    (BN.restrict H).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · exact Subtype.ext (hH.2.2.2 x x.2 fun z hz => hx ⟨z, hz⟩)
  · refine Subtype.ext (hH.2.2.2 y y.2 fun z hz => ?_)
    rw [← hBN.neg_eq, neg_eq_zero]
    exact hy ⟨z, hz⟩

theorem IsLeviSpace.isCompl (hH : IsLeviSpace BN ℓ H) (hBN : BN.IsAlt) :
    IsCompl H (BN.orthogonal H) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hBN.isRefl
    (hH.restrict_nondegenerate hBN)

theorem IsLeviSpace.finrank_orthogonal (hH : IsLeviSpace BN ℓ H) (hBNnd : BN.Nondegenerate) :
    finrank K (BN.orthogonal H) = finrank K N - 4 := by
  rw [LinearMap.BilinForm.finrank_orthogonal hBNnd, hH.2.2.1]

theorem IsLeviSpace.orthogonal_line (hH : IsLeviSpace BN ℓ H) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) : BN.orthogonal ℓ = ℓ ⊔ BN.orthogonal H := by
  have hle : ℓ ⊔ BN.orthogonal H ≤ BN.orthogonal ℓ := by
    refine sup_le (fun x hx => ?_) (LinearMap.BilinForm.orthogonal_le hH.2.1)
    exact fun n hn => hH.1.1 n hn x hx
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hinf : ℓ ⊓ BN.orthogonal H = ⊥ :=
    eq_bot_iff.mpr (le_trans (inf_le_inf_right _ hH.2.1) (hH.isCompl hBN).inf_eq_bot.le)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq ℓ (BN.orthogonal H)
  rw [hinf, finrank_bot, add_zero, hH.1.2, hH.finrank_orthogonal hBNnd] at h1
  have h2 := LinearMap.BilinForm.finrank_orthogonal hBNnd ℓ
  have h3 : 4 ≤ finrank K N := hH.2.2.1 ▸ Submodule.finrank_le H
  rw [h1, h2, hH.1.2]
  omega

end Basic

theorem exists_isLeviSpace [FiniteDimensional K N] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) : ∃ H, IsLeviSpace BN ℓ H := by
  obtain ⟨a, c, hac, hind, rfl⟩ := hℓ.exists_pair
  have hca : BN c a = 0 := by rw [← hBN.neg_eq a c, hac, neg_zero]
  have haa : BN a a = 0 := hBN.self_eq_zero a
  have hcc : BN c c = 0 := hBN.self_eq_zero c
  obtain ⟨x₁, hx₁⟩ := exists_apply_eq_of_linearIndependent hBNnd hind ![1, 0]
  obtain ⟨x₂, hx₂⟩ := exists_apply_eq_of_linearIndependent hBNnd hind ![0, 1]
  have h1a : BN x₁ a = 1 := by simpa using hx₁ 0
  have h1c : BN x₁ c = 0 := by simpa using hx₁ 1
  have h2a : BN x₂ a = 0 := by simpa using hx₂ 0
  have h2c : BN x₂ c = 1 := by simpa using hx₂ 1
  have hBaX₁ : BN a x₁ = -1 := by
    have h := hBN.neg_eq x₁ a
    rw [h1a] at h
    exact h.symm
  have hBcX₁ : BN c x₁ = 0 := by
    have h := hBN.neg_eq x₁ c
    rw [h1c, neg_zero] at h
    exact h.symm
  have hBaX₂ : BN a x₂ = 0 := by
    have h := hBN.neg_eq x₂ a
    rw [h2a, neg_zero] at h
    exact h.symm
  have hBcX₂ : BN c x₂ = -1 := by
    have h := hBN.neg_eq x₂ c
    rw [h2c] at h
    exact h.symm
  have hrep : ∀ g : Fin 4 → K,
      ∑ i, g i • ![a, c, x₁, x₂] i = g 0 • a + g 1 • c + g 2 • x₁ + g 3 • x₂ := by
    intro g
    simp [Fin.sum_univ_four, add_assoc]
  have hexp : ∀ α β γ δ : K, ∀ y : N,
      BN (α • a + β • c + γ • x₁ + δ • x₂) y
        = α * BN a y + β * BN c y + γ * BN x₁ y + δ * BN x₂ y := by
    intro α β γ δ y
    simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hli : LinearIndependent K ![a, c, x₁, x₂] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [hrep g] at hg
    have e1 : BN (g 0 • a + g 1 • c + g 2 • x₁ + g 3 • x₂) a = 0 := by
      rw [hg]
      simp
    have e2 : BN (g 0 • a + g 1 • c + g 2 • x₁ + g 3 • x₂) c = 0 := by
      rw [hg]
      simp
    rw [hexp] at e1 e2
    have hg2 : g 2 = 0 := by simpa [haa, hca, h1a, h2a] using e1
    have hg3 : g 3 = 0 := by simpa [hac, hcc, h1c, h2c] using e2
    rw [hg2, hg3] at hg
    have hg' : g 0 • a + g 1 • c = 0 := by simpa using hg
    obtain ⟨hg0, hg1⟩ := LinearIndependent.pair_iff.mp hind (g 0) (g 1) hg'
    intro i
    fin_cases i <;> simp [hg0, hg1, hg2, hg3]
  set H : Submodule K N := Submodule.span K (Set.range ![a, c, x₁, x₂]) with hHdef
  have ha_H : a ∈ H := Submodule.subset_span (show a ∈ Set.range ![a, c, x₁, x₂] from ⟨0, rfl⟩)
  have hc_H : c ∈ H := Submodule.subset_span (show c ∈ Set.range ![a, c, x₁, x₂] from ⟨1, rfl⟩)
  have hx₁_H : x₁ ∈ H :=
    Submodule.subset_span (show x₁ ∈ Set.range ![a, c, x₁, x₂] from ⟨2, rfl⟩)
  have hx₂_H : x₂ ∈ H :=
    Submodule.subset_span (show x₂ ∈ Set.range ![a, c, x₁, x₂] from ⟨3, rfl⟩)
  refine ⟨H, ?_⟩
  unfold IsLeviSpace
  refine ⟨hℓ, ?_, ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · exact ha_H
    · exact hc_H
  · rw [hHdef, finrank_span_eq_card hli, Fintype.card_fin]
  · intro h hh hperp
    rw [hHdef] at hh
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hh
    rw [hrep g] at hg
    subst hg
    have e_a := hperp a ha_H
    have e_c := hperp c hc_H
    have e_x₁ := hperp x₁ hx₁_H
    have e_x₂ := hperp x₂ hx₂_H
    rw [hexp] at e_a e_c e_x₁ e_x₂
    have hg2 : g 2 = 0 := by simpa [haa, hca, h1a, h2a] using e_a
    have hg3 : g 3 = 0 := by simpa [hac, hcc, h1c, h2c] using e_c
    have hg0 : g 0 = 0 := by simpa [hg2, hg3, hBaX₁, hBcX₁] using e_x₁
    have hg1 : g 1 = 0 := by simpa [hg2, hg3, hBaX₂, hBcX₂] using e_x₂
    simp [hg0, hg1, hg2, hg3]

end CFSG.ClassicalGroups.Alternating
