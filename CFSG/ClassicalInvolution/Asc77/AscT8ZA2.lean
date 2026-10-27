module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZA1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CliffordAlgebra CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.Exotic

namespace T8ZZ

variable {p f : ℕ} [Fact p.Prime]

theorem plus_prod_central (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R₁ R₂ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (h₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)))
    (h₂ : R₂ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hc : Commutes R₁ R₂) {ζ₁ ζ₂ : spinGroup (quadPlus 4 (GaloisField p f))}
    (hζ₁ : InvOf R₁ ζ₁) (hζ₂ : InvOf R₂ ζ₂) :
    ζ₁ * ζ₂ ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hQ := centralQuot_plus (p := p) (f := f) hp2 (le_refl 4) hn3 hq
  have hodd := odd_card_galoisField hp2 hq
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [finrank_plus]
  obtain ⟨i₁, hi₁⟩ := hQ.map_mem R₁ h₁
  obtain ⟨i₂, hi₂⟩ := hQ.map_mem R₂ h₂
  have e₁ : spinAction (quadPlus 4 (GaloisField p f)) ζ₁ = i₁ :=
    invOf_eq hodd hi₁ (hQ.invOf h₁ hζ₁)
  have e₂ : spinAction (quadPlus 4 (GaloisField p f)) ζ₂ = i₂ :=
    invOf_eq hodd hi₂ (hQ.invOf h₂ hζ₂)
  obtain ⟨c, hcv⟩ := fund_prod_scalar hodd hdim hi₁ hi₂ ((hQ.commutes_iff h₁).mpr hc)
  refine mem_center_of_spinAction_eq_smul _
    (exists_map_ne_zero_of_hypPair _ (plusPair (GaloisField p f) (⟨0, by norm_num⟩ : Fin 4)))
    (c := c) (fun v => ?_)
  rw [map_mul]
  show (spinAction (quadPlus 4 (GaloisField p f)) ζ₁ *
    spinAction (quadPlus 4 (GaloisField p f)) ζ₂) v = c • v
  rw [e₁, e₂]
  exact hcv v

theorem plus_card_center_le :
    Nat.card (Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f)))) ≤ 4 := by
  have hn3 : 3 ≤ 4 := by norm_num
  set F := GaloisField p f with hF
  set Q := quadPlus 4 F with hQ
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := F) hn3
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_hypPair _ (plusPair F (⟨0, by norm_num⟩ : Fin 4))
  have hQ0 : Q ≠ 0 := (nondegenerate_quadPlus 4 F).ne_zero
  have hpm : ∀ x ∈ Subgroup.center (spinGroup Q),
      (∀ v, spinAction Q x v = v) ∨ (∀ v, spinAction Q x v = -v) := by
    intro x hx
    have hx' : x ∈ (StatedScalars _ F).comap (spinMatrix Q) := by
      rw [← hcomap, hZ]
      exact hx
    rw [Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hx'
    obtain ⟨c, hc⟩ := mem_scalars.mp hx'
    have hc2 : c * c = 1 := by
      have h := map_spinAction Q x v₀
      rw [hc, map_smul_eq_sq] at h
      have h' : (c ^ 2 - 1) * Q v₀ = 0 := by rw [sub_mul, h, one_mul, sub_self]
      linear_combination (mul_eq_zero.mp h').resolve_right hv₀
    rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
    · left
      intro v
      rw [hc, one_smul]
    · right
      intro v
      rw [hc, neg_smul, one_smul]
  have hker : ∀ x : spinGroup Q, (∀ v, spinAction Q x v = v) →
      x = 1 ∨ x = spinGroup.negOne Q hQ0 := by
    intro x hx
    have hxk : x ∈ (spinMatrix Q).ker := by
      rw [ker_spinMatrix, MonoidHom.mem_ker]
      exact LinearEquiv.ext hx
    rcases (mem_ker_spinMatrix_quadPlus_iff x).mp hxk with h | h
    · exact Or.inl h
    · exact Or.inr ((eq_negOne_iff Q hQ0 x).mpr h)
  set ε : spinGroup Q := spinGroup.negOne Q hQ0 with hε
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : spinGroup Q, ∀ x ∈ Subgroup.center (spinGroup Q),
      (∀ v, spinAction Q x v = -v) → x = x₁ ∨ x = ε * x₁ := by
    by_cases hB : ∃ x₀ ∈ Subgroup.center (spinGroup Q), ∀ v, spinAction Q x₀ v = -v
    · obtain ⟨x₀, hx₀, hx₀v⟩ := hB
      refine ⟨x₀⁻¹, fun x hx hxv => ?_⟩
      have hy : ∀ v, spinAction Q (x * x₀) v = v := fun v => by
        rw [map_mul, LinearEquiv.mul_apply, hx₀v, map_neg, hxv, neg_neg]
      rcases hker _ hy with h | h
      · left
        calc x = (x * x₀) * x₀⁻¹ := by group
          _ = x₀⁻¹ := by rw [h, one_mul]
      · right
        calc x = (x * x₀) * x₀⁻¹ := by group
          _ = ε * x₀⁻¹ := by rw [h]
    · exact ⟨1, fun x hx hxv => absurd ⟨x, hx, hxv⟩ hB⟩
  have hsub : (Subgroup.center (spinGroup Q) : Set (spinGroup Q)) ⊆ {1, ε, x₁, ε * x₁} := by
    intro x hx
    rcases hpm x hx with h | h
    · rcases hker x h with h1 | h1
      · simp [h1]
      · simp [h1]
    · rcases hx₁ x hx h with h1 | h1 <;> simp [h1]
  calc Nat.card (Subgroup.center (spinGroup Q))
      = (Subgroup.center (spinGroup Q) : Set (spinGroup Q)).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, ε, x₁, ε * x₁} : Set (spinGroup Q)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      have h2 := Set.ncard_insert_le ε ({x₁, ε * x₁} : Set (spinGroup Q))
      have h3 := Set.ncard_insert_le x₁ ({ε * x₁} : Set (spinGroup Q))
      rw [Set.ncard_singleton] at h3
      omega

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
