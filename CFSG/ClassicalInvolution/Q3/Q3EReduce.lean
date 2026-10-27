module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsCentral

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open

variable {K K' X : Type} [Group K] [Group K'] [Group X]

theorem false_of_isClassicalMember3_of_central_cover [Finite K] [Finite X] (Φ : K →* K')
    (hΦ : Function.Surjective Φ) (hΦker : Φ.ker ≤ Subgroup.center K) (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hψker : ψ.ker ≤ Subgroup.center K)
    (hP : ∀ w : K', w * w = 1 → ∀ N : Subgroup K', N ≤ Subgroup.centralizer ({w} : Set K') →
      IsSubnormal N (Subgroup.centralizer ({w} : Set K')) → Group.IsSolvable N →
        IsOddGenerated N → derivedSeries ↥N 2 = ⊥)
    {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) (hz : z ∉ Subgroup.center X) :
    False := by
  classical
  have : Finite K' := Finite.of_surjective Φ hΦ
  set Z : Subgroup X := Φ.ker.map ψ with hZ
  have hZc : Z ≤ Subgroup.center X := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k', rfl⟩ := hψ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hΦker hk) k']
  have hZn : Z.Normal := Subgroup.normal_of_le_center hZc
  set π : X →* X ⧸ Z := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker ≤ Subgroup.center X := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hZc
  have hπz : π z ≠ 1 := fun h1 => hz (hπker (MonoidHom.mem_ker.mpr h1))
  have h' : IsClassicalMember3 (L.map π) (π z) := h.map_central π hπs hπker hπz
  have hker : Φ.ker ≤ (π.comp ψ).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨k, hk, rfl⟩
  let ψ' : K' →* X ⧸ Z := (MonoidHom.liftOfSurjective Φ hΦ) ⟨π.comp ψ, hker⟩
  have hψ'Φ : ∀ k, ψ' (Φ k) = π (ψ k) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply Φ (Function.surjInv hΦ)
      (Function.rightInverse_surjInv hΦ) ⟨π.comp ψ, hker⟩ k
  have hψ's : Function.Surjective ψ' := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    obtain ⟨k, rfl⟩ := hψ x
    exact ⟨Φ k, hψ'Φ k⟩
  have hψ'ker : ψ'.ker ≤ Subgroup.center K' := by
    intro y hy
    obtain ⟨k, rfl⟩ := hΦ y
    rw [MonoidHom.mem_ker, hψ'Φ, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨k₀, hk₀, hk₀k⟩ := hy
    have hkk : k₀⁻¹ * k ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hk₀k, inv_mul_cancel]
    have hc : k ∈ Subgroup.center K := by
      have e : k = k₀ * (k₀⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hΦker hk₀) (hψker hkk)
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨k', rfl⟩ := hΦ y'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc k']
  have : Finite (X ⧸ Z) := Finite.of_surjective π hπs
  exact false_of_isClassicalMember3_of_oddGenerated ψ' hψ's hψ'ker hP h'

end CFSG.ClassicalInvolution.Q3
