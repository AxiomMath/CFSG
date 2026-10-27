module

public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerStructure
public import CFSG.Adapters.Involutions

public section

namespace CFSG

open scoped Pointwise

theorem eq_oddCore_mul_centralizer_of_mem {X : Type*} [Group X] [Finite X] {τ : X}
    (hτ : τ * τ = 1)
    (h : ∀ g : X, g * τ * g⁻¹ * τ⁻¹ ∈ oddCore X) :
    (⊤ : Set X) = (oddCore X : Set X) *
      (Subgroup.centralizer ({τ} : Set X) : Set X) := by
  have hcen : (QuotientGroup.mk τ : X ⧸ oddCore X) ∈
      Subgroup.center (X ⧸ oddCore X) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (oddCore X) y
    show ((g * τ : X) : X ⧸ oddCore X) = ((τ * g : X) : X ⧸ oddCore X)
    rw [QuotientGroup.eq_iff_div_mem]
    have hdiv : (g * τ) / (τ * g) = g * τ * g⁻¹ * τ⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      exact (mul_assoc _ _ _).symm
    rw [hdiv]
    exact h g
  apply le_antisymm
  · intro g _
    obtain ⟨c, hc, k, hk, rfl⟩ :=
      CFSG.Adapters.eq_centralizer_mul_oddCore (G := X) (z := τ) hτ hcen g
    have hOn : (oddCore X).Normal := oddCore_normal X
    have ho : c * k * c⁻¹ ∈ oddCore X := hOn.conj_mem k hk c
    have hmem : c * k * c⁻¹ * c ∈ (oddCore X : Set X) *
        (Subgroup.centralizer ({τ} : Set X) : Set X) :=
      Set.mul_mem_mul ho hc
    have hEq : c * k * c⁻¹ * c = c * k := by group
    rwa [hEq] at hmem
  · exact Set.subset_univ _

theorem eq_oddCore_mul_centralizer_of_isolated {X : Type*} [Group X] [Finite X] {τ : X}
    (hτ1 : τ ≠ 1) (hτ : τ * τ = 1)
    (hiso : ∀ g : X, (g * τ * g⁻¹) * τ = τ * (g * τ * g⁻¹) → g * τ * g⁻¹ = τ) :
    (⊤ : Set X) = (oddCore X : Set X) *
      (Subgroup.centralizer ({τ} : Set X) : Set X) := by
  classical
  let e : Shrink.{0} X ≃* X := Shrink.mulEquiv
  let τ' : Shrink.{0} X := e.symm τ
  haveI : Finite (Shrink.{0} X) := Finite.of_equiv X e.symm.toEquiv
  letI : Fintype (Shrink.{0} X) := Fintype.ofFinite _
  have hτ'e : e τ' = τ := e.apply_symm_apply τ
  have hτ'1 : τ' ≠ 1 := by
    intro h
    apply hτ1
    calc τ = e τ' := (e.apply_symm_apply τ).symm
      _ = e 1 := by rw [h]
      _ = 1 := map_one e
  have hτ'sq : τ' * τ' = 1 := by
    apply e.injective
    simp [map_mul, hτ'e, hτ]
  have hiso' : ∀ g : Shrink.{0} X,
      (g * τ' * g⁻¹) * τ' = τ' * (g * τ' * g⁻¹) →
        g * τ' * g⁻¹ = τ' := by
    intro g hg
    apply e.injective
    have hg' : (e g * τ * (e g)⁻¹) * τ = τ * (e g * τ * (e g)⁻¹) := by
      have := congrArg e hg
      simpa [map_mul, map_inv, hτ'e] using this
    have h := hiso (e g) hg'
    simpa [map_mul, map_inv, hτ'e] using h
  obtain ⟨N', hN'n, hN'odd, hN'⟩ :=
    CFSG.ZStar.BrauerSuzukiFinal.glauberman_zStar (Shrink.{0} X) τ' hτ'1 hτ'sq hiso'
  have hN'O : N' ≤ oddCore (Shrink.{0} X) :=
    CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore N' hN'n hN'odd
  have hOmap : (oddCore (Shrink.{0} X)).map e.toMonoidHom = oddCore X := by
    rw [CFSG.QuasiDihedralFusion.oddCore_eq_pPrimeCore (Shrink.{0} X),
      CFSG.QuasiDihedralFusion.oddCore_eq_pPrimeCore X]
    exact CFSG.pPrimeCore_map_iso 2 e
  refine eq_oddCore_mul_centralizer_of_mem (X := X) hτ ?_
  intro g
  have hg' : e (e.symm g * τ' * (e.symm g)⁻¹ * τ'⁻¹) ∈ (oddCore X : Set X) := by
    have hmem := hN'O (hN' (e.symm g))
    have hmap : e (e.symm g * τ' * (e.symm g)⁻¹ * τ'⁻¹) ∈
        (oddCore (Shrink.{0} X)).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    rwa [hOmap] at hmap
  simpa [map_mul, map_inv, hτ'e] using hg'

end CFSG
