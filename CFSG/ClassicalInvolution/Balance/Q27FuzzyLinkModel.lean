module

public import CFSG.ClassicalInvolution.Balance.Q27FuzzyModel
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnModel

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (componentClassificationOddCore)
open scoped commutatorElement

section Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem perfect_fundamental_of_member (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (j : Fin D.card) {K : Subgroup G} (hK : K ∈ Φ)
    {R : Subgroup (compModel D j).K} (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hRK : R.map (secComponentHom hs.normalizes D j) = modOdd a K) : ⁅R, R⁆ = R := by
  obtain ⟨z, hz⟩ := hs.member K hK
  exact perfect_of_member_image hp2 (D.isFundTag j) (D.admissible j)
    (fieldCase_of_exp_eq hp2 hq (D.exp_eq j)) (secComponentHom hs.normalizes D j) hR (hs.le K hK)
    hz.nonempty_equiv hRK.symm

theorem secData_exists_conj_of_vertices_free (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (j : Fin D.card) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (hK₁ : K₁ ∈ Φ) (hK₂ : K₂ ∈ Φ) (hz₁ : IsCentralInvolution K₁ z₁)
    (hz₂ : IsCentralInvolution K₂ z₂)
    (h₁ : modOdd a K₁ ≤ (secComponentHom hs.normalizes D j).range)
    (h₂ : modOdd a K₂ ≤ (secComponentHom hs.normalizes D j).range) :
    ∃ (g : G) (hg : g ∈ Subgroup.centralizer ({a} : Set G)),
      oddQuotMk a ⟨g, hg⟩ ∈ (secComponentHom hs.normalizes D j).range ∧ g * z₁ * g⁻¹ = z₂ := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set ψ := secComponentHom hs.normalizes D j with hψ
  have hC₁ : K₁ ≤ C := hs.le K₁ hK₁
  have hC₂ : K₂ ≤ C := hs.le K₂ hK₂
  have hz₁C : z₁ ∈ C := hC₁ hz₁.mem
  have hz₂C : z₂ ∈ C := hC₂ hz₂.mem
  obtain ⟨R₁, hR₁, hR₁K⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hK₁, hC₁⟩ h₁
  obtain ⟨R₂, hR₂, hR₂K⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hK₂, hC₂⟩ h₂
  obtain ⟨w₁, hw₁R, hw₁, hw₁c⟩ := hs.exists_central_lift D j hz₁ hz₁C hR₁K
    (perfect_fundamental_of_member hs D hp2 hq j hK₁ hR₁ hR₁K)
  obtain ⟨w₂, hw₂R, hw₂, hw₂c⟩ := hs.exists_central_lift D j hz₂ hz₂C hR₂K
    (perfect_fundamental_of_member hs D hp2 hq j hK₂ hR₂ hR₂K)
  have hne₁ : ψ w₁ ≠ 1 := by
    rw [hw₁]
    exact oddQuotMk_ne_one hz₁C hz₁.sq hz₁.ne_one
  have hne₂ : ψ w₂ ≠ 1 := by
    rw [hw₂]
    exact oddQuotMk_ne_one hz₂C hz₂.sq hz₂.ne_one
  obtain ⟨g₀, hg₀⟩ := exists_conj_of_central_lifts hp2 (D.isFundTag j) (D.admissible j) ψ
    (secComponentHom_ker_le_center hs.normalizes D j) hR₁ hR₂ hw₁R hw₂R hw₁c hw₂c hne₁ hne₂
    (by rw [hw₁]; exact oddQuotMk_sq_eq_one hz₁C hz₁.sq)
    (by rw [hw₂]; exact oddQuotMk_sq_eq_one hz₂C hz₂.sq)
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (componentClassificationOddCore ↥C) (ψ g₀)
  have hc' : oddQuotMk a c = ψ g₀ := hc
  have himg : oddQuotMk a (c * ⟨z₁, hz₁C⟩ * c⁻¹) = oddQuotMk a ⟨z₂, hz₂C⟩ := by
    have h1 := congrArg ψ hg₀
    rw [map_mul, map_mul, map_inv, hw₁, hw₂, ← hc'] at h1
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hmem : ((c : G) * z₁ * (c : G)⁻¹)⁻¹ * z₂ ∈ oddCoreIn C :=
    ⟨_, QuotientGroup.eq.mp himg, rfl⟩
  have hx2 : (c : G) * z₁ * (c : G)⁻¹ * ((c : G) * z₁ * (c : G)⁻¹) = 1 := by
    calc (c : G) * z₁ * (c : G)⁻¹ * ((c : G) * z₁ * (c : G)⁻¹)
        = (c : G) * (z₁ * z₁) * (c : G)⁻¹ := by group
      _ = 1 := by rw [hz₁.sq]; group
  obtain ⟨y, hy, hyc⟩ := exists_mem_oddCoreIn_conj_eq (X := C) hx2 hz₂.sq hmem
  have hyC : y ∈ C := oddCoreIn_le C hy
  refine ⟨y * c, C.mul_mem hyC c.2, ?_, ?_⟩
  · have : oddQuotMk a ⟨y * c, C.mul_mem hyC c.2⟩ = oddQuotMk a ⟨y, hyC⟩ * oddQuotMk a c := by
      rw [← map_mul]
      rfl
    rw [this, oddQuotMk_eq_one_of_mem_oddCoreIn hy hyC, one_mul, hc']
    exact MonoidHom.mem_range.mpr ⟨g₀, rfl⟩
  · calc y * c * z₁ * (y * c)⁻¹ = y * ((c : G) * z₁ * (c : G)⁻¹) * y⁻¹ := by group
      _ = z₂ := hyc

end Model

end CFSG.ClassicalInvolution.Balance.Q27
