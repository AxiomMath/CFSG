module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {X S : Subgroup G}

theorem mem_normalizer_of_theta_normalizes (hA : Asc81bHyp X S) {M : Subgroup G}
    (hMX : M ≤ X) (hSM : S ≤ M) {Ω : Type*} (θ : ↥M →* Equiv.Perm Ω)
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S) (g : ↥M)
    (hg : θ g ∈ Subgroup.normalizer
      ((((thompsonJ S).subgroupOf M).map θ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))) :
    (g : G) ∈ Subgroup.normalizer (S : Set G) := by
  classical
  set W : Subgroup (Equiv.Perm Ω) := ((thompsonJ S).subgroupOf M).map θ with hW
  have hJS : thompsonJ S ≤ S := thompsonJ_le_self S
  set R : Subgroup G := (W.comap θ).map M.subtype with hR
  have hRS : R ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨j, hj, hjy⟩ := hy
    have h1 : θ (j⁻¹ * y) = 1 := by rw [map_mul, map_inv, hjy, inv_mul_cancel]
    have h2 := hker _ h1
    have hjS : (j : G) ∈ S := hJS (Subgroup.mem_subgroupOf.1 hj)
    have : (y : G) = (j : G) * ((j⁻¹ * y : ↥M) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    show (y : G) ∈ S
    rw [this]
    exact S.mul_mem hjS h2
  have hJR : thompsonJ S ≤ R := by
    intro x hx
    exact ⟨⟨x, hSM (hJS hx)⟩, ⟨⟨x, hSM (hJS hx)⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩, rfl⟩
  have hJeq : thompsonJ R = thompsonJ S := (CFSG.Quasithin.thompsonJ_eq_of_le hJR hRS).symm
  have hgR : (g : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hnorm := Subgroup.mem_normalizer_iff.1 hg
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨g * y * g⁻¹, ?_, by simp⟩
      have := (hnorm (θ y)).1 hy
      simpa [map_mul, map_inv] using this
    · rintro ⟨y, hy, hyx⟩
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · have h1 : θ (g⁻¹ * y * g) = (θ g)⁻¹ * θ y * θ g := by simp [map_mul, map_inv]
        have h2 : θ g * ((θ g)⁻¹ * θ y * θ g) * (θ g)⁻¹ = θ y := by group
        have := (hnorm ((θ g)⁻¹ * θ y * θ g)).2 (by rw [h2]; exact hy)
        simpa [h1] using this
      · have hyx' : (y : G) = (g : G) * x * (g : G)⁻¹ := hyx
        show ((g⁻¹ * y * g : ↥M) : G) = x
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hyx']
        group
  have hgJ : (g : G) ∈ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← hJeq]; exact normalizer_le_normalizer_thompsonJ R hgR
  have hS2 := hA.twoRadical.isPGroup
  have hS1 := hA.twoRadical.2.1
  have hne : thompsonJ S ≠ ⊥ := Setup.thompsonJ_ne_bot hS2 hS1
  have hchar := Setup.characteristic_thompsonJ S
  have hcgs : X ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ cgsIn X S :=
    le_iSup_of_le (thompsonJ S) (le_iSup_of_le hJS (le_iSup_of_le hne (le_iSup_of_le hchar le_rfl)))
  rw [hA.cgs] at hcgs
  exact (hcgs ⟨hMX g.2, hgJ⟩).2

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
