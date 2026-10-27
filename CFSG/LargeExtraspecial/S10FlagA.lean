module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S7Perm

public section

namespace CFSG.LargeExtraspecial.S10

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_add_sub_le {X P A : Submodule K V} (hX : X ≤ P ⊓ A) :
    finrank K X + (finrank K ↥(P ⊔ A) - finrank K A) ≤ finrank K P := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P A
  have h2 := Submodule.finrank_mono hX
  have h3 := Submodule.finrank_mono (le_sup_right : A ≤ P ⊔ A)
  omega

theorem finrank_flag (f : V →ₗ[K] V) {A B : Submodule K V} (hAB : A ≤ B) (hA : A.map f ≤ A)
    (hB : B.map f ≤ B) :
    finrank K (A.map f) + (finrank K ↥(B.map f ⊔ A) - finrank K A) +
      (finrank K ↥(LinearMap.range f ⊔ B) - finrank K B) ≤ finrank K (LinearMap.range f) := by
  have h1 := finrank_add_sub_le (X := A.map f) (P := B.map f) (A := A)
    (le_inf (Submodule.map_mono hAB) hA)
  have h2 := finrank_add_sub_le (X := B.map f) (P := LinearMap.range f) (A := B)
    (le_inf (LinearMap.map_le_range) hB)
  omega

theorem finrank_range_le_map_add (f : V →ₗ[K] V) (U : Submodule K V) :
    finrank K (LinearMap.range f) ≤ finrank K (U.map f) + (finrank K V - finrank K U) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  have hrange : LinearMap.range f ≤ U.map f ⊔ C.map f := by
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ U ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hu) (Submodule.mem_map_of_mem hc)
  have h1 := Submodule.finrank_mono hrange
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (U.map f) (C.map f)
  have h3 := Submodule.finrank_map_le f C
  have h4 := Submodule.finrank_add_eq_of_isCompl hC
  omega

theorem finrank_map_add_finrank_ker {U : Type*} [AddCommGroup U] [Module K U] (χ : V →ₗ[K] U)
    {P : Submodule K V} (h : LinearMap.ker χ ≤ P) :
    finrank K (P.map χ) + finrank K (LinearMap.ker χ) = finrank K P := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (χ.domRestrict P)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  rw [← h1, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h)]

theorem finrank_commSpace_sup_fixSpace {x t : V ≃ₗ[K] V} (hxt : x * t = t * x) :
    finrank K ↥(LinearMap.range ((x : V →ₗ[K] V) - 1) ⊔ LinearMap.ker ((t : V →ₗ[K] V) - 1)) =
      finrank K ((LinearMap.range ((t : V →ₗ[K] V) - 1)).map ((x : V →ₗ[K] V) - 1)) +
        finrank K (LinearMap.ker ((t : V →ₗ[K] V) - 1)) := by
  set χ : V →ₗ[K] V := (t : V →ₗ[K] V) - 1 with hχ
  set f : V →ₗ[K] V := (x : V →ₗ[K] V) - 1 with hf
  have hcomm : χ ∘ₗ f = f ∘ₗ χ := by
    ext v
    have e : x (t v) = t (x v) := by
      rw [← LinearEquiv.mul_apply, hxt, LinearEquiv.mul_apply]
    simp only [hχ, hf, LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe,
      Module.End.one_apply, map_sub, e]
    abel
  have hker : (LinearMap.ker χ).map χ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact (Submodule.mem_bot K).mpr hv
  have hmap : (LinearMap.range f ⊔ LinearMap.ker χ).map χ = (LinearMap.range χ).map f := by
    rw [Submodule.map_sup, hker, sup_bot_eq, ← LinearMap.range_comp, hcomm,
      LinearMap.range_comp]
  rw [← hmap, finrank_map_add_finrank_ker χ le_sup_right]

theorem finrank_swap (x : V ≃ₗ[K] V) {U U' D : Submodule K V} (hU : U.map (x : V →ₗ[K] V) ≤ U')
    (hD : U ⊓ U' = D) :
    finrank K ↥(U ⊔ U') + finrank K D ≤
      finrank K ↥(U.map ((x : V →ₗ[K] V) - 1) ⊔ D) + finrank K U' := by
  set P := U.map ((x : V →ₗ[K] V) - 1) ⊔ D with hP
  have hle : U ⊔ U' ≤ P ⊔ U' := by
    refine sup_le (fun u hu => ?_) le_sup_right
    have e : u = x u - ((x : V →ₗ[K] V) - 1) u := by simp
    rw [e]
    refine sub_mem (Submodule.mem_sup_right (hU (Submodule.mem_map_of_mem hu))) ?_
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_map_of_mem hu))
  have hD' : D ≤ P ⊓ U' := le_inf le_sup_right (hD ▸ inf_le_right)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P U'
  have h2 := Submodule.finrank_mono hle
  have h3 := Submodule.finrank_mono hD'
  omega

end CFSG.LargeExtraspecial.S10
