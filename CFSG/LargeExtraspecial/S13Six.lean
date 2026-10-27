module

public import CFSG.LargeExtraspecial.S13Dich

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem exists_pair_of_two_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V} (hU : 2 ≤ finrank (ZMod 2) U) :
    ∃ v₁ ∈ U, ∃ v₂ ∈ U, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ := by
  have hne : U ≠ ⊥ := fun h => by rw [h, finrank_bot] at hU; omega
  obtain ⟨v₁, hv₁, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : (ZMod 2) ∙ v₁ < U := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hv₁) fun h => ?_
    have := finrank_span_singleton (K := ZMod 2) hv₁0
    rw [h] at this
    omega
  obtain ⟨v₂, hv₂, hv₂n⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨v₁, hv₁, v₂, hv₂, hv₁0, fun h => hv₂n (h ▸ zero_mem _), fun h => hv₂n ?_⟩
  rw [← h]
  exact Submodule.mem_span_singleton_self _

theorem two_le_finrank_fix {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V} (hU : 3 ≤ finrank (ZMod 2) U)
    {f : V ≃ₗ[ZMod 2] V} {w : V} (hf : ∀ v ∈ U, f v - v ∈ (ZMod 2) ∙ w) :
    2 ≤ finrank (ZMod 2) (U ⊓ fixSpace f : Submodule (ZMod 2) V) := by
  set ψ : U →ₗ[ZMod 2] V := ((f : V →ₗ[ZMod 2] V) - 1).comp U.subtype with hψ
  have hrange : LinearMap.range ψ ≤ (ZMod 2) ∙ w := by
    rintro _ ⟨v, rfl⟩
    exact hf v v.2
  have hker : (LinearMap.ker ψ).map U.subtype ≤ U ⊓ fixSpace f := by
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.mem_inf.mpr ⟨v.2, mem_fixSpace.mpr ?_⟩
    have : ψ v = 0 := hv
    simpa [hψ, sub_eq_zero] using this
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 := (Submodule.finrank_mono hrange).trans (finrank_span_le_card ({w} : Set V))
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  simp only [Set.toFinset_singleton, Finset.card_singleton] at h2
  omega

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem mem_Lbar_of_le_clSub {l : S.O} (hl : l ∈ S.Lbar g) (hlE : l ∉ Ebar S g K)
    {U : Submodule (ZMod 2) S.Qt} (hU3 : 3 ≤ finrank (ZMod 2) U)
    (hpts : ∀ v ∈ U, v ≠ 0 → ∃ h : S.M, v = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∧
      l ∈ S.Lbar ((h : G) * g) ∧ U ≤ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)))
    {u : S.M} (huU : S.cl ((u : G) * g * S.z * ((u : G) * g)⁻¹) ∉ U)
    (hUu : U ≤ S.clSub (S.QG ⊓ S.Qa ((u : G) * g))) :
    l ∈ S.Lbar ((u : G) * g) := by
  have Yu : Hyp13 S ((u : G) * g) K := Y.mul rfl
  have hlinv : ∀ k ∈ K, l * k * l⁻¹ = k⁻¹ := Y.inv_of_not_mem hl hlE
  have hlM : l ∈ S.Mbar := S.Lbar_le_Mbar g hl
  have hll : l * l = 1 := mul_self_of_mem_Lbar S Y.haQ hl
  have hlinv' : l⁻¹ = l := (eq_inv_of_mul_eq_one_left hll).symm
  obtain ⟨v₁, hv₁, v₂, hv₂, hv₁0, hv₂0, hv12⟩ :=
    exists_pair_of_two_le (by omega : 2 ≤ finrank (ZMod 2) U)
  obtain ⟨h₁, rfl, hl₁, -⟩ := hpts _ hv₁ hv₁0
  obtain ⟨h₂, rfl, hl₂, -⟩ := hpts _ hv₂ hv₂0
  have hfix : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((u : G) * g * S.z * ((u : G) * g)⁻¹)) =
      S.cl ((u : G) * g * S.z * ((u : G) * g)⁻¹) :=
    fix_of_mem_Lbar_inf hv12 hl₁ hl₂
      (cl_mem_clSub_symm Y.H (hUu hv₁)) (cl_mem_clSub_symm Y.H (hUu hv₂))
  have hlN : l ∈ normalizer (S.Lbar ((u : G) * g) : Set S.O) :=
    mem_normalizer_of_fix Y.haQ Y.hne (h := u) hlM hfix
  have hcomm : ∀ x ∈ S.Lbar ((u : G) * g), l * x = x * l := by
    intro x hx
    have hxM : x ∈ S.Mbar := S.Lbar_le_Mbar _ hx
    have hxU : ∀ v ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
        (ZMod 2) ∙ S.cl ((u : G) * g * S.z * ((u : G) * g)⁻¹) := fun v hv =>
      S.sub_mem_span_of_mem_clSub hx (hUu hv)
    obtain ⟨w₁, hw₁, w₂, hw₂, hw₁0, hw₂0, hw12⟩ :=
      exists_pair_of_two_le (two_le_finrank_fix hU3 hxU)
    obtain ⟨hw₁U, hw₁x⟩ := Submodule.mem_inf.mp hw₁
    obtain ⟨hw₂U, hw₂x⟩ := Submodule.mem_inf.mp hw₂
    obtain ⟨k₁, rfl, hlk₁, hUk₁⟩ := hpts _ hw₁U hw₁0
    obtain ⟨k₂, rfl, hlk₂, -⟩ := hpts _ hw₂U hw₂0
    have hxN₁ : x ∈ normalizer (S.Lbar ((k₁ : G) * g) : Set S.O) :=
      mem_normalizer_of_fix Y.haQ Y.hne (h := k₁) hxM (mem_fixSpace.mp hw₁x)
    have hxN₂ : x ∈ normalizer (S.Lbar ((k₂ : G) * g) : Set S.O) :=
      mem_normalizer_of_fix Y.haQ Y.hne (h := k₂) hxM (mem_fixSpace.mp hw₂x)
    set ρ := l * (x * l * x⁻¹) with hρ
    have hρ₁ : ρ ∈ S.Lbar ((k₁ : G) * g) :=
      mul_mem hlk₁ ((mem_normalizer_iff.mp hxN₁ l).mp hlk₁)
    have hρ₂ : ρ ∈ S.Lbar ((k₂ : G) * g) :=
      mul_mem hlk₂ ((mem_normalizer_iff.mp hxN₂ l).mp hlk₂)
    have hρu : ρ ∈ S.Lbar ((u : G) * g) := by
      have e : ρ = (l * x * l⁻¹) * x⁻¹ := by rw [hρ, hlinv']; group
      rw [e]
      exact mul_mem ((mem_normalizer_iff.mp hlN x).mp hx) (inv_mem hx)
    have hρE : ρ ∈ Ebar S ((k₁ : G) * g) K := by
      refine (mem_Ebar).mpr ⟨hρ₁, fun k hk => ?_⟩
      have h1 := hlinv k hk
      have hk' : x⁻¹ * k * x ∈ K := by
        have := Y.normal _ (inv_mem hxM) k hk
        simpa using this
      have h2 := hlinv _ hk'
      have e : ρ * k * ρ⁻¹ = k := by
        rw [hρ]
        calc l * (x * l * x⁻¹) * k * (l * (x * l * x⁻¹))⁻¹
            = l * x * (l * (x⁻¹ * k * x) * l⁻¹) * x⁻¹ * l⁻¹ := by group
          _ = l * x * (x⁻¹ * k * x)⁻¹ * x⁻¹ * l⁻¹ := by rw [h2]
          _ = (l * k * l⁻¹)⁻¹ := by group
          _ = k := by rw [h1, inv_inv]
      calc k * ρ = ρ * k * ρ⁻¹ * ρ := by rw [e]
        _ = ρ * k := by group
    have Y₁ : Hyp13 S ((k₁ : G) * g) K := Y.mul rfl
    have hns : S.cl ((u : G) * g * S.z * ((u : G) * g)⁻¹) ∉ Submodule.span (ZMod 2)
        {S.cl ((k₁ : G) * g * S.z * ((k₁ : G) * g)⁻¹),
          S.cl ((k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹)} := fun h =>
      huU ((Submodule.span_le.mpr (Set.insert_subset hw₁U (Set.singleton_subset_iff.mpr hw₂U)))
        h)
    have hρ1 : ρ = 1 := Y₁.eq_one_of_three' hρE ⟨1, by simp⟩ ⟨k₂ * k₁⁻¹, by simp [mul_assoc]⟩
      ⟨u * k₁⁻¹, by simp [mul_assoc]⟩ hρ₁ hρ₂ hρu hw12 (hUk₁ hw₂U)
      (cl_mem_clSub_symm Y.H (hUu hw₁U)) (cl_mem_clSub_symm Y.H (hUu hw₂U)) hns
    have e1 : x * l * x⁻¹ = l := by
      have : x * l * x⁻¹ = l⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← hρ1, hρ])
      rw [this, hlinv']
    calc l * x = x * l * x⁻¹ * x := by rw [e1]
      _ = x * l := by group
  have hρuM : S.ρ u ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨u, rfl⟩
  have hl' : S.ρ u * l * (S.ρ u)⁻¹ ∈ S.Lbar ((u : G) * g) := conj_mem_Lbar_mul S u hl
  have key := conj_mem_Lbar_of_commute' Yu.haQ Yu.C hl' (inv_mem hρuM) (fun x hx => by
    have e : (S.ρ u)⁻¹⁻¹ = S.ρ u := inv_inv _
    rw [show (S.ρ u)⁻¹ * (S.ρ u * l * (S.ρ u)⁻¹) * (S.ρ u)⁻¹⁻¹ = l by group]
    exact hcomm x hx)
  rwa [show (S.ρ u)⁻¹ * (S.ρ u * l * (S.ρ u)⁻¹) * (S.ρ u)⁻¹⁻¹ = l by group] at key

end Hyp13

end CFSG.LargeExtraspecial.S13
