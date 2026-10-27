module

public import CFSG.LieType.SpecialLinear.CurtisDatum.NegExcept
public import CFSG.LieType.TitsSimplicity.Core

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits CFSG.LieType.TitsSimplicity
open scoped MatrixGroups

section General

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

theorem nrep_mul_mem_iSup (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (a b : W) :
    nrep hct a * nrep hct b * (nrep hct (a * b))⁻¹ ∈ ⨆ i, H i :=
  mem_iSup_of_actsAs_one hct hext
    (mul_mem (mul_mem (nrep_mem_weylN hct a) (nrep_mem_weylN hct b))
      (inv_mem (nrep_mem_weylN hct (a * b))))
    (by
      have h := ((actsAs_nrep hct a).mul (actsAs_nrep hct b)).mul (actsAs_nrep hct (a * b)).inv
      simpa using h)

theorem iSup_le_normalizer_negUnipotent (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) :
    (⨆ i, H i : Subgroup K) ≤ Subgroup.normalizer ((negUnipotent D : Subgroup K) : Set K) :=
  le_normalizer_iSup₂ fun _t htT γ hγ y hy =>
    (le_iSup₂ (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}) => D.rootGroup γ) γ hγ)
      ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ.1 htT) y).1 hy)

theorem exists_cover (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (g : K) :
    ∃ l ∈ negUnipotent D, ∃ w : W, ∃ h ∈ ⨆ i, H i, ∃ u ∈ posUnipotent D,
      g = l * nrep hct w * (h * u) := by
  classical
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  obtain ⟨v, b₁, hb₁, b₂, hb₂, he⟩ :=
    exists_mem_bruhatCell hct hext ((nrep hct w₀)⁻¹ * g)
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb₁ hb₂
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hb₁
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := hb₂
  have hg : g = nrep hct w₀ * (h₁ * u₁) * nrep hct v * (h₂ * u₂) := by
    calc g = nrep hct w₀ * ((nrep hct w₀)⁻¹ * g) := by group
      _ = nrep hct w₀ * (h₁ * u₁ * nrep hct v * (h₂ * u₂)) := by rw [he]
      _ = nrep hct w₀ * (h₁ * u₁) * nrep hct v * (h₂ * u₂) := by group
  let h₃ : K := nrep hct w₀ * h₁ * (nrep hct w₀)⁻¹
  have hh₃ : h₃ ∈ ⨆ i, H i :=
    conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w₀) hh₁
  let l₁ : K := nrep hct w₀ * u₁ * (nrep hct w₀)⁻¹
  have hl₁ : l₁ ∈ negUnipotent D :=
    nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hu₁
  let h₄ : K := nrep hct w₀ * nrep hct v * (nrep hct (w₀ * v))⁻¹
  have hh₄ : h₄ ∈ ⨆ i, H i := nrep_mul_mem_iSup hct hext w₀ v
  let l₂ : K := h₃ * l₁ * h₃⁻¹
  have hl₂ : l₂ ∈ negUnipotent D :=
    (Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_negUnipotent hct hh₃) l₁).1 hl₁
  let h₅ : K := (nrep hct (w₀ * v))⁻¹ * (h₃ * h₄) * nrep hct (w₀ * v)
  have hh₅ : h₅ ∈ ⨆ i, H i :=
    inv_conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct (w₀ * v)) (mul_mem hh₃ hh₄)
  refine ⟨l₂, hl₂, w₀ * v, h₅ * h₂, mul_mem hh₅ hh₂, u₂, hu₂, ?_⟩
  have e₃ : h₃ = nrep hct w₀ * h₁ * (nrep hct w₀)⁻¹ := rfl
  have e₁ : l₁ = nrep hct w₀ * u₁ * (nrep hct w₀)⁻¹ := rfl
  have e₄ : h₄ = nrep hct w₀ * nrep hct v * (nrep hct (w₀ * v))⁻¹ := rfl
  have e₂ : l₂ = h₃ * l₁ * h₃⁻¹ := rfl
  have e₅ : h₅ = (nrep hct (w₀ * v))⁻¹ * (h₃ * h₄) * nrep hct (w₀ * v) := rfl
  rw [hg]
  simp only [e₂, e₁, e₃, e₄, e₅]
  group

end General

section SpecialLinear

variable (m : ℕ) (F : Type) [Field F]

set_option hygiene false in
local notation "W" => (coxeterMatrix (isFiniteType_A m)).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem
set_option hygiene false in
local notation "nW" =>
  nrep (D := rootDatum m F) (n := weylRep m F) (H := torus m F) (isCTGroupDatum m F)

theorem nW_one : nW (1 : W) = 1 :=
  nrep_one (D := rootDatum m F) (n := weylRep m F) (H := torus m F) (isCTGroupDatum m F)

theorem nW_simple_mul (w : W) (s : Fin m)
    (h : (cs).length ((cs).simple s * w) = (cs).length w + 1) :
    nW ((cs).simple s * w) = weylRep m F s * nW w :=
  nrep_simple_mul (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
    (isCTGroupDatum m F) ((cs).not_isLeftDescent_iff.2 h)

theorem nW_conj (w : W) (s : Fin m)
    (h : (cs).length ((cs).simple s * w) = (cs).length w + 1)
    {x : SpecialLinearGroup (Fin (m + 1)) F} (hx : x ∈ rootGroup m F (Pi.single s 1)) :
    (nW w)⁻¹ * x * nW w ∈ posUnipotent (rootDatum m F) :=
  inversionUnipotent_le_posUnipotent (D := rootDatum m F) ((cs).simple s * w)
    (rootGroup_inv_single_le_inversionUnipotent (D := rootDatum m F)
      ((cs).not_isLeftDescent_iff.2 h)
      (nrep_inv_conj_mem (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
        (isCTGroupDatum m F) w
        ((RootSystem.ofCartan (isFiniteType_A m) ∅).single_mem s) hx))

theorem nW_mul (a b : W) :
    ∃ h ∈ ⨆ k, torus m F k, nW a * nW b = h * nW (a * b) :=
  ⟨nW a * nW b * (nW (a * b))⁻¹,
    nrep_mul_mem_iSup (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
      (isCTGroupDatum m F) (steinbergExtras m F) a b,
    by rw [mul_assoc, inv_mul_cancel, mul_one]⟩

theorem cover (g : SpecialLinearGroup (Fin (m + 1)) F) :
    ∃ l ∈ negUnipotent (rootDatum m F), ∃ w : W,
      ∃ h ∈ ⨆ k, torus m F k, ∃ u ∈ posUnipotent (rootDatum m F),
        g = l * nW w * (h * u) :=
  exists_cover (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
    (isCTGroupDatum m F) (steinbergExtras m F) g

end SpecialLinear

end CFSG.LieType.SpecialLinear

