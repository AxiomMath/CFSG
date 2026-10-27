module

public import CFSG.LocalAnalysis.EvenBN.U5.LinGraphField
public import CFSG.LocalAnalysis.EvenBN.U5.LinTorus
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineD

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinGF

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.ABGLocalTools (IsSylowOf)

theorem gfl_le_of_map_le {M Λ : Type*} [Group M] [Group Λ] (π : M →* Λ) {R W W' : Subgroup M}
    (hinj : ∀ x ∈ R, π x = 1 → x = 1) (hW : W ≤ R) (hW' : W' ≤ R)
    (hle : W.map π ≤ W'.map π) : W ≤ W' := by
  intro x hx
  obtain ⟨x', hx', hπx'⟩ := hle (Subgroup.mem_map_of_mem π hx)
  have hxR : x'⁻¹ * x ∈ R := R.mul_mem (R.inv_mem (hW' hx')) (hW hx)
  have hπ1 : π (x'⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hπx', inv_mul_cancel]
  obtain rfl := inv_mul_eq_one.1 (hinj _ hxR hπ1)
  exact hx'

theorem gfl_eq_of_map_eq {M Λ : Type*} [Group M] [Group Λ] (π : M →* Λ) {R W W' : Subgroup M}
    (hinj : ∀ x ∈ R, π x = 1 → x = 1) (hW : W ≤ R) (hW' : W' ≤ R)
    (h : W.map π = W'.map π) : W = W' :=
  le_antisymm (gfl_le_of_map_le π hinj hW hW' h.le) (gfl_le_of_map_le π hinj hW' hW h.ge)

theorem radicals_map_of_injOn {M Λ : Type*} [Group M] [Group Λ] (π : M →* Λ)
    {R R₁ R₂ : Subgroup M} {q : ℕ} (hR : Radicals R R₁ R₂ q)
    (hinj : ∀ x ∈ R, π x = 1 → x = 1) :
    Radicals (R.map π) (R₁.map π) (R₂.map π) q := by
  have hφinj : Function.Injective (π.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hinj (g : M) g.2 hg)
  have hRtop : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hRmap : R.map π = (⊤ : Subgroup R).map (π.comp R.subtype) := by
    rw [← Subgroup.map_map, hRtop]
  have e₁ : (R₁.subgroupOf R).map (π.comp R.subtype) = R₁.map π := by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hR.le₁]
  have e₂ : (R₂.subgroupOf R).map (π.comp R.subtype) = R₂.map π := by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hR.le₂]
  have hR' : Radicals (⊤ : Subgroup R) (R₁.subgroupOf R) (R₂.subgroupOf R) q := by
    apply LinCase.radicals_of_map R.subtype_injective
    rw [hRtop, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hR.le₁, inf_eq_left.2 hR.le₂]
    exact hR
  have hφR := LinearThree.Radicals.map hφinj hR'
  rw [e₁, e₂, ← hRmap] at hφR
  exact hφR

theorem swap_lift {M Λ : Type} [Group M] [Group Λ] [Finite M] [Finite Λ] {f : ℕ} (hf : 2 ≤ f)
    (hΛ : LieModel Λ .PSL 3 2 (2 * f)) {A : Subgroup Λ} (hA : LieModel A .PSU 3 2 f)
    (π : M →* Λ) (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker))
    {τ : MulAut Λ} (hτ : orderOf τ = 2) (hfix : ∀ a ∈ A, τ a = a)
    (hout : τ ∉ (MulAut.conj : Λ →* MulAut Λ).range)
    {σ : MulAut M} (hσ : ∀ m, π (σ m) = τ (π m))
    {R R₁ R₂ : Subgroup M} (hR : IsSylowOf 2 R ⊤)
    (hrad : Radicals R R₁ R₂ ((2 ^ f) ^ 2)) (hσR : R.map σ.toMonoidHom = R) :
    R₁.map σ.toMonoidHom = R₂ ∧ R₂.map σ.toMonoidHom = R₁ := by
  have hRinj : ∀ x ∈ R, π x = 1 → x = 1 := sec39d_jf_inj π hker R hR.isPGroup
  have hV : IsSylowOf 2 (R.map π) ⊤ := LinCase.linto_isSylowOf_map π hπ hker hR
  have hradM : Radicals (R.map π) (R₁.map π) (R₂.map π) ((2 ^ f) ^ 2) :=
    radicals_map_of_injOn π hrad hRinj
  have hcomp : τ.toMonoidHom.comp π = π.comp σ.toMonoidHom := by
    ext m
    exact (hσ m).symm
  have hmapcomp : ∀ W : Subgroup M,
      (W.map σ.toMonoidHom).map π = (W.map π).map τ.toMonoidHom := by
    intro W
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hτV : (R.map π).map τ.toMonoidHom = R.map π := by
    rw [← hmapcomp, hσR]
  obtain ⟨h1, h2⟩ := graphField_swaps_radicals hf hΛ hA hτ hfix hout hV hradM hτV
  have hsig : ∀ W : Subgroup M, W ≤ R → W.map σ.toMonoidHom ≤ R := by
    intro W hW y hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hw' : σ.toMonoidHom w ∈ R.map σ.toMonoidHom := Subgroup.mem_map_of_mem _ (hW hw)
    rwa [hσR] at hw'
  refine ⟨gfl_eq_of_map_eq π hRinj (hsig R₁ hrad.le₁) hrad.le₂ ((hmapcomp R₁).trans h1),
    gfl_eq_of_map_eq π hRinj (hsig R₂ hrad.le₂) hrad.le₁ ((hmapcomp R₂).trans h2)⟩

end LinGF

end CFSG.LocalAnalysis.EvenBN.U5
