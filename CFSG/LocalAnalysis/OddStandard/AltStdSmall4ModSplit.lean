module

public import CFSG.LocalAnalysis.SteinbergBVGL3NaturalSelfExtension

public section

namespace CFSG.OddStandard.AltStdSmall4.ModSplit

open Matrix

theorem exists_section {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) W)
    (i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W) (ι : W →ₗ[ZMod 2] W)
    (hi : ∀ (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
      i ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = ρ g (i v))
    (hι : ∀ (g : GL (Fin 3) (ZMod 2)) (w : W), ι (ρ g w) = ρ g (ι w))
    (hinj : Function.Injective i) (hker : LinearMap.ker ι = LinearMap.range i)
    (hrange : LinearMap.range ι = LinearMap.range i) :
    ∃ j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W,
      (∀ (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
        j ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = ρ g (j v)) ∧
      ∀ v, ι (j v) = i v := by
  have hmem : ∀ w, ι w ∈ LinearMap.range i := fun w => hrange ▸ LinearMap.mem_range_self ι w
  let π : W →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    (LinearEquiv.ofInjective i hinj).symm.toLinearMap ∘ₗ ι.codRestrict (LinearMap.range i) hmem
  have hπ : ∀ w, i (π w) = ι w := fun w =>
    LinearEquiv.ofInjective_symm_apply (f := i) (h := hinj) (ι.codRestrict _ hmem w)
  have hπρ : ∀ (g : GL (Fin 3) (ZMod 2)) (w : W),
      π (ρ g w) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ π w := fun g w =>
    hinj (by rw [hπ, hι, ← hπ, hi])
  have hsurj : Function.Surjective π := by
    intro v
    obtain ⟨w, hw⟩ := (hrange ▸ LinearMap.mem_range_self i v : i v ∈ LinearMap.range ι)
    exact ⟨w, hinj (by rw [hπ, hw])⟩
  have hkerπ : LinearMap.ker π = LinearMap.range i := by
    rw [← hker]
    ext w
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hπ, ← map_zero i]
    exact hinj.eq_iff.symm
  obtain ⟨j, hj, hπj, -⟩ :=
    LocalAnalysis.SteinbergBV.natural_binary_three_space_self_extension_splitting ρ i π hi hπρ
      hinj hsurj hkerπ
  refine ⟨j, hj, fun v => ?_⟩
  rw [← hπ]
  exact congrArg i (LinearMap.congr_fun hπj v)

end CFSG.OddStandard.AltStdSmall4.ModSplit
