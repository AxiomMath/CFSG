module

public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Extra

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section IG109

variable {G : Type} [Group G]

theorem mem_center_iff_zOf {Q : Subgroup G} (x : ↥Q) : x ∈ Subgroup.center ↥Q ↔ (x : G) ∈ zOf Q := by
  rw [← center_map_eq]
  exact (Subgroup.mem_map_iff_mem Q.subtype_injective).symm

theorem exists_inner_of_extraspecial_gen [Finite G] {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQe : IsExtraspecialPGroup p ↥Q) (hexp : ∀ x ∈ Q, x ^ p = 1) {g : G}
    (hgN : g ∈ normalizer (Q : Set G)) (hQg : ∀ x ∈ Q, ⁅x⁻¹, g⁆ ∈ zOf Q) :
    ∃ u ∈ Q, u⁻¹ * g ∈ centralizer (Q : Set G) := by
  have hexpD : ∀ x : ↥Q, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hZ : Subgroup.center ↥Q = _root_.commutator ↥Q := hQe.2.1.symm
  have hcZ : Nat.card (Subgroup.center ↥Q) = p := hQe.2.2.2
  obtain ⟨ε⟩ : Nonempty (Subgroup.center ↥Q ≃* Multiplicative (ZMod p)) := by
    have : Fact p.Prime := ⟨hp⟩
    exact CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hcZ
  have : NeZero p := ⟨hp.ne_zero⟩
  have _hmod : Module (ZMod p) (Additive (Abelianization ↥Q)) :=
    AddCommGroup.zmodModule (CFSG.OddSolvableUnitary.nsmul_abelianization_eq_zero hexpD)
  obtain ⟨B, hBa, hBn, hB⟩ := CFSG.OddSolvableUnitary.exists_commForm hZ ε
  let α : ↥Q → ↥Q := fun x => ⟨g * x * g⁻¹, (mem_normalizer_iff.mp hgN x).mp x.2⟩
  have hα_mul : ∀ x y : ↥Q, α (x * y) = α x * α y := fun x y => Subtype.ext (by
    show g * ((x : G) * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
    group)
  have hf : ∀ x : ↥Q, x⁻¹ * α x ∈ Subgroup.center ↥Q := by
    intro x
    rw [mem_center_iff_zOf]
    have h1 : (((x⁻¹ * α x : ↥Q)) : G) = ⁅(x : G)⁻¹, g⁆ := by
      show (x : G)⁻¹ * (g * x * g⁻¹) = ⁅(x : G)⁻¹, g⁆
      rw [commutatorElement_def]; group
    rw [h1]
    exact hQg x x.2
  let f : ↥Q →* Subgroup.center ↥Q :=
    { toFun := fun x => ⟨x⁻¹ * α x, hf x⟩
      map_one' := Subtype.ext (by
        show (1 : ↥Q)⁻¹ * α 1 = 1
        have : α 1 = 1 := Subtype.ext (by show g * (1 : G) * g⁻¹ = 1; group)
        rw [this]; simp)
      map_mul' := fun x y => Subtype.ext (by
        show (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        rw [hα_mul, mul_inv_rev]
        have hc := mem_center_iff.1 (hf x) y⁻¹
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group) }
  let ℓ : Additive (Abelianization ↥Q) →ₗ[ZMod p] ZMod p :=
    (MonoidHom.toAdditiveLeft (ε.toMonoidHom.comp (Abelianization.lift f))).toZModLinearMap p
  have hℓ : ∀ x : ↥Q, ℓ (Additive.ofMul (Abelianization.of x)) = Multiplicative.toAdd (ε (f x)) :=
    fun x => rfl
  have hex : ∃ w : Additive (Abelianization ↥Q), ∀ v, B w v = ℓ v := by
    have : Fact p.Prime := ⟨hp⟩
    have : Finite (Additive (Abelianization ↥Q)) :=
      Finite.of_surjective (fun x : ↥Q => Additive.ofMul (Abelianization.of x))
        fun v => QuotientGroup.mk_surjective (Additive.toMul v)
    have : FiniteDimensional (ZMod p) (Additive (Abelianization ↥Q)) := Module.Finite.of_finite
    exact ⟨(B.toDual hBn).symm ℓ, fun v => by
      rw [← LinearMap.BilinForm.toDual_def hBn, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨w, hw⟩ := hex
  obtain ⟨u, hu⟩ : ∃ u : ↥Q, Additive.ofMul (Abelianization.of u) = w := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    refine ⟨x, ?_⟩
    change Additive.ofMul (QuotientGroup.mk x : Abelianization ↥Q) = w
    rw [hx]
    rfl
  have hcomm : ∀ x : ↥Q, ⁅(u : G), (x : G)⁆ = (x : G)⁻¹ * (g * x * g⁻¹) := by
    intro x
    have h1 := hw (Additive.ofMul (Abelianization.of x))
    rw [← hu, hB u x, hℓ] at h1
    have h3 := ε.injective (Multiplicative.toAdd.injective h1)
    exact congrArg (fun t : Subgroup.center ↥Q => ((t : ↥Q) : G)) h3
  have hE : ExtraG p Q := extraG_of_isExtraspecial hQe
  refine ⟨u, u.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
  have hx := hcomm ⟨h, hh⟩
  have hcZ : ⁅(u : G), h⁆ ∈ zOf Q := by
    rw [← hE.comm_eq]
    exact Subgroup.commutator_mem_commutator u.2 hh
  have hhc : h * ⁅(u : G), h⁆ = ⁅(u : G), h⁆ * h := Subgroup.mem_centralizer_iff.mp hcZ.2 h hh
  have hconj : g * h * g⁻¹ = (u : G) * h * (u : G)⁻¹ := by
    calc g * h * g⁻¹ = h * (h⁻¹ * (g * h * g⁻¹)) := by group
      _ = h * ⁅(u : G), h⁆ := by rw [← hx]
      _ = ⁅(u : G), h⁆ * h := hhc
      _ = (u : G) * h * (u : G)⁻¹ := by rw [commutatorElement_def]; group
  calc h * ((u : G)⁻¹ * g) = (u : G)⁻¹ * ((u : G) * h * (u : G)⁻¹) * g := by group
    _ = (u : G)⁻¹ * (g * h * g⁻¹) * g := by rw [← hconj]
    _ = ((u : G)⁻¹ * g) * h := by group

theorem exists_inner_of_extraspecial [Finite G] {p : ℕ} (hp : p.Prime) {Q P : Subgroup G}
    (hQe : IsExtraspecialPGroup p ↥Q) (hexp : ∀ x ∈ Q, x ^ p = 1) (hQP : ⁅Q, P⁆ ≤ zOf Q)
    (hPn : P ≤ normalizer (Q : Set G)) {g : G} (hg : g ∈ P) :
    ∃ u ∈ Q, u⁻¹ * g ∈ centralizer (Q : Set G) :=
  exists_inner_of_extraspecial_gen hp hQe hexp (hPn hg) fun _ hx =>
    hQP (Subgroup.commutator_mem_commutator (Q.inv_mem hx) hg)

end IG109

end CFSG.GH74.GLS.Stage2.Bender.Thm1
