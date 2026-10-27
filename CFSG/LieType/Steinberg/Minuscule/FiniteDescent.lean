module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Chevalley


variable {τ : Tag} {D : MinData τ} (hV : D.Valid)

theorem minBC_comp {k k' k'' : Type*} [Field k] [Field k'] [Field k'']
    (ι : k →+* k') (η : k' →+* k'') :
    (minBC hV η).comp (minBC hV ι) = minBC hV (η.comp ι) := by
  apply MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top hV k)
  rintro _ ⟨i, c, rfl | rfl⟩ <;>
    simp only [MonoidHom.comp_apply, minBC_xm_single, minBC_xm_neg_single,
      RingHom.comp_apply]

theorem MinData.Valid.exists_finset_descent {k : Type*} [Field k]
    (g : hV.minGroup k) :
    ∃ S : Finset k, ∀ F : Subfield k, (S : Set k) ⊆ F →
      ∃ g₀ : hV.minGroup F, minBC hV F.subtype g₀ = g := by
  classical
  have hg : g ∈ Subgroup.closure {x : hV.minGroup k | ∃ (i : Fin τ.rank) (c : k),
      x = hV.xm k (Pi.single i 1) c ∨ x = hV.xm k (-Pi.single i 1) c} := by
    rw [closure_xm_simple_eq_top]
    exact Subgroup.mem_top _
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, c, rfl | rfl⟩ := hx
    · refine ⟨{c}, fun F hF => ⟨hV.xm F (Pi.single i 1) ⟨c, hF (by simp)⟩, ?_⟩⟩
      rw [minBC_xm_single]
      rfl
    · refine ⟨{c}, fun F hF => ⟨hV.xm F (-Pi.single i 1) ⟨c, hF (by simp)⟩, ?_⟩⟩
      rw [minBC_xm_neg_single]
      rfl
  | one =>
    exact ⟨∅, fun F _ => ⟨1, map_one _⟩⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨S, hS⟩ := ihx
    obtain ⟨T, hT⟩ := ihy
    refine ⟨S ∪ T, fun F hF => ?_⟩
    obtain ⟨x₀, hx₀⟩ := hS F fun a ha => hF (Finset.mem_union_left T ha)
    obtain ⟨y₀, hy₀⟩ := hT F fun a ha => hF (Finset.mem_union_right S ha)
    exact ⟨x₀ * y₀, by rw [map_mul, hx₀, hy₀]⟩
  | inv x hx ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨S, fun F hF => ?_⟩
    obtain ⟨x₀, hx₀⟩ := hS F hF
    exact ⟨x₀⁻¹, by rw [map_inv, hx₀]⟩

theorem MinData.Valid.exists_finite_subfield_lift
    {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    (S : Finset (hV.minGroup Ω))
    (k₀ : Type) [Field k₀] [Finite k₀] (ι₀ : k₀ →+* Ω) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (κ : k₀ →+* k) (ι : k →+* Ω),
      ι.comp κ = ι₀ ∧ ∀ g ∈ S, ∃ g₀ : hV.minGroup k, minBC hV ι g₀ = g := by
  classical
  have : CharP k₀ 2 := RingHom.charP ι₀ ι₀.injective 2
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra k₀ Ω := ι₀.toAlgebra
  have : IsScalarTower (ZMod 2) k₀ Ω :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : Algebra.IsAlgebraic k₀ Ω :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := k₀)
  have hdesc : ∀ g : {x // x ∈ S}, ∃ T : Finset Ω, ∀ F : Subfield Ω, (T : Set Ω) ⊆ F →
      ∃ g₀ : hV.minGroup F, minBC hV F.subtype g₀ = g.1 := fun g =>
    hV.exists_finset_descent g.1
  choose Ts hTs using hdesc
  let T : Finset Ω := Finset.univ.biUnion Ts
  obtain ⟨F, hFfin, hTF, hkF⟩ := exists_finite_subfield_of_finset (K := k₀) (L := Ω) T
  refine ⟨F, inferInstance, hFfin, ι₀.codRestrict F (fun x => hkF ⟨x, rfl⟩),
    F.subtype, RingHom.ext fun _ => rfl, ?_⟩
  intro g hg
  exact hTs ⟨g, hg⟩ F fun a ha => hTF (Finset.mem_biUnion.mpr
    ⟨⟨g, hg⟩, Finset.mem_univ _, ha⟩)

end CFSG.LieType.Steinberg.Minuscule
