module

public import CFSG.HardMathSupport.Lang.D4Three.CharThree

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K]


theorem exists_layerAct_of_stable (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (H : Subgroup ↥(adjointGroup Tag.D4 K))
    (hH : H = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hU : H.map α.toMonoidHom = H) :
    ∃ (σ : K ≃+* K) (ε : ℕ) (la : LayerAct Tag.D4 α σ), σ ^ 3 = 1 ∧ ε < 3 ∧
      (σ = 1 → ε = 0 → α ∈ inner ↥(adjointGroup Tag.D4 K)) ∧
      ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1 := by
  classical
  have hmemH : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ H ↔ (y : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K :=
    fun y => by rw [hH, Subgroup.mem_subgroupOf]
  obtain ⟨g, a, σ, ε, hε3, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα3
  have hνA : (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ∈ unipotentPairAut Tag.D4 K :=
    mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)
  have hνH : H.map (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε).toMonoidHom = H := by
    rw [hH]; exact hνA.1
  have hgeq : MulAut.conj g = α * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)⁻¹ := by
    rw [hαeq]; group
  have hgH : H.map (MulAut.conj g).toMonoidHom = H := by
    rw [hgeq, map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq hνH, hU]
  have hgH' : H.map (MulAut.conj g)⁻¹.toMonoidHom = H := map_inv_toMonoidHom_of_map_eq hgH
  have hnorm : (g : ModGL Tag.D4 K) ∈
      Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxG : x ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hx
      have hmem : (⟨x, hxG⟩ : ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj g) ⟨x, hxG⟩ ∈ H.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgH] at h1
      exact (hmemH _).1 h1
    · intro hx
      have hxG' : (g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹ ∈ adjointGroup Tag.D4 K :=
        posUnipotent_le_adjointGroup hx
      have hxG : x ∈ adjointGroup Tag.D4 K := by
        have := mul_mem (mul_mem (inv_mem g.2) hxG') g.2
        simpa [mul_assoc] using this
      have hmem : (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj g)⁻¹ ⟨_, hxG'⟩ ∈ H.map (MulAut.conj g)⁻¹.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgH'] at h1
      have e : (MulAut.conj g)⁻¹ (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) = ⟨x, hxG⟩ := by
        apply Subtype.ext
        simp [MulAut.conj_apply, mul_assoc]
      rw [e] at h1
      exact (hmemH _).1 h1
  have hgB : (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
    rw [← CFSG.Quasithin.H13.NQCat.LieCartan.G2.normalizer_posUnipotent_inf_eq
      (K := K) (τ := Tag.D4)]
    exact ⟨hnorm, g.2⟩
  have hg := borelScalar_of_mem_borelGroup hgB
  have hβ : ∀ x : ↥(adjointGroup Tag.D4 K), ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      (g : ModGL Tag.D4 K) * d4F K a σ ε (x : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K)⁻¹ := by
    intro x
    rw [hαeq]
    rfl
  refine ⟨σ, ε, d4LayerAct hg a σ ε hβ, hσ3, hε3, ?_, fun k δ => rfl⟩
  intro hσ hε
  subst hσ
  subst hε
  exact mem_inner_of_normal_form_one hαeq hα3

end CFSG.LocalAnalysis.GLTheoremA
