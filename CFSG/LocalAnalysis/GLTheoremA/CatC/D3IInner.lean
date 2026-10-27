module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IBound
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Split

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.HardMathSupport.Timmesfeld.DFour
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Inner

variable {K : Type} [Field K] [Finite K]


theorem chev_card_le_inner [CharP K 3] (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hnot : α ∉ Inn ↥(adjointGroup Tag.D4 K)) (g : ↥(adjointGroup Tag.D4 K)) (hg2 : g * g = 1)
    (hg1 : g ≠ 1) (hαg : α g = g) (S : Sylow 3 ↥(adjointGroup Tag.D4 K))
    (hSα : (S : Subgroup ↥(adjointGroup Tag.D4 K)).map α.toMonoidHom = S)
    (hSg : (S : Subgroup ↥(adjointGroup Tag.D4 K)).map (MulAut.conj g).toMonoidHom = S)
    (A : Subgroup ↥(adjointGroup Tag.D4 K)) (hAS : A ≤ (S : Subgroup ↥(adjointGroup Tag.D4 K)))
    (hfix : ∀ a ∈ A, α a = a) (hfixg : ∀ a ∈ A, g * a * g⁻¹ = a) :
    Nat.card A ≤ Nat.card K ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨P₀, hP₀⟩ := (exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀).1
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (adjointGroup Tag.D4 K) P₀ S
  set U₀ : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) with hU₀
  have hS : (S : Subgroup ↥(adjointGroup Tag.D4 K)) = U₀.map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP₀]
    rfl
  have hmemS : ∀ y, y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) ↔ x⁻¹ * y * x ∈ U₀ := by
    intro y
    rw [hS]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu
    · intro hy
      exact ⟨x⁻¹ * y * x, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hαS : ∀ y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)),
      α y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
    intro y hy
    have := Subgroup.mem_map_of_mem α.toMonoidHom hy
    rwa [hSα] at this
  have hgS : ∀ y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)),
      g * y * g⁻¹ ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
    intro y hy
    have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy
    rw [hSg] at this
    simpa [MulAut.conj_apply] using this
  set α' : MulAut ↥(adjointGroup Tag.D4 K) := (MulAut.conj x)⁻¹ * α * MulAut.conj x with hα'
  have hα'apply : ∀ y, α' y = x⁻¹ * α (x * y * x⁻¹) * x := by
    intro y
    simp [hα', MulAut.conj_apply, MulAut.conj_inv_apply]
  have hα'3 : α' ^ 3 = 1 := by
    have : α' ^ 3 = (MulAut.conj x)⁻¹ * α ^ 3 * MulAut.conj x := by
      have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := α) (i := 3)
      rwa [inv_inv] at h
    rw [this, hα3]; group
  have hnot' : α' ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    rintro ⟨y, hy⟩
    apply hnot
    refine ⟨x * y * x⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hy, hα']
    group
  have hU' : U₀.map α'.toMonoidHom = U₀ := by
    have hle : U₀.map α'.toMonoidHom ≤ U₀ := by
      rintro _ ⟨u, hu, rfl⟩
      have h1 : x * u * x⁻¹ ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
        rw [hmemS]; simpa [mul_assoc] using hu
      have h2 := hαS _ h1
      rw [hmemS] at h2
      change α' u ∈ U₀
      rw [hα'apply]
      exact h2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective α'.injective]
  set g' : ↥(adjointGroup Tag.D4 K) := x⁻¹ * g * x with hg'
  have hg'2 : g' * g' = 1 := by
    calc g' * g' = x⁻¹ * (g * g) * x := by rw [hg']; group
      _ = 1 := by rw [hg2]; group
  have hg'1 : g' ≠ 1 := by
    intro h
    apply hg1
    have : g = x * g' * x⁻¹ := by rw [hg']; group
    rw [this, h]; group
  have hαg' : α' g' = g' := by
    rw [hα'apply]
    have : x * g' * x⁻¹ = g := by rw [hg']; group
    rw [this, hαg]
  have hgU' : U₀.map (MulAut.conj g').toMonoidHom = U₀ := by
    have hle : U₀.map (MulAut.conj g').toMonoidHom ≤ U₀ := by
      rintro _ ⟨u, hu, rfl⟩
      have h1 : x * u * x⁻¹ ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
        rw [hmemS]; simpa [mul_assoc] using hu
      have h2 := hgS _ h1
      rw [hmemS] at h2
      have e : (MulAut.conj g') u = x⁻¹ * (g * (x * u * x⁻¹) * g⁻¹) * x := by
        rw [MulAut.conj_apply, hg']; group
      change (MulAut.conj g') u ∈ U₀
      rw [e]
      exact h2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g').injective]
  set A' : Subgroup ↥(adjointGroup Tag.D4 K) := A.map (MulAut.conj x)⁻¹.toMonoidHom with hA'
  have hA'U : A' ≤ U₀ := by
    rintro _ ⟨a, ha, rfl⟩
    have := (hmemS a).1 (hAS ha)
    change (MulAut.conj x)⁻¹ a ∈ U₀
    rw [MulAut.conj_inv_apply]
    exact this
  have hfix' : ∀ a ∈ A', α' a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change α' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ a
    rw [hα'apply, MulAut.conj_inv_apply]
    have : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
    rw [this, hfix a ha]
  have hfixg'' : ∀ a ∈ A', g' * a * g'⁻¹ = a := by
    rintro _ ⟨a, ha, rfl⟩
    change g' * (MulAut.conj x)⁻¹ a * g'⁻¹ = (MulAut.conj x)⁻¹ a
    rw [MulAut.conj_inv_apply, hg']
    have : x⁻¹ * g * x * (x⁻¹ * a * x) * (x⁻¹ * g * x)⁻¹ = x⁻¹ * (g * a * g⁻¹) * x := by group
    rw [this, hfixg a ha]
  have hcard : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj x)⁻¹.injective
  rw [← hcard]
  exact chev_card_le_inner_stable α' hα'3 hnot' hU' g' hg'2 hg'1 hgU' hαg' A' hA'U hfix' hfixg''

end Inner

@[expose] def D3InnerSylow : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ t : MulAut (D4Model K), t ^ 3 = 1 → t ∉ D4Img K →
      ∀ z : MulAut (D4Model K), z ^ 2 = 1 → z ≠ 1 →
        z ∈ Inn (D4Model K) → z * t = t * z →
        ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → A ≠ ⊥ →
          (∀ a ∈ A, t a = a) → (∀ a ∈ A, z a = a) →
          ∃ S : Sylow 3 (D4Model K), A ≤ (S : Subgroup (D4Model K)) ∧
            (S : Subgroup (D4Model K)).map t.toMonoidHom = S ∧
            (S : Subgroup (D4Model K)).map z.toMonoidHom = S

end CFSG.LocalAnalysis.GLTheoremA
