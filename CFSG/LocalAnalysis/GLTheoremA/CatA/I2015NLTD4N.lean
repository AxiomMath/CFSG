module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Cert


theorem td4n_exists_conj_le_graphFixedParabolic (t : TwistTag) {k : Type} [Field k] [Finite k]
    {r : ℕ} [Fact r.Prime] [CharP k r] (σ : k ≃+* k)
    (hσ : σ ^ t.order = 1) {A R : Subgroup (ModGL t.tag k)}
    (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom)
    (hRC : R ≤ graphFixedRootGroup t k σ.toRingHom) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag k))) :
    ∃ x ∈ graphFixedRootGroup t k σ.toRingHom, ∃ J : Set (Fin t.foldedTag.rank),
      J ≠ Set.univ ∧
        A.map (MulAut.conj x).toMonoidHom ≤ graphFixedParabolic t k σ.toRingHom J := by
  have := finite_modGL (τ := t.tag) (K := k)
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      r R hRC hRr hR
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL t.tag k, g' = g := ⟨g, rfl⟩
  have hgC : g' ∈ graphFixedRootGroup t k σ.toRingHom := hg
  have hJ' : ((RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l :
      Set (Fin t.foldedTag.rank)) ≠ Set.univ := hJ
  set J : Set (Fin t.foldedTag.rank) := (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l
  change {x : ModGL t.tag k | x ∈ graphFixedRootGroup t k σ.toRingHom ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule t.tag k)) = F c} =
    ((graphFixedParabolic t k σ.toRingHom J).map (MulAut.conj g').toMonoidHom :
      Set (ModGL t.tag k)) at hset
  refine ⟨g'⁻¹, inv_mem hgC, J, hJ', ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hmem := (Set.ext_iff.1 hset a).1
    (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
  rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact hmem

end Cert

@[expose] def TD4NoSL2 (N : ℕ) (E : Type) [Group E] : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F ≤ N →
    ∀ ι : E →* Matrix.SpecialLinearGroup (Fin 2) F, ¬ Function.Injective ι

theorem TD4NoSL2.of_mulEquiv {N : ℕ} {E E' : Type} [Group E] [Group E'] (e : E ≃* E')
    (h : TD4NoSL2 N E') : TD4NoSL2 N E := by
  intro F _ _ _ hF ι hι
  exact h F hF (ι.comp e.symm.toMonoidHom) (hι.comp e.symm.injective)

theorem td4n_exists_hom_complement {G : Type*} [Group G] {P Q L : Subgroup G}
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hdisj : Q ⊓ L = ⊥)
    (hfac : ∀ g ∈ P, ∃ q ∈ Q, ∃ l ∈ L, g = q * l) {E : Subgroup G} (hE : E ≤ P) :
    ∃ ρ : ↥E →* G, (∀ x, ρ x ∈ L) ∧ ∀ x : E, (x : G) * (ρ x)⁻¹ ∈ Q := by
  have hex : ∀ x : E, ∃ l ∈ L, (x : G) * l⁻¹ ∈ Q := by
    intro x
    obtain ⟨q, hq, l, hl, hxql⟩ := hfac x (hE x.2)
    refine ⟨l, hl, ?_⟩
    have : (x : G) * l⁻¹ = q := by rw [hxql]; group
    rw [this]
    exact hq
  have huniq : ∀ (x : G) (l₁ l₂ : G), l₁ ∈ L → l₂ ∈ L → x * l₁⁻¹ ∈ Q → x * l₂⁻¹ ∈ Q → l₁ = l₂ := by
    intro x l₁ l₂ hl₁ hl₂ h₁ h₂
    have hQ : l₂ * l₁⁻¹ ∈ Q := by
      have := Q.mul_mem (Q.inv_mem h₂) h₁
      have e : (x * l₂⁻¹)⁻¹ * (x * l₁⁻¹) = l₂ * l₁⁻¹ := by group
      rwa [e] at this
    have hL : l₂ * l₁⁻¹ ∈ L := L.mul_mem hl₂ (L.inv_mem hl₁)
    have h0 : l₂ * l₁⁻¹ ∈ Q ⊓ L := Subgroup.mem_inf.2 ⟨hQ, hL⟩
    rw [hdisj, Subgroup.mem_bot, mul_inv_eq_one] at h0
    exact h0.symm
  choose ρ₀ hρL hρQ using hex
  refine ⟨MonoidHom.mk' ρ₀ fun x y => ?_, hρL, hρQ⟩
  have hx := hρQ x
  have hy := hρQ y
  have hnorm : (x : G) * ((y : G) * (ρ₀ y)⁻¹) * (x : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.1 (hPQ (hE x.2)) _).1 hy
  refine (huniq ((x * y : E) : G) _ _ (hρL _) (L.mul_mem (hρL x) (hρL y)) (hρQ _) ?_)
  have e : ((x * y : E) : G) * (ρ₀ x * ρ₀ y)⁻¹ =
      ((x : G) * ((y : G) * (ρ₀ y)⁻¹) * (x : G)⁻¹) * ((x : G) * (ρ₀ x)⁻¹) := by
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  rw [e]
  exact Q.mul_mem hnorm hx

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
