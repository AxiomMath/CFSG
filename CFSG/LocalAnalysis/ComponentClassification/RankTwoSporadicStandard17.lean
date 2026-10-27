module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPWitness

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Conj

variable {G : Type*} [Group G]

theorem mem_normalizer_rightConjugate_iff {H : Subgroup G} {g c : G} :
    c ∈ normalizer (rightConjugate H g : Set G) ↔ g * c * g⁻¹ ∈ normalizer (H : Set G) := by
  simp only [mem_normalizer_iff, mem_rightConjugate_iff]
  constructor
  · intro hh y
    have := hh (g⁻¹ * y * g)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group,
      show g * (c * (g⁻¹ * y * g) * c⁻¹) * g⁻¹ = g * c * g⁻¹ * y * (g * c * g⁻¹)⁻¹ by group]
      at this
  · intro hh y
    have := hh (g * y * g⁻¹)
    rwa [show g * c * g⁻¹ * (g * y * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * y * c⁻¹) * g⁻¹ by group]
      at this

theorem centralizer_rightConjugate (H : Subgroup G) (g : G) :
    centralizer (rightConjugate H g : Set G) = rightConjugate (centralizer (H : Set G)) g := by
  ext x
  rw [mem_rightConjugate_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ rightConjugate H g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hy
    have := h _ hy'
    calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * y := by group
  · intro h y hy
    have hy' : g * y * g⁻¹ ∈ H := (mem_rightConjugate_iff H g y).mp hy
    have := h _ hy'
    calc y * x = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by rw [this]
      _ = x * y := by group

noncomputable def rightConjugateEquiv' (H : Subgroup G) (g : G) : ↥(rightConjugate H g) ≃* ↥H :=
  (H.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm

end Conj

theorem exc_of_yCensus17 (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} (hA : AS76b.Hyp31 A) {X₀ W : Type*} [Group X₀] [Group W]
    [Finite W] {X : Subgroup W} (hW : AutModel X₀ W X) (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X)
    (e : ↥A ⧸ center ↥A ≃* X₀) :
    ∃ ψ : normalizer (A : Set G) →* W, IsActionHom A X ψ ∧
      ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ T : Subgroup G,
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) ∧
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
        ∀ Exc : Subgroup W → Prop, YCensus17 X Exc →
          Exc ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, g, hg, T, hT1, hT2, hY⟩ := exc_of_yCensus h32 h33 hA hW e
  refine ⟨ψ, hψ, g, hg, T, hT1, hT2, fun Exc hc => ?_⟩
  have hYc : YCensus X (fun E => Exc E ∨ PWitness X E) := fun E h1 h2 h3 =>
    (hc E h1 h2 (fun h => h3 (Or.inl h))).resolve_right (fun h => h3 (Or.inr h))
  rcases hY _ hYc with hExc | hPW
  · exact hExc
  exfalso
  have hR := h32 G A hA
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  set A' := rightConjugate A g
  have hCA' : centralizer (A' : Set G) = rightConjugate (centralizer (A : Set G)) g :=
    centralizer_rightConjugate A g
  have hK2 : ∀ k ∈ centralizer (A' : Set G), IsPGroup 2 (zpowers k) → k ^ 2 = 1 := by
    intro k hk hk2
    rw [hCA'] at hk
    have hkK : g * k * g⁻¹ ∈ centralizer (A : Set G) := (mem_rightConjugate_iff _ g k).mp hk
    have h2 : IsPGroup 2 (zpowers (g * k * g⁻¹)) := by
      have := hk2.map (MulAut.conj g).toMonoidHom
      rwa [MonoidHom.map_zpowers] at this
    have hsq := sq_eq_one_of_isPGroup_zpowers hR hkK h2
    have hc' : (g * k * g⁻¹) ^ 2 = g * k ^ 2 * g⁻¹ := conj_pow
    rw [hc'] at hsq
    have := congrArg (fun y => g⁻¹ * y * g) hsq
    simpa [mul_assoc] using this
  have hTC : T ≤ centralizer (A' : Set G) := hCA' ▸ hT2.le
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (A' : Set G) := by
    intro t ht ht1 c _ hct
    have ht2 : t ^ 2 = 1 := hK2 t (hTC ht) (hT2.isPGroup.to_le (zpowers_le.mpr ht))
    have hcK := mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hT2.le ht) ht1 ht2 hct
    rw [mem_normalizer_rightConjugate_iff, hA.standard.2.2.2.1] at hcK
    exact mem_normalizer_rightConjugate_iff.mpr hcK
  let eA : ↥A' ≃* ↥A := rightConjugateEquiv' A g
  have hA'p : commutator ↥A' = ⊤ := by
    have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.standard.1.1
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective)
  let e' : ↥A' ⧸ center ↥A' ≃* X₀ :=
    (QuotientGroup.congr (center ↥A') (center ↥A) eA (map_center_eq eA)).trans e
  obtain ⟨ψ', hψ'⟩ := exists_isActionHom hW hA'p e'
  exact not_pWitness_map hψ hψ' hWX hTC hQ hK2 hPW

theorem sporadicCaseOdd_of_yCensus17 (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {s : TauCeti.SporadicName} {W : Type*} [Group W] [Finite W] {X : Subgroup W}
    (hW : AutModel (Blueprint.NativeSporadic.Carrier s) W X) (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X)
    (hcII : YCensus X (· ≤ X)) (hc : YCensus17 X (fun _ => False)) : SporadicCaseOdd s := by
  intro G _ _ A hH hodd ⟨e⟩
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus hW hcII hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, -, g, -, T, -, -, hExc⟩ := exc_of_yCensus17 h32 h33 hyp hW hWX e
  exact hExc _ hc

end CFSG.ComponentClassification.RankTwoSporadic
