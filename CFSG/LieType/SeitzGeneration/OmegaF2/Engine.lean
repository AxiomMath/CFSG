module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Descent
public import CFSG.LieType.SeitzGeneration.OmegaF2.ConfigC

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LieType.SeitzGeneration.RootPairOrth
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] {d : ℕ} {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem orthPair_of_F2 [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q)
    (hnd : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdeg : Module.finrank k K = p) (hK : Nat.card K = Nat.card k ^ p)
    (hGen : GenerationFromLine Q k)
    (hDich : ∀ σ : K ≃+* K, (∀ x, x ∈ k ↔ σ x = x) → ∀ (g : Matrix (Fin d) (Fin d) K) (μ : K),
      μ ≠ 0 → g.det ≠ 0 → (∀ v, Q (g *ᵥ v) = μ * Q v) →
      GoodConfig Q k g μ ∨ ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c)
    (hsetup : ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldSetup k Q₀ Q σ p)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hne : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≠
      subfieldFixedGroup k Q₀ Q) :
    Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
      ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
        Set (matrixProjectiveDerived Q))) = ⊤ := by
  obtain ⟨σ, hσo, hσk⟩ := exists_gen_aut k hp hdeg
  have hS := hsetup σ hσo hσk
  set gm : GL (Fin d) K := gp.val.left with hgm
  have hg : ∀ v, Q (gm.val *ᵥ v) = (multiplier Q gp : K) * Q v := fun v => by
    have h := multiplier_spec Q gp v
    rw [coordinateSemilinearMap_apply, hgp] at h
    exact h
  have hdet : gm.val.det ≠ 0 :=
    (((Matrix.isUnit_iff_isUnit_det _).mp gm.isUnit)).ne_zero
  rcases hDich σ hσk gm.val (multiplier Q gp : K) (Units.ne_zero _) hdet hg with
    hgood | ⟨a, ha, heig⟩
  · have hl := elementaryGroup_le_lift_of_good_F2 hk hext hσk hder hnd hp hp2 hK hGen
      (H := Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
        ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
          Set (matrixProjectiveDerived Q))))
      (fun x hx => Subgroup.subset_closure (Or.inl hx)) gp hgp
      (fun x hx => Subgroup.subset_closure (Or.inr hx)) hgood
    exact eq_top_of_elementaryGroup_le hder hl
  · exfalso
    have hle := map_le_of_eigen hS gp hgp ha heig
    apply hne
    have hcard : Nat.card ((subfieldFixedGroup k Q₀ Q).map
        (matrixProjectiveConjugationHom Q gp).toMonoidHom) =
        Nat.card (subfieldFixedGroup k Q₀ Q) :=
      Subgroup.card_map_of_injective (matrixProjectiveConjugationHom Q gp).injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

private theorem linearIndependent_mulVec_pair_smul {g : Matrix (Fin d) (Fin d) K}
    (hdet : g.det ≠ 0) {v w : Fin d → K} (hind : LinearIndependent K ![v, w]) {c : K}
    (hc : c ≠ 0) : LinearIndependent K ![g *ᵥ v, c • (g *ᵥ w)] := by
  have hinj : ∀ x : Fin d → K, g *ᵥ x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hne, hx⟩)
  rw [LinearIndependent.pair_iff] at hind ⊢
  intro s t hst
  have h1 : s • v + (t * c) • w = 0 := by
    apply hinj
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, mul_smul]
    exact hst
  obtain ⟨hs, htc⟩ := hind s (t * c) h1
  exact ⟨hs, (mul_eq_zero.mp htc).resolve_right hc⟩

theorem dich_of_hypCoord [CharP K 2] (S : HypCoord Q) (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) (htail : TailAnisotropic S) :
    ∀ σ : K ≃+* K, (∀ x, x ∈ k ↔ σ x = x) → ∀ (g : Matrix (Fin d) (Fin d) K) (μ : K),
      μ ≠ 0 → g.det ≠ 0 → (∀ v, Q (g *ᵥ v) = μ * Q v) →
      GoodConfig Q k g μ ∨ ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c := by
  intro σ hσk g μ hμ hdet hg
  by_cases hgood : GoodConfig Q k g μ
  · exact Or.inl hgood
  right
  have hbad : ∀ v w : Fin d → K, IsRat k v → IsRat k w → Q v = 0 → Q w = 0 →
      polar Q v w = 0 → BadPlane Q k (g *ᵥ v) (μ⁻¹ • (g *ᵥ w)) := by
    intro v w hv hw hQv hQw hvw
    by_contra hnot
    exact hgood ⟨v, w, hv, hw, hQv, hQw, hvw, hnot⟩
  have hstab : SigmaStable Q k σ g := by
    intro v w hv hw hQv hQw hvw hind
    obtain ⟨hc₁, hc₂, hc₁₂⟩ := similarity_plane_ts hμ hg hQv hQw hvw
    have hind' : LinearIndependent K ![g *ᵥ v, μ⁻¹ • (g *ᵥ w)] :=
      linearIndependent_mulVec_pair_smul hdet hind (inv_ne_zero hμ)
    obtain ⟨h1, -⟩ := sigma_stable_of_bad S hk hext hnd htail hσk hc₁ hc₂ hc₁₂ hind'
      (hbad v w hv hw hQv hQw hvw)
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h1
    exact Submodule.mem_span_pair.mpr ⟨a, b * μ⁻¹, by rw [← hab, mul_smul]⟩
  exact eigen_of_sigma_stable_hyp S hext hσk hdet hstab

theorem orthPair_of_hypCoord_F2 [Finite K] [CharP K 2]
    (S : HypCoord Q) (htail : TailAnisotropic S) (hk : Nat.card k = 2)
    (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q)
    (hnd : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdeg : Module.finrank k K = p) (hK : Nat.card K = Nat.card k ^ p)
    (hsetup : ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldSetup k Q₀ Q σ p)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hne : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≠
      subfieldFixedGroup k Q₀ Q) :
    Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
      ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
        Set (matrixProjectiveDerived Q))) = ⊤ :=
  orthPair_of_F2 hk hext hder hnd hp hp2 hdeg hK
    (generationFromLine_of_hypCoord S hk hext hnd htail) (dich_of_hypCoord S hk hext hnd htail)
    hsetup gp hgp hne

end CFSG.LieType.SeitzGeneration.OmegaF2
