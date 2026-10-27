module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6Inner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6C4

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem BurgCoreFor.of_conj_eq {T : Type} [Group T] {α γ ψ : MulAut T} (h : ψ * α * ψ⁻¹ = γ)
    (hγ : BurgCoreFor γ) : BurgCoreFor α := by
  have hc := hγ.conj ψ⁻¹
  rwa [← h, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at hc


theorem burgRow_E6 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (α : MulAut (adjointGroup .E6 K)) (hα : orderOf α = 2) :
    BurgCoreFor α ∨ BurgTorusFor α := by
  have : Fact p.Prime := ⟨hp⟩
  have hf := (one_le_and_three_le_of_card hp hp2 hK).1
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have h1 : ∀ x : ModGL Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF α
  have hσ2 := hsq α g a σ ε hgaσ hα2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε with hε | hε
    ·
      exact burgRow_E6_innerDiag hp hp2 hK (g := g) (a := a) (fun h => by
        rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]) hα
    ·
      left
      obtain ⟨ψ, hψ | hψ⟩ := exists_conj_eq_graph_of_graphCoset hodd (g := g) (a := a) (α := α)
        (fun h => (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)) hα2
      · have hc := burgCoreFor_E6_graphField hK2 (δ := (1 : K ≃+* K)) (mul_one 1)
        rw [entrywiseAdjointAut_one, mul_one] at hc
        exact BurgCoreFor.of_conj_eq hψ hc
      · exact BurgCoreFor.of_conj_eq hψ (burgCoreFor_E6_signedGraph hK2)
  ·
    obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    have hσσ : σ * σ = 1 := by rw [← sq]; exact hσ2
    obtain ⟨hfield, β', -, hβα'⟩ :=
      exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
    left
    rcases hε with hε | hε
    ·
      obtain ⟨β, -, hβα⟩ := hfield Tag.E6
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, hψ, -⟩ := hconj α (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one])
        ((sq α).symm.trans hα2)
      have hψe : ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.E6 σ :=
        MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (coe_entrywiseAdjointAut _ σ u).symm)
      exact BurgCoreFor.of_conj_eq hψe (burgCoreFor_E6_entrywise hK2 hσσ)
    ·
      let α' : MulAut (adjointGroup TwistTag.E6.tag K) := α
      obtain ⟨-, hconj⟩ := hβα' g a
      obtain ⟨ψ, hψ, -⟩ := hconj α' (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl))
        ((sq α').symm.trans hα2)
      have hψe : ψ * α' * ψ⁻¹ =
          diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ := by
        refine MulEquiv.ext fun u => Subtype.ext ((hψ u).trans ?_)
        rw [MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut]
      exact BurgCoreFor.of_conj_eq hψe (burgCoreFor_E6_graphField hK2 hσσ)

theorem burgoynePropA_E6 {X : Type} [Group X] [Finite X] (hX : IsM4 X) {n p f : ℕ}
    (hp2 : p ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .E6 n p f) {t : X}
    (ht : orderOf t = 2) {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -⟩ := hX
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hmod⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
  · exfalso
    simp [classicalTags] at hcl
  · obtain ⟨⟨hp, -, -⟩, hU⟩ := hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hU
    exact propAConclusion_of_rows hsimple hnab center_adjointGroup_eq_bot e
      (burgRow_E6 hp hp2 hK) ht hY hYO
  · exfalso
    simp [reeTitsTags] at hree
  · exact absurd h (by decide)

end CFSG.ComponentClassification.Burgoyne.E2
