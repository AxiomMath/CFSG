module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaExc

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)


theorem oddCoreExp_E6_t1 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    OddCoreExp (rootDiagAut .E6 K (bitsTuple e6BitsD5)) (Nat.card K - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine oddCoreExp_of_fix (center_adjointGroup_eq_bot_field .E6 K)
    (isQuasisimple_e6QD5 hp hp2 hK) (e6QD5_le_fixedSubgroup hK2)
    (fixedSubgroup_le_normalizer_e6QD5 hK2) fun β hβ _ hfix => ?_
  obtain ⟨e, rfl, -⟩ := exists_eq_rootDiagAut_of_odd_fix_e6QD5 hK2 hβ hfix
  change (rootDiagAutHom .E6 K e) ^ (Nat.card K - 1) = 1
  have he : e ^ (Nat.card K - 1) = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    exact PSL.units_pow_card_sub_one (e i)
  rw [← map_pow, he, map_one]

theorem burgRowExp_E6_innerDiag {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {α : MulAut (adjointGroup .E6 K)}
    {g : adjointGroup .E6 K} {a : Fin (Tag.rank .E6) → Kˣ}
    (hαg : ∀ h : adjointGroup .E6 K, (α h : ModGL .E6 K) =
      (g : ModGL .E6 K) * rootDiagUnit .E6 a * h * (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹)
    (hα : orderOf α = 2) : BurgCoreFor α ∨ OddCoreExp α (Nat.card K - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨ψ, b, hb, hψ⟩ := exists_conj_eq_rootDiagAut_of_innerDiagonal
    (Or.inr (Or.inr (Or.inl rfl))) hodd hαg hα2
  have hαψ : α = ψ⁻¹ * rootDiagAut .E6 K b * ψ⁻¹⁻¹ := by
    rw [← hψ]
    group
  obtain ⟨ρ, hρ, w, hw, -⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 e6SignOrbit_check hb
  obtain ⟨n, hn⟩ := exists_conj_rootDiagAut_of_rootChar hw
  have hrow : BurgCoreFor (rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ [])))) ∨
      OddCoreExp (rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))))
        (Nat.card K - 1) →
      BurgCoreFor α ∨ OddCoreExp α (Nat.card K - 1) := by
    rintro (h | h)
    · left
      rw [hαψ, hn, show ψ⁻¹ * (MulAut.conj n *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (MulAut.conj n)⁻¹) * ψ⁻¹⁻¹ = (ψ⁻¹ * MulAut.conj n) *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (ψ⁻¹ * MulAut.conj n)⁻¹ by group]
      exact h.conj _
    · right
      rw [hαψ, hn, show ψ⁻¹ * (MulAut.conj n *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (MulAut.conj n)⁻¹) * ψ⁻¹⁻¹ = (ψ⁻¹ * MulAut.conj n) *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (ψ⁻¹ * MulAut.conj n)⁻¹ by group]
      exact h.conj _
  rw [length_e6SignReps] at hρ
  interval_cases ρ
  ·
    exfalso
    have h1 : rootDiagAut .E6 K (bitsTuple (listMask (τ := .E6) (e6SignReps.getD 0 []))) = 1 := by
      rw [listMask_e6SignReps_zero]
      have : bitsTuple (K := K) (fun _ : Fin (Tag.rank .E6) => false) = 1 := by
        funext j
        simp [bitsTuple]
      rw [this]
      exact (rootDiagAutHom .E6 K).map_one
    rw [h1, mul_one, mul_inv_cancel] at hn
    rw [hαψ, hn, mul_one, inv_inv, inv_mul_cancel, orderOf_one] at hα
    exact absurd hα (by decide)
  · apply hrow
    rw [listMask_e6SignReps_one]
    exact Or.inr (oddCoreExp_E6_t1 hp hp2 hK)
  · apply hrow
    rw [listMask_e6SignReps_two]
    exact Or.inl (burgCoreFor_E6_t2 hK2)

theorem burgRowExp_E6 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (α : MulAut (adjointGroup .E6 K)) (hα : orderOf α = 2) :
    BurgCoreFor α ∨ OddCoreExp α (Nat.card K - 1) := by
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
      exact burgRowExp_E6_innerDiag hp hp2 hK (g := g) (a := a) (fun h => by
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

theorem pow_eq_one_of_mem_oddCentralizerCore_E6 (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .E6 n p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hmod⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
  · exfalso
    simp [classicalTags] at hcl
  · obtain ⟨⟨hp, -, -⟩, hU⟩ := hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hU
    have h1 := pow_eq_one_of_rows hsimple hnab center_adjointGroup_eq_bot e
      (burgRowExp_E6 hp hp2 hK) ht hy
    obtain ⟨c, hc⟩ := PSL.card_sub_one_dvd_sq_sub_one (p ^ f)
    rw [hc, pow_mul, ← hK, h1, one_pow]
  · exfalso
    simp [reeTitsTags] at hree
  · exact absurd h (by decide)

end CFSG.ComponentClassification.Burgoyne.E2
