module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeModelDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeProj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmMinusThree
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.ClassicalGroups.Orthogonal

namespace OmMinus

theorem three_ne_zero_of_not_dvd_card {K : Type} [Field K] [Finite K]
    (h : ¬ 3 ∣ Nat.card K) : (3 : K) ≠ 0 := by
  intro h0
  have h1 : (3 : ℕ) • (1 : K) = 0 := by simpa using h0
  have hdvd : addOrderOf (1 : K) ∣ 3 := addOrderOf_dvd_of_nsmul_eq_zero h1
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1' | h3'
  · exact one_ne_zero (AddMonoid.addOrderOf_eq_one_iff.1 h1')
  · apply h
    rw [← h3']
    exact addOrderOf_dvd_natCard _

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem toLinEquiv_mem_orthogonalGroup {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) {A : GL ι K} (hA : A ∈ StatedOmega Q₀) :
    toLinEquiv ι K A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hA
  refine Subgroup.commutator_le.2 ?_ hA
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
    (Subgroup.inv_mem _ h₂)

theorem scalar_sq_eq_one {Q : QuadraticForm K (ι → K)} {v₀ : ι → K} (hv₀ : Q v₀ ≠ 0)
    {z : GL ι K} (hz : z ∈ StatedScalars ι K)
    (hzQ : toLinEquiv ι K z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : z ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.1 ((mem_statedScalars_iff z).1 hz)
  have hcc : c * c = 1 := by
    have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hzQ v₀
    rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h1
    exact mul_right_cancel₀ hv₀ (by rw [one_mul]; exact h1)
  apply (toLinEquiv ι K).injective
  refine LinearEquiv.ext fun v => ?_
  rw [map_pow, map_one, pow_two, LinearEquiv.mul_apply, hc, hc, smul_smul, hcc, one_smul]
  rfl

end Bridge

end OmMinus

open CFSG.LieType.Universal.Spin OmMinus in
theorem i294CrossModelPOmegaMinus4_holds : I294CrossModelPOmegaMinus4 := by
  intro K _ _ hK b c hirr x hx
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_not_dvd_card hK
  have hQ0 : ⇑(quadMinus 4 K b c) = StatedQuadMinus 4 K b c := coe_quadMinus 4 K b c
  obtain ⟨hnd, hT⟩ := regular_quadMinus (n := 4) (by norm_num) hirr
  set Q := quadMinus 4 K b c with hQdef
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, Q v₀ ≠ 0 := by
    obtain ⟨m, hm0⟩ := exists_ne (0 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)
    obtain ⟨n, -, hn⟩ := exists_mem_map_ne_zero (Q := Q) (polarNondegOn_top hnd)
      (Submodule.mem_top (x := m)) hm0
    exact ⟨n, hn⟩
  have hΩO : ∀ A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K,
      A ∈ StatedOmega (StatedQuadMinus 4 K b c) →
        toLinEquiv _ K A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun A hA =>
    toLinEquiv_mem_orthogonalGroup hQ0 hA
  have hZ : ∀ z ∈ (StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 4 K b c)), z ^ 2 = 1 := by
    intro z hz
    have hzs := Subgroup.mem_subgroupOf.1 hz
    exact Subtype.ext (scalar_sq_eq_one hv₀ hzs (hΩO _ z.2))
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨g, hg3, hgx⟩ := exists_lift_pow_three (N := 2) (by norm_num) hZ hx3
  have hg3' : (g : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) ^ 3 = 1 := by
    have := congrArg Subtype.val hg3
    simpa using this
  set ĝ := toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K (g : GL _ K) with hĝ
  have hĝO : ĝ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hΩO _ g.2
  have hĝ3 : ĝ ^ 3 = 1 := by rw [hĝ, ← map_pow, hg3', map_one]
  have hdim : 7 ≤ Module.finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨φ₀, hinj, hφO, hφcomm⟩ := exists_injective_hom_three h3 hnd hdim hĝO hĝ3
  let φ : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →*
      GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K :=
    (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).symm.toMonoidHom.comp φ₀
  have hφ_apply : ∀ a, toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K (φ a) = φ₀ a :=
    fun a => by simp [φ]
  have hφinj : Function.Injective φ :=
    (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).symm.injective.comp hinj
  have hpowA : ∀ a : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3),
      a ^ 3 = 1 := by decide
  have hcommA : ∀ a b : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3), a * b = b * a := fun a b => mul_comm a b
  have hcardA : Nat.card (Multiplicative (ZMod 3) × Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3)) = 3 ^ 3 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hH : ∀ a, φ a ∈ StatedOmega (StatedQuadMinus 4 K b c) := by
    intro a
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hφ_apply]
    obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
    refine hodd (φ₀ a) (hφO a) ?_
    have : orderOf (φ₀ a) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpowA a, map_one])
    exact Odd.of_dvd_nat (by decide) this
  have hsc : ∀ a, φ a ∈ StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K → a = 1 := by
    intro a ha
    have hsq : φ a ^ 2 = 1 := scalar_sq_eq_one hv₀ ha (by rw [hφ_apply]; exact hφO a)
    have hcube : φ a ^ 3 = 1 := by rw [← map_pow, hpowA a, map_one]
    have h1 : φ a = 1 := by
      have e : φ a = φ a ^ 3 * (φ a ^ 2)⁻¹ := by group
      rw [e, hcube, hsq]
      simp
    exact hφinj (h1.trans (map_one φ).symm)
  have hg : ∀ a, (g : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) * φ a =
      φ a * (g : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) := by
    intro a
    apply (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).injective
    rw [map_mul, map_mul, hφ_apply]
    exact (hφcomm a).symm
  have key := le_pRank_centralizer_statedProj hcommA hpowA hcardA φ hφinj hH hsc g hg
  rw [hgx] at key
  exact key

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
