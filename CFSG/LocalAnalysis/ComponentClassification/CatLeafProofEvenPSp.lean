module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocleSuzuki
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem nonempty_mulEquiv_psp_of_lieModel {J : Type} [Group J] {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSp n p f) (hm : Blueprint.LieModel J .PSp n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (J ≃* StatedProj (StatedSp n K)) :=
  CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psp_of_lieModel' hadm hm

variable {r : ℕ} {K : Type} [Field K]

theorem conj_injective_statedProj_statedSp_charTwo [NeZero r] [CharP K 2] :
    Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective x
  obtain ⟨h, rfl⟩ := SymplecticHigher.proj_surjective y
  rw [← spInner_eq_conj, ← spInner_eq_conj] at hxy
  rw [spInner_injective hxy]

theorem even_sp_field_evenLieConclusion {f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {a : MulAut (StatedProj (StatedSp r K))} (ha : a * a = 1)
    (g : StatedSp r K) (σ : K ≃+* K) (hag : a = spInner r K g * fieldAut r K σ) (hσ : σ ≠ 1)
    (M : Subgroup (fixedSubgroup a)) (hM : IsPComponent 2 M) : EvenLieConclusion M := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hfe, hσx, hk, -, -, -, -, -, -, -, h, hah⟩ :=
    even_symplectic_quadratic_involution_descent (by omega : 1 ≤ r) hf hK ha g σ hag hσ
  have hf2 : 2 ≤ f := by
    obtain ⟨t, ht⟩ := hfe
    omega
  obtain ⟨hNinn, -, hιjinj, ⟨act, -, Θ, hΘ⟩, -, -⟩ :=
    even_symplectic_field_centralizers_and_intermediate_odd_cores hr hf2 hfe hK σ hσx
  have hN : inner (StatedProj (StatedSp r K)) ⊓ centralizer {fieldAut r K σ} =
      ((spInner r K).comp (subfieldSpHom r (descentField σ))).range := by
    apply le_antisymm
    · intro x hx
      have hxE : x ∈ spSemilinearAutGroup r K ⊓ centralizer {fieldAut r K σ} :=
        ⟨inner_le_spSemilinearAutGroup hx.1, hx.2⟩
      obtain ⟨⟨g', φ⟩, hg'⟩ := Θ.surjective ⟨x, hxE⟩
      have hx' : x = spInner r K (subfieldSpHom r (descentField σ) g') * fieldAut r K φ := by
        rw [← hΘ, hg']
      have hφ : φ = 1 := by
        by_contra hφ
        refine (spInner_mul_fieldAut_not_mem_inner_iff
          (subfieldSpHom r (descentField σ) g') φ).mpr hφ ?_
        rw [← hx']
        exact hx.1
      subst hφ
      refine ⟨g', ?_⟩
      rw [hx', map_one, mul_one]
      rfl
    · rintro _ ⟨g', rfl⟩
      refine ⟨hNinn ⟨g', rfl⟩, ?_⟩
      have h1 := (Θ ⟨g', 1⟩).2.2
      rw [hΘ, map_one, mul_one] at h1
      exact h1
  have hc : MulAut.congr (conjAut r K ⟨h, statedSp_le_gsp h.2⟩) (fieldAut r K σ) = a :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (conjAut r K ⟨h, statedSp_le_gsp h.2⟩)
      (fieldAut r K σ) = _).trans hah.symm
  have hcj := conj_injective_statedProj_statedSp_charTwo (r := r) (K := K)
  let Φ : fixedSubgroup a ≃* StatedSp r (descentField σ) :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      ((fixedSubgroupCongrEquiv _ _).symm.trans
        ((fixedInnerEquiv hcj _).trans
          ((MulEquiv.subgroupCongr hN).trans (MonoidHom.ofInjective hιjinj).symm)))
  exact evenLieConclusion_of_mulEquiv Φ
    (fun M' hM' => evenLieConclusion_statedSp (by omega) hk (by omega) M' hM') hM

theorem even_sp_suzuki_evenLieConclusion {m : ℕ} (hm : 1 ≤ m)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1))
    {a : MulAut (StatedProj (StatedSp 2 K))} (ha : a * a = 1) (s : StatedSp 2 K)
    (has : a = spInner 2 K s * exceptionalAut K ^ (2 * m + 1))
    (M : Subgroup (fixedSubgroup a)) (hM : IsPComponent 2 M) : EvenLieConclusion M := by
  subst has
  obtain ⟨χ, -, hχ⟩ := OutcomeLocal.exists_inner_conj_eta hK ha
  obtain ⟨ψ, -, hψinj, -, hrange, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core hm hK (exceptionalAut K)
      exceptionalAut_proj
  obtain ⟨-, -, hSz⟩ := LieType.Ree.suzuki_simple hm hK
  have hcj := conj_injective_statedProj_statedSp_charTwo (r := 2) (K := K)
  have hc : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) =
      spInner 2 K s * exceptionalAut K ^ (2 * m + 1) :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) = _).trans
      hχ.symm
  let Φ : fixedSubgroup (spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) ≃*
      Blueprint.suzukiGroup m K :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      ((fixedSubgroupCongrEquiv _ _).symm.trans
        ((fixedInnerEquiv hcj _).trans
          ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hψinj).symm)))
  have hadm : StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) :=
    ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
  exact evenLieConclusion_of_simple Φ (Or.inl ⟨.twistedB2, 0, 2 * m + 1, hadm,
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, m, hm, K, inferInstance, inferInstance, rfl, hK,
      ⟨MulEquiv.refl _⟩⟩))⟩) hM

theorem evenOuterFamilyInput_PSp : EvenOuterFamilyInput .PSp := by
  intro J _ n f hadm hm α hα hαo P hP
  change EvenLieConclusion P
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hnf : (n, 2 ^ f) ≠ (2, 2) := hadm.2.2.2
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α * MulAut.congr e α = 1 := by
    rw [← sq, ← hβ, pow_orderOf_eq_one]
  have hβo : MulAut.congr e α ∉ inner (StatedProj (StatedSp n K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  refine evenLieConclusion_of_mulEquiv (fixedSubgroupCongrEquiv e α) ?_ hP
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup n K →
      ∀ M : Subgroup (fixedSubgroup (MulAut.congr e α)), IsPComponent 2 M →
        EvenLieConclusion M := by
    intro hmem M hM
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    exact even_sp_field_evenLieConclusion hn hf hK hβ2 g σ hgσ hσ M hM
  by_cases hn3 : 3 ≤ n
  · apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
    exact mem_top _
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    rcases Nat.even_or_odd f with hfe | hfo
    · exact hE (heven hfe _ hβ)
    · obtain ⟨s, hs⟩ := hodd hfo _ hβ hβo
      obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h0
        obtain rfl : m = 0 := by omega
        exact hnf rfl
      rw [eq_exceptionalAut hγ] at hs
      exact fun M hM => even_sp_suzuki_evenLieConclusion hm hK hβ2 s hs M hM

end CFSG.ComponentClassification.CatLeafProof
