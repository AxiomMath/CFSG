module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenOuter

public noncomputable section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {r : ℕ} {K : Type} [Field K]

theorem psp_field_fixed {f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {a : MulAut (StatedProj (StatedSp r K))} (ha : a * a = 1) (g : StatedSp r K) (σ : K ≃+* K)
    (hag : a = spInner r K g * fieldAut r K σ) (hσ : σ ≠ 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (f / 2) ∧ f = 2 * (f / 2) ∧
      Nonempty (fixedSubgroup a ≃* StatedSp r k) := by
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
  have hcj := CatLeafProof.conj_injective_statedProj_statedSp_charTwo (r := r) (K := K)
  let Φ : fixedSubgroup a ≃* StatedSp r (descentField σ) :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      ((fixedSubgroupCongrEquiv _ _).symm.trans
        ((CatLeafProof.fixedInnerEquiv hcj _).trans
          ((MulEquiv.subgroupCongr hN).trans (MonoidHom.ofInjective hιjinj).symm)))
  exact ⟨descentField σ, inferInstance, inferInstance, hk,
    by obtain ⟨t, ht⟩ := hfe; omega, ⟨Φ⟩⟩

theorem notSp6Components_psp_suzuki {m : ℕ} (hm : 1 ≤ m)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1))
    {a : MulAut (StatedProj (StatedSp 2 K))} (ha : a * a = 1) (s : StatedSp 2 K)
    (has : a = spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) :
    NotSp6Components (fixedSubgroup a) := by
  subst has
  obtain ⟨χ, -, hχ⟩ := OutcomeLocal.exists_inner_conj_eta hK ha
  obtain ⟨ψ, -, hψinj, -, hrange, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core hm hK (exceptionalAut K)
      exceptionalAut_proj
  obtain ⟨-, -, hSz⟩ := LieType.Ree.suzuki_simple hm hK
  have hcj := CatLeafProof.conj_injective_statedProj_statedSp_charTwo (r := 2) (K := K)
  have hc : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) =
      spInner 2 K s * exceptionalAut K ^ (2 * m + 1) :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) = _).trans
      hχ.symm
  let Φ : fixedSubgroup (spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) ≃*
      Blueprint.suzukiGroup m K :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      ((fixedSubgroupCongrEquiv _ _).symm.trans
        ((CatLeafProof.fixedInnerEquiv hcj _).trans
          ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hψinj).symm)))
  have hadm : StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) :=
    ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
  have hLie : LieModel (Blueprint.suzukiGroup m K) .twistedB2 0 2 (2 * m + 1) :=
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, m, hm, K, inferInstance, inferInstance, rfl, hK,
      ⟨MulEquiv.refl _⟩⟩))
  have : IsSimpleGroup (fixedSubgroup (spInner 2 K s * exceptionalAut K ^ (2 * m + 1))) :=
    Φ.isSimpleGroup
  exact notSp6Components_of_isSimpleGroup (Or.inr rfl) hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv Φ.symm hLie) fun h => absurd h.1 (by decide)

theorem psp_outer_fixed {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel J .PSp n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNotSp6 (fixedSubgroup α) (fun r g => r = n ∧ e = 2 * g) := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hnf : (n, 2 ^ e) ≠ (2, 2) := hadm.2.2.2
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite J := Finite.of_equiv _ eJ.symm.toEquiv
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α * MulAut.congr eJ α = 1 := by
    rw [← sq, ← hβ, pow_orderOf_eq_one]
  have hβo : MulAut.congr eJ α ∉ inner (StatedProj (StatedSp n K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  refine spFixedOrNotSp6_of_mulEquiv (fixedSubgroupCongrEquiv eJ α) ?_
  have hE : MulAut.congr eJ α ∈ spSemilinearAutGroup n K →
      SpFixedOrNotSp6 (fixedSubgroup (MulAut.congr eJ α)) (fun r g => r = n ∧ e = 2 * g) := by
    intro hmem
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    obtain ⟨k, _, _, hk, he2, ⟨Φ⟩⟩ := psp_field_fixed hn hf hK hβ2 g σ hgσ hσ
    exact Or.inl ⟨k, inferInstance, inferInstance, n, e / 2, hk, by omega, ⟨rfl, he2⟩, ⟨Φ⟩⟩
  by_cases hn3 : 3 ≤ n
  · apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
    exact mem_top _
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    rcases Nat.even_or_odd e with hfe | hfo
    · exact hE (heven hfe _ hβ)
    · obtain ⟨s, hs⟩ := hodd hfo _ hβ hβo
      obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h0
        obtain rfl : m = 0 := by omega
        exact hnf rfl
      rw [eq_exceptionalAut hγ] at hs
      exact Or.inr (notSp6Components_psp_suzuki hm hK hβ2 s hs)

theorem catSp6EvenOuterFamily_PSp (hdet : Sp6EvenTypeDet) :
    CatSp6EvenOuterFamily .PSp := by
  intro S _ _ _ _ n e hadm hm σ hσ hout f D hD hD6 _
  obtain ⟨⟨rfl, rfl⟩, hfix⟩ :=
    sp6_of_spFixedOrNotSp6 hdet (psp_outer_fixed hadm hm σ hσ hout) hD hD6
  exact ⟨Or.inl hm, hfix⟩

end CFSG.SeitzReduction.F4Pilot
