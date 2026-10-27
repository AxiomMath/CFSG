module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.G2Class
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Odd
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false


@[expose] def TriD4A2NoL34 : Prop :=
  ∀ (ℓ f : ℕ) (hℓ : ℓ.Prime), 5 ≤ ℓ → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, TrialityA2Rep ℓ f hℓ K σ s →
      NoL34Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

namespace OutTri

theorem noL34Layer_cocycle_q1 (hA2 : TriD4A2NoL34) {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    NoL34Layer (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  refine noL34Layer_of_conj_eq y hyn ?_
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
    refine noL34Layer_of_conj_eq y' hconj ?_
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      rw [hs1, map_one, one_mul]
      exact noL34Layer_fieldActor_odd hp hp2 hf hK σ hσ
    · exact hA2 p f hp hp5 hf K hK σ hσ s (Or.inl ⟨hq, d, hd, hd3, hd1, hsd⟩)
  · obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
      ellQ1_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
    exact noL34Layer_of_conj_eq y₀ hconj
      (hA2 p f hp hp5 hf K hK σ hσ s (Or.inl ⟨hq, d, hd, hd3, hd1, hsd⟩))

theorem noL34Layer_outer_q2 (hA2 : TriD4A2NoL34) {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφord : orderOf φ = 3)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    NoL34Layer φ := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hG2 : NoL34Layer (fieldActor (t := TwistTag.D4) σ σ) :=
    noL34Layer_fieldActor_odd hp hp2 hf hK σ hσ
  have hTor : ∀ s, D4MinusToral p f hp K σ s →
      NoL34Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := fun s hs =>
    hA2 p f hp hp5 hf K hK σ hσ s (Or.inr ⟨hq, hs⟩)
  rcases d4Minus_outer_three_nf hp hp2 hp3 hf hq K hK σ hσ φ hφord hφ with
    ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
  · rcases hy with hy | hy
    · exact noL34Layer_of_conj_eq y hy hG2
    · exact noL34Layer_of_conj_eq y hy ((noL34Layer_inv_iff _).2 hG2)
  · rcases hys with hys | hys
    · exact noL34Layer_of_conj_eq y hys (hTor s hs)
    · exact noL34Layer_of_conj_eq y hys ((noL34Layer_inv_iff _).2 (hTor s hs))
  · have hc := pow_three_of_conj_eq y hφ3 hyn
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    obtain ⟨y₀, s, hsT, hconj⟩ :=
      minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hN
    have hPL := noL34Layer_of_conj_eq y₀ hconj (hTor s hsT)
    rcases hyn with hyn | hyn
    · exact noL34Layer_of_conj_eq y hyn hPL
    · exact noL34Layer_of_conj_eq y hyn ((noL34Layer_inv_iff _).2 hPL)

theorem noL34Layer_three_D4_outer_odd (hA2 : TriD4A2NoL34) {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    NoL34Layer φ := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hq3 : ¬ 3 ∣ p ^ f := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hmod : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by omega
  rcases hmod with hq | hq
  · obtain ⟨g, hg, hφ' | hφ'⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ φ hφord hφ
    · rw [hφ']
      exact noL34Layer_cocycle_q1 hA2 hp hp5 hf hq hK σ hσ g hg
    · have h := noL34Layer_cocycle_q1 hA2 hp hp5 hf hq hK σ hσ g hg
      rw [← hφ'] at h
      exact (noL34Layer_inv_iff _).1 h
  · exact noL34Layer_outer_q2 hA2 hp hp5 hf hq hK σ hσ φ hφ3 hφord hφ

end OutTri

end CFSG.HardMathSupport.Dickson.Sec6
