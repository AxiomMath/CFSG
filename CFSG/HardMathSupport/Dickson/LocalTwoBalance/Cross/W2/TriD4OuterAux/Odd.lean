module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddTwo

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.HardMathSupport.Lang.E6Descent

set_option linter.unusedSectionVars false


theorem coreFreeAt_of_conj_eq' {Y : Type*} [Group Y] (y : Y) {φ ψ : MulAut Y}
    (h : MulAut.conj y * φ * (MulAut.conj y)⁻¹ = ψ) (hψ : CoreFreeAt 3 ψ) : CoreFreeAt 3 φ := by
  rw [← h] at hψ
  exact (coreFreeAt_conj_iff φ (MulAut.conj y)).1 hψ

theorem coreFreeAt_cocycle_q1 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    CoreFreeAt 3 (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  refine coreFreeAt_of_conj_eq' y hyn ?_
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
    refine coreFreeAt_of_conj_eq' y' hconj ?_
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      rw [hs1, map_one, one_mul]
      exact coreFreeAt_three_fieldActor_self hp hp3 hf hK σ hσ
    · exact trialityA2CoreFree_holds p f hp hp3 hf K hK σ hσ s (Or.inl ⟨hq, d, hd, hd3, hd1, hsd⟩)
  · obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
      ellQ1_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
    exact coreFreeAt_of_conj_eq' y₀ hconj
      (trialityA2CoreFree_holds p f hp hp3 hf K hK σ hσ s (Or.inl ⟨hq, d, hd, hd3, hd1, hsd⟩))

theorem coreFreeAt_outer_q2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφord : orderOf φ = 3)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    CoreFreeAt 3 φ := by
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hG2 : CoreFreeAt 3 (fieldActor (t := TwistTag.D4) σ σ) :=
    coreFreeAt_three_fieldActor_self hp hp3 hf hK σ hσ
  have hTor : ∀ s, D4MinusToral p f hp K σ s →
      CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := fun s hs =>
    trialityA2CoreFree_holds p f hp hp3 hf K hK σ hσ s (Or.inr ⟨hq, hs⟩)
  rcases d4Minus_outer_three_nf hp hp2 hp3 hf hq K hK σ hσ φ hφord hφ with
    ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
  · rcases hy with hy | hy
    · exact coreFreeAt_of_conj_eq' y hy hG2
    · exact coreFreeAt_of_conj_eq' y hy hG2.inv
  · rcases hys with hys | hys
    · exact coreFreeAt_of_conj_eq' y hys (hTor s hs)
    · exact coreFreeAt_of_conj_eq' y hys (hTor s hs).inv
  · have hc := pow_three_of_conj_eq y hφ3 hyn
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    obtain ⟨y₀, s, hsT, hconj⟩ :=
      minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hN
    have hPL := coreFreeAt_of_conj_eq' y₀ hconj (hTor s hsT)
    rcases hyn with hyn | hyn
    · exact coreFreeAt_of_conj_eq' y hyn hPL
    · exact coreFreeAt_of_conj_eq' y hyn hPL.inv

theorem coreFreeAt_three_D4_outer_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    CoreFreeAt 3 φ := by
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hq3 : ¬ 3 ∣ p ^ f := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hmod : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by omega
  rcases hmod with hq | hq
  · obtain ⟨g, hg, hφ' | hφ'⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ φ hφord hφ
    · rw [hφ']
      exact coreFreeAt_cocycle_q1 hp hp2 hp3 hf hq hK σ hσ g hg
    · have h := coreFreeAt_cocycle_q1 hp hp2 hp3 hf hq hK σ hσ g hg
      rw [← hφ'] at h
      have h' := h.inv
      rwa [inv_inv] at h'
  · exact coreFreeAt_outer_q2 hp hp2 hp3 hf hq hK σ hσ φ hφ3 hφord hφ

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
