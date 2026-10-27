module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerH
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Open Subgroup CFSG.SL2MinimalFaithful
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

private lemma not_mul_self_dvd_480_of_odd {q : ℕ} (hodd : Odd q) (hq : 1 < q)
    (h : q * q ∣ 480) : False := by
  obtain ⟨m, rfl⟩ := hodd
  have hm1 : 1 ≤ m := by omega
  have hle : (2 * m + 1) * (2 * m + 1) ≤ 480 := Nat.le_of_dvd (by norm_num) h
  have hmle : m ≤ 10 := by
    have h21 : 2 * m + 1 ≤ 21 := by nlinarith
    omega
  interval_cases m <;> norm_num at h

private lemma eq_five_of_dvd {q : ℕ} (hq : 1 < q)
    (h60 : 60 ∣ q * (q ^ 2 - 1) / 2) (hN : q * (q ^ 2 - 1) / 2 ∣ 480) : q = 5 := by
  have hNle : q * (q ^ 2 - 1) / 2 ≤ 480 := Nat.le_of_dvd (by norm_num) hN
  have hqle : q ≤ 9 := by
    by_contra h
    push Not at h
    have hq10 : 10 ≤ q := by omega
    have hq99 : 10 ^ 2 - 1 ≤ q ^ 2 - 1 := by
      have : 100 ≤ q ^ 2 := by nlinarith
      omega
    have hmono : 10 * (10 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq10 hq99
    have hdiv : (10 * (10 ^ 2 - 1)) / 2 ≤ q * (q ^ 2 - 1) / 2 := Nat.div_le_div_right hmono
    norm_num at hdiv
    omega
  have hq2 : 2 ≤ q := by omega
  have hfin : ∀ r ∈ Finset.Icc 2 9,
      (60 ∣ r * (r ^ 2 - 1) / 2 ∧ r * (r ^ 2 - 1) / 2 ∣ 480) → r = 5 := by decide
  exact hfin q (Finset.mem_Icc.mpr ⟨hq2, hqle⟩) ⟨h60, hN⟩

theorem card_centralizer_u1_ne {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    Nat.card (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) ≠ 480 := by
  intro hC
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  set φ : Multiplicative K × Multiplicative K →* StatedProj (StatedSp 2 K) :=
    (proj 2 K).comp ((blkSL K).comp ((unipotentHom (F := K)).prodMap (unipotentHom (F := K))))
    with hφdef
  have hφapply : ∀ x : Multiplicative K × Multiplicative K,
      φ x = proj 2 K (blkSL K (unipotentHom x.1, unipotentHom x.2)) := by
    intro x
    rw [hφdef]
    simp only [MonoidHom.comp_apply, MonoidHom.prodMap_def, MonoidHom.prod_apply]
    rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h1
    have h1' : proj 2 K (blkSL K (unipotentHom a, unipotentHom b)) = 1 := by
      rw [hφapply] at h1
      exact h1
    rcases (proj_blkSL_eq_one_iff (unipotentHom a, unipotentHom b)).mp h1' with
      ⟨hg, hh⟩ | ⟨hg, -⟩
    · have ha : a = 1 := by
        apply unipotentHom_injective
        rw [map_one]
        exact Subtype.ext hg
      have hb : b = 1 := by
        apply unipotentHom_injective
        rw [map_one]
        exact Subtype.ext hh
      exact Prod.ext ha hb
    · exfalso
      have h00 : ((unipotentHom a : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
        change ((unipotent a.toAdd : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) 0 0 = 1
        rw [coe_unipotent]
        simp
      have hneg : (1 : K) = -1 := by
        have hh00 := congrFun (congrFun hg 0) 0
        rw [h00] at hh00
        simpa using hh00
      exact h2 (by linear_combination hneg)
  have hcard : Nat.card φ.range = Nat.card K * Nat.card K := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod]
    simp only [Nat.card_congr Multiplicative.toAdd]
  have hle : φ.range ≤ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
    rintro _ ⟨z, rfl⟩
    refine X0_le_centralizer ?_
    rw [mem_X0 h2]
    refine ⟨(unipotentHom z.1, unipotentHom z.2), ?_⟩
    rw [hφapply]
  have hdvd : Nat.card K * Nat.card K ∣ 480 := by
    have h := Subgroup.card_dvd_of_le hle
    rw [hC] at h
    rwa [hcard] at h
  exact not_mul_self_dvd_480_of_odd hodd Finite.one_lt_card hdvd

theorem card_K_eq_five_of_u2 {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (hC : Nat.card (centralizer ({u2 K} : Set (StatedProj (StatedSp 2 K)))) = 480)
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hMC : M ≤ centralizer ({u2 K} : Set _))
    (hMp : ⁅M, M⁆ = M) (hM : Nat.card M = 60) : Nat.card K = 5 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hML : M ≤ Lsub K := perfect_le_L h2 hMC hMp
  have h60 : 60 ∣ Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
    have hdvd := Subgroup.card_dvd_of_le hML
    rw [hM] at hdvd
    rwa [card_Lsub hodd] at hdvd
  have hN : Nat.card K * (Nat.card K ^ 2 - 1) / 2 ∣ 480 := by
    have hdvd := Subgroup.card_dvd_of_le (Lsub_le_centralizer (K := K))
    rw [hC] at hdvd
    rwa [card_Lsub hodd] at hdvd
  exact eq_five_of_dvd Finite.one_lt_card h60 hN

end CFSG.EvenSporadicStandard.HNRecog.Harada
