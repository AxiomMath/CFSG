module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddTwo
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.RankThree.PartOne.KGD CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Pure

theorem conj_conj_mulAut {Y : Type*} [Group Y] (y y' : Y) (φ : MulAut Y) :
    MulAut.conj y' * (MulAut.conj y * φ * (MulAut.conj y)⁻¹) * (MulAut.conj y')⁻¹ =
      MulAut.conj (y' * y) * φ * (MulAut.conj (y' * y))⁻¹ := by
  rw [map_mul]
  group

end Pure

section Small


variable {K : Type} [Field K] [Finite K]

theorem fieldActor_eq_and_pow_of_central (σ : K ≃+* K)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} {d : Kˣ} (hd3 : d ^ 3 = 1)
    (hsd : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [coe_fieldActor_eq_conj, hsd]
    exact d4Minus_s0_comm d
  · rw [Subgroup.coe_pow, hsd, Subgroup.coe_one]
    exact d4Minus_s0_pow3 hd3

theorem fieldActor_eq_and_pow_of_minusToral {p f : ℕ} (hp : p.Prime) (σ : K ≃+* K)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hs : D4MinusToral p f hp K σ s) :
    fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 := by
  obtain ⟨L, _, _, _, _, g₀, b, ⟨-, hg₀P, -⟩, hb3, -, hsL⟩ := hs
  have h1 : (diagramMap TwistTag.D4 L)⁻¹ * g₀ = g₀ * (diagramMap TwistTag.D4 L)⁻¹ := by
    calc (diagramMap TwistTag.D4 L)⁻¹ * g₀ = (diagramMap TwistTag.D4 L)⁻¹ *
        (g₀ * diagramMap TwistTag.D4 L) * (diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L * g₀) *
          (diagramMap TwistTag.D4 L)⁻¹ := by rw [hg₀P]
      _ = g₀ * (diagramMap TwistTag.D4 L)⁻¹ := by group
  refine ⟨triEmb_injective (L := L) ?_, triEmb_injective (L := L) ?_⟩
  · rw [triEmb_apply, coe_fieldActor_eq_conj, map_mul, map_mul, map_inv,
      baseChangeGL_diagramMap, ← triEmb_apply, hsL]
    have hd := d4Minus_s0_comm b
    set P := diagramMap TwistTag.D4 L
    set d := rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]
    calc P⁻¹ * (g₀ * d * g₀⁻¹) * P = (P⁻¹ * g₀) * d * (P⁻¹ * g₀)⁻¹ := by group
      _ = (g₀ * P⁻¹) * d * (g₀ * P⁻¹)⁻¹ := by rw [h1]
      _ = g₀ * (P⁻¹ * d * P) * g₀⁻¹ := by group
      _ = g₀ * d * g₀⁻¹ := by rw [hd]
  · rw [map_pow, hsL, map_one, conj_pow, d4Minus_s0_pow3 hb3]
    group

theorem normSeq_eq_one_of_conj {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {g y n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1)
    (hyn : MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
      (MulAut.conj y)⁻¹ = MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) :
    normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1 := by
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  exact normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube

end Small

section Large


theorem threeD4FixedNF_holds : ThreeD4FixedNF := by
  intro p f hp hp5 hf K _ _ hK σ hσ g hg
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hq3 : ¬ 3 ∣ p ^ f := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by omega
  rcases hq with hq | hq
  · obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
    have hN := normSeq_eq_one_of_conj hK σ hσ hg hyn
    by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
    · obtain ⟨y', s, hs, hs3, hconj, -⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
      refine ⟨y' * y, s, hs, hs3, ?_⟩
      rw [← conj_conj_mulAut, hyn, hconj]
    · obtain ⟨y', s, d, hconj, -, hd3, -, hsd⟩ :=
        D4Dual.ellQ1_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
      obtain ⟨hs, hs3⟩ := fieldActor_eq_and_pow_of_central σ hd3 hsd
      refine ⟨y' * y, s, hs, hs3, ?_⟩
      rw [← conj_conj_mulAut, hyn, hconj]
  · rcases d4MinusNF p f hp hp2 hp3 hf hq K hK σ hσ g hg with
      ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
    · exact ⟨y, 1, map_one _, one_pow 3, by rw [hy, map_one, one_mul]⟩
    · obtain ⟨hsδ, hs3⟩ := fieldActor_eq_and_pow_of_minusToral hp σ hs
      exact ⟨y, s, hsδ, hs3, hys⟩
    · have hN := normSeq_eq_one_of_conj hK σ hσ hg hyn
      obtain ⟨y', s, hs, hconj⟩ :=
        D4Dual.minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK σ hσ n hn hN
      obtain ⟨hsδ, hs3⟩ := fieldActor_eq_and_pow_of_minusToral hp σ hs
      refine ⟨y' * y, s, hsδ, hs3, ?_⟩
      rw [← conj_conj_mulAut, hyn, hconj]

end Large

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd
