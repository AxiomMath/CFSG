module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLinOuter
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open (IsElemAbelian)

section Torus

variable {K : Type} [Field K]

@[expose] def weights2 (u : Kˣ) : Fin 2 → Kˣ := ![u, u⁻¹]

theorem prod_weights2 (u : Kˣ) : ∏ i, weights2 u i = 1 := by
  rw [Fin.prod_univ_two]
  simp [weights2]

@[expose] noncomputable def torus2 : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun u := CFSG.LieType.SeitzGeneration.diagSLn (weights2 u) (prod_weights2 u)
  map_one' := CFSG.LieType.SeitzGeneration.toGL_injective' (by
    rw [CFSG.LieType.SeitzGeneration.toGL_diagSLn, map_one]
    have : weights2 (1 : Kˣ) = 1 := by
      funext i
      fin_cases i <;> simp [weights2]
    rw [this, CFSG.RankThree.PartOne.KFU.diagU_one])
  map_mul' u v := CFSG.LieType.SeitzGeneration.toGL_injective' (by
    rw [map_mul, CFSG.LieType.SeitzGeneration.toGL_diagSLn,
      CFSG.LieType.SeitzGeneration.toGL_diagSLn, CFSG.LieType.SeitzGeneration.toGL_diagSLn]
    have : weights2 (u * v) = weights2 u * weights2 v := by
      funext i
      fin_cases i <;> simp [weights2, mul_inv, mul_comm]
    rw [this, CFSG.RankThree.PartOne.KFU.diagU_mul])

theorem torus2_injective : Function.Injective (torus2 (K := K)) := by
  intro u v h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) K =>
    ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) h
  change (Matrix.diagonal fun i => ((weights2 u i : Kˣ) : K)) 0 0 =
    (Matrix.diagonal fun i => ((weights2 v i : Kˣ) : K)) 0 0 at h1
  simp only [Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

end Torus

section SL2

variable {K : Type} [Field K] [Finite K]

theorem isCyclic_sylow_SL2_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (P : Sylow p (SpecialLinearGroup (Fin 2) K)) : IsCyclic P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  set T : Subgroup (SpecialLinearGroup (Fin 2) K) := (torus2 (K := K)).range with hT
  have hTcard : Nat.card T = Nat.card K - 1 := by
    rw [hT, ← Nat.card_units]
    exact (Nat.card_congr (MonoidHom.ofInjective torus2_injective).toEquiv).symm
  haveI : IsCyclic T := isCyclic_of_surjective (torus2 (K := K)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  have hpq : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hd hpK
    have : Nat.card K - (Nat.card K - 1) = 1 := by omega
    rw [this] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpq1 : ¬ p ∣ Nat.card K + 1 := by
    intro hd
    have h1 : p ∣ Nat.card K + 1 - (Nat.card K - 1) := Nat.dvd_sub hd hpK
    have : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
    rw [this] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 2) K) =
      Nat.card K * ((Nat.card K - 1) * (Nat.card K + 1)) := by
    rw [card_SL_eq (by norm_num)]
    have h2 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      have := Nat.sq_sub_sq (Nat.card K) 1
      simpa [mul_comm] using this
    have h3 : 2 * (2 - 1) / 2 = 1 := by norm_num
    rw [h3, pow_one, Finset.Icc_self, Finset.prod_singleton, h2]
  have hv : (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization p =
      (Nat.card K - 1).factorization p := by
    have hne1 : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have hne2 : Nat.card K - 1 ≠ 0 := by omega
    have hne3 : Nat.card K + 1 ≠ 0 := by omega
    rw [hcardSL, Nat.factorization_mul hne1 (mul_ne_zero hne2 hne3),
      Nat.factorization_mul hne2 hne3]
    simp [Nat.factorization_eq_zero_of_not_dvd hpq, Nat.factorization_eq_zero_of_not_dvd hpq1]
  obtain ⟨PT⟩ : Nonempty (Sylow p T) := inferInstance
  have hPTcard : Nat.card PT = p ^ (Nat.card K - 1).factorization p := by
    rw [Sylow.card_eq_multiplicity, hTcard]
  let S : Subgroup (SpecialLinearGroup (Fin 2) K) := (PT : Subgroup T).map T.subtype
  have hScard : Nat.card S = p ^ (Nat.card (SpecialLinearGroup (Fin 2) K)).factorization p := by
    rw [hv, ← hPTcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (PT : Subgroup T) T.subtype
      T.subtype_injective).toEquiv).symm
  let S₀ : Sylow p (SpecialLinearGroup (Fin 2) K) := Sylow.ofCard S hScard
  have hS₀ : IsCyclic ↥S₀ := by
    have hPTc : IsCyclic ↥PT := Subgroup.isCyclic (PT : Subgroup T)
    have e1 : ↥(PT : Subgroup T) ≃* ↥S :=
      Subgroup.equivMapOfInjective (PT : Subgroup T) T.subtype T.subtype_injective
    exact (MulEquiv.isCyclic e1).1 hPTc
  exact (MulEquiv.isCyclic (Sylow.equiv S₀ P)).1 hS₀

theorem false_of_elemAbelian_sq_SL2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : ¬ p ∣ Nat.card K)
    {W : Subgroup (SpecialLinearGroup (Fin 2) K)} (hW : IsElemAbelian p W)
    (hWc : Nat.card W = p ^ 2) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isElementaryAbelian_of_isElemAbelian hW
  have hWp : IsPGroup p W := IsPGroup.of_card hWc
  by_cases hpK : p ∣ Nat.card K - 1
  · obtain ⟨P, hP⟩ := hWp.exists_le_sylow
    have hcyc := isCyclic_sylow_SL2_of_dvd hp hp2 hpK P
    have : IsCyclic W := isCyclic_of_injective (Subgroup.inclusion hP)
      (Subgroup.inclusion_injective hP)
    exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hWc this
  ·
    set W' : Subgroup (GL (Fin 2) K) := W.map SpecialLinearGroup.toGL with hW'
    have hW'c : Nat.card W' = p ^ 2 := by
      rw [hW', Subgroup.card_map_of_injective CFSG.LieType.SeitzGeneration.toGL_injective']
      exact hWc
    haveI := isElementaryAbelian_of_isElemAbelian
      (CFSG.Open.IsElemAbelian.map hW (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K))
    obtain ⟨hpos, -⟩ := orderOf_card_spec (K := K) hp hpc
    have hne1 : orderOf (Nat.card K : ZMod p) ≠ 1 := by
      intro h1
      have h2 : (Nat.card K : ZMod p) = 1 := orderOf_eq_one_iff.1 h1
      apply hpK
      have h3 : ((Nat.card K - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'), h2]
        simp
      exact (ZMod.natCast_eq_zero_iff _ _).1 h3
    have hdiv : 2 / orderOf (Nat.card K : ZMod p) ≤ 1 := by
      have := (Nat.div_lt_iff_lt_mul hpos).2 (by omega : 2 < 2 * orderOf (Nat.card K : ZMod p))
      omega
    exact CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.false_of_sylow_cyclic W' hW'c
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isCyclic_sylow_gl_of_div (hp.odd_of_ne_two hp2) hpc
        hdiv)

theorem false_of_elemAbelian_sq_projectiveSL_two [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (projectiveSL 2 K)} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) : False := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hpc : ¬ p ∣ Nat.card K := by
    intro hd
    rw [hcard] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  let e : projectiveSL 2 K ≃* SpecialLinearGroup (Fin 2) K := LinearCover.projectiveSLTwoEquivSL K
  refine false_of_elemAbelian_sq_SL2 hp hp2 hpc (W := E.map e.toMonoidHom)
    (CFSG.Open.IsElemAbelian.map hE e.toMonoidHom) ?_
  rw [Subgroup.card_map_of_injective e.injective]
  exact hEc

end SL2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
