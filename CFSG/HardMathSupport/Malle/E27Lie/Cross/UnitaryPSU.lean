module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniBlock
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.MapPerfect
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.UnitaryBlockCard
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.PrimaryCount

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni
open scoped commutatorElement

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_perfect_three_dvd_autFix_of_quasisimple [Finite K] (y : primeFormUnitary h (idGram K n))
    (Q : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)))
    (hQc : Q ≤ unitaryCentralizer (idForm h n) (toLinU h n y))
    (hQd : ∀ g ∈ Q, LinearMap.det (g : Module.End K (Fin n → K)) = 1)
    (hQ : CFSG.IsQuasisimple ↥Q) (h3 : 3 ∣ Nat.card Q) :
    ∃ R : Subgroup (primeFormP h (idGram K n)),
      R ≤ autFix (primeFormConjHom h (idGram K n) y) ∧ ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R := by
  classical
  have hrange : Q ≤ (phiS h (n := n)).range := by
    intro g hg
    exact mem_range_phiS (mem_sesqSpecialUnitaryGroup.mpr
      ⟨(mem_unitaryCentralizer.mp (hQc hg)).1, hQd g hg⟩)
  set Bq : Subgroup ↥(gramSU h (idGram K n)) := Q.comap (phiS h) with hBq
  have hmap : Bq.map (phiS h) = Q := Subgroup.map_comap_eq_self hrange
  have hBqq : CFSG.IsQuasisimple ↥Bq := by
    have e : ↥Bq ≃* ↥Q := (Subgroup.equivMapOfInjective Bq (phiS h) phiS_injective).trans
      (MulEquiv.subgroupCongr hmap)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  let π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  have hker : π.ker ≤ Subgroup.center ↥(gramSU h (idGram K n)) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    have hg' : g ∈ normOneScalars h (gramSU h (idGram K n)) n := by
      have := hg
      rwa [show π.ker = normOneScalars h (gramSU h (idGram K n)) n from
        QuotientGroup.ker_mk' _] at this
    obtain ⟨c, -, -, hc⟩ := hg'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (GeneralLinearGroup.scalar_commute c _).symm
  set R : Subgroup (primeFormP h (idGram K n)) := Bq.map π with hR
  have hfix : R ≤ autFix (primeFormConjHom h (idGram K n) y) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_autFix]
    change primeFormConjHom h (idGram K n) y (g : primeFormP h (idGram K n)) =
      (g : primeFormP h (idGram K n))
    rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    have hcomm := (mem_unitaryCentralizer.mp (hQc (show phiS h g ∈ Q from hg))).2
    have hc : (y : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * y := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul]
      exact Units.ext hcomm.eq.symm
    change (y : GL (Fin n) K) * g * (y : GL (Fin n) K)⁻¹ = g
    rw [hc, mul_inv_cancel_right]
  have h1 : ⁅Bq, Bq⁆ = Bq := commutator_eq_of_isPerfect hBqq.1
  have h2 : ⁅R, R⁆ = R := by rw [hR, ← Subgroup.map_commutator, h1]
  have h3Bq : 3 ∣ Nat.card Bq := by
    have e : ↥Bq ≃* ↥Q := (Subgroup.equivMapOfInjective Bq (phiS h) phiS_injective).trans
      (MulEquiv.subgroupCongr hmap)
    rwa [Nat.card_congr e.toEquiv]
  have : Finite ↥(gramSU h (idGram K n)) := inferInstance
  exact ⟨R, hfix, h2, three_dvd_card_map_of_perfect π hker h1 h3Bq⟩


section Assembly

variable {y : primeFormUnitary h (idGram K n)}

theorem exists_quasisimple_three_dvd_block [Finite K] (h3K : ((3 : ℕ) : K) ≠ 0) (hℓ3 : ℓ ≠ 3)
    (hx : Squarefree (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))))
    (a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (toLinU h n y) a) :
    ∃ Q : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)),
      Q ≤ unitaryCentralizer (idForm h n) (toLinU h n y) ∧
      (∀ g ∈ Q, LinearMap.det (g : Module.End K (Fin n → K)) = 1) ∧
      CFSG.IsQuasisimple ↥Q ∧ 3 ∣ Nat.card Q := by
  have HU := primaryData_toLinU y hx
  have hF := specialBlockFacts_of_good HU (two_le_pow h) a ha
  refine ⟨specialBlock (idForm h n) (toLinU h n y) (a : K[X]), specialBlock_le_unitaryCentralizer,
    hF.detK, hF.quasisimple ha.1, ?_⟩
  by_cases hself : dualPoly h.bar (a : K[X]) = a
  · exact three_dvd_card_specialBlock_selfDual HU a hself ha.1 hℓ3
  · exact three_dvd_card_specialBlock_paired a (pairedPrimaryBlock HU a (Ne.symm hself)) ha.1
      (by exact_mod_cast h3K)

open scoped Classical in
theorem exists_perfect_three_dvd_centralizer_primeFormP [Finite K] (hℓ3 : ℓ ≠ 3)
    (hq : (4 ≤ ℓ ^ f ∧ 4 ≤ n) ∨ (ℓ ^ f = 2 ∧ 10 ≤ n))
    {z : primeFormP h (idGram K n)} (hz : z ^ 3 = 1) :
    ∃ Q : Subgroup (primeFormP h (idGram K n)),
      Q ≤ Subgroup.centralizer ({z} : Set (primeFormP h (idGram K n))) ∧ ⁅Q, Q⁆ = Q ∧
        3 ∣ Nat.card Q := by
  have hℓ := h.prime
  have : CharP K ℓ := h.charP
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    intro hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  set y : primeFormUnitary h (idGram K n) := ⟨((s : gramSU h (idGram K n)) : GL (Fin n) K), s.2.1⟩ with hy
  have hs3 : s ^ 3 ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hz
  obtain ⟨c, -, -, hc⟩ := hs3
  have hyp : (y : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
    have e1 : (y : GL (Fin n) K) = ((s : gramSU h (idGram K n)) : GL (Fin n) K) := rfl
    rw [e1, ← Subgroup.coe_pow, hc]
  have hx := squarefree_minpoly_toLinU_of_pow_scalar y h3K hyp
  have hX : ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  have hdeg : (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))).natDegree ≤ 3 := by
    have hdvd : minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ∣ (X ^ 3 - C (c : K) : K[X]) := by
      refine minpoly.dvd K _ ?_
      rw [hX]
      exact SPLCell.aeval_linEnd_X_pow_sub_C c hyp
    have hne0 : (X ^ 3 - C (c : K) : K[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
    have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [natDegree_X_pow_sub_C] at h4
  have hfr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hgood : ∃ a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)), IsGoodBlock h (toLinU h n y) a := by
    rcases hq with ⟨hq4, hn4⟩ | ⟨hq2, hn10⟩
    · obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 1) hx hdeg (by omega)
      exact ⟨a, isGoodBlock_of_numeric a (by omega) (fun _ => hq4) (fun _ => by omega)⟩
    · obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 3) hx hdeg (by omega)
      exact ⟨a, isGoodBlock_of_numeric a (by omega) (fun e => by omega) (fun e => by omega)⟩
  obtain ⟨a, ha⟩ := hgood
  obtain ⟨Q, hQc, hQd, hQ, hQ3⟩ := exists_quasisimple_three_dvd_block h3K hℓ3 hx a ha
  obtain ⟨R, hRfix, hRp, hR3⟩ := exists_perfect_three_dvd_autFix_of_quasisimple y Q hQc hQd hQ hQ3
  refine ⟨R, ?_, hRp, hR3⟩
  intro r hr
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective r
  have h1 : primeFormConjHom h (idGram K n) y ((t : gramSU h (idGram K n)) :
      primeFormP h (idGram K n)) = (t : primeFormP h (idGram K n)) := hRfix hr
  rw [primeFormConjHom_mk] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : (⟨(y : GL (Fin n) K) * (t : GL (Fin n) K) * (y : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h (idGram K n) y.2 t.2⟩ : gramSU h (idGram K n)) = s * t * s⁻¹ :=
    Subtype.ext rfl
  rw [h2] at h1
  change ((s * t * s⁻¹ : gramSU h (idGram K n)) : primeFormP h (idGram K n)) = _ at h1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

end Assembly

end CFSG.HardMathSupport.Malle.E27Lie
