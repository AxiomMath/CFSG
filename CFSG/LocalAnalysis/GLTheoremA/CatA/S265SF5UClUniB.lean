module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniBlock
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClDist
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClDeg
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix Polynomial Module
open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.CanonU3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem false_of_component_primeForm_five {f N e : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (A : primeFormUnitary h (idGram K N)) {c : Kˣ}
    (hA : (A : GL (Fin N) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hβ : primeFormConjHom h (idGram K N) A ≠ 1)
    {T : Subgroup (primeFormP h (idGram K N))}
    (hT : IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K N) A)))
    (hZ : Subgroup.center ↥T = ⊥) (h5 : 5 ∣ 2 ^ e + 1) (h25 : ¬ 25 ∣ 2 ^ e + 1)
    (hcard : Nat.card T = ordTwistedA 4 (2 ^ e)) : False := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 ≤ 2 ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) (by norm_num : 1 < 2)
    omega
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · norm_num at h5
    · exact he
  set x : LinearMap.GeneralLinearGroup K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) with hxdef
  have hH : UnitaryPrimaryData h.bar (idForm h N) x :=
    primaryData_toLin' h A.2 (by norm_num : Nat.Prime 5) (by norm_num) hA
  obtain ⟨a, haT⟩ := exists_good_block_of_component hq A hxdef hH T hT
  haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  have hd : 1 ≤ (a.1 : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.1.2)
  have hfd : 1 ≤ f * (a.1 : K[X]).natDegree := Nat.mul_pos h.one_le hd
  obtain ⟨gS, hgSsurj, hgSker, hgSkerProp⟩ := exists_surjective_specialBlock hq hH a T haT
  have hcen : ∀ {X : Type} [Group X] (g : X →* ↥T), Function.Surjective g →
      g.ker ≤ Subgroup.center X → g.ker = Subgroup.center X := by
    intro X _ g hg hker
    refine le_antisymm hker fun z hz => ?_
    have hgz : g z ∈ Subgroup.center ↥T := Subgroup.mem_center_iff.2 fun y => by
      obtain ⟨w, rfl⟩ := hg y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
    rw [hZ, Subgroup.mem_bot] at hgz
    exact MonoidHom.mem_ker.2 hgz
  have hSL : ∀ (m k : ℕ) (E : Type) [Field E] [Finite E], 2 ≤ m → 1 ≤ k →
      Nat.card E = 2 ^ k → (m = 2 → 4 ≤ 2 ^ k) →
      ∀ g : SpecialLinearGroup (Fin m) E →* ↥T, Function.Surjective g →
        g.ker ≤ Subgroup.center _ → False := by
    intro m k E _ _ hm hk hE h4 g hg hker
    have hmod : StatedClassicalModel ↥T .PSL m 2 k :=
      ⟨⟨Nat.prime_two, hk, hm, fun hc => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj hc
        have := h4 h1
        omega, fun hc => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj hc
        have := h4 h1
        omega⟩, E, inferInstance, inferInstance, hE,
        ⟨(QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
          ((QuotientGroup.quotientMulEquivOfEq (hcen g hg hker)).trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E))⟩⟩
    exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := m - 1) (u := 4) (by omega) hk
      (by norm_num) he1
      (((CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl).symm.trans hcard)
  by_cases hself : dualPoly h.bar (a.1 : K[X]) = (a.1 : K[X])
  · rcases exists_field_factor_of_selfDual hq hH a.1 hself a.2 with
      ⟨F, _, _, -, hFcard, h4, ⟨eSL2⟩⟩ | ⟨E, _, _, -, hEcard, hm3, hne, ⟨eSU⟩⟩
    · obtain ⟨g, hg, hker⟩ := exists_central_surjection_of_mulEquiv eSL2 gS hgSsurj hgSker
      exact hSL 2 _ F le_rfl hfd (by rw [Nat.card_eq_fintype_card, hFcard])
        (fun _ => by rw [← hFcard]; exact h4) g hg hker
    have hEnat : Nat.card E = (2 ^ (f * (a.1 : K[X]).natDegree)) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hEcard]
    obtain ⟨g, hg, hker⟩ := exists_central_surjection_of_mulEquiv eSU gS hgSsurj hgSker
    have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) hEnat hm3
      hne
    have hmod : StatedClassicalModel ↥T .PSU
        (primaryMultiplicity (x : Module.End K (Fin N → K)) (a.1 : K[X])) 2
        (f * (a.1 : K[X]).natDegree) :=
      ⟨⟨Nat.prime_two, hfd, hm3, hne⟩, E, inferInstance, inferInstance, hEnat,
        ⟨(QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
          (QuotientGroup.quotientMulEquivOfEq ((hcen g hg hker).trans hQ.2))⟩⟩
    obtain ⟨hm5, hfde⟩ := eq_four_of_ordTwistedA_eq (by omega) hfd he1
      (((CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl).symm.trans hcard)
    by_cases hV : primaryComponent (x : Module.End K (Fin N → K)) (a.1 : K[X]) = ⊤
    ·
      have hx5 : (x : Module.End K (Fin N → K)) ^ 5 =
          algebraMap K (Module.End K (Fin N → K)) (c : K) := by
        rw [← Units.val_pow_eq_pow_val, hxdef, ← map_pow, hA]
        exact toLin_scalar_eq_algebraMap c
      have hdvd : (a.1 : K[X]) ∣ X ^ 5 - C (c : K) :=
        (mem_primaryFactors.mp a.1.2).2.2.trans (minpoly.dvd K _ (by
          rw [map_sub, map_pow, aeval_X, aeval_C, hx5, sub_self]))
      have hK5 : ¬ 5 ∣ Nat.card K := fun h5K => by
        rw [h.card] at h5K
        have := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5K
        omega
      rcases natDegree_eq_one_or_five_of_dvd hK5 (irreducible_of_mem_primaryFactors a.1.2)
          c.ne_zero hdvd (selfDualPrimaryBlock hH a.1 hself).odd_natDegree with hd1 | hd5
      · have hfr : Module.finrank K (primaryComponent (x : Module.End K (Fin N → K)) (a.1 : K[X]))
            = (a.1 : K[X]).natDegree *
              primaryMultiplicity (x : Module.End K (Fin N → K)) (a.1 : K[X]) := by
          rw [finrank_primaryComponent]
        have hN : (a.1 : K[X]).natDegree *
            primaryMultiplicity (x : Module.End K (Fin N → K)) (a.1 : K[X]) = N := by
          rw [← hfr, hV, finrank_top, Module.finrank_fin_fun]
        have hN1 : 1 ≤ N := by
          have := Nat.mul_le_mul hd hm3
          omega
        exact hβ (primeFormConjHom_eq_one_of_primaryComponent_top hN1 A hd1 hV)
      · rw [hd5] at hfde
        subst hfde
        rw [mul_comm] at h5 h25
        exact h25 (twentyFive_dvd_two_pow_add_one h5)
    obtain ⟨b, hb⟩ := exists_ne_primaryFactor_of_primaryComponent_ne_top hH hV
    have hc5 : Subgroup.center ↥(StatedSU
        (primaryMultiplicity (x : Module.End K (Fin N → K)) (a.1 : K[X]))
        (2 ^ (f * (a.1 : K[X]).natDegree)) E) ≠ ⊥ := by
      rw [show primaryMultiplicity (x : Module.End K (Fin N → K)) (a.1 : K[X]) = 5 by omega]
      exact center_statedSU_five_ne_bot hEnat (by rw [hfde]; exact h5)
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc5
    have hucen : ∀ w, w * eSU.symm z = eSU.symm z * w := fun w => eSU.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 z.2 (eSU w))
    have hgu : gS (eSU.symm z) ∈ Subgroup.center ↥T := Subgroup.mem_center_iff.2 fun y => by
      obtain ⟨w, rfl⟩ := hgSsurj y
      rw [← map_mul, ← map_mul, hucen w]
    rw [hZ, Subgroup.mem_bot] at hgu
    obtain ⟨v, hvto, hvN⟩ := hgSkerProp _ hgu
    have hv1 := eq_one_of_mem_specialBlock_of_mem_normOneScalars hH hself hb
      (by rw [hvto]; exact (eSU.symm z).2) hvN
    have hu1 : eSU.symm z = 1 := by
      apply Subtype.ext
      rw [← hvto, hv1, map_one]
      rfl
    apply hz1
    apply Subtype.ext
    rw [← eSU.apply_symm_apply (z : ↥(StatedSU _ _ E)), hu1, map_one]
    rfl
  obtain ⟨eSL⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock hH a.1 (Ne.symm hself))
  haveI : Finite (AdjoinRoot (a.1 : K[X])) := Module.finite_of_finite K
  obtain ⟨g, hg, hker⟩ := exists_central_surjection_of_mulEquiv eSL gS hgSsurj hgSker
  refine hSL _ _ (AdjoinRoot (a.1 : K[X])) a.2.1 (by omega)
    (CFSG.RankThree.PartOne.KCUnitary.natCard_adjoinRoot h) (fun _ => ?_) g hg hker
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * (f * (a.1 : K[X]).natDegree)) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
