module

public import CFSG.LinearAlgebra.CoordinateSemilinearCommutant
public import CFSG.LinearAlgebra.PrimeOrderIrreducible
public import CFSG.LinearAlgebra.SemilinearPrimeCubeIndex
public import CFSG.StronglyEmbedded.SteinbergBSPrimeFixedPointFreeNilpotent
public import CFSG.GroupTheory.CyclicQuotient
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofCube

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {A : Type*} [Group A] [Finite A] {K : Type} [Field K] [Finite K]

theorem no_cyclic_irreducible_normal_of_semilinear_rank
    (hK : Nat.card K = 4)
    (rho : A →* coordinateSemilinearGroup 3 K)
    (tau : linearKernel rho →* GL (Fin 3) K)
    (htau : ∀ j : linearKernel rho, rho (j : A) = SemidirectProduct.inl (tau j))
    (htau_inj : Function.Injective tau)
    (hindex : (linearKernel rho).index = 2)
    (hirr : IsIrreducibleMatrixRep tau.range.subtype)
    (hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (linearKernel rho)))
    (Z : Subgroup (linearKernel rho)) (hZcard : Nat.card Z = 3)
    (hZscalar : ∀ z ∈ Z, ∃ c : Kˣ,
      tau z = GeneralLinearGroup.scalar (Fin 3) c)
    (hno : ∀ N : Subgroup A, N.Normal → N.index ≠ 3)
    (C : Subgroup (GL (Fin 3) K)) (hC_le : C ≤ tau.range)
    (hCcyc : IsCyclic C) (hCirr : IsIrreducibleMatrixRep C.subtype)
    (hCnorm : ∀ g ∈ tau.range, ∀ x ∈ C, g * x * g⁻¹ ∈ C) :
    False := by
  classical
  obtain ⟨hKcNormal, hKcCyclic, hKcCardDvd, hKcIndexDvd, hGcardDvd⟩ :=
    cyclic_centralizer_structure_of_cyclic_irreducible_normal
      (K := K) (n := 3) Nat.prime_three (G := tau.range) (H := C)
      hC_le hCnorm hCcyc hCirr
  let Kc : Subgroup tau.range :=
    (Subgroup.centralizer (C : Set (GL (Fin 3) K))).subgroupOf tau.range
  have hGdvd189 : Nat.card tau.range ∣ 189 := by
    have h := hGcardDvd
    rw [hK] at h
    norm_num at h ⊢
    exact h
  have hcardJG : Nat.card (linearKernel rho) = Nat.card tau.range :=
    Nat.card_congr (MonoidHom.ofInjective htau_inj).toEquiv
  have hJdvd189 : Nat.card (linearKernel rho) ∣ 189 := by
    rw [hcardJG]
    exact hGdvd189
  by_cases h7 : 7 ∣ Nat.card tau.range
  ·
    have hKcCard63 : Nat.card Kc ∣ 63 := by
      have h := hKcCardDvd
      rw [hK] at h
      norm_num at h
      exact h
    have h7Kc : 7 ∣ Nat.card Kc := by
      have h7prod : 7 ∣ Nat.card Kc * Kc.index := by
        rwa [Subgroup.card_mul_index Kc]
      rcases (Nat.prime_seven.dvd_mul).mp h7prod with h7k | h7i
      · exact h7k
      · exact absurd (h7i.trans hKcIndexDvd) (by norm_num)
    have h49Kc : ¬ 49 ∣ Nat.card Kc := by
      intro h
      exact absurd (h.trans hKcCard63) (by norm_num)
    have hKcFac : (Nat.card Kc).factorization 7 = 1 := by
      haveI : Nonempty Kc := ⟨1⟩
      have hne : Nat.card Kc ≠ 0 := (Nat.card_pos (α := Kc)).ne'
      have hpos : 0 < (Nat.card Kc).factorization 7 :=
        Nat.prime_seven.factorization_pos_of_dvd hne h7Kc
      have hlt : (Nat.card Kc).factorization 7 < 2 := by
        by_contra hge
        have h2 : 2 ≤ (Nat.card Kc).factorization 7 := not_lt.mp hge
        have hpow : 7 ^ 2 ∣ Nat.card Kc :=
          (Nat.prime_seven.pow_dvd_iff_le_factorization hne).2 h2
        exact h49Kc (by simpa [show (7 : ℕ) ^ 2 = 49 by norm_num] using hpow)
      omega
    let S : Sylow 7 Kc := default
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    haveI : Finite Kc := Subtype.finite
    haveI : IsCyclic Kc := hKcCyclic
    have hScard : Nat.card (S : Subgroup Kc) = 7 := by
      rw [S.card_eq_multiplicity, hKcFac, pow_one]
    have hSnorm : (S : Subgroup Kc).Normal := Subgroup.normal_of_isMulCommutative _
    have hSchar : (S : Subgroup Kc).Characteristic :=
      Sylow.characteristic_of_normal S hSnorm
    haveI : Kc.Normal := hKcNormal
    haveI : (S : Subgroup Kc).Characteristic := hSchar
    have hQnorm : ((S : Subgroup Kc).map Kc.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hQp : IsPGroup 7 ((S : Subgroup Kc).map Kc.subtype) :=
      S.isPGroup'.map Kc.subtype
    have hQcard : Nat.card ((S : Subgroup Kc).map Kc.subtype) = 7 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Kc)]
      exact hScard
    have h7pCore : 7 ∣ Nat.card (CFSG.pCore 7 tau.range) := by
      have hle : (S : Subgroup Kc).map Kc.subtype ≤ CFSG.pCore 7 tau.range := by
        unfold CFSG.pCore
        exact le_sSup ⟨hQnorm, hQp⟩
      have hcdvd : Nat.card ((S : Subgroup Kc).map Kc.subtype) ∣
          Nat.card (CFSG.pCore 7 tau.range) :=
        Subgroup.card_dvd_of_le hle
      rwa [hQcard] at hcdvd
    have hPcard : Nat.card (CFSG.pCore 7 tau.range) = 7 := by
      haveI : Finite (CFSG.pCore 7 tau.range) := Subtype.finite
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 7) (G := tau.range)).exists_card_eq
      have h7pow : 7 ∣ 7 ^ k := by
        rwa [hk] at h7pCore
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0] at h7pow
          norm_num at h7pow
        · exact hkpos
      have hklt : k < 2 := by
        by_contra hge
        have h2 : 2 ≤ k := not_lt.mp hge
        have h49P : 49 ∣ Nat.card (CFSG.pCore 7 tau.range) := by
          rw [hk]
          have hpow : 7 ^ 2 ∣ 7 ^ k := pow_dvd_pow 7 h2
          simpa [show (7 : ℕ) ^ 2 = 49 by norm_num] using hpow
        have h49G : 49 ∣ Nat.card tau.range := by
          have hcdvd : Nat.card (CFSG.pCore 7 tau.range) ∣
              Nat.card (⊤ : Subgroup tau.range) :=
            Subgroup.card_dvd_of_le (H := CFSG.pCore 7 tau.range) (K := ⊤) le_top
          rw [Subgroup.card_top] at hcdvd
          exact h49P.trans hcdvd
        exact absurd (h49G.trans hGdvd189) (by norm_num)
      have hk1 : k = 1 := by omega
      rw [hk, hk1]
      norm_num
    set U : Subgroup (GL (Fin 3) K) := (CFSG.pCore 7 tau.range).map tau.range.subtype with hUdef
    have hUcard : Nat.card U = 7 := by
      rw [hUdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective tau.range), hPcard]
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hUcyc : IsCyclic U := isCyclic_of_prime_card (p := 7) hUcard
    obtain ⟨u, hu⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := U)).mp hUcyc
    have huord : orderOf (u : GL (Fin 3) K) = 7 := by
      have h1 : orderOf u = Nat.card U := orderOf_eq_card_of_zpowers_eq_top hu
      rw [Subgroup.orderOf_coe u, h1, hUcard]
    have hUzp : Subgroup.zpowers (u : GL (Fin 3) K) = U := by
      have hmap := MonoidHom.map_zpowers (Subgroup.subtype U) u
      rw [hu, Subgroup.map_top, Subgroup.range_subtype] at hmap
      exact hmap.symm
    have hUirr : IsIrreducibleMatrixRep U.subtype := by
      rw [← hUzp]
      exact isIrreducibleMatrixRep_zpowers_of_orderOf_eq_seven hK huord
    have hU : ∀ a : A, ∀ u ∈ U, coordinateSemilinearGLAct 3 K (rho a) u ∈ U := by
      intro a u hu
      have hP : tau.range.map (coordinateSemilinearGLAct 3 K (rho a)).toMonoidHom =
          tau.range :=
        tau_range_map_coordinateSemilinearGLAct_eq 3 K rho tau htau a
      have hcore : ((CFSG.pCore 7 tau.range).map tau.range.subtype).map
          (coordinateSemilinearGLAct 3 K (rho a)).toMonoidHom =
            (CFSG.pCore 7 tau.range).map tau.range.subtype :=
        CFSG.StronglyEmbedded.map_map_subtype_eq_of_characteristic
          (α := coordinateSemilinearGLAct 3 K (rho a)) (P := tau.range) hP
          (CFSG.pCore 7 tau.range)
      change u ∈ (CFSG.pCore 7 tau.range).map tau.range.subtype at hu
      have hmem : coordinateSemilinearGLAct 3 K (rho a) u ∈
          ((CFSG.pCore 7 tau.range).map tau.range.subtype).map
            (coordinateSemilinearGLAct 3 K (rho a)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rw [hcore] at hmem
      simpa only [hUdef] using hmem
    set δA : A →* RingAut (commutant U) := semilinearCommutantAction rho U hU with hδA
    set δJ : linearKernel rho →* RingAut (commutant U) :=
      δA.comp (linearKernel rho).subtype with hδJ
    have hδJcard : Nat.card δJ.range ∣ 3 := by
      have h := natCard_range_semilinearCommutantAction_comp_ker_dvd
        (n := 3) (K := K) Nat.prime_three rho U hU hUcyc hUirr tau htau
      simpa [hδA, hδJ, linearKernel] using h
    have hker : δJ.ker =
        (Subgroup.centralizer (U : Set (GL (Fin 3) K))).comap tau := by
      have h := linearKernel_semilinearCommutantAction_eq
        (n := 3) (K := K) Nat.prime_three rho U hU hUcyc hUirr tau htau
      simpa [hδA, hδJ, linearKernel] using h
    have hδJcases : Nat.card δJ.range = 1 ∨ Nat.card δJ.range = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp hδJcard
    rcases hδJcases with hδJone | hδJthree
    ·
      have hrangeBot : δJ.range = ⊥ := Subgroup.card_eq_one.mp hδJone
      have hδJeqOne : δJ = 1 := MonoidHom.range_eq_bot_iff.mp hrangeBot
      have hkerTop : δJ.ker = ⊤ := by
        rw [hδJeqOne]
        exact MonoidHom.ker_one
      have hcomapTop : (Subgroup.centralizer (U : Set (GL (Fin 3) K))).comap tau = ⊤ := by
        rw [← hker, hkerTop]
      have hrangeLe : tau.range ≤ Subgroup.centralizer (U : Set (GL (Fin 3) K)) := by
        intro g hg
        rcases hg with ⟨j, rfl⟩
        have hm : j ∈ (Subgroup.centralizer (U : Set (GL (Fin 3) K))).comap tau := by
          rw [hcomapTop]
          exact Subgroup.mem_top j
        exact hm
      haveI : IsCyclic (Subgroup.centralizer (U : Set (GL (Fin 3) K))) := by
        have hsub : IsCyclic ((Subgroup.centralizer (U : Set (GL (Fin 3) K))).subgroupOf
            (⊤ : Subgroup (GL (Fin 3) K))) :=
          isCyclic_cyclicCentralizer_subgroupOf
            (K := K) (n := 3) Nat.prime_three (G := ⊤) (H := U) hUirr
        exact (Subgroup.subgroupOfEquivOfLe
          (le_top : Subgroup.centralizer (U : Set (GL (Fin 3) K)) ≤ ⊤)).isCyclic.mp hsub
      have hcycRange : IsCyclic tau.range :=
        isCyclic_of_injective (Subgroup.inclusion hrangeLe)
          (Subgroup.inclusion_injective hrangeLe)
      haveI : IsCyclic tau.range := hcycRange
      have hcycJ : IsCyclic (linearKernel rho) :=
        (MonoidHom.ofInjective htau_inj).isCyclic.mpr hcycRange
      have hcycTop : IsCyclic (⊤ : Subgroup (linearKernel rho)) :=
        Subgroup.topEquiv.isCyclic.mpr hcycJ
      have hrankLe := CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcycTop
      omega
    ·
      have hrangeLe : δJ.range ≤ δA.range := by
        rw [hδJ, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _
      have h3dvd : 3 ∣ Nat.card δA.range := by
        have h := Subgroup.card_dvd_of_le hrangeLe
        rwa [hδJthree] at h
      haveI : IsCyclic (RingAut (commutant U)) :=
        (card_ringAut_commutant_eq_six_and_isCyclic hK hUcyc hUirr).2
      haveI : IsCyclic δA.range := inferInstance
      exact (CFSG.not_dvd_card_range_of_no_normal_index δA (by norm_num) hno) h3dvd
  ·
    have hcop : Nat.Coprime (Nat.card tau.range) 7 :=
      ((Nat.prime_seven.coprime_iff_not_dvd).2 h7).symm
    have hGdvd27 : Nat.card tau.range ∣ 27 := by
      have h189 : Nat.card tau.range ∣ 27 * 7 := by
        simpa [show 27 * 7 = 189 by norm_num] using hGdvd189
      exact hcop.dvd_of_dvd_mul_right h189
    have hcardJdvd27 : Nat.card (linearKernel rho) ∣ 27 := by
      rw [hcardJG]
      exact hGdvd27
    have hnotAbelian : ¬ IsMulCommutative (linearKernel rho) := by
      intro hcomm
      have hcommRange : ∀ a ∈ tau.range, ∀ b ∈ tau.range, a * b = b * a := by
        intro a ha b hb
        rcases ha with ⟨ja, rfl⟩
        rcases hb with ⟨jb, rfl⟩
        simpa using congrArg (fun z : linearKernel rho => (tau z : GL (Fin 3) K))
          (hcomm.is_comm.comm ja jb)
      have hcycRange : IsCyclic tau.range :=
        (cyclic_of_irreducible_of_commute (K := K) (n := 3) Nat.prime_three
          (G := tau.range) hirr hcommRange).1
      haveI : IsCyclic tau.range := hcycRange
      have hcycJ : IsCyclic (linearKernel rho) :=
        (MonoidHom.ofInjective htau_inj).isCyclic.mpr hcycRange
      have hcycTop : IsCyclic (⊤ : Subgroup (linearKernel rho)) :=
        Subgroup.topEquiv.isCyclic.mpr hcycJ
      have hrankLe := CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcycTop
      omega
    have hcard27 : Nat.card (linearKernel rho) = 27 := by
      by_contra hne
      change Nat.card (linearKernel rho) ∣ 3 ^ 3 at hcardJdvd27
      obtain ⟨k, hk, hcardk⟩ :=
        (Nat.dvd_prime_pow Nat.prime_three).mp hcardJdvd27
      have hdvd9 : Nat.card (linearKernel rho) ∣ 9 := by
        interval_cases k
        · rw [hcardk]
          norm_num
        · rw [hcardk]
          norm_num
        · rw [hcardk]
          norm_num
        · norm_num at hcardk
          change Nat.card (linearKernel rho) = 27 at hcardk
          exact absurd hcardk hne
      exact hnotAbelian (CFSG.RankThree.PartTwo.Sec14.Res9ON.isMulCommutative_of_card_dvd_nine hdvd9)
    have hnc : ∃ x y : linearKernel rho, x * y ≠ y * x := by
      by_contra h
      apply hnotAbelian
      refine ⟨⟨fun x y => ?_⟩⟩
      by_contra hxy
      exact h ⟨x, y, hxy⟩
    obtain ⟨N, hN, hNindex⟩ :=
      exists_normal_index_three_of_semilinear_card_twenty_seven_index_two
        (A := A) (K := K) hK rho tau htau htau_inj hindex hcard27 hnc Z hZcard hZscalar
    exact hno N hN hNindex

end CFSG.LinearAlgebra
