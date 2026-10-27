module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeLin
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.AGLEmbedding

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

theorem pow_three_eq_one_of_card_eq_four (hK : Nat.card K = 4) {μ : K} (hμ : μ ≠ 0) :
    μ ^ 3 = 1 := by
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 μ hμ)
  rw [h3] at this
  simpa using congrArg Units.val this

theorem natDegree_eq_one_of_dvd_X_pow_three_sub_one (hK : Nat.card K = 4) {b : K[X]}
    (hb : Irreducible b) (hdvd : b ∣ X ^ 3 - C 1) : b.natDegree = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsurj : Function.Surjective (fun t : Bool => if t then (1 : K) else 0) := fun z => by
      by_cases hz : z = 0
      · exact ⟨false, by simp [hz]⟩
      · exact ⟨true, by simp [hall z hz]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hK, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    omega
  have hω3 := pow_three_eq_one_of_card_eq_four hK hω0
  have hωq : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      calc (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
        _ = 0 := by rw [hω3, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  have hfac : (X ^ 3 - C 1 : K[X]) = (X - C 1) * (X - C ω) * (X - C (ω ^ 2)) := by
    have e1 : C (1 + ω + ω ^ 2) = (0 : K[X]) := by
      rw [show (1 : K) + ω + ω ^ 2 = ω ^ 2 + ω + 1 by ring, hωq, map_zero]
    have e2 : C (ω ^ 3) = (1 : K[X]) := by rw [hω3, map_one]
    calc (X ^ 3 - C 1 : K[X]) = X ^ 3 - C (1 + ω + ω ^ 2) * X ^ 2 +
          C (1 + ω + ω ^ 2) * C ω * X - C (ω ^ 3) := by
            rw [e1, e2, map_one]; ring
      _ = (X - C 1) * (X - C ω) * (X - C (ω ^ 2)) := by
            simp only [map_add, map_pow, map_one]; ring
  rw [hfac] at hdvd
  have hlin : ∀ μ : K, b ∣ X - C μ → b.natDegree = 1 := fun μ h => by
    have := natDegree_le_of_dvd h (X_sub_C_ne_zero μ)
    rw [natDegree_X_sub_C] at this
    have := hb.natDegree_pos
    omega
  rcases hb.prime.dvd_or_dvd hdvd with h | h
  · rcases hb.prime.dvd_or_dvd h with h | h
    · exact hlin 1 h
    · exact hlin ω h
  · exact hlin (ω ^ 2) h

theorem exists_quasisimple_of_selfDual (hK : UnitaryFieldData 2 1 K) {n : ℕ}
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (b : primaryFactors
      ((x : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    (SB : SelfDualPrimaryBlock hK (idForm hK n) x b)
    (hq : ∀ (hE : UnitaryFieldData 2 (1 * (b : K[X]).natDegree) (AdjoinRoot (b : K[X])))
      (Hf : primaryComponent (x : Module.End K (Fin n → K)) (b : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K (Fin n → K)) (b : K[X]) →ₗ[AdjoinRoot (b : K[X])]
          AdjoinRoot (b : K[X])), Hf.IsSymm → Hf.SeparatingLeft →
      (supportedUnitary (idForm hK n) x {(b : K[X])} ≃* sesqUnitaryGroup Hf) →
      CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf)) :
    ∃ L : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)), CFSG.IsQuasisimple L ∧
      L ≤ unitaryCentralizer (idForm hK n) x ∧
      ∀ g ∈ L, LinearMap.det (g : Module.End K (Fin n → K)) = 1 := by
  obtain ⟨-, hE, -, -, Hf, hHf, hHfl, -, -, φ, -, hdet⟩ := SB
  have hSU := hq hE Hf hHf hHfl φ
  have hL : CFSG.IsQuasisimple ((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm hSU
  set ψ := (supportedUnitary (idForm hK n) x {(b : K[X])}).subtype.comp φ.symm.toMonoidHom
  have hψ : Function.Injective ψ := (Subgroup.subtype_injective _).comp φ.symm.injective
  refine ⟨_, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ ψ hψ) hL, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact (φ.symm s).2.1
  · rintro _ ⟨s, hs, rfl⟩
    refine hdet (φ.symm s) ?_
    rw [MulEquiv.apply_symm_apply]
    exact hs

theorem exists_quasisimple_of_paired (hK : UnitaryFieldData 2 1 K) {n : ℕ}
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (b : primaryFactors
      ((x : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    (PB : PairedPrimaryBlock hK (idForm hK n) x b)
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X]))
    (h4 : ∃ s : Finset (AdjoinRoot (b : K[X])), s.card = 4) :
    ∃ L : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)), CFSG.IsQuasisimple L ∧
      L ≤ unitaryCentralizer (idForm hK n) x ∧
      ∀ g ∈ L, LinearMap.det (g : Module.End K (Fin n → K)) = 1 := by
  obtain ⟨φ, ψ, -, -, hdetψ, hdetK⟩ := PB.factor
  have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hm (Or.inr h4)
  have hL : CFSG.IsQuasisimple (⊤ : Subgroup (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X])))
      (AdjoinRoot (b : K[X])))) := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    Subgroup.topEquiv.symm hq
  set χ := ((supportedUnitary (idForm hK n) x {(b : K[X]), dualPoly hK.bar (b : K[X])}).subtype.comp
    ψ.symm.toMonoidHom).comp Matrix.SpecialLinearGroup.toGL
  have hχ : Function.Injective χ := ((Subgroup.subtype_injective _).comp ψ.symm.injective).comp
    Matrix.SpecialLinearGroup.toGL_injective
  refine ⟨_, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ χ hχ) hL, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact (ψ.symm _).2.1
  · rintro _ ⟨s, -, rfl⟩
    refine hdetK (ψ.symm (Matrix.SpecialLinearGroup.toGL s)) ?_
    rw [← hdetψ, MulEquiv.apply_symm_apply]
    exact s.2

open scoped _root_.Classical in
theorem exists_quasisimple_of_linear_component (hK : UnitaryFieldData 2 1 K) {n : ℕ}
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (UA : UnitaryPrimaryAlgebra hK (idForm hK n)
      (idForm_isSymm hK n) (idForm_separatingLeft hK n) x)
    (b : primaryFactors ((x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (hdeg : (b : K[X]).natDegree = 1)
    {g : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hgO : g ∈ supportedUnitary (idForm hK n) x {(b : K[X]), dualPoly hK.bar (b : K[X])})
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ L : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)), CFSG.IsQuasisimple L ∧
      L ≤ unitaryCentralizer (idForm hK n) x ∧
      ∀ g ∈ L, LinearMap.det (g : Module.End K (Fin n → K)) = 1 := by
  have hK4 : Nat.card K = 4 := by rw [hK.card]; norm_num
  have : Fact p.Prime := ⟨hp⟩
  by_cases hself : dualPoly hK.bar (b : K[X]) = b
  · have hgO' : g ∈ supportedUnitary (idForm hK n) x {(b : K[X])} := by
      rwa [hself, Set.pair_eq_singleton] at hgO
    refine exists_quasisimple_of_selfDual hK b (UA.selfDual b hself) fun hE Hf hHf hHfl φ => ?_
    let g' : supportedUnitary (idForm hK n) x {(b : K[X])} := ⟨g, hgO'⟩
    refine isQuasisimple_sesqSU_of_prime_order hE (Or.inl (by rw [hdeg])) hHf hHfl (g := φ g')
      hp hp5 ?_ ?_
    · rw [← map_pow, show g' ^ p = 1 from Subtype.ext (by simpa using hgp), map_one]
    · exact fun h1 => hg1 (congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm)))
  · have PB := UA.paired b (Ne.symm hself)
    obtain ⟨-, ψ, -, -, -, -⟩ := PB.factor
    have hirr := irreducible_of_mem_primaryFactors b.2
    have hE4 : Nat.card (AdjoinRoot (b : K[X])) = 4 := by
      have : Module.Finite K (AdjoinRoot (b : K[X])) :=
        (AdjoinRoot.powerBasis hirr.ne_zero).finite
      rw [Module.natCard_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, hdeg, hK4, pow_one]
    have : Fintype (AdjoinRoot (b : K[X])) :=
      @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero (by rw [hE4]; norm_num))
    have h4 : ∃ s : Finset (AdjoinRoot (b : K[X])), s.card = 4 :=
      ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hE4]⟩
    by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X])
    · exact exists_quasisimple_of_paired hK b PB hm h4
    · exfalso
      let g' : supportedUnitary (idForm hK n) x {(b : K[X]), dualPoly hK.bar (b : K[X])} :=
        ⟨g, hgO⟩
      have hg'p : g' ^ p = 1 := Subtype.ext (by simpa using hgp)
      have hg'1 : g' ≠ 1 := fun h1 => hg1 (congrArg Subtype.val h1)
      have hord : orderOf (ψ g') = p := by
        rw [MulEquiv.orderOf_eq]
        exact orderOf_eq_prime hg'p hg'1
      refine not_dvd_card_GL_of_small hp hp5 ?_ (hord ▸ orderOf_dvd_natCard (ψ g'))
      rcases (show primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X]) = 0 ∨
          primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X]) = 1 by omega) with
        h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨h1, by rw [← Nat.card_eq_fintype_card, hE4]⟩)

open scoped _root_.Classical in
theorem exists_quasisimple_of_cube_eq_one (hK : UnitaryFieldData 2 1 K) {n : ℕ}
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (hx : x ∈ sesqUnitaryGroup (idForm hK n))
    (hx3 : x ^ 3 = 1) {y : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hy : y ∈ unitaryCentralizer (idForm hK n) x) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hyp : y ^ p = 1) (hy1 : y ≠ 1) :
    ∃ L : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)), CFSG.IsQuasisimple L ∧
      L ≤ unitaryCentralizer (idForm hK n) x ∧
      ∀ g ∈ L, LinearMap.det (g : Module.End K (Fin n → K)) = 1 := by
  have hK4 : Nat.card K = 4 := by rw [hK.card]; norm_num
  have : Finite K := hK.finite
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    have : CharP K 2 := hK.charP
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hxe : (x : Module.End K (Fin n → K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  have hsq := CFSG.RankThree.PartOne.KCLinComm.squarefree_minpoly_of_pow_eq_one h3K hxe
  have UA := r3e_unitary_semisimple_primary_algebra_and_full_centralizer hK (idForm hK n)
    (idForm_isSymm hK n) (idForm_separatingLeft hK n) x hx hsq
  obtain ⟨hcomm, hind, hsup⟩ := UA.directProduct
  have : Finite (adjointOrbits hK x) :=
    (((primaryFactors (x : Module.End K (Fin n → K))).finite_toSet).image _).to_subtype
  rw [← hsup] at hy
  obtain ⟨⟨O, hO⟩, g, hgO, hgp, hg1⟩ := exists_ne_one_mem_of_iSupIndep
    (H := fun O : adjointOrbits hK x => supportedUnitary (idForm hK n) x (O : Set K[X]))
    (fun i j hij u v hu hv => hcomm i i.2 j j.2 (fun h => hij (Subtype.ext h)) u hu v hv)
    hind hy hyp hy1
  obtain ⟨a, ha, rfl⟩ := hO
  exact exists_quasisimple_of_linear_component hK UA ⟨a, ha⟩
    (natDegree_eq_one_of_dvd_X_pow_three_sub_one hK4 (irreducible_of_mem_primaryFactors ha)
      ((mem_primaryFactors.mp ha).2.2.trans (minpoly.dvd K _ (by simp [hxe])))) hgO hp hp5 hgp hg1

theorem irreducible_X_pow_three_sub_C_of_card_four (hK : Nat.card K = 4) {c : K} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) : Irreducible (X ^ 3 - C c : K[X]) := by
  have hdeg : (X ^ 3 - C c : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp)
    fun μ hμ => ?_
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hμ]; ring)
  exact hc1 (by rw [← hμ, pow_three_eq_one_of_card_eq_four hK hμ0])

open scoped _root_.Classical in
theorem exists_quasisimple_of_cube_eq_scalar (hK : UnitaryFieldData 2 1 K) {n : ℕ} (hn : 4 ≤ n)
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (hx : x ∈ sesqUnitaryGroup (idForm hK n))
    {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hx3 : (x : Module.End K (Fin n → K)) ^ 3 = algebraMap K _ c) :
    ∃ L : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)), CFSG.IsQuasisimple L ∧
      L ≤ unitaryCentralizer (idForm hK n) x ∧
      ∀ g ∈ L, LinearMap.det (g : Module.End K (Fin n → K)) = 1 := by
  have hK4 : Nat.card K = 4 := by rw [hK.card]; norm_num
  have hPirr := irreducible_X_pow_three_sub_C_of_card_four hK4 hc0 hc1
  have hPmon : (X ^ 3 - C c : K[X]).Monic := monic_X_pow_sub_C c (by norm_num)
  have hPx : aeval (x : Module.End K (Fin n → K)) (X ^ 3 - C c) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hx3, sub_self]
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Fin n → K) := Function.nontrivial
  have hmin : minpoly K (x : Module.End K (Fin n → K)) = X ^ 3 - C c :=
    (minpoly.eq_of_irreducible_of_monic hPirr hPx hPmon).symm
  have hsq : Squarefree (minpoly K (x : Module.End K (Fin n → K))) :=
    hmin ▸ hPirr.squarefree
  have UA := r3e_unitary_semisimple_primary_algebra_and_full_centralizer hK (idForm hK n)
    (idForm_isSymm hK n) (idForm_separatingLeft hK n) x hx hsq
  have hPmem : (X ^ 3 - C c : K[X]) ∈ primaryFactors (x : Module.End K (Fin n → K)) :=
    mem_primaryFactors.mpr ⟨hPirr, hPmon, hmin.symm ▸ dvd_rfl⟩
  have honly : ∀ a ∈ primaryFactors (x : Module.End K (Fin n → K)), a = X ^ 3 - C c := by
    intro a ha
    obtain ⟨hairr, hamon, hadvd⟩ := mem_primaryFactors.mp ha
    rw [hmin] at hadvd
    exact eq_of_monic_of_associated hamon hPmon (hairr.associated_of_dvd hPirr hadvd)
  have hself := honly _ (UA.dual_mem _ hPmem)
  have : Fact (Irreducible (X ^ 3 - C c : K[X])) := ⟨hPirr⟩
  have htop : primaryComponent (x : Module.End K (Fin n → K)) (X ^ 3 - C c) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, hPx, LinearMap.zero_apply]
  have hfr := finrank_primaryComponent (x : Module.End K (Fin n → K)) (X ^ 3 - C c)
  have hn' : finrank K (primaryComponent (x : Module.End K (Fin n → K)) (X ^ 3 - C c)) = n := by
    rw [htop, finrank_top, Module.finrank_fin_fun]
  rw [hn', natDegree_X_pow_sub_C] at hfr
  refine exists_quasisimple_of_selfDual hK ⟨_, hPmem⟩ (UA.selfDual ⟨_, hPmem⟩ hself)
    fun hE Hf hHf hHfl _ => ?_
  refine CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf
    hHfl ?_ ⟨fun _ => ?_, fun _ => ?_⟩
  · change 2 ≤ finrank (AdjoinRoot (X ^ 3 - C c : K[X]))
      (primaryComponent (x : Module.End K (Fin n → K)) (X ^ 3 - C c))
    omega
  · change 4 ≤ 2 ^ (1 * (X ^ 3 - C c : K[X]).natDegree)
    rw [natDegree_X_pow_sub_C]
    norm_num
  · change 3 ≤ 2 ^ (1 * (X ^ 3 - C c : K[X]).natDegree)
    rw [natDegree_X_pow_sub_C]
    norm_num

end CFSG.AGLEmbedding
