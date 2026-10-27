module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

section Quasisimple

open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth3_isQuasisimple_specialBlock_paired (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    have := hp.two_le
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4)

theorem orth3_isQuasisimple_specialBlock_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hd0 : d ≠ 0 := by
    rintro rfl
    have : 0 < finrank K (AdjoinRoot h) := Module.finrank_pos
    omega
  have hq4 : 4 ≤ ℓ ^ (f * d) := by
    have h1 : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq, pow_mul]
    have h2 : Nat.card K ≤ Nat.card K ^ d := Nat.le_self_pow hd0 _
    omega
  have hnq : ∀ n, (n, ℓ ^ (f * d)) ≠ (3, 2) := fun n e => by
    have := congrArg Prod.snd e
    simp only at this
    omega
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm ?_
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with h2 | h3
  · have hm2 : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := by
      have : primaryMultiplicity x.toLinearMap h = 2 := by omega
      exact this
    exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup hU hBsymm hBl hm2 hq4
  · exact isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl h3 (hnq _)

theorem orth3_quasisimple_specialBlock (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact orth3_isQuasisimple_specialBlock_selfDual hx hp hp2 hK4 hh hne1 hself hm
  · exact orth3_isQuasisimple_specialBlock_paired hx hp hp2 hh hne1 hself hm

theorem orth3_specialBlock_le_orthDerived (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    specialBlock Q x h ≤ orthDerived Q :=
  specialBlock_le_orthDerived_of_perfect (orth3_quasisimple_specialBlock hx hp hp2 hK4 hh hne1 hm).1
    ((specialBlock_le_isometryCentralizer h).trans
      (fun _ hg => (Subgroup.mem_inf.mp hg).1))

end Quasisimple


section Centralizer

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth3_conj_injective_and_centralizer
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p) :
    Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        centralizerImage Q (x : V ≃ₗ[K] V) := by
  classical
  obtain ⟨-, -, -, hsimple, hnonab, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  obtain ⟨x₀, ⟨-, -⟩, huniq, hcent⟩ := hlift p hp hp2 a ha
  have hxx₀ : x = x₀ := huniq x hxa hxp
  subst hxx₀
  refine ⟨conj_injective_of_center_eq_bot hcenterT, ?_⟩
  rw [hcent]
  exact map_centralizer_eq_centralizerImage x

end Centralizer


section Special

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth3_special_facts
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep)
    {h : K[X]} (hh : h ∈ Rep) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) :
    specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q ∧
      componentImage Q (x : V ≃ₗ[K] V) h ≠ ⊥ ∧
      componentImage Q (x : V ≃ₗ[K] V) h ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
      IsComponent (((componentImage Q (x : V ≃ₗ[K] V) h).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))) := by
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨hinj, hNeq⟩ := orth3_conj_injective_and_centralizer hQ hT hp hp2 a ha x hxa hxp
  have hhh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap := hRep.1 hh
  have hFΩ := orth3_specialBlock_le_orthDerived hx hp hp2 hK4 hhh hne1 hm
  have hq := orth3_quasisimple_specialBlock hx hp hp2 hK4 hhh hne1 hm
  have hqJ := isQuasisimple_map_projective hFΩ hq
  have hJN : componentImage Q (x : V ≃ₗ[K] V) h ≤
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := by
    rw [hNeq]
    exact componentImage_le_centralizerImage
  have hJnorm : ((componentImage Q (x : V ≃ₗ[K] V) h).subgroupOf
      (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).Normal := by
    rw [hNeq]
    exact normal_componentImage
  refine ⟨hFΩ, ?_, hJN, isComponent_conj_subgroupOf hB a hinj hJN hJnorm hqJ⟩
  have := CFSG.LocalCores.isQuasisimple_nontrivial hqJ
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this

end Special

section FixedLayer

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth3_split_four_factors
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha1 : a ≠ 1) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    (hW4 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4)
    (hsplit : ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
      ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0)
    (hq : 3 < Nat.card K) :
    ∃ (ψ : fixedSpace (x : V ≃ₗ[K] V) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
      (e : ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)) ≃* DeterminantIsometries K),
      (∀ v, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) v = (ψ v).det) ∧
      (∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype))) (X : Matrix (Fin 2) (Fin 2) K),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      (⨆ i, fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
        (splitFourFactors e i)) = fixedLayerImage Q (x : V ≃ₗ[K] V) ∧
      (∀ i, supportedFactor (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i) ≤ orthDerived Q ∧
        fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i) ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i)) ∧
        fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i) ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
        ((fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i)).subgroupOf
            (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
        IsComponent (((fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e i)).map
            (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
      ∀ u ∈ fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e 0),
        ∀ v ∈ fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp)
          (splitFourFactors e 1), u * v = v * u := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha : orderOf a = p := by
    refine orderOf_eq_prime ?_ ha1
    rw [← hxa, ← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one]
    rfl
  obtain ⟨hinj, hNeq⟩ := orth3_conj_injective_and_centralizer hQ hT hp hp2 a ha x hxa hxp
  have hlist : FixedLayerListed Q (x : V ≃ₗ[K] V) :=
    ⟨by omega, by rintro (⟨h, -⟩ | ⟨-, h⟩) <;> omega⟩
  obtain ⟨ψ, e, hψ, he, hsup, hC, hcomm⟩ := hx.fixedLayer_splitFour hW4 hsplit hq
  refine ⟨ψ, e, hψ, he, ?_, fun i => ?_, hcomm⟩
  · rw [hsup]
    simp [fixedLayerImage, hlist]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hC i
    rw [← hNeq] at h4 h5
    exact ⟨h1, h2, h3, h4, h5,
      isComponent_conj_subgroupOf_of_subnormal hB a hinj h4 h5 h3⟩

theorem orth3_unsplit_fixed_layer
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha1 : a ≠ 1) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    (hlist : FixedLayerListed Q (x : V ≃ₗ[K] V))
    (hns : ¬ (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
      ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0)) :
    fixedComponentImage Q (x : V ≃ₗ[K] V) ≠ ⊥ ∧
      CFSG.IsQuasisimple ↥(fixedComponentImage Q (x : V ≃ₗ[K] V)) ∧
      fixedComponentImage Q (x : V ≃ₗ[K] V) ≤
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
      ((fixedComponentImage Q (x : V ≃ₗ[K] V)).subgroupOf
        (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).IsSubnormal ∧
      IsComponent (((fixedComponentImage Q (x : V ≃ₗ[K] V)).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha : orderOf a = p := by
    refine orderOf_eq_prime ?_ ha1
    rw [← hxa, ← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one]
    rfl
  obtain ⟨hinj, hNeq⟩ := orth3_conj_injective_and_centralizer hQ hT hp hp2 a ha x hxa hxp
  have hqW := orthogonal_regular_space_derived_quasisimple (Q.comp (fixedSpace _).subtype)
    hx.polarBilin_fixed_nondegenerate hlist.1 hlist.2 hns
  obtain ⟨h1, h2, -, h4, h5⟩ := hx.fixedLayer_unsplit hqW
  rw [← hNeq] at h4 h5
  exact ⟨h1, h2, h4, h5, isComponent_conj_subgroupOf_of_subnormal hB a hinj h4 h5 h2⟩

end FixedLayer

end CFSG.HardMathSupport.Timmesfeld.CrossChar
