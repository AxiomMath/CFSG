module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Local
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Fixed

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical

section Special

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth3_dvd_card_orthSpecialBlock_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    p ∣ Nat.card ↥(specialBlock Q x h) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
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
  have hrange : (specialBlockGL Q x h).range =
      CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH,
      CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
    e₀ he₀
  have hn : 2 ≤ finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := hm
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root hp hh hne1
  have hζ : IsPrimitiveRoot (AdjoinRoot.root h) p := by
    have h1 : IsPrimitiveRoot (Units.mk0 (AdjoinRoot.root h) hlam0) p :=
      hord ▸ IsPrimitiveRoot.orderOf _
    simpa using IsPrimitiveRoot.coe_units_iff.mpr h1
  have hσ : hU.barEquiv (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := by
    show hU.bar _ = _
    rw [hbar, hroot]
  obtain ⟨s, hs⟩ := exists_orderOf_SUid_of_conj_inv hU.barEquiv hp hn hζ hσ
  rw [Nat.card_congr (e₁.trans e₂).toEquiv, ← hs]
  exact orderOf_dvd_natCard s

theorem orth3_dvd_card_orthSpecialBlock (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    p ∣ Nat.card ↥(specialBlock Q x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact orth3_dvd_card_orthSpecialBlock_selfDual hx hp hp2 hh hne1 hself hm
  · exact dvd_card_orthSpecialBlock_paired hx hp hh hne1 hself hm

end Special

section Local

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth3_orderOf_mk_projOrth (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : orthDerived Q} (hy : orderOf y = p) :
    orderOf (QuotientGroup.mk y : ProjOrthDerived Q) = p := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, hZ, -⟩ := orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  refine orderOf_map_eq_of_coprime_ker_orth
    (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
      (orthDerived Q))) hp ?_ hy
  rw [QuotientGroup.ker_mk']
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hpos : 0 < Nat.card ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
      (orthDerived Q)) := Nat.card_pos
  have := Nat.le_of_dvd hpos hdvd
  have := hp.two_le
  omega

variable (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
  (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
  {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)

include hQ hT hp hp2 hK4 hpl in
theorem orth3_componentImage_le_fixSub (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn p H E)
    (x : orthDerived Q) (hxp : orderOf x = p)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    (Rep : Finset K[X]) (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep)
    (h : K[X]) (hh : h ∈ Rep) (hne : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) :
    componentImage Q (x : V ≃ₗ[K] V) h ≤ fixSub g := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha := orth3_orderOf_mk_projOrth hQ hT hp hp2 hxp
  obtain ⟨hΩ, -, hle, hcomp⟩ :=
    orth3_special_facts hQ hT hp hp2 hK4 hpl H hH _ ha x rfl hxp hRep hh hne hm
  have hdvd := orth3_dvd_card_orthSpecialBlock hx hp hp2 (hRep.1 hh) hne hm
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set s' : orthDerived Q := ⟨(s : V ≃ₗ[K] V), hΩ s.2⟩ with hs'
  have hs'p : orderOf s' = p := by
    rw [← hs, ← Subgroup.orderOf_coe s, ← Subgroup.orderOf_coe s']
  have hρ := orth3_orderOf_mk_projOrth hQ hT hp hp2 hs'p
  have hmem : (QuotientGroup.mk s' : ProjOrthDerived Q) ∈ componentImage Q (x : V ≃ₗ[K] V) h :=
    ⟨s', Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
  have ha1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ha
    exact hp.one_lt.ne' ha.symm
  refine le_fixSub_of_component hp hinj hg he (fun h1 => ha1 (hinj (by rw [h1, map_one])))
    ?_ hcomp (not_coprime_card_of_orderOf_orth hp hmem hρ)
  rintro _ ⟨t, ht, rfl⟩
  refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hle ht)]

include hQ hT hp hp2 hK4 hpl in
theorem orth3_fixedComponentImage_le_fixSub (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn p H E)
    (x : orthDerived Q) (hxp : orderOf x = p)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    {w : V ≃ₗ[K] V} (hw : w ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1)) (hwp : w ^ p = 1)
    (hw1 : w ≠ 1) (h3 : 3 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V))) :
    fixedComponentImage Q (x : V ≃ₗ[K] V) ≤ fixSub g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha := orth3_orderOf_mk_projOrth hQ hT hp hp2 hxp
  have ha1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ha
    exact hp.one_lt.ne' ha.symm
  have he1 : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 :=
    fun h1 => ha1 (hinj (by rw [h1, map_one]))
  have hx1 : (x : V ≃ₗ[K] V) ≠ 1 := fun h1 => ha1 (by
    have : x = 1 := Subtype.ext h1
    rw [this, QuotientGroup.mk_one])
  set gW : ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)) :=
    ⟨restrictFixed Q (x : V ≃ₗ[K] V) ⟨w, hw⟩, restrictFixed_mem_orthogonalGroup _⟩ with hgW
  have hgWp : orderOf gW = p := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      change restrictFixed Q (x : V ≃ₗ[K] V) ⟨w, hw⟩ ^ p = 1
      rw [← map_pow]
      have : (⟨w, hw⟩ : ↥(supportedBlock Q (x : V ≃ₗ[K] V) (X - 1))) ^ p = 1 := Subtype.ext hwp
      rw [this, map_one]
    · intro h1
      have h2 : restrictFixed Q (x : V ≃ₗ[K] V) ⟨w, hw⟩ = 1 := congrArg Subtype.val h1
      exact hw1 (hx.eq_one_of_restrictFixed_eq_one hw h2)
  have hlist : FixedLayerListed Q (x : V ≃ₗ[K] V) :=
    ⟨h3, by rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega⟩
  have hwS : w ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V) :=
    orth3_mem_supportedFixedDerived hx hp hp2 hK4 h3 hw hwp
  have hwΩ := hx.supportedFixedDerived_le_orthDerived hwS
  set w' : orthDerived Q := ⟨w, hwΩ⟩ with hw'
  have hw'p : orderOf w' = p := orderOf_eq_prime (Subtype.ext hwp)
    (fun h1 => hw1 (congrArg Subtype.val h1))
  have hρw := orth3_orderOf_mk_projOrth hQ hT hp hp2 hw'p
  have hmemF : (QuotientGroup.mk w' : ProjOrthDerived Q) ∈
      fixedComponentImage Q (x : V ≃ₗ[K] V) :=
    ⟨w', Subgroup.mem_subgroupOf.mpr hwS, rfl⟩
  have hTC : ∀ S : Subgroup (ProjOrthDerived Q),
      S ≤ Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q)) →
      S.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
        H ⊓ Subgroup.centralizer ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q))) := by
    intro S hS
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hS ht)]
  by_cases hs4 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
      ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0
  ·
    have hq : 3 < Nat.card K := by omega
    obtain ⟨ψ, e, -, -, hsup, hC, hcomm⟩ := orth3_split_four_factors hQ hT hp hp2
      hpl H hH _ ha1 x rfl hxp hs4.1 hs4.2 hq
    rw [fixedLayerImage_of_listed hlist] at hsup
    set C : Fin 2 → Subgroup (ProjOrthDerived Q) := fun i =>
      fixedFactorImage (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp) (splitFourFactors e i)
      with hCdef
    have hcard : ∀ i, Nat.card (C i) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      fun i => card_fixedFactorImage_splitFourFactors _ hx1 e i (hC i).1
    have hpair : Pairwise fun i j : Fin 2 => ∀ u v : ProjOrthDerived Q, u ∈ C i → v ∈ C j →
        Commute u v := by
      intro i j hij u v hu hv
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hcomm u hu v hv
      · exact (hcomm v hv u hu).symm
      · exact absurd rfl hij
    have hpow : ∀ i, ∀ c ∈ C i, c ^ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
      intro i c hc
      rw [← hcard i]
      have := pow_card_eq_one' (G := C i) (x := ⟨c, hc⟩)
      exact congrArg Subtype.val this
    have hdvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [← hρw]
      refine orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_iSup_commute_orth C hpair hpow ?_)
      rw [hsup]
      exact hmemF
    rw [← hsup]
    refine iSup_le fun i => ?_
    obtain ⟨-, -, -, hle, -, hcomp⟩ := hC i
    refine le_fixSub_of_component hp hinj hg he he1 (hTC _ hle) hcomp fun hc => ?_
    rw [hcard i] at hc
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hdvd)
  · obtain ⟨-, -, hle, -, hcomp⟩ := orth3_unsplit_fixed_layer hQ hT hp hp2 hpl
      H hH _ ha1 x rfl hxp hlist hs4
    exact le_fixSub_of_component hp hinj hg he he1 (hTC _ hle) hcomp
      (not_coprime_card_of_orderOf_orth hp hmemF hρw)

end Local
section Derived

open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth3_commutator_centralizer_le_of_blocks
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (x : orthDerived Q) (hxp : orderOf x = p) (F : Subgroup (ProjOrthDerived Q))
    (hspec : ∀ Rep : Finset K[X], IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep →
      ∀ h ∈ Rep, h ≠ X - 1 → 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
        componentImage Q (x : V ≃ₗ[K] V) h ≤ F)
    (hfix : 3 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V)) →
      fixedComponentImage Q (x : V ≃ₗ[K] V) ≤ F) :
    ⁅Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} : Set (ProjOrthDerived Q)),
      Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q))⁆ ≤ F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  set a : ProjOrthDerived Q := QuotientGroup.mk x with ha_def
  have ha : orderOf a = p := by
    have h1 : a ^ p = 1 := by
      rw [ha_def, ← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one, QuotientGroup.mk_one]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h2 | h2
    · exfalso
      have ha1 : a = 1 := orderOf_eq_one_iff.mp h2
      obtain ⟨-, -, hZ, -⟩ :=
        CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
      have hxZ : x ∈ (CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q) :=
        (QuotientGroup.eq_one_iff x).mp ha1
      have hdvd : p ∣ Nat.card ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
          (orthDerived Q)) := by
        rw [← hxp]
        exact Subgroup.orderOf_dvd_natCard _ hxZ
      have hpos : 0 < Nat.card ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
          (orthDerived Q)) := Nat.card_pos
      have := Nat.le_of_dvd hpos hdvd
      have := hp.two_le
      omega
    · exact h2
  obtain ⟨-, hNeq⟩ := orth3_conj_injective_and_centralizer hQ hT hp hp2 a ha x rfl hxp
  obtain ⟨Rep0, hRep0⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))
    with hN
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
    with hρ
  set Mo : Subgroup ↥(orthDerived Q) := (isometryCentralizer Q xe).subgroupOf (orthDerived Q)
    with hMo
  have hbot : ∀ h ∈ Rep0, ¬ 2 ≤ primaryMultiplicity xe.toLinearMap h → specialBlock Q xe h = ⊥ := by
    intro h hh hm
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep0.1 hh)⟩
    have hpos := hx.primaryMultiplicity_pos (hRep0.1 hh)
    have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
    exact hx.specialBlock_eq_bot_of_finrank_eq_one (hRep0.1 hh) h1
  have hspecΩ : ∀ h ∈ Rep0, h ≠ X - 1 → specialBlock Q xe h ≤ orthDerived Q := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · exact orth3_specialBlock_le_orthDerived hx hp hp2 hK4 (hRep0.1 hh) hne hm
    · rw [hbot h hh hm]
      exact bot_le
  have hspecF : ∀ h ∈ Rep0, h ≠ X - 1 → componentImage Q xe h ≤ F := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · exact hspec Rep0 hRep0 h hh hne hm
    · have : componentImage Q xe h = ⊥ := by
        unfold componentImage
        rw [hbot h hh hm, Subgroup.bot_subgroupOf, Subgroup.map_bot]
      rw [this]
      exact bot_le
  set K₀ : Subgroup (V ≃ₗ[K] V) := (F.comap ρ).map (orthDerived Q).subtype with hK₀
  have hmemK₀ : ∀ b : ↥(orthDerived Q), ρ b ∈ F → (b : V ≃ₗ[K] V) ∈ K₀ :=
    fun b hb => ⟨b, hb, rfl⟩
  have hspK₀ : specialProduct Q xe Rep0 ≤ K₀ := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    intro j hj
    have hjΩ := hspecΩ h hh hne hj
    refine hmemK₀ ⟨j, hjΩ⟩ (hspecF h hh hne ?_)
    exact Subgroup.mem_map.mpr ⟨⟨j, hjΩ⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hsfdK₀ : 3 ≤ finrank K (fixedSpace xe) → supportedFixedDerived Q xe ≤ K₀ := by
    intro h3 f hf
    have hfΩ := hx.supportedFixedDerived_le_orthDerived hf
    refine hmemK₀ ⟨f, hfΩ⟩ (hfix h3 ?_)
    exact Subgroup.mem_map.mpr ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  have hspM : specialProduct Q xe Rep0 ≤ isometryCentralizer Q xe :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  have hkey : ⁅Mo, Mo⁆ ≤ F.comap ρ := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    have hmM : (m : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm
    have hm'M : (m' : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm'
    have hg : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈
        ⁅isometryCentralizer Q xe, isometryCentralizer Q xe⁆ :=
      Subgroup.commutator_mem_commutator hmM hm'M
    obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep0 hg
    have hgK : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈ K₀ := by
      by_cases hdim : 3 ≤ finrank K (fixedSpace xe)
      · rw [hgjf]
        exact K₀.mul_mem (hspK₀ hj) (hsfdK₀ hdim hf)
      · have hdim2 : finrank K (fixedSpace xe) ≤ 2 := by omega
        have hfM : f ∈ isometryCentralizer Q xe := supportedFixedDerived_le_isometryCentralizer hf
        have hjM : j ∈ isometryCentralizer Q xe := hspM hj
        have hgM : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := by
          rw [hgjf]
          exact mul_mem hjM hfM
        have h1 : isometryRestrictFixed Q xe ⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V),
            hgM⟩ = 1 := by
          have h2 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) =
              ⁅(⟨(m : V ≃ₗ[K] V), hmM⟩ : ↥(isometryCentralizer Q xe)),
                (⟨(m' : V ≃ₗ[K] V), hm'M⟩ : ↥(isometryCentralizer Q xe))⁆ :=
            Subtype.ext rfl
          rw [h2, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hx.restrict_commute_of_mem_orthDerived hp2' hQ hRep0 hdim2 hmM m.2 hm'M m'.2).eq
        have h3 : isometryRestrictFixed Q xe ⟨f, hfM⟩ = 1 := by
          have h4 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ := Subtype.ext hgjf
          rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep0 hj hjM,
            one_mul] at h1
          exact h1
        have hfB := supportedFixedDerived_le_supportedBlock hf
        have h5 : restrictFixed Q xe ⟨f, hfB⟩ = 1 := by
          rw [← isometryRestrictFixed_restrictFixed]
          exact h3
        have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
        rw [hgjf, hf1, mul_one]
        exact hspK₀ hj
    obtain ⟨b, hb, hbg⟩ := hgK
    have hb' : b = ⁅m, m'⁆ := Subtype.ext hbg
    rw [hb'] at hb
    exact hb
  have hNN : ⁅N, N⁆ = ⁅Mo, Mo⁆.map ρ := by
    rw [hNeq]
    exact (Subgroup.map_commutator Mo Mo ρ).symm
  rw [hNN]
  exact Subgroup.map_le_iff_le_comap.mpr hkey

end Derived

section Main

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem localDeltaIn_eq_bot_projOrth3
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (E₁ : Subgroup (ProjOrthDerived Q)) (hE₁ : IsElemAbelian p E₁) (hc : Nat.card E₁ = p ^ 2)
    (hrig : ∀ g : MulAut (ProjOrthDerived Q),
      (∀ a ∈ E₁, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, g n = n) → g = 1)
    {H : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H) :
    localDeltaIn p H (E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))) =
      ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial V := nontrivial_of_totallySingular_orth hT
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj := conj_injective_of_center_eq_bot_orth hcenter
  have hH' : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H := hH
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  have hE₁' : CFSG.Assembly.IsElemAbelian p E₁ := ⟨hE₁.1, hE₁.2⟩
  obtain ⟨Ã, hÃM, hsyl, e, he, -, -, -, -, hline, -, -, -, -, -⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ E₁ hE₁' hc
  have hK := kernelLineData Q hQ hp hp2 hpl E₁ hE₁' hc Ã ⟨hÃM, hsyl⟩
  have hord : ∀ x : Ã, x ≠ 1 → orderOf (x : orthDerived Q) = p := fun x hx1 => by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hK.exp x) hx1
  have hmemE : ∀ x : Ã, (QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q) ∈ E₁ :=
    fun x => by
      have h1 := he x
      rw [QuotientGroup.mk'_apply] at h1
      rw [← h1]
      exact (e x).2
  have hconjE : ∀ x : Ã, MulAut.conj (QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q) ∈
      E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    fun x => ⟨_, hmemE x, rfl⟩
  have hfix : ∀ M : Subgroup Ã, Nat.card M = p → ∀ x ∈ M, x ≠ 1 →
      fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V) = planeFixSpace Ã ⊔ lineSpace M := by
    intro M hM x hxM hx1
    obtain ⟨h1, h2⟩ := hline M hM x hxM hx1
    rw [← h2, ← h1]
    rfl
  have hoi : ∀ x : Ã, x ≠ 1 → OddOrderIsometry Q p ((x : orthDerived Q) : V ≃ₗ[K] V) :=
    fun x hx1 => oddOrderIsometry_of_orthDerived hp hpl hQ _ (hord x hx1)
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hact : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ → ∀ x ∈ M, x ≠ 1 →
      3 ≤ finrank K (fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V)) →
      fixedComponentImage Q ((x : orthDerived Q) : V ≃ₗ[K] V) ≤ fixSub g := by
    intro M hM hMne x hxM hx1 h3
    obtain ⟨z, hzM⟩ : ∃ z : Ã, z ∉ M := by
      by_contra hall
      push Not at hall
      have hMtop : M = ⊤ := eq_top_iff.2 fun z _ => hall z
      have h1 : Nat.card M = Nat.card Ã := by rw [hMtop, Subgroup.card_top]
      rw [hM, hK.card] at h1
      have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
      omega
    have hz1 : z ≠ 1 := fun h => hzM (h ▸ M.one_mem)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
    have hvW : v ∈ fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V) := by
      rw [hfix M hM x hxM hx1]
      exact Submodule.mem_sup_right hv
    have hzv : ((z : orthDerived Q) : V ≃ₗ[K] V) v ≠ v := fun h =>
      hv0 (CFSG.LieType.SeitzGeneration.eq_zero_of_fixed_of_not_mem hp hK hM hz1 hzM hv h)
    have hzC : ((z : orthDerived Q) : V ≃ₗ[K] V) ∈
        isometryCentralizer Q ((x : orthDerived Q) : V ≃ₗ[K] V) := by
      refine Subgroup.mem_inf.2 ⟨orthDerived_le_orthogonalGroup (z : orthDerived Q).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun y : Ã => ((y : orthDerived Q) : V ≃ₗ[K] V)) (hK.comm z x)
    have hzp : ((z : orthDerived Q) : V ≃ₗ[K] V) ^ p = 1 := by
      have := congrArg (fun y : Ã => ((y : orthDerived Q) : V ≃ₗ[K] V)) (hK.exp z)
      simpa using this
    obtain ⟨w, hw, hwp, hw1⟩ := orth_exists_supported_of_moves (hoi x hx1) hzC hzp hvW hzv
    exact orth3_fixedComponentImage_le_fixSub hQ hT hp hp2 hK4 hpl hinj hH' hg _ (hord x hx1)
      (hconjE x)
      hw hwp hw1 h3
  have hFL : ∀ x : Ã, x ≠ 1 → 3 ≤ finrank K (fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V)) →
      fixedComponentImage Q ((x : orthDerived Q) : V ≃ₗ[K] V) ≤ fixSub g := by
    intro x hx1 h3
    have hxp : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hK.exp x) hx1
    by_cases hne : lineSpace (Subgroup.zpowers x) = ⊥
    · obtain ⟨M₁, -, hM₁, -, -, hM₁ne, -⟩ := hK.two_active
      obtain ⟨y, hyM, hy1⟩ : ∃ y ∈ M₁, y ≠ 1 := by
        by_contra hall
        push Not at hall
        have : M₁ = ⊥ := eq_bot_iff.2 fun y hy => hall y hy
        rw [this, Subgroup.card_bot] at hM₁
        exact hp.one_lt.ne hM₁
      have hxy : fixedSpace ((x : orthDerived Q) : V ≃ₗ[K] V) ≤
          fixedSpace ((y : orthDerived Q) : V ≃ₗ[K] V) := by
        rw [hfix _ hxp x (Subgroup.mem_zpowers x) hx1, hne, sup_bot_eq,
          hfix M₁ hM₁ y hyM hy1]
        exact le_sup_left
      have h3y := h3.trans (Submodule.finrank_mono hxy)
      exact (orthFixedComponentImage_mono (hoi x hx1) (hoi y hy1) hxy).trans
        (hact M₁ hM₁ hM₁ne y hyM hy1 h3y)
    · exact hact _ hxp hne x (Subgroup.mem_zpowers x) hx1 h3
  have hKL : ∀ x : Ã, x ≠ 1 →
      ⁅Subgroup.centralizer ({(QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q)} :
          Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({(QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q)} :
          Set (ProjOrthDerived Q))⁆ ≤ fixSub g := fun x hx1 =>
    orth3_commutator_centralizer_le_of_blocks hQ hT hp hp2 hK4 hpl _ (hord x hx1) (fixSub g)
      (fun Rep hRep h hh hne hm => orth3_componentImage_le_fixSub hQ hT hp hp2 hK4 hpl hinj hH' hg _
        (hord x hx1) (hconjE x) Rep hRep h hh hne hm) (hFL x hx1)
  refine hrig g fun a ha ha1 n hn => ?_
  set x : Ã := e.symm ⟨a, ha⟩ with hxdef
  have hxa : (QuotientGroup.mk (x : orthDerived Q) : ProjOrthDerived Q) = a := by
    have h1 := he x
    rw [QuotientGroup.mk'_apply] at h1
    rw [← h1, hxdef, MulEquiv.apply_symm_apply]
  have hx1 : x ≠ 1 := fun h => ha1 (by
    rw [← hxa, h, OneMemClass.coe_one, QuotientGroup.mk_one])
  rw [← hxa] at hn
  exact hKL x hx1 hn

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
