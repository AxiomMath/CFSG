module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Plane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Fix

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

section Cyc3

variable (K : Type) [Field K]

@[expose] noncomputable def cyc3 (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

theorem natDegree_cyc3 : (cyc3 K).natDegree = 2 := by
  unfold cyc3
  compute_degree!

theorem monic_cyc3 : (cyc3 K).Monic := by
  unfold cyc3
  monicity!

variable {K} in
theorem irreducible_cyc3 (hK : Nat.card K = 2) : Irreducible (cyc3 K) := by
  have := charP_two_of_card hK
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_cyc3]
    decide
  · intro a ha
    rcases eq_zero_or_one_of_card hK a with rfl | rfl
    · simp [cyc3, IsRoot] at ha
    · have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h3 : (1 : K) ^ 2 + 1 + 1 = 1 := by
        rw [one_pow, add_assoc, ← two_mul, h2, zero_mul, add_zero]
      simp only [cyc3, IsRoot, eval_add, eval_pow, eval_X, eval_one] at ha
      rw [h3] at ha
      exact one_ne_zero ha

theorem cyc3_ne_X_sub_one : cyc3 K ≠ X - 1 := fun h => by
  have := congrArg natDegree h
  rw [natDegree_cyc3, ← C_1, natDegree_X_sub_C] at this
  omega

theorem reciprocal_cyc3 : reciprocalPolynomial (cyc3 K) = cyc3 K := by
  have h0 : (cyc3 K).coeff 0 = 1 := by simp [cyc3]
  rw [reciprocalPolynomial, h0, inv_one, map_one, one_mul]
  ext n
  rw [coeff_reverse, natDegree_cyc3]
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 2 < n by omega) with rfl | rfl | rfl | hn
  · rw [revAt_le (by norm_num)]
    simp [cyc3, coeff_X, coeff_one]
  · rw [revAt_le (by norm_num)]
  · rw [revAt_le (by norm_num)]
    simp [cyc3, coeff_X, coeff_one]
  · rw [revAt_eq_self_of_lt hn]

variable {K} in
theorem aeval_cyc3 {W : Type*} [AddCommGroup W] [Module K W] (T : Module.End K W) :
    aeval T (cyc3 K) = T ^ 2 + T + 1 := by
  simp [cyc3]

end Cyc3

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth2_exists_unitary_model (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h) :
    ∃ (d ℓ f : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar] primaryComponent x.toLinearMap h →ₗ[
        AdjoinRoot h] AdjoinRoot h),
      d ≠ 0 ∧ Nat.card K = ℓ ^ f ∧ B.IsSymm ∧ B.SeparatingLeft ∧
        (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
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
  exact ⟨d, ℓ, f, hU, B, hd0, hq, hBsymm, hBl, hrange⟩

theorem orth2_isQuasisimple_specialBlock_selfDual (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 4 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  obtain ⟨d, ℓ, f, hU, B, -, -, hBsymm, hBl, hrange⟩ :=
    orth2_exists_unitary_model hx hp2 hh hne1 hself
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm ?_
  refine isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl (by
    have : primaryMultiplicity x.toLinearMap h =
      finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := rfl
    omega) fun e => ?_
  have := congrArg Prod.fst e
  simp only at this
  have h2 : primaryMultiplicity x.toLinearMap h =
      finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := rfl
  omega

variable (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
  (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)

include hQ hT in
theorem orth2_special_facts (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 4 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) :
    specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q ∧
      componentImage Q (x : V ≃ₗ[K] V) h ≠ ⊥ ∧
      componentImage Q (x : V ≃ₗ[K] V) h ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
      IsComponent (((componentImage Q (x : V ≃ₗ[K] V) h).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))) := by
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨hinj, hNeq⟩ := orth3_conj_injective_and_centralizer hQ hT hp hp2 a ha x hxa hxp
  have hq := orth2_isQuasisimple_specialBlock_selfDual hx (hp.odd_of_ne_two hp2) hh hne1 hself hm
  have hFΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
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

include hQ hT in
theorem orth2_componentImage_le_fixSub (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn p H E)
    (x : orthDerived Q) (hxp : orderOf x = p)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 4 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) :
    componentImage Q (x : V ≃ₗ[K] V) h ≤ fixSub g := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha := orth3_orderOf_mk_projOrth hQ hT hp hp2 hxp
  obtain ⟨hΩ, -, hle, hcomp⟩ :=
    orth2_special_facts hQ hT hp hp2 hpl H hH _ ha x rfl hxp hh hne1 hself hm
  have hdvd := orth3_dvd_card_orthSpecialBlock hx hp hp2 hh hne1 (by omega)
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

omit [Finite K] in
theorem orth2_exists_smul_of_commute_specialBlock [Finite K] (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) {G : V ≃ₗ[K] V}
    (hGx : G ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hcomm : ∀ f ∈ specialBlock Q x h, G * f = f * G) :
    ∃ c : AdjoinRoot h, ∀ w : primaryComponent x.toLinearMap h,
      (G (w : V) : V) = ((c • w : primaryComponent x.toLinearMap h) : V) := by
  obtain ⟨d, ℓ, f, hU, B, hd0, hq, hBsymm, hBl, hrange⟩ :=
    orth2_exists_unitary_model hx hp2 hh hne1 hself
  have hq2 : 2 ≤ ℓ ^ (f * d) := by
    rw [pow_mul, ← hq]
    have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
    exact h1.trans (Nat.le_self_pow hd0 _)
  set γ : BlockGL x h := centralizerGL x h ⟨G, hGx⟩ with hγ
  obtain ⟨c, hc⟩ := KCUnitary.exists_smul_of_commute_special_unitary hU hBsymm hBl hm hq2
    (γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (fun δ hδ => by
      rw [← hrange] at hδ
      obtain ⟨⟨g', hg'⟩, rfl⟩ := hδ
      refine LinearMap.ext fun w => Subtype.ext ?_
      change G (g' (w : V)) = g' (G (w : V))
      have := congrArg (fun e : V ≃ₗ[K] V => e (w : V)) (hcomm g' hg')
      simpa using this)
  refine ⟨c, fun w => ?_⟩
  have h1 : (G (w : V) : V) = ((γ : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) w : V) := (coe_centralizerGL x h ⟨G, hGx⟩ w).symm
  rw [h1, hc w]


variable (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
  (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)

include hQ hT in
theorem orth2_fixes_unitary (hK : Nat.card K = 2)
    (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn 3 H E)
    (x : orthDerived Q) (hxp : orderOf x = 3)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    (h8 : 8 ≤ finrank K (primaryComponent (x : V ≃ₗ[K] V).toLinearMap (cyc3 K)))
    {G : V ≃ₗ[K] V} (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGx : G * (x : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) * G)
    (hmk : Function.Injective (QuotientGroup.mk : orthDerived Q → ProjOrthDerived Q))
    (hGg : ∀ y : orthDerived Q, g (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q))
    {k : ℕ} (hk : Nat.Coprime 3 k) (hGk : G ^ k = 1) :
    ∀ v ∈ primaryComponent (x : V ≃ₗ[K] V).toLinearMap (cyc3 K), G v = v := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar_eq_two_of_card hK]; norm_num
  have : Fact (Irreducible (cyc3 K)) := ⟨irreducible_cyc3 hK⟩
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  have hne : primaryComponent xe.toLinearMap (cyc3 K) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h8
    omega
  have hh : cyc3 K ∈ primaryFactors xe.toLinearMap :=
    mem_primaryFactors_of_primaryComponent_ne_bot (irreducible_cyc3 hK) (monic_cyc3 K) hne
  have hm : 4 ≤ primaryMultiplicity xe.toLinearMap (cyc3 K) := by
    have h1 := finrank_primaryComponent (x := xe.toLinearMap) (a := cyc3 K)
    rw [natDegree_cyc3] at h1
    have : primaryMultiplicity xe.toLinearMap (cyc3 K) =
      finrank (AdjoinRoot (cyc3 K)) (primaryComponent xe.toLinearMap (cyc3 K)) := rfl
    omega
  have hF := orth2_componentImage_le_fixSub hQ hT hp hp2 hpl hinj hH hg x hxp he hh
    (cyc3_ne_X_sub_one K) (reciprocal_cyc3 K).symm hm
  have hcomm : ∀ f ∈ specialBlock Q xe (cyc3 K), G * f = f * G := by
    intro f hf
    have hq := orth2_isQuasisimple_specialBlock_selfDual hx (Nat.odd_iff.2 rfl) hh
      (cyc3_ne_X_sub_one K) (reciprocal_cyc3 K).symm hm
    have hFΩ : specialBlock Q xe (cyc3 K) ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer _).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    have hmem : (QuotientGroup.mk (⟨f, hFΩ hf⟩ : orthDerived Q) : ProjOrthDerived Q) ∈
        componentImage Q xe (cyc3 K) :=
      ⟨⟨f, hFΩ hf⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
    have h1 := mem_fixSub.1 (hF hmem)
    rw [hGg] at h1
    have h2 : G * f * G⁻¹ = f := congrArg Subtype.val (hmk h1)
    calc G * f = G * f * G⁻¹ * G := by group
      _ = f * G := by rw [h2]
  have hGc : G ∈ Subgroup.centralizer ({xe} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hGx
  obtain ⟨c, hc⟩ := orth2_exists_smul_of_commute_specialBlock hx (Nat.odd_iff.2 rfl) hh
    (cyc3_ne_X_sub_one K) (reciprocal_cyc3 K).symm (by omega) hGc hcomm
  have hGpow : ∀ (n : ℕ) (w : primaryComponent xe.toLinearMap (cyc3 K)),
      ((G ^ n) (w : V) : V) = ((c ^ n • w : primaryComponent xe.toLinearMap (cyc3 K)) : V) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', LinearEquiv.mul_apply, ih w, pow_succ', mul_smul, hc]
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw₀' : (⟨w₀, hw₀⟩ : primaryComponent xe.toLinearMap (cyc3 K)) ≠ 0 := fun h0 =>
    hw₀0 (congrArg Subtype.val h0)
  have hck : c ^ k = 1 := by
    have h1 : ((⟨w₀, hw₀⟩ : primaryComponent xe.toLinearMap (cyc3 K)) : V) =
        ((c ^ k • ⟨w₀, hw₀⟩ : primaryComponent xe.toLinearMap (cyc3 K)) : V) := by
      rw [← hGpow k ⟨w₀, hw₀⟩, hGk]
      rfl
    have h2 : (c ^ k - 1) • (⟨w₀, hw₀⟩ : primaryComponent xe.toLinearMap (cyc3 K)) = 0 := by
      apply Subtype.ext
      rw [sub_smul, one_smul, Submodule.coe_sub, ← h1]
      simp
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hw₀'
  have hk0 : k ≠ 0 := by
    rintro rfl
    norm_num at hk
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hck
    exact zero_ne_one hck
  have hc3 : c ^ 3 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have : Module.Finite K (AdjoinRoot (cyc3 K)) :=
      (AdjoinRoot.powerBasis (irreducible_cyc3 hK).ne_zero).finite
    have : Finite (AdjoinRoot (cyc3 K)) := Module.finite_of_finite K
    have : Fintype (AdjoinRoot (cyc3 K)) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot (cyc3 K)) = 4 := by
      rw [Module.card_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis
        (irreducible_cyc3 hK).ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_cyc3,
        ← Nat.card_eq_fintype_card, hK]
      norm_num
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hcard] at this
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc3, hck⟩
    rwa [Nat.Coprime.gcd_eq_one hk, pow_one] at this
  intro v hv
  have := hc ⟨v, hv⟩
  rw [hc1, one_smul] at this
  exact this

end CFSG.HardMathSupport.Timmesfeld.CrossChar
