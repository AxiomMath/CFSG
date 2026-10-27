module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelSelfDual
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial
open scoped Classical

noncomputable section

theorem polarBilin_nondegenerate_of_regular {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    (QuadraticMap.polarBilin Q).Nondegenerate :=
  ⟨fun v hv => hx.regular v fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using hv w,
   fun v hv => hx.regular v fun w => by
    rw [QuadraticMap.polar_comm]; simpa [QuadraticMap.polarBilin_apply_apply] using hv w⟩

theorem nontrivial_of_isQuasisimple_specialBlock {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) : Nontrivial V := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    haveI : Subsingleton ↥(specialBlock Q x h) :=
      ⟨fun u v => Subtype.ext (LinearEquiv.ext fun w => Subsingleton.elim _ _)⟩
    exact hab (Subsingleton.elim (a * b) (b * a))
  · exact hV

theorem not_isQuasisimple_sesqSpecialUnitaryGroup_three_two {f₀ : ℕ} {E : Type} [Field E]
    {M : Type} [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    (hU : UnitaryFieldData 2 f₀ E) (hf : 2 ^ f₀ = 2)
    {B : M →ₛₗ[hU.bar] M →ₗ[E] E} (hBs : B.IsSymm) (hBl : B.SeparatingLeft)
    (hdim : Module.finrank E M = 3) :
    ¬ CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) := by
  intro hq
  haveI : Finite E := hU.finite
  haveI : Finite M := Module.finite_of_finite E
  haveI : Finite (M ≃ₗ[E] M) :=
    Finite.of_injective (fun e : M ≃ₗ[E] M => (e : M → M))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hcard : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
    have h : (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) = 216 := by
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hU hBs hBl hdim (by omega)).2.1
      rw [h1, hf]
      norm_num [Finset.prod_Icc_succ_top]
    exact_mod_cast h
  haveI : Fintype ↥(sesqSpecialUnitaryGroup B) := Fintype.ofFinite _
  have hcardF : Fintype.card ↥(sesqSpecialUnitaryGroup B) = 2 ^ 3 * 3 ^ 3 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  have hsolv : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) hcardF
  haveI : Nontrivial ↥(sesqSpecialUnitaryGroup B) := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hab (Subsingleton.elim (a * b) (b * a))
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
    (G := ↥(sesqSpecialUnitaryGroup B))).ne hq.1.commutator_eq_top

theorem onLie_isUnitaryCharTwoIdx_of_isUnA {k q m : ℕ} (hk : 3 ≤ k) (hq : q = 2 ^ m)
    {i : TauCeti.CFSGIndex} (h : CFSG.LocalAnalysis.GLTheoremA.isUnA k q i) :
    onLie isUnitaryCharTwoIdx i := by
  cases i with
  | lie idx =>
    simp only [CFSG.LocalAnalysis.GLTheoremA.isUnA, onLie] at h
    rcases h with h | ⟨hk2, -⟩
    · obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r qq =>
        obtain ⟨-, hcard⟩ := h
        refine ⟨r, qq, rfl, ?_⟩
        have h1 : qq.p ∣ qq.card := by
          rw [TauCeti.PrimePower.card_def]
          exact dvd_pow_self _ qq.exponent_pos.ne'
        rw [hcard, hq] at h1
        exact (Nat.prime_dvd_prime_iff_eq qq.prime_p Nat.prime_two).1
          (qq.prime_p.dvd_of_dvd_pow h1)
      | _ => simp [CFSG.LocalAnalysis.GLTheoremA.isLnEps] at h
    · omega
  | cyclic n hn =>
    simp only [CFSG.LocalAnalysis.GLTheoremA.isUnA, onLie, false_or] at h
    exact absurd h.1 (by omega)
  | alternating n hn =>
    simp only [CFSG.LocalAnalysis.GLTheoremA.isUnA, onLie, false_or] at h
    exact absurd h.1 (by omega)
  | sporadic s =>
    simp only [CFSG.LocalAnalysis.GLTheoremA.isUnA, onLie, false_or] at h
    exact absurd h.1 (by omega)

theorem catalogIs_componentImage_selfDual {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) {h : K[X]}
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (ha : 3 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) :
    catalogIs (PSimple p (componentImage Q (x : V ≃ₗ[K] V) h))
      (onLie isUnitaryCharTwoIdx) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Nontrivial V := nontrivial_of_isQuasisimple_specialBlock hq
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate := polarBilin_nondegenerate_of_regular hx
  have hpi : Function.Injective (piOrth Q) := CFSG.RankThree.PartOne.piOrth_injective hQ
  obtain ⟨f₀, hU, B, hBs, hBl, hpq, -, -, -, hrange⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_selfDual_setting hx hp hp2 hh hne1 hself
  let eSU : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)
  have hqSU : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eSU hq
  have hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
  have hmapJ : ((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)).map (piOrth Q) =
      componentImage Q (x : V ≃ₗ[K] V) h := rfl
  let eJ : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ≃*
      ↥(componentImage Q (x : V ≃ₗ[K] V) h) :=
    (Subgroup.subgroupOfEquivOfLe hspecΩ).symm.trans
      ((Subgroup.equivMapOfInjective _ (piOrth Q) hpi).trans (MulEquiv.subgroupCongr hmapJ))
  let e : ↥(sesqSpecialUnitaryGroup B) ≃* ↥(componentImage Q (x : V ≃ₗ[K] V) h) :=
    eSU.symm.trans eJ
  set a := primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h with ha'
  have hdim : Module.finrank (AdjoinRoot h)
      (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) = a := ha'.symm
  have hk : 4 ≤ a ∨ ((a = 2 ∨ a = 3) ∧ 4 ≤ 2 ^ f₀) := by
    by_cases h4 : 4 ≤ a
    · exact Or.inl h4
    · right
      have ha3 : a = 3 := by omega
      refine ⟨Or.inr ha3, ?_⟩
      by_contra hlt
      have hf : 2 ^ f₀ = 2 := by
        have h1 : f₀ < 2 := by
          refine (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp ?_
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
          omega
        have h2 : 1 ≤ f₀ := hU.one_le
        obtain rfl : f₀ = 1 := by omega
        norm_num
      have hdim3 : Module.finrank (AdjoinRoot h)
          (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) = 3 := by
        rw [hdim, ha3]
      exact not_isQuasisimple_sesqSpecialUnitaryGroup_three_two hU hf hBs hBl hdim3 hqSU
  have hcat : catalogIs (PSimple p (sesqSpecialUnitaryGroup B)) (isUnA a (2 ^ f₀)) :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen
      hU hBs hBl hdim hk hp hp2 hpq
  have hcat' : catalogIs (PSimple p (sesqSpecialUnitaryGroup B))
      (onLie isUnitaryCharTwoIdx) :=
    CFSG.LocalAnalysis.GLTheoremA.S10.catalogIs_imp
      (fun i hi => onLie_isUnitaryCharTwoIdx_of_isUnA (q := 2 ^ f₀) (m := f₀) ha rfl hi) hcat
  exact CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _
    (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p e) hcat'

theorem orthSelfDualCatalogue : OrthSelfDualCatalogue := by
  intro K V _ _ _ _ _ _ Q p hp hp2 x y hx hyc hyp h hh hne1 hself hq J hJeq hN ha
  rw [hJeq]
  exact catalogIs_componentImage_selfDual hp hp2 hx hh hne1 hself hq ha

end

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
