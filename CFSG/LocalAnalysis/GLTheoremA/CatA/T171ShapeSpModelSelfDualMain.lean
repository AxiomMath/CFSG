module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelPairedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelSelfDual
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelTransport
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.RankTwoTwistedA
import all CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgSymplectic
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightSpGood
import CFSG.HardMathSupport.Curtis.UnitaryLevi.TailTrivialThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCUnitary
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)
open scoped commutatorElement MatrixGroups

theorem nonempty_sesqSpecialUnitaryGroup_mulEquiv_unitarySU {ℓ f : ℕ} {E : Type} [Field E]
    {W : Type*} [AddCommGroup W] [Module E W]
    {hE : UnitaryFieldData ℓ f E} {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (e : Module.Basis (Fin (Module.finrank E W)) E W)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) :
    Nonempty (↥(sesqSpecialUnitaryGroup B) ≃* unitarySU ℓ f E (Module.finrank E W)) := by
  obtain ⟨eSU⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e
    (G := 1) (fun i j => by rw [he i j, Matrix.one_apply])
  exact ⟨eSU.trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)⟩

private theorem isSolvable_sesqUnitaryGroup_of_two_pow_eq_two {E W : Type} [Field E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] {f : ℕ}
    {hE : UnitaryFieldData 2 f E} {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (hBs : B.IsSymm) (hBl : B.SeparatingLeft) (hdim : Module.finrank E W ≤ 3)
    (hf : 2 ^ f = 2) : Group.IsSolvable ↥(sesqUnitaryGroup B) := by
  obtain rfl : f = 1 := Nat.pow_right_injective le_rfl (hf.trans (pow_one 2).symm)
  exact CFSG.HardMathSupport.Curtis.UnitaryLevi.isSolvable_sesqUnitaryGroup_of_finrank_le_three
    hE hBs hBl hdim

private theorem two_pow_eq_two_or_four_le {M : ℕ} (hM : 1 ≤ M) :
    2 ^ M = 2 ∨ 4 ≤ 2 ^ M := by
  rcases eq_or_lt_of_le hM with rfl | hgt
  · exact Or.inl (by norm_num)
  · exact Or.inr (calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hgt)

private structure SelfDualPrelim (m n p : ℕ) (K : Type) [Field K] [Finite K]
    (x : StatedSp m K) where
  hn1 : 1 ≤ n
  hchar : CharP K 2
  h2 : (2 : K) = 0
  hm1 : 1 ≤ m
  hproj : Function.Injective (proj m K)
  hxne : proj m K x ≠ 1
  ha : orderOf (proj m K x) = p
  hxp' : orderOf x = p
  hblocks : SpPrimaryBlocks 2 n p x (proj m K x)

private theorem selfDual_prelim {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : StatedSp m K) (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    SelfDualPrelim m n p K x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      have hc := Finite.one_lt_card (α := K)
      omega
    · exact h0
  haveI hchar : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [Fintype.card_eq_nat_card, hK])
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero m := ⟨by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hproj : Function.Injective (proj m K) :=
    CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154s_proj_injective (r := m) (K := K) h2
  have hxne : proj m K x ≠ 1 := fun hx' =>
    hx1 ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := m) (K := K)).1 (by rw [hx', map_one]))
  have ha : orderOf (proj m K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) hxne
  have hxp' : orderOf x = p := orderOf_eq_prime hxp hx1
  have hblocks : SpPrimaryBlocks 2 n p x (proj m K x) :=
    (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := n) (p := p) (r := m)
      (K := K) Nat.prime_two hn1 hK hp hp2 hp2 hm1 (proj m K x) ha).2 x rfl hxp'
  exact { hn1, hchar, h2, hm1, hproj, hxne, ha, hxp', hblocks }

private structure SelfDualHalf (m n p : ℕ) (K : Type) [Field K] [Finite K]
    (x : StatedSp m K) (h : K[X]) [Fact (Irreducible (h : K[X]))] where
  d : ℕ
  hdeg : (h : K[X]).natDegree = 2 * d
  hpdvd : p ∣ (2 ^ n) ^ d + 1
  σ : AdjoinRoot (h : K[X]) ≃ₐ[K] AdjoinRoot (h : K[X])
  hσpow : ∀ z, σ z = z ^ ((2 ^ n) ^ d)
  hσne : σ ≠ 1
  hσσ : ∀ z, σ (σ z) = z
  hσroot : σ (AdjoinRoot.root (h : K[X])) = (AdjoinRoot.root (h : K[X]))⁻¹
  hσadj : ∀ (e : AdjoinRoot (h : K[X])) (v w : primaryComponent (spEnd x) (h : K[X])),
    spForm m K ((e • v : primaryComponent (spEnd x) (h : K[X])) : Fin m ⊕ Fin m → K)
      (w : Fin m ⊕ Fin m → K) =
    spForm m K (v : Fin m ⊕ Fin m → K)
      ((σ e • w : primaryComponent (spEnd x) (h : K[X])) : Fin m ⊕ Fin m → K)
  hE : UnitaryFieldData 2 (n * d) (AdjoinRoot (h : K[X]))
  hbar : ∀ z, hE.bar z = σ z
  Hf : primaryComponent (spEnd x) (h : K[X]) →ₛₗ[hE.bar]
      primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])] AdjoinRoot (h : K[X])
  hHf : Hf.IsSymm
  hHfl : Hf.SeparatingLeft
  η : AdjoinRoot (h : K[X])
  hη0 : η ≠ 0
  hηbar : hE.bar η = -η
  htrace : ∀ (v w : primaryComponent (spEnd x) (h : K[X])) (c : AdjoinRoot (h : K[X])),
    Algebra.trace K (AdjoinRoot (h : K[X])) (c * Hf v w) =
      spForm m K (v : Fin m ⊕ Fin m → K)
        (((c * η) • w : primaryComponent (spEnd x) (h : K[X])) : Fin m ⊕ Fin m → K)
  eb : Module.Basis (Fin (primaryMultiplicity (spEnd x) (h : K[X])))
      (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))
  hbasis_orth : ∀ i j, Hf (eb i) (eb j) = if i = j then 1 else 0
  φ : spSupported x {(h : K[X])} ≃* sesqUnitaryGroup Hf
  hφ : ∀ (g : spSupported x {(h : K[X])}) (v : Fin m ⊕ Fin m → K)
      (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      blockApply (φ g : blockGL (spEnd x) (h : K[X])) v hv = spEnd (g : StatedSp m K) v
  hd1 : 1 ≤ d
  hnpos : 1 ≤ n * d

private noncomputable def selfDual_half {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (hn1 : 1 ≤ n) (hh : h ∈ primaryFactors (spEnd x))
    (hb : SpSelfDualBlock 2 n p x ⟨h, hh⟩) :
    SelfDualHalf m n p K x h := by
  classical
  refine Classical.choice ?_
  obtain ⟨d, hdeg, hpdvd, σ, hσpow, hσne, hσσ, hσroot, hσadj, hE, hbar, Hf, hHf, hHfl,
    ⟨η, hη0, hηbar, htrace⟩, ⟨eb, hbasis_orth⟩, φ, hφ⟩ := hb.exists_half
  have hd1 : 1 ≤ d := by
    have hpos : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hh)
    have hdeg' : (h : K[X]).natDegree = 2 * d := hdeg
    omega
  have hnpos : 1 ≤ n * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact ⟨⟨d, hdeg, hpdvd, σ, hσpow, hσne, hσσ, hσroot, hσadj, hE, hbar, Hf, hHf, hHfl,
    η, hη0, hηbar, htrace, eb, hbasis_orth, φ, hφ, hd1, hnpos⟩⟩

private noncomputable def selfDualTheta {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) :
    ↥(sesqSpecialUnitaryGroup H.Hf) →* ↥(sesqUnitaryGroup H.Hf) :=
  Subgroup.inclusion (sesqSpecialUnitaryGroup_le H.Hf)

private noncomputable def selfDualPsi {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) :
    ↥(sesqSpecialUnitaryGroup H.Hf) →* StatedSp m K :=
  (spSupported x ({h} : Set K[X])).subtype.comp
    (H.φ.symm.toMonoidHom.comp (selfDualTheta H))

private theorem selfDual_multiplicity_two_le {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) (J : Subgroup (StatedProj (StatedSp m K)))
    (hproj : Function.Injective (proj m K))
    (hJeq : J = (⁅spSupported x ({h} : Set K[X]),
      spSupported x ({h} : Set K[X])⁆).map (proj m K))
    (hJnt : Nontrivial ↥J) :
    2 ≤ primaryMultiplicity (spEnd x) h := by
  classical
  let E := AdjoinRoot (h : K[X])
  let W := primaryComponent (spEnd x) (h : K[X])
  letI : Finite E := H.hE.finite
  letI : CharP E 2 := H.hE.charP
  let A : Subgroup (StatedSp m K) := spSupported x ({h} : Set K[X])
  let D : Subgroup (StatedSp m K) := ⁅A, A⁆
  have ha_dim : Module.finrank E W = primaryMultiplicity (spEnd x) h := rfl
  by_contra hlt
  have hle : Module.finrank E W ≤ 1 := by omega
  have hcommA : ∀ a1 a2 : ↥A, Commute a1 a2 := by
    intro a1 a2
    apply H.φ.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    apply Units.ext
    exact (End_commute_of_finrank_le_one hle
      (((H.φ a1 : ↥(sesqUnitaryGroup H.Hf)) : LinearMap.GeneralLinearGroup E W) :
        Module.End E W)
      (((H.φ a2 : ↥(sesqUnitaryGroup H.Hf)) : LinearMap.GeneralLinearGroup E W) :
        Module.End E W)).eq
  have hDbot : D = ⊥ := by
    rw [Subgroup.commutator_self_eq_bot_iff]
    exact ⟨⟨fun x y => (hcommA x y).eq⟩⟩
  have hJbot : J = ⊥ := by
    rw [hJeq]
    change D.map (proj m K) = ⊥
    rw [hDbot, Subgroup.map_bot]
  haveI : Subsingleton ↥J := by rw [hJbot]; infer_instance
  obtain ⟨j1, j2, hj⟩ := hJnt.exists_pair_ne
  exact hj (Subsingleton.elim j1 j2)

private theorem selfDual_small_block_false {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) (J : Subgroup (StatedProj (StatedSp m K)))
    (hproj : Function.Injective (proj m K))
    (hJeq : J = (⁅spSupported x ({h} : Set K[X]),
      spSupported x ({h} : Set K[X])⁆).map (proj m K))
    (hJnsolv : ¬ Group.IsSolvable ↥J)
    (hsmall : (primaryMultiplicity (spEnd x) h = 2 ∧ 2 ^ (n * H.d) = 2) ∨
      (primaryMultiplicity (spEnd x) h = 3 ∧ 2 ^ (n * H.d) = 2)) : False := by
  classical
  let E := AdjoinRoot (h : K[X])
  let W := primaryComponent (spEnd x) (h : K[X])
  letI : Finite E := H.hE.finite
  letI : CharP E 2 := H.hE.charP
  let A : Subgroup (StatedSp m K) := spSupported x ({h} : Set K[X])
  let D : Subgroup (StatedSp m K) := ⁅A, A⁆
  have hDF : D ≤ A := Subgroup.commutator_le_self A
  let eJ' : ↥D ≃* ↥J :=
    (Subgroup.equivMapOfInjective D (proj m K) hproj).trans
      (MulEquiv.subgroupCongr hJeq.symm)
  have ha_dim : Module.finrank E W = primaryMultiplicity (spEnd x) h := rfl
  have hUsolv : Group.IsSolvable ↥(sesqUnitaryGroup H.Hf) := by
    rcases hsmall with ⟨ha2', hq2⟩ | ⟨ha3', hq2⟩
    · exact isSolvable_sesqUnitaryGroup_of_two_pow_eq_two H.hHf H.hHfl
        (by rw [ha_dim, ha2']; omega) hq2
    · exact isSolvable_sesqUnitaryGroup_of_two_pow_eq_two H.hHf H.hHfl
        (by rw [ha_dim, ha3']) hq2
  have hAsolv : Group.IsSolvable ↥A :=
    Group.isSolvable_of_surjective (f := H.φ.symm.toMonoidHom)
      (show Function.Surjective H.φ.symm.toMonoidHom from H.φ.symm.surjective)
  have hDsolv : Group.IsSolvable ↥D :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hDF) (Subgroup.inclusion_injective hDF)
  have hJsolv : Group.IsSolvable ↥J :=
    Group.isSolvable_of_surjective (f := eJ'.toMonoidHom)
      (show Function.Surjective eJ'.toMonoidHom from eJ'.surjective)
  exact hJnsolv hJsolv

private theorem selfDual_finrank_conditions {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h)
    (hsmall : ¬ ((primaryMultiplicity (spEnd x) h = 2 ∧ 2 ^ (n * H.d) = 2) ∨
      (primaryMultiplicity (spEnd x) h = 3 ∧ 2 ^ (n * H.d) = 2))) :
    (Module.finrank (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X])) = 2 →
        4 ≤ 2 ^ (n * H.d)) ∧
      (Module.finrank (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X])) = 3 →
        3 ≤ 2 ^ (n * H.d)) := by
  have ha_dim : Module.finrank (AdjoinRoot (h : K[X]))
      (primaryComponent (spEnd x) (h : K[X])) = primaryMultiplicity (spEnd x) h := rfl
  constructor
  · intro hdim2
    have haeq : primaryMultiplicity (spEnd x) h = 2 := by rw [← ha_dim]; exact hdim2
    rcases two_pow_eq_two_or_four_le H.hnpos with hq | hq
    · exact absurd (Or.inl ⟨haeq, hq⟩) hsmall
    · exact hq
  · intro hdim3
    have haeq : primaryMultiplicity (spEnd x) h = 3 := by rw [← ha_dim]; exact hdim3
    have hqne : 2 ^ (n * H.d) ≠ 2 := fun hq => hsmall (Or.inr ⟨haeq, hq⟩)
    rcases two_pow_eq_two_or_four_le H.hnpos with hq | hq
    · exact absurd hq hqne
    · omega

private theorem selfDual_perfectData {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) (ha2 : 2 ≤ primaryMultiplicity (spEnd x) h)
    (hqcond : (Module.finrank (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])) = 2 → 4 ≤ 2 ^ (n * H.d)) ∧
      (Module.finrank (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])) = 3 → 3 ≤ 2 ^ (n * H.d))) :
    commutator ↥(sesqSpecialUnitaryGroup H.Hf) = ⊤ ∧
      Function.Injective (selfDualPsi H) ∧
      (selfDualPsi H).range =
        ⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆ := by
  classical
  let E := AdjoinRoot (h : K[X])
  let W := primaryComponent (spEnd x) (h : K[X])
  letI : Finite E := H.hE.finite
  letI : CharP E 2 := H.hE.charP
  let U := sesqUnitaryGroup H.Hf
  let SU := sesqSpecialUnitaryGroup H.Hf
  let θ : ↥SU →* ↥U := selfDualTheta H
  have hθrange : θ.range = SU.subgroupOf U := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  have hψ_inj : Function.Injective (selfDualPsi H) := by
    rw [show selfDualPsi H = (spSupported x ({h} : Set K[X])).subtype.comp
      (H.φ.symm.toMonoidHom.comp θ) from rfl]
    exact Subtype.val_injective.comp
      (H.φ.symm.injective.comp (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le H.Hf)))
  have ha_dim : Module.finrank E W = primaryMultiplicity (spEnd x) h := rfl
  have hSUq : CFSG.IsQuasisimple ↥SU :=
    isQuasisimple_sesqSpecialUnitaryGroup_of_two_le H.hE H.hHf H.hHfl
      (by rw [ha_dim]; omega) hqcond
  have hSUperf : commutator ↥SU = ⊤ := Group.isPerfect_def.mp hSUq.1
  have hkerSU : (unitaryDet H.Hf).ker = SU.subgroupOf U :=
    (unitary_full_group_order H.hE H.hHf H.hHfl (n := Module.finrank E W) rfl
      (by rw [ha_dim]; omega)).2.2.2.2.1
  have hθ : θ.range = commutator ↥U := by
    refine CFSG.LocalAnalysis.GLTheoremA.H1431c.lieSEightSp_range_eq_commutator_of_perfect θ
      hSUperf (unitaryDet H.Hf) ?_
    rw [hkerSU, hθrange]
  have hψ_range : (selfDualPsi H).range =
      ⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆ := by
    rw [show selfDualPsi H = (spSupported x ({h} : Set K[X])).subtype.comp
      (H.φ.symm.toMonoidHom.comp θ) from rfl]
    exact CFSG.LocalAnalysis.GLTheoremA.H1431c.lieSEightSp_range_comp_eq_commutator H.φ θ hθ
  exact ⟨hSUperf, hψ_inj, hψ_range⟩

private structure SelfDualUnitaryData {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x y : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) (J : Subgroup (StatedProj (StatedSp m K)))
    (hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))) where
  y_h : StatedSp m K
  hy_h : y_h ∈ spSupported x ({h} : Set K[X])
  hTy : MulAut.conj (proj m K y) ∈ CFSG.GroupActions.subgroupStabAut J
  hSUperf : commutator ↥(sesqSpecialUnitaryGroup H.Hf) = ⊤
  eD : ↥(⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆) ≃*
      unitarySU 2 (n * H.d) (AdjoinRoot (h : K[X])) (primaryMultiplicity (spEnd x) h)
  eJ : ↥(⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆) ≃* ↥J
  π' : ↥(sesqSpecialUnitaryGroup H.Hf) →* ↥J
  hπ'_surj : Function.Surjective π'
  hπ'_ker : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup H.Hf)
  hconj : ∀ s : ↥(sesqSpecialUnitaryGroup H.Hf),
    CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj (proj m K y), hTy⟩ (π' s) =
      π' (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj (B := H.Hf)
        (H.φ ⟨y_h, hy_h⟩) s)

private noncomputable def selfDual_unitaryData {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x y : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) (J : Subgroup (StatedProj (StatedSp m K)))
    (hh : h ∈ primaryFactors (spEnd x))
    (hproj : Function.Injective (proj m K))
    (hJeq : J = (⁅spSupported x ({h} : Set K[X]),
      spSupported x ({h} : Set K[X])⁆).map (proj m K))
    (hblocks : SpPrimaryBlocks 2 n p x (proj m K x))
    (hxy : x * y = y * x) (hsd : reciprocalPolynomial (h : K[X]) = h)
    (hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K))))
    (hSUperf : commutator ↥(sesqSpecialUnitaryGroup H.Hf) = ⊤)
    (hψ_inj : Function.Injective (selfDualPsi H))
    (hψ_range : (selfDualPsi H).range =
      ⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆) :
    SelfDualUnitaryData H J hN := by
  classical
  let E := AdjoinRoot (h : K[X])
  let W := primaryComponent (spEnd x) (h : K[X])
  letI : Finite E := H.hE.finite
  letI : CharP E 2 := H.hE.charP
  let A : Subgroup (StatedSp m K) := spSupported x ({h} : Set K[X])
  let Dsub : Subgroup (StatedSp m K) := ⁅A, A⁆
  have hDF : Dsub ≤ A := Subgroup.commutator_le_self A
  let U := sesqUnitaryGroup H.Hf
  let SU := sesqSpecialUnitaryGroup H.Hf
  let θ : ↥SU →* ↥U := selfDualTheta H
  let ψ : ↥SU →* StatedSp m K := selfDualPsi H
  have hO : ({h} : Set K[X]) ∈ reciprocalOrbits (spEnd x) := by
    rw [reciprocalOrbits]
    refine ⟨h, hh, ?_⟩
    change ({h, reciprocalPolynomial h} : Set K[X]) = {h}
    rw [hsd, Set.pair_eq_singleton]
  let hex :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_mem_spSupported_commute_of_commute
      hblocks hxy.symm ⟨{h}, hO⟩
  let y_h := Classical.choose hex
  let hy_h := (Classical.choose_spec hex).1
  let hz := (Classical.choose_spec hex).2
  have hy_h' : y_h ∈ A := hy_h
  have hTy : MulAut.conj (proj m K y) ∈ CFSG.GroupActions.subgroupStabAut J := by
    change Subgroup.map (MulAut.conj (proj m K y)).toMonoidHom J = J
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
  let ψ' : ↥SU →* ↥Dsub :=
    ψ.codRestrict Dsub (fun s => by
      show ψ s ∈ ⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆
      rw [← hψ_range]
      exact ⟨s, rfl⟩)
  have hψ'_inj : Function.Injective ψ' := by
    intro a b hab
    exact hψ_inj (congrArg (fun z : ↥Dsub => (z : StatedSp m K)) hab)
  have hψ'_surj : Function.Surjective ψ' := by
    intro dd
    have hd : (dd : StatedSp m K) ∈ ψ.range := by rw [hψ_range]; exact dd.2
    obtain ⟨s, hs⟩ := hd
    exact ⟨s, Subtype.ext hs⟩
  let eDcomm : ↥SU ≃* ↥Dsub := MulEquiv.ofBijective ψ' ⟨hψ'_inj, hψ'_surj⟩
  let eSU := Classical.choice
    (nonempty_sesqSpecialUnitaryGroup_mulEquiv_unitarySU (hE := H.hE) H.eb H.hbasis_orth)
  let eD : ↥Dsub ≃* unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h) :=
    eDcomm.symm.trans eSU
  let eJ : ↥Dsub ≃* ↥J :=
    (Subgroup.equivMapOfInjective Dsub (proj m K) hproj).trans
      (MulEquiv.subgroupCongr hJeq.symm)
  let π' : ↥SU →* ↥J := eJ.toMonoidHom.comp eDcomm.toMonoidHom
  have hπ'_surj : Function.Surjective π' := eJ.surjective.comp eDcomm.surjective
  have hπ'_inj : Function.Injective π' := eJ.injective.comp eDcomm.injective
  have hπ'_ker : π'.ker ≤ Subgroup.center ↥SU := by
    rw [(MonoidHom.ker_eq_bot_iff π').mpr hπ'_inj]
    exact bot_le
  have hπ'_apply : ∀ s,
      ((π' s : ↥J) : StatedProj (StatedSp m K)) = proj m K (ψ s) := by
    intro s
    rfl
  refine ⟨y_h, hy_h, hTy, hSUperf, eD, eJ, π', hπ'_surj, hπ'_ker, ?_⟩
  exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.unitaryComponent_conjLaw (r := m) (K := K)
    H.φ hy_h' hz (ψ := ψ) (fun s => rfl) (fun s => (H.φ.symm _).2) hTy hπ'_apply rfl

private theorem selfDual_inner_of_dim_two {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x y : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) {J : Subgroup (StatedProj (StatedSp m K))}
    {hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))}
    (D : SelfDualUnitaryData H J hN) (hp : p.Prime) (hp2 : p ≠ 2)
    (hqJ_open : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hdim2 : primaryMultiplicity (spEnd x) h = 2)
    (ha_dim : Module.finrank (AdjoinRoot (h : K[X]))
      (primaryComponent (spEnd x) (h : K[X])) = primaryMultiplicity (spEnd x) h)
    (hyp : y ^ p = 1) :
    MI.indAut p J (proj m K y) hN ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite (AdjoinRoot (h : K[X])) := H.hE.finite
  letI : CharP (AdjoinRoot (h : K[X])) 2 := H.hE.charP
  have hypN : (proj m K y) ^ p = 1 := by rw [← map_pow, hyp, map_one]
  exact indAut_mem_inner_of_sesqSUConj_two hp hp2 hqJ_open hpJ hN hypN H.hHf H.hHfl
    (by rw [ha_dim, hdim2]) (H.φ ⟨D.y_h, D.hy_h⟩) D.π' D.hπ'_surj D.hπ'_ker D.hconj

private theorem selfDual_catalog_unitary {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x y : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) {J : Subgroup (StatedProj (StatedSp m K))}
    {hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))}
    (D : SelfDualUnitaryData H J hN)
    (hJeq : J = (⁅spSupported x ({h} : Set K[X]),
      spSupported x ({h} : Set K[X])⁆).map (proj m K))
    (hproj : Function.Injective (proj m K)) (hchar : CharP K 2) (hm1 : 1 ≤ m)
    (hp : p.Prime) (hqJ : CFSG.Assembly.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (ha3 : 3 ≤ primaryMultiplicity (spEnd x) h)
    (hqne : (primaryMultiplicity (spEnd x) h, 2 ^ (n * H.d)) ≠ (3, 2)) :
    catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP K 2 := hchar
  let E := AdjoinRoot (h : K[X])
  let W := primaryComponent (spEnd x) (h : K[X])
  letI : Finite E := H.hE.finite
  letI : CharP E 2 := H.hE.charP
  let A : Subgroup (StatedSp m K) := spSupported x ({h} : Set K[X])
  let Dsub : Subgroup (StatedSp m K) := ⁅A, A⁆
  have hcat : catalogIs (LargeEvenProj (unitarySU 2 (n * H.d) E
      (primaryMultiplicity (spEnd x) h))) (onLie isUnitaryCharTwoIdx) :=
    catalogIs_largeEvenProj_statedSU H.hE ha3 hqne
  have hpD : p ∣ Nat.card ↥Dsub := by
    rw [Nat.card_congr D.eJ.toEquiv]
    exact hpJ
  have hqJ_native : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp hqJ
  have hqD_native : CFSG.IsQuasisimple ↥Dsub :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv D.eJ.symm hqJ_native
  have hqD : CFSG.Open.IsQuasisimple ↥Dsub :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥Dsub).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Dsub).mpr
        hqD_native)
  open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoInAux in
  have hOcore : GLAPPrimeCore p ↥Dsub ≤ Subgroup.center ↥Dsub :=
    pPrimeCore_le_center_of_quasisimple hqD hp hpD
  haveI : Group.IsPerfect ↥Dsub := Group.isPerfect_def.mpr hqD.1
  let e1 : PSimple p Dsub ≃* (↥Dsub ⧸ Subgroup.center ↥Dsub) :=
    (CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot p hOcore).symm
  let e2 : (↥Dsub ⧸ Subgroup.center ↥Dsub) ≃*
      (↥(unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h)) ⧸
        Subgroup.center ↥(unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h))) :=
    QuotientGroup.congr (Subgroup.center ↥Dsub)
      (Subgroup.center ↥(unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h)))
      D.eD (Subgroup.map_center_eq D.eD)
  have hcenterSU : Subgroup.center ↥(unitarySU 2 (n * H.d) E
      (primaryMultiplicity (spEnd x) h)) =
      (LargeEvenScalars (Fin (primaryMultiplicity (spEnd x) h)) E).subgroupOf
        (unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h)) := by
    have hcard : Nat.card E = (2 ^ (n * H.d)) ^ 2 := by
      rw [H.hE.card, show 2 * (n * H.d) = (n * H.d) * 2 by omega, pow_mul]
    have := CFSG.HardMathSupport.Curtis.UnitaryLevi.center_statedSU_eq_scalars_of_ne
      (K := E) (f := n * H.d) hcard ha3 hqne
    simpa [CFSG.Assembly.LargeEvenScalars, CFSG.Open.StatedScalars, unitarySU] using this
  let e3 : (↥(unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h)) ⧸
        Subgroup.center ↥(unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h))) ≃*
      LargeEvenProj (unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h)) :=
    QuotientGroup.quotientMulEquivOfEq hcenterSU
  have hcenterSp : Subgroup.center (StatedSp m K) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot hm1
  have hf : ∀ g : StatedSp m K, proj m K g = 1 → g ∈ Subgroup.center (StatedSp m K) := by
    intro g hg
    rw [hcenterSp]
    exact Subgroup.mem_bot.mpr (hproj hg)
  obtain ⟨eJp⟩ := CFSG.LocalAnalysis.GLTheoremA.S172X.nonempty_pSimple_equiv_map_of_central
    p (proj m K) hf (inferInstance : Group.IsPerfect ↥Dsub)
  let e : PSimple p J ≃*
      LargeEvenProj (unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h)) :=
    (hJeq.symm ▸ eJp).symm.trans (e1.trans (e2.trans e3))
  exact CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv
    (LargeEvenProj (unitarySU 2 (n * H.d) E (primaryMultiplicity (spEnd x) h)))
    (PSimple p J) e.symm hcat

private theorem selfDual_innAutDerived {m n p : ℕ} {K : Type} [Field K] [Finite K]
    {x y : StatedSp m K} {h : K[X]} [Fact (Irreducible (h : K[X]))]
    (H : SelfDualHalf m n p K x h) {J : Subgroup (StatedProj (StatedSp m K))}
    {hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))}
    (D : SelfDualUnitaryData H J hN) (hp : p.Prime) (hp2 : p ≠ 2)
    (hqJ_open : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hyp : y ^ p = 1) :
    MI.indAut p J (proj m K y) hN ∈ innAutDerived (PSimple p J) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite (AdjoinRoot (h : K[X])) := H.hE.finite
  letI : CharP (AdjoinRoot (h : K[X])) 2 := H.hE.charP
  have hypN : (proj m K y) ^ p = 1 := by rw [← map_pow, hyp, map_one]
  exact indAut_mem_innAutDerived_of_sesqSUConj hp hp2 hqJ_open hpJ hN hypN H.hHf H.hHfl
    D.hSUperf (H.φ ⟨D.y_h, D.hy_h⟩) D.π' D.hπ'_surj D.hπ'_ker D.hconj

theorem spSelfDualBlockAnalysis_holds : SpSelfDualBlockAnalysis := by
  intro m n p K _ _ hK hm hp hp2 x y hxp hyp hxy hx1 h hh h1 hsd hb J hJeq hqJ hN
  classical
  obtain S := selfDual_prelim hK hm hp hp2 x hxp hx1
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP K 2 := S.hchar
  letI : NeZero m := ⟨by omega⟩
  letI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hpJ : p ∣ Nat.card J
  · have hqJ_open : CFSG.Open.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥J).mp hqJ
    have hJnt : Nontrivial ↥J := by
      haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hqJ_open.2.toNontrivial
      exact Function.Surjective.nontrivial
        (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
    have hJnsolv : ¬ Group.IsSolvable ↥J := by
      haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hqJ_open.1
      exact Group.IsPerfect.not_isSolvable ↥J
    let H := selfDual_half S.hn1 hh hb
    have ha_dim : Module.finrank (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])) = primaryMultiplicity (spEnd x) h := rfl
    have ha2 : 2 ≤ primaryMultiplicity (spEnd x) h :=
      selfDual_multiplicity_two_le H J S.hproj hJeq hJnt
    by_cases hsmall : (primaryMultiplicity (spEnd x) h = 2 ∧ 2 ^ (n * H.d) = 2) ∨
        (primaryMultiplicity (spEnd x) h = 3 ∧ 2 ^ (n * H.d) = 2)
    · exact (selfDual_small_block_false H J S.hproj hJeq hJnsolv hsmall).elim
    · have hqcond := selfDual_finrank_conditions H hsmall
      obtain ⟨hSUperf, hψ_inj, hψ_range⟩ := selfDual_perfectData H ha2 hqcond
      let D := selfDual_unitaryData H J hh S.hproj hJeq S.hblocks hxy hsd hN
        hSUperf hψ_inj hψ_range
      by_cases hdim2 : primaryMultiplicity (spEnd x) h = 2
      · exact Or.inr (Or.inr (selfDual_inner_of_dim_two H D hp hp2 hqJ_open hpJ hdim2
          ha_dim hyp))
      · have ha3 : 3 ≤ primaryMultiplicity (spEnd x) h := by omega
        have hqne : (primaryMultiplicity (spEnd x) h, 2 ^ (n * H.d)) ≠ (3, 2) := by
          intro heq
          exact hsmall (Or.inr ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩)
        exact Or.inl ⟨selfDual_catalog_unitary H D hJeq S.hproj S.hchar S.hm1 hp hqJ hpJ
          ha3 hqne, selfDual_innAutDerived H D hp hp2 hqJ_open hpJ hyp⟩
  · haveI := subsingleton_pSimple_of_not_dvd hp hpJ
    exact Or.inr (Or.inr (mem_inner_of_subsingleton _))

theorem sympComponentBlockAnalysis_holds : SympComponentBlockAnalysis :=
  sympComponentBlockAnalysis_of_selfDualAnalysis spSelfDualBlockAnalysis_holds

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
