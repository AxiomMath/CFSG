module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGood
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitBlocks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagSplitTransvection
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA3
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA2
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleCommutator

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Polynomial Module Matrix
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

theorem exists_lifts_of_le_linearAutGroup {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n)
    {k : Type} [Field k] [Finite k] {D : Subgroup (MulAut (projectiveSL n k))}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2) (hDl : D ≤ linearAutGroup n k) :
    ∃ A B : GL (Fin n) k, conjAut n k A ∈ D ∧ conjAut n k B ∈ D ∧ conjAut n k A ≠ 1 ∧
      conjAut n k B ∉ Subgroup.zpowers (conjAut n k A) ∧
      (∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a) ∧
      (∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b) ∧
      ∃ z : kˣ, z ^ p = 1 ∧ A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin n) z := by
  classical
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact absurd hcard.symm (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'
  obtain ⟨⟨x, hxD⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨y, hyD, hyx⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm53A.exists_mem_not_mem_zpowers hp hD hcard hxD
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hDl hxD)
  obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 (hDl hyD)
  have hAp : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a := by
    refine exists_eq_scalar_of_conjAut_eq_one hn ?_
    rw [map_pow, hA, hxp]
  have hBp : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b := by
    refine exists_eq_scalar_of_conjAut_eq_one hn ?_
    rw [map_pow, hB]
    exact hD.2 y hyD
  have hcab : x * y = y * x := hcomm x hxD y hyD
  obtain ⟨z, hz⟩ := exists_commutator_eq_scalar_of_commute_conjAut (A := A) (B := B) hn
    (by rw [hA, hB, hcab])
  have hzpow : z ^ p = 1 := by
    obtain ⟨a, ha⟩ := hAp
    have hcen : ⁅A, B⁆ ∈ Subgroup.center (GL (Fin n) k) := by
      rw [commutatorElement_def, hz]
      exact Subgroup.mem_center_iff.2 fun g => (GeneralLinearGroup.scalar_commute z g).symm
    have hApc : A ^ p ∈ Subgroup.center (GL (Fin n) k) := by
      rw [ha]
      exact Subgroup.mem_center_iff.2 fun g => (GeneralLinearGroup.scalar_commute a g).symm
    have hone : ⁅A ^ p, B⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hApc B).symm
    have hpow : ⁅A ^ p, B⁆ = ⁅A, B⁆ ^ p := by
      simpa using CFSG.commutator_pow_pow_of_mem_center (x := A) (y := B) p 1 hcen
    have h1 : GeneralLinearGroup.scalar (Fin n) (z ^ p) =
        (GeneralLinearGroup.scalar (Fin n) z) ^ p := map_pow _ z p
    have hscal : GeneralLinearGroup.scalar (Fin n) (z ^ p) = 1 := by
      rw [h1, ← hz]
      show (⁅A, B⁆ : GL (Fin n) k) ^ p = 1
      rw [← hpow, hone]
    refine glScalar_injective (n := n) (F := k) (by omega) ?_
    rw [hscal, map_one]
  refine ⟨A, B, ?_, ?_, ?_, ?_, hAp, hBp, z, hzpow, hz⟩
  · rw [hA]; exact hxD
  · rw [hB]; exact hyD
  · rw [hA]; exact hx1'
  · rw [hA, hB]; exact hyx

theorem card_comap_blockImage_of_good {n : ℕ} {F : Type} [Field F]
    {x : Module.End F (Fin n → F)} {hsq : Squarefree (minpoly F x)} {h : primaryFactors x}
    (hgood : GoodBlock h) :
    Nat.card ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) =
      Nat.card (blockImage hsq h) := by
  have hrange := blockImage_le_range_toGL_of_good hsq h hgood
  let e0 : ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) ≃*
        blockImage hsq h :=
    (Subgroup.equivMapOfInjective _ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →*
      GL (Fin n) F) SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hrange))
  exact Nat.card_congr e0.toEquiv

theorem dvd_card_blockProj_of_not_dvd_center {n : ℕ} {F : Type} [Field F]
    {x : Module.End F (Fin n → F)} {hsq : Squarefree (minpoly F x)} {h : primaryFactors x}
    {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)))
    (hgood : GoodBlock h) (hpd : p ∣ Nat.card (blockImage hsq h)) :
    p ∣ Nat.card (blockProj hsq h) := by
  classical
  set T := (blockImage hsq h).comap
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F) with hT
  set ψ := blockToProj (x := x) hsq h with hψ
  have hsurj : Function.Surjective ψ := blockToProj_surjective
  have hcard : Nat.card ψ.ker * Nat.card (blockProj hsq h) = Nat.card T := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top] at h1
    exact h1
  have hpd' : p ∣ Nat.card T := by
    rw [card_comap_blockImage_of_good (hsq := hsq) (h := h) hgood]
    exact hpd
  have hker : Nat.card ψ.ker ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) := by
    have hle : ψ.ker.map (Subgroup.subtype T) ≤
        Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : proj n F (y : SpecialLinearGroup (Fin n) F) = 1 := congrArg Subtype.val hy
      exact (scalars_eq_center n F).le (proj_eq_one_iff.1 h1)
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective T)]
    exact Subgroup.card_dvd_of_le hle
  rw [← hcard] at hpd'
  rcases (Nat.Prime.dvd_mul hp).1 hpd' with h | h
  · exact absurd (h.trans hker) hZ
  · exact h

theorem perfect_fixSubgroup_blockProj {n : ℕ} {k : Type} [Field k] {M : GL (Fin n) k}
    {x : Module.End k (Fin n → k)}
    (hx : Matrix.toLin' (M : Matrix (Fin n) (Fin n) k) = x)
    {hsq : Squarefree (minpoly k x)} {h : primaryFactors x} (hgood : GoodBlock h) :
    blockProj hsq h ≤ fixSubgroup (conjAut n k M) ∧
      ⁅blockProj hsq h, blockProj hsq h⁆ = blockProj hsq h := by
  constructor
  · intro q hq
    rw [mem_fixSubgroup]
    obtain ⟨s, hs, rfl⟩ := hq
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation]
    have hcomm := commute_of_mem_blockImage_of_toLin' hx hs
    have h2 : M * SpecialLinearGroup.toGL s * M⁻¹ = SpecialLinearGroup.toGL s := by
      rw [← hcomm]; group
    have h1 := congrArg Units.val h2
    simpa using h1
  · haveI : Group.IsPerfect ↥(blockProj hsq h) := (blockProj_isQuasisimple hgood).1
    exact Subgroup.commutator_eq_self

theorem exists_perfect_fixSubgroup_of_goodBlock_of_primitiveRoot {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {n : ℕ} {k : Type} [Field k] {M : GL (Fin n) k} {x : Module.End k (Fin n → k)}
    (hx : Matrix.toLin' (M : Matrix (Fin n) (Fin n) k) = x)
    {hsq : Squarefree (minpoly k x)} {h : primaryFactors x} (hgood : GoodBlock h)
    {ω : k} (hω : IsPrimitiveRoot ω p) :
    ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup (conjAut n k M) ∧ ⁅Q, Q⁆ = Q ∧
      p ∣ Nat.card Q :=
  ⟨blockProj hsq h, (perfect_fixSubgroup_blockProj hx hgood).1,
    (perfect_fixSubgroup_blockProj hx hgood).2, dvd_card_blockProj hp hp2 hgood hω⟩

theorem exists_perfect_fixSubgroup_of_goodBlock_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} {k : Type} [Field k] {M : GL (Fin n) k} {x : Module.End k (Fin n → k)}
    (hx : Matrix.toLin' (M : Matrix (Fin n) (Fin n) k) = x)
    {hsq : Squarefree (minpoly k x)} {h : primaryFactors x} (hgood : GoodBlock h)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) k)))
    (hpd : p ∣ Nat.card (blockImage hsq h)) :
    ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup (conjAut n k M) ∧ ⁅Q, Q⁆ = Q ∧
      p ∣ Nat.card Q :=
  ⟨blockProj hsq h, (perfect_fixSubgroup_blockProj hx hgood).1,
    (perfect_fixSubgroup_blockProj hx hgood).2,
    dvd_card_blockProj_of_not_dvd_center hp hZ hgood hpd⟩

theorem exists_perfect_fixSubgroup_of_diagonal_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} {k : Type} [Field k] [Finite k] (hpq : p ∣ Nat.card k - 1) {M P : GL (Fin n) k}
    (hM : M ^ p = 1)
    (hdiag : ∀ i j, i ≠ j → ((P * M * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0)
    {i j : Fin n} (hij : i ≠ j)
    (hd : ((P * M * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i =
      ((P * M * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) j j) :
    ∃ Q : Subgroup (projectiveSL n k),
      Q ≤ fixSubgroup (conjAut n k M) ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q := by
  classical
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq2 : 1 < Nat.card k := Finite.one_lt_card
  have hq4 : 4 ≤ Nat.card k := by
    have h1 := Nat.le_of_dvd (by omega : 0 < Nat.card k - 1) hpq
    omega
  have hpk : ¬ p ∣ Nat.card k := by
    intro hdvd
    have h1 : p ∣ Nat.card k - (Nat.card k - 1) := Nat.dvd_sub hdvd hpq
    rw [show Nat.card k - (Nat.card k - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : k) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpk
  have hMx : (Matrix.toLin' (M : Matrix (Fin n) (Fin n) k)) ^ p = 1 := toLin'_pow_eq_one hM
  have hsq : Squarefree (minpoly k (Matrix.toLin' (M : Matrix (Fin n) (Fin n) k))) :=
    squarefree_minpoly_of_pow_eq_one hpK hMx
  obtain ⟨hX, hmult, -⟩ := transvection_mem_blockImage_gl M P hdiag hij hd 0 hsq
  set h' : primaryFactors (Matrix.toLin' (M : Matrix (Fin n) (Fin n) k)) :=
    ⟨X - C (((P * M * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i), hX⟩ with hh'
  have hcardE : Nat.card (Efac (Matrix.toLin' (M : Matrix (Fin n) (Fin n) k)) h') =
      Nat.card k := by
    have : Fact (Irreducible (X - C (((P * M * P⁻¹ : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i i) : k[X])) := ⟨irreducible_X_sub_C _⟩
    change Nat.card (AdjoinRoot (X - C _)) = _
    rw [natCard_adjoinRoot, natDegree_X_sub_C, pow_one]
  have hgood : GoodBlock h' := Or.inr ⟨hmult, by rw [hcardE]; omega⟩
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_of_dvd hp hpq
  exact exists_perfect_fixSubgroup_of_goodBlock_of_primitiveRoot (hsq := hsq) hp hp2 rfl hgood hω

private theorem exists_sl_lift_of_dvd_of_modEq {p m : ℕ} (hp : p.Prime) {n : ℕ}
    {k : Type} [Field k] [Finite k] {A : GL (Fin n) k}
    (hdvd : (Nat.card k - 1) ∣ m) (hmod : m ≡ 1 [MOD p])
    (hA : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a) :
    ∃ A₁ : SpecialLinearGroup (Fin n) k, A₁ ^ p = 1 ∧
      SpecialLinearGroup.toGL A₁ = A ^ m ∧
      conjAut n k (SpecialLinearGroup.toGL A₁) = conjAut n k A := by
  classical
  obtain ⟨a, ha⟩ := hA
  have haq : a ^ (Nat.card k - 1) = 1 := by
    rw [← Nat.card_units k]
    exact pow_card_eq_one'
  have hdetq : GeneralLinearGroup.det A ^ (Nat.card k - 1) = 1 := by
    rw [← Nat.card_units k]
    exact pow_card_eq_one'
  have hunit : GeneralLinearGroup.det A ^ m = 1 := by
    obtain ⟨t, rfl⟩ := hdvd
    rw [pow_mul, hdetq, one_pow]
  have hdet : ((A ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det = 1 := by
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow, ← GeneralLinearGroup.val_det_apply,
      ← Units.val_pow_eq_pow_val, hunit, Units.val_one]
  let A₁ : SpecialLinearGroup (Fin n) k :=
    ⟨((A ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k), hdet⟩
  have htoGL : SpecialLinearGroup.toGL A₁ = A ^ m := Units.ext rfl
  have hAq : (A ^ (Nat.card k - 1)) ^ p = 1 := by
    rw [← pow_mul, mul_comm (Nat.card k - 1) p, pow_mul, ha, ← map_pow, haq, map_one]
  have hAmp : (A ^ m) ^ p = 1 := by
    obtain ⟨t, rfl⟩ := hdvd
    have h1 : A ^ ((Nat.card k - 1) * t) = (A ^ (Nat.card k - 1)) ^ t := pow_mul _ _ _
    rw [h1, ← pow_mul, mul_comm t p, pow_mul, hAq, one_pow]
  have hA₁p : A₁ ^ p = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, map_one, htoGL, hAmp]
  have hc : conjAut n k (SpecialLinearGroup.toGL A₁) = conjAut n k A := by
    rw [htoGL, map_pow]
    have hcAp : conjAut n k A ^ p = 1 := by rw [← map_pow, ha, conjAut_scalar]
    exact (pow_eq_pow_of_modEq hmod hcAp).trans (pow_one _)
  exact ⟨A₁, hA₁p, htoGL, hc⟩

private theorem exists_dvd_and_modEq_one {p : ℕ} (hp : p.Prime) {k : Type} [Field k] [Finite k]
    (hpq : ¬ p ∣ Nat.card k - 1) :
    ∃ m : ℕ, (Nat.card k - 1) ∣ m ∧ m ≡ 1 [MOD p] := by
  have hcop : Nat.Coprime (Nat.card k - 1) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨(Nat.card k - 1) * m, ⟨m, rfl⟩, ?_⟩
  show (Nat.card k - 1) * m % p = 1 % p
  rw [hm, Nat.mod_eq_of_lt hp.one_lt]

private theorem sl_plane_kernel {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n) {k : Type}
    [Field k] [Finite k] (hpq : ¬ p ∣ Nat.card k - 1) {A₁ B₁ : SpecialLinearGroup (Fin n) k}
    (hA₁p : A₁ ^ p = 1) (hB₁p : B₁ ^ p = 1) (hA₁B₁ : A₁ * B₁ = B₁ * A₁)
    {x : SpecialLinearGroup (Fin n) k}
    (hx : x ∈ Subgroup.zpowers A₁ ⊔ Subgroup.zpowers B₁)
    (hc : conjAut n k (SpecialLinearGroup.toGL x) = 1) : x = 1 := by
  obtain ⟨c, hc'⟩ := exists_eq_scalar_of_conjAut_eq_one hn hc
  have hsGL : SpecialLinearGroup.toGL x = GeneralLinearGroup.scalar (Fin n) c := hc'
  have hxp : x ^ p = 1 := by
    obtain ⟨-, hexpCl⟩ := closure_pair_comm_and_pow_eq_one hA₁B₁ hA₁p hB₁p
    refine hexpCl x ?_
    rw [CFSG.StandardType.closure_pair_eq_sup]
    exact hx
  have hcp : c ^ p = 1 := by
    refine glScalar_injective (n := n) (F := k) (by omega) ?_
    calc GeneralLinearGroup.scalar (Fin n) (c ^ p)
        = (GeneralLinearGroup.scalar (Fin n) c) ^ p := map_pow _ c p
      _ = (SpecialLinearGroup.toGL x) ^ p := by rw [hsGL]
      _ = SpecialLinearGroup.toGL (x ^ p) := (map_pow _ x p).symm
      _ = 1 := by rw [hxp, map_one]
  have hdvd' : orderOf c ∣ Nat.gcd p (Nat.card kˣ) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcp) (orderOf_dvd_natCard c)
  have hgcd : Nat.gcd p (Nat.card kˣ) = 1 := by
    rw [Nat.card_units k]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
  rw [hgcd] at hdvd'
  have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd')
  apply SpecialLinearGroup.toGL_injective
  rw [hsGL, hc1, map_one, map_one]

private theorem exists_sl_plane {p m : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n)
    {k : Type} [Field k] [Finite k] (hdvd : (Nat.card k - 1) ∣ m) (hmod : m ≡ 1 [MOD p])
    (hpq : ¬ p ∣ Nat.card k - 1) {A B : GL (Fin n) k} (hAB : A * B = B * A)
    (hA : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hB : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hA1 : conjAut n k A ≠ 1) (hBA : conjAut n k B ∉ Subgroup.zpowers (conjAut n k A)) :
    ∃ (A₁ B₁ : SpecialLinearGroup (Fin n) k) (E₀ : Subgroup (SpecialLinearGroup (Fin n) k)),
      A₁ ^ p = 1 ∧ B₁ ^ p = 1 ∧
      conjAut n k (SpecialLinearGroup.toGL A₁) = conjAut n k A ∧
      conjAut n k (SpecialLinearGroup.toGL B₁) = conjAut n k B ∧
      E₀ = Subgroup.zpowers A₁ ⊔ Subgroup.zpowers B₁ ∧
      Nat.card ↥E₀ = p ^ 2 ∧ CFSG.IsElementaryAbelian p ↥E₀ ∧
      (∀ x : SpecialLinearGroup (Fin n) k, x ∈ E₀ →
        conjAut n k (SpecialLinearGroup.toGL x) = 1 → x = 1) ∧
      (∀ a : E₀, conjAut n k (SpecialLinearGroup.toGL (a : SpecialLinearGroup (Fin n) k)) ∈
        Subgroup.closure {conjAut n k A, conjAut n k B}) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₁, hA₁p, hA₁toGL, hcA⟩ := exists_sl_lift_of_dvd_of_modEq hp hdvd hmod hA
  obtain ⟨B₁, hB₁p, hB₁toGL, hcB⟩ := exists_sl_lift_of_dvd_of_modEq hp hdvd hmod hB
  have hA₁B₁ : A₁ * B₁ = B₁ * A₁ := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, hA₁toGL, hB₁toGL]
    exact ((show Commute A B from hAB).pow_pow m m).eq
  have hA₁1 : A₁ ≠ 1 := fun h => hA1 (by rw [← hcA, h]; simp)
  have hB₁A₁ : B₁ ∉ Subgroup.zpowers A₁ := by
    intro h
    apply hBA
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
    have h2 : conjAut n k (SpecialLinearGroup.toGL B₁) =
        conjAut n k (SpecialLinearGroup.toGL A₁) ^ j := by
      simp only [← hj, map_zpow]
    rw [hcA, hcB] at h2
    rw [h2]
    exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩
  have hcentB₁ : ∀ e ∈ Subgroup.zpowers A₁, e * B₁ = B₁ * e := by
    intro e he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact (show Commute A₁ B₁ from hA₁B₁).zpow_left i
  refine ⟨A₁, B₁, Subgroup.zpowers A₁ ⊔ Subgroup.zpowers B₁, hA₁p, hB₁p, hcA, hcB, rfl,
    ?_, ?_, ?_, ?_⟩
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (Subgroup.zpowers A₁) hB₁p hB₁A₁
      hcentB₁, Nat.card_zpowers, orderOf_eq_prime hA₁p hA₁1]
    ring
  · obtain ⟨hcommCl, hexpCl⟩ := closure_pair_comm_and_pow_eq_one hA₁B₁ hA₁p hB₁p
    have hE₀eq : Subgroup.zpowers A₁ ⊔ Subgroup.zpowers B₁ =
        Subgroup.closure ({A₁, B₁} : Set (SpecialLinearGroup (Fin n) k)) :=
      (CFSG.StandardType.closure_pair_eq_sup A₁ B₁).symm
    haveI hmc : IsMulCommutative ↥(Subgroup.zpowers A₁ ⊔ Subgroup.zpowers B₁) :=
      isMulCommutative_iff.2 fun (x y : ↥(Subgroup.zpowers A₁ ⊔ Subgroup.zpowers B₁)) =>
        Subtype.ext (hcommCl (x : SpecialLinearGroup (Fin n) k) (by rw [← hE₀eq]; exact x.2)
          (y : SpecialLinearGroup (Fin n) k) (by rw [← hE₀eq]; exact y.2))
    exact
      { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun
          (x : ↥(Subgroup.zpowers A₁ ⊔ Subgroup.zpowers B₁)) =>
          Subtype.ext (hexpCl (x : SpecialLinearGroup (Fin n) k) (by rw [← hE₀eq]; exact x.2)) }
  · intro x hx hc
    exact sl_plane_kernel hp hn hpq hA₁p hB₁p hA₁B₁ hx hc
  · intro a
    have ha : (a : SpecialLinearGroup (Fin n) k) ∈
        Subgroup.closure ({A₁, B₁} : Set (SpecialLinearGroup (Fin n) k)) := by
      rw [CFSG.StandardType.closure_pair_eq_sup]
      exact a.2
    have himg : ((conjAut n k).comp SpecialLinearGroup.toGL) ''
        ({A₁, B₁} : Set (SpecialLinearGroup (Fin n) k)) =
        {conjAut n k A, conjAut n k B} := by
      ext z
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, MonoidHom.coe_comp,
        Function.comp_apply]
      constructor
      · rintro ⟨s, rfl | rfl, rfl⟩
        · left; rw [hcA]
        · right; rw [hcB]
      · rintro (rfl | rfl)
        · exact ⟨A₁, Or.inl rfl, hcA⟩
        · exact ⟨B₁, Or.inr rfl, hcB⟩
    have h1 : ((conjAut n k).comp SpecialLinearGroup.toGL) (a : SpecialLinearGroup (Fin n) k)
        ∈ Subgroup.map ((conjAut n k).comp SpecialLinearGroup.toGL)
            (Subgroup.closure ({A₁, B₁} : Set (SpecialLinearGroup (Fin n) k))) :=
      Subgroup.mem_map_of_mem _ ha
    rwa [MonoidHom.map_closure, himg] at h1

private theorem exists_good_of_elementary_plane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (hpk : ¬ p ∣ Nat.card k)
    (hpq : ¬ p ∣ Nat.card k - 1) (hp4 : 3 < p ∨ 4 ≤ Nat.card k)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) k)))
    (E₀ : Subgroup (SpecialLinearGroup (Fin n) k)) [CFSG.IsElementaryAbelian p ↥E₀]
    (hE₀card : Nat.card ↥E₀ = p ^ 2) {E : Subgroup (MulAut (projectiveSL n k))}
    (hmem : ∀ a : E₀, conjAut n k (SpecialLinearGroup.toGL (a : SpecialLinearGroup (Fin n) k)) ∈ E)
    (hne : ∀ a : E₀, a ≠ 1 →
      conjAut n k (SpecialLinearGroup.toGL (a : SpecialLinearGroup (Fin n) k)) ≠ 1) :
    ∃ β ∈ E, β ≠ 1 ∧
      ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup β ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q := by
  classical
  have hpK : (p : k) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpk
  by_contra hgoal
  have hblocks : ∀ a ∈ E₀, a ≠ 1 →
      ∀ (hsq : Squarefree (minpoly k (Matrix.toLin' (a : Matrix (Fin n) (Fin n) k))))
        (h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) k))), GoodBlock h →
        p ∣ Nat.card (blockImage hsq h) →
        blockImage hsq h ≤ (⊥ : Subgroup (SpecialLinearGroup (Fin n) k)).map
          SpecialLinearGroup.toGL := by
    intro a ha ha1 hsq h hgood hpd
    exfalso
    obtain ⟨Q, hQfix, hQperf, hQp⟩ :=
      exists_perfect_fixSubgroup_of_goodBlock_of_dvd hp hp2
        (M := SpecialLinearGroup.toGL a) rfl hgood hZ hpd
    have ha1' : (⟨a, ha⟩ : E₀) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    exact hgoal ⟨_, hmem ⟨a, ha⟩, hne ⟨a, ha⟩ ha1', Q, hQfix, hQperf, hQp⟩
  have htop := eq_top_of_good_blocks_le' hp hp4 hpK hpk hpq E₀ hE₀card
    (⊥ : Subgroup (SpecialLinearGroup (Fin n) k)) hblocks
  haveI hnt : Nontrivial (SpecialLinearGroup (Fin n) k) := by
    obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, i ≠ j :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    refine ⟨SpecialLinearGroup.transvection hij 1, 1, ?_⟩
    intro h
    have h2 : ((SpecialLinearGroup.transvection hij 1 : SpecialLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j = ((1 : SpecialLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j := by rw [h]
    rw [SpecialLinearGroup.transvection_coe] at h2
    simp [hij] at h2
  have hbot : (⊥ : Subgroup (SpecialLinearGroup (Fin n) k)) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : SpecialLinearGroup (Fin n) k)
    have : x ∈ (⊥ : Subgroup (SpecialLinearGroup (Fin n) k)) := by
      rw [h]; exact Subgroup.mem_top x
    exact hx (by simpa using this)
  exact hbot htop

private theorem exists_good_of_not_dvd_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (hpk : ¬ p ∣ Nat.card k)
    (h32 : ¬ (p = 3 ∧ Nat.card k = 2)) (hpq : ¬ p ∣ Nat.card k - 1)
    {A B : GL (Fin n) k} (hAB : A * B = B * A)
    (hA : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hB : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hA1 : conjAut n k A ≠ 1) (hBA : conjAut n k B ∉ Subgroup.zpowers (conjAut n k A)) :
    ∃ β ∈ Subgroup.closure {conjAut n k A, conjAut n k B}, β ≠ 1 ∧
      ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup β ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q := by
  classical
  have hq2 : 1 < Nat.card k := Finite.one_lt_card
  have hp4 : 3 < p ∨ 4 ≤ Nat.card k := by
    by_cases h3 : p = 3
    · right
      have hk2 : Nat.card k ≠ 2 := fun h => h32 ⟨h3, h⟩
      have hk3 : ¬ 3 ∣ Nat.card k := h3 ▸ hpk
      have hle3 : ¬ Nat.card k ≤ 3 := by
        intro hle
        have h23 : Nat.card k = 2 ∨ Nat.card k = 3 := by omega
        rcases h23 with h | h
        · exact hk2 h
        · exact hk3 (h ▸ by norm_num)
      omega
    · left
      have := hp.two_le
      omega
  have hZ : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) k)) := fun hd =>
    hpq (hd.trans ((CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega) k).trans
      (Nat.gcd_dvd_right _ _)))
  obtain ⟨m, hdvd, hmod⟩ := exists_dvd_and_modEq_one hp hpq
  obtain ⟨A₁, B₁, E₀, hA₁p, hB₁p, hcA, hcB, hE₀def, hE₀card, hE₀el, hker, hmem⟩ :=
    exists_sl_plane (m := m) hp hn hdvd hmod hpq hAB hA hB hA1 hBA
  haveI := hE₀el
  refine exists_good_of_elementary_plane hp hp2 hn hpk hpq hp4 hZ E₀ hE₀card ?_ ?_
  · intro a
    exact hmem a
  · intro a ha1
    exact fun h1 => ha1 (Subtype.ext (hker _ a.2 h1))

private theorem exists_good_of_diag {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    {k : Type} [Field k] [Finite k] (hpq : p ∣ Nat.card k - 1)
    {M P A B : GL (Fin n) k} (hM : M ^ p = 1)
    (hdiag : ∀ i j, i ≠ j → ((P * M * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0)
    {i j : Fin n} (hij : i ≠ j)
    (hd : ((P * M * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i =
      ((P * M * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) j j)
    (hME : conjAut n k M ∈ Subgroup.closure {conjAut n k A, conjAut n k B})
    (hM1 : conjAut n k M ≠ 1) :
    ∃ β ∈ Subgroup.closure {conjAut n k A, conjAut n k B}, β ≠ 1 ∧
      ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup β ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q :=
  ⟨conjAut n k M, hME, hM1, exists_perfect_fixSubgroup_of_diagonal_eq hp hp2 hpq hM hdiag hij hd⟩

private theorem exists_good_of_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (hpq : p ∣ Nat.card k - 1)
    {A B : GL (Fin n) k} (hAB : A * B = B * A)
    (hAs : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p))
    (hBs : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (b ^ p))
    (hA1 : conjAut n k A ≠ 1) (hBA : conjAut n k B ∉ Subgroup.zpowers (conjAut n k A)) :
    ∃ β ∈ Subgroup.closure {conjAut n k A, conjAut n k B}, β ≠ 1 ∧
      ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup β ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hAs
  obtain ⟨b, hb⟩ := hBs
  obtain ⟨hA'p, hcA⟩ := glRescale_lift (n := n) (p := p) (A := A) (a := a) ha
  obtain ⟨hB'p, hcB⟩ := glRescale_lift (n := n) (p := p) (A := B) (a := b) hb
  set A' : GL (Fin n) k := GeneralLinearGroup.scalar (Fin n) a⁻¹ * A with hA'def
  set B' : GL (Fin n) k := GeneralLinearGroup.scalar (Fin n) b⁻¹ * B with hB'def
  have hAB' : A' * B' = B' * A' := glScalar_mul_commute hAB a⁻¹ b⁻¹
  obtain ⟨hcomm, hexp⟩ := closure_pair_comm_and_pow_eq_one hAB' hA'p hB'p
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd hp hpq
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime ⟨ζ, hζ⟩
    (Subgroup.closure ({A', B'} : Set (GL (Fin n) k))) hcomm hexp
  have hA'mem : A' ∈ Subgroup.closure ({A', B'} : Set (GL (Fin n) k)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hB'mem : B' ∈ Subgroup.closure ({A', B'} : Set (GL (Fin n) k)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set dA : Fin n → k :=
    fun l => ((P * A' * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) l l with hdA
  set dB : Fin n → k :=
    fun l => ((P * B' * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) l l with hdB
  have hAd : ((P * A' * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal dA :=
    glConj_eq_diagonal (hP A' hA'mem)
  have hBd : ((P * B' * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal dB :=
    glConj_eq_diagonal (hP B' hB'mem)
  have hdAp : ∀ l, dA l ^ p = 1 := fun l => by
    simpa [hAd] using
      CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.isDiag_entry_pow_eq_one
        (g := P * A' * P⁻¹) (by rw [hAd]; exact Matrix.isDiag_diagonal dA)
        (by simp [hA'p]) l
  have hdBp : ∀ l, dB l ^ p = 1 := fun l => by
    simpa [hBd] using
      CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.isDiag_entry_pow_eq_one
        (g := P * B' * P⁻¹) (by rw [hBd]; exact Matrix.isDiag_diagonal dB)
        (by simp [hB'p]) l
  set i : Fin n := ⟨0, by omega⟩ with hidef
  set j : Fin n := ⟨1, by omega⟩ with hjdef
  have hij : i ≠ j := by simp [hidef, hjdef]
  have hmemA : conjAut n k A ∈ Subgroup.closure {conjAut n k A, conjAut n k B} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmemB : conjAut n k B ∈ Subgroup.closure {conjAut n k A, conjAut n k B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmemA' : conjAut n k A' ∈ Subgroup.closure {conjAut n k A, conjAut n k B} := by
    rw [hcA]; exact hmemA
  have hmemB' : conjAut n k B' ∈ Subgroup.closure {conjAut n k A, conjAut n k B} := by
    rw [hcB]; exact hmemB
  rcases CFSG.LinearAlgebra.eq_or_exists_pow_mul_eq hp hdAp hdBp i j with h | ⟨k₀, hk⟩
  · refine exists_good_of_diag (P := P) hp hp2 hpq hA'p (fun r s hrs => ?_) hij ?_ hmemA' ?_
    · rw [hAd]; exact Matrix.diagonal_apply_ne _ hrs
    · rw [hAd]; exact h
    · rw [hcA]; exact hA1
  · have hMp : (A' ^ k₀ * B') ^ p = 1 := by
      rw [(show Commute (A' ^ k₀) B' from (show Commute A' B' from hAB').pow_left k₀).mul_pow,
        ← pow_mul, mul_comm k₀ p, pow_mul, hA'p, one_pow, hB'p, one_mul]
    have hMd : ((P * (A' ^ k₀ * B') * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        Matrix.diagonal (fun l => dA l ^ k₀ * dB l) := glConj_pow_mul_eq_diagonal hAd hBd k₀
    have hmem : conjAut n k (A' ^ k₀ * B') ∈
        Subgroup.closure {conjAut n k A, conjAut n k B} := by
      rw [map_mul, map_pow, hcA, hcB]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hmemA k₀) hmemB
    have hne : conjAut n k (A' ^ k₀ * B') ≠ 1 := by
      rw [map_mul, map_pow, hcA, hcB]
      intro h1
      apply hBA
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k₀)
    refine exists_good_of_diag (P := P) hp hp2 hpq hMp (fun r s hrs => ?_) hij ?_ hmem hne
    · rw [hMd]; exact Matrix.diagonal_apply_ne _ hrs
    · rw [hMd]; exact hk

theorem goodBlock_of_nonsplit_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n)
    {k : Type} [Field k] {R S : GL (Fin n) k} (hRS : R * S = S * R) {c : kˣ}
    (hR : R ^ p = GeneralLinearGroup.scalar (Fin n) c) (hirr : Irreducible (X ^ p - C (c : k)))
    (hS : S ^ p = 1)
    (hsqS : Squarefree (minpoly k (Matrix.toLin' (S : Matrix (Fin n) (Fin n) k))))
    {ω : k} (hω : IsPrimitiveRoot ω p) :
    ∀ b : primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) k)), GoodBlock b := by
  intro b
  left
  obtain ⟨ζ, hζ⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp.ne_zero hω hS b.2
  have hdeg : (b : k[X]).natDegree = 1 := by rw [hζ]; exact natDegree_X_sub_C ζ
  have h1 := finrank_primaryComponent (Matrix.toLin' (S : Matrix (Fin n) (Fin n) k)) (b : k[X])
  rw [hdeg, one_mul] at h1
  have h2 : p ≤ Module.finrank k
      (primaryComponent (Matrix.toLin' (S : Matrix (Fin n) (Fin n) k)) (b : k[X])) :=
    le_finrank_primaryComponent hn hp.ne_zero hRS hirr hR hsqS b.2
  have h3 : 3 ≤ p := by
    have h2' : 2 ≤ p := hp.two_le
    rcases Nat.eq_or_lt_of_le h2' with h | h
    · exact absurd h.symm hp2
    · exact h
  have h4 : 3 ≤ Module.finrank k
      (primaryComponent (Matrix.toLin' (S : Matrix (Fin n) (Fin n) k)) (b : k[X])) :=
    le_trans h3 h2
  rwa [h1] at h4

private theorem false_of_nonsplit_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn2 : n = 2)
    {k : Type} [Field k] [Finite k] {A B : GL (Fin n) k}
    (hA : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hB : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hns : ¬ ((∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p)) ∧
        ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (b ^ p))) : False := by
  subst hn2
  have h2 : ¬ p ∣ Fintype.card (Fin 2) := by
    rw [Fintype.card_fin]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  rcases not_and_or.1 hns with hna | hnb
  · push Not at hna
    obtain ⟨a, ha⟩ := hA
    have hM : ((A : Matrix (Fin 2) (Fin 2) k)) ^ p = Matrix.scalar (Fin 2) (a : k) := by
      rw [← Units.val_pow_eq_pow_val, ha, GeneralLinearGroup.coe_scalar]
    obtain ⟨c, hc⟩ :=
      CFSG.StandardType.TypeA.PGLTor.exists_pow_eq_of_pow_eq_scalar (K := k) hp hM h2
    refine hna c ?_
    rw [hc]
    exact ha
  · push Not at hnb
    obtain ⟨b, hb⟩ := hB
    have hM : ((B : Matrix (Fin 2) (Fin 2) k)) ^ p = Matrix.scalar (Fin 2) (b : k) := by
      rw [← Units.val_pow_eq_pow_val, hb, GeneralLinearGroup.coe_scalar]
    obtain ⟨c, hc⟩ :=
      CFSG.StandardType.TypeA.PGLTor.exists_pow_eq_of_pow_eq_scalar (K := k) hp hM h2
    refine hnb c ?_
    rw [hc]
    exact hb

private theorem exists_good_of_nonsplit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (hpq : p ∣ Nat.card k - 1)
    {A B : GL (Fin n) k} (hAB : A * B = B * A)
    (hA : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hB : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hA1 : conjAut n k A ≠ 1) (hBA : conjAut n k B ∉ Subgroup.zpowers (conjAut n k A))
    (hns : ¬ ((∃ c : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (c ^ p)) ∧
        ∃ d : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (d ^ p))) :
    ∃ β ∈ Subgroup.closure {conjAut n k A, conjAut n k B}, β ≠ 1 ∧
      ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup β ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q := by
  classical
  have hq2 : 1 < Nat.card k := Finite.one_lt_card
  have hpF : ¬ p ∣ Nat.card k := by
    intro hd
    have h1 : p ∣ Nat.card k - (Nat.card k - 1) := Nat.dvd_sub hd hpq
    rw [show Nat.card k - (Nat.card k - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · exact (false_of_nonsplit_two hp hp2 (by omega) hA hB hns).elim
  · have hpK : (p : k) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpF
    have hAp : conjAut n k A ^ p = 1 := by
      obtain ⟨a, ha⟩ := hA
      rw [← map_pow, ha, conjAut_scalar]
    have hBp : conjAut n k B ^ p = 1 := by
      obtain ⟨b, hb⟩ := hB
      rw [← map_pow, hb, conjAut_scalar]
    obtain ⟨R, S, hRS, ⟨c, hR, hc⟩, hS, hS1, -, hSE⟩ :=
      exists_nonsplit_pair (by omega : 3 ≤ n) hp hAB hAp hBp hA1 hBA hns
    obtain ⟨ω, hω⟩ := exists_primitiveRoot_of_dvd hp hpq
    have hirr : Irreducible (X ^ p - C (c : k)) :=
      CFSG.LinearAlgebra.X_pow_sub_C_irreducible_of_prime_of_units hp hc
    have hsqS : Squarefree (minpoly k (Matrix.toLin' (S : Matrix (Fin n) (Fin n) k))) :=
      squarefree_minpoly_of_pow_eq_one hpK (toLin'_pow_eq_one hS)
    obtain ⟨b, hb, -, -, -⟩ :=
      exists_ne_mem_primaryFactors (by omega : 0 < n) hp.ne_zero hpK hω hS hS1
    have hgood : GoodBlock (⟨b, hb⟩ : primaryFactors
        (Matrix.toLin' (S : Matrix (Fin n) (Fin n) k))) :=
      goodBlock_of_nonsplit_pair hp hp2 (by omega) hRS hR hirr hS hsqS hω ⟨b, hb⟩
    refine ⟨conjAut n k S, hSE, hS1, blockProj hsqS ⟨b, hb⟩, ?_, ?_, ?_⟩
    · exact (perfect_fixSubgroup_blockProj (M := S) rfl hgood).1
    · exact (perfect_fixSubgroup_blockProj (M := S) rfl hgood).2
    · exact dvd_card_blockProj hp hp2 hgood hω

theorem exists_good_of_commuting_lifts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (hpk : ¬ p ∣ Nat.card k)
    (h32 : ¬ (p = 3 ∧ Nat.card k = 2)) {A B : GL (Fin n) k} (hAB : A * B = B * A)
    (hA : ∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hB : ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hA1 : conjAut n k A ≠ 1) (hBA : conjAut n k B ∉ Subgroup.zpowers (conjAut n k A)) :
    ∃ β ∈ Subgroup.closure {conjAut n k A, conjAut n k B}, β ≠ 1 ∧
      ∃ Q : Subgroup (projectiveSL n k), Q ≤ fixSubgroup β ∧ ⁅Q, Q⁆ = Q ∧ p ∣ Nat.card Q := by
  by_cases hpq : p ∣ Nat.card k - 1
  · by_cases hs : (∃ a : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p)) ∧
        ∃ b : kˣ, B ^ p = GeneralLinearGroup.scalar (Fin n) (b ^ p)
    · exact exists_good_of_split hp hp2 hn hpq hAB hs.1 hs.2 hA1 hBA
    · exact exists_good_of_nonsplit hp hp2 hn hpq hAB hA hB hA1 hBA hs
  · exact exists_good_of_not_dvd_sub_one hp hp2 hn hpk h32 hpq hAB hA hB hA1 hBA

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
