module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
import CFSG.RankThree.PartOne.KC.CommonEigenbasis
import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
import CFSG.Timmesfeld.RankOne.SL2
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Polynomial Module
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary CFSG.RankThree.CALinearPlane

private theorem linCore_basis_char {G E W : Type*} [Group G] [Finite G] [Field E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] {ζ : E} (hζ : IsPrimitiveRoot ζ 3)
    (φ : G →* Module.End E W) (hc : ∀ y z, Commute (φ y) (φ z)) (h3 : ∀ y, φ y ^ 3 = 1) :
    ∃ (bs : Basis (Fin (finrank E W)) E W) (χ : Fin (finrank E W) → G →* E),
      ∀ y j, φ y (bs j) = χ j y • bs j := by
  obtain ⟨bs, μ, hμ⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ (fun y => φ y) hc h3
  have hμ' : ∀ y j, φ y (bs j) = μ y j • bs j := hμ
  have hinj : ∀ j, Function.Injective fun c : E => c • bs j :=
    fun j => smul_left_injective E (bs.ne_zero j)
  refine ⟨bs, fun j => ⟨⟨fun y => μ y j, hinj j ?_⟩, fun y z => hinj j ?_⟩, hμ'⟩
  · show μ 1 j • bs j = (1 : E) • bs j
    rw [← hμ', map_one, one_smul, Module.End.one_apply]
  · show μ (y * z) j • bs j = (μ y j * μ z j) • bs j
    rw [← hμ', map_mul, Module.End.mul_apply, hμ' z, map_smul, hμ' y, smul_smul, mul_comm]

private theorem linCore_embed {F : Type} [Field F] {n : ℕ}
    {g : Matrix.SpecialLinearGroup (Fin n) F}
    (hsq : Squarefree (minpoly F (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)))) {a : F[X]}
    (ha : a ∈ primaryFactors (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F))) {m : ℕ}
    (bs : Basis (Fin m) (AdjoinRoot a)
      (primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a)) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot a) →* Matrix.SpecialLinearGroup (Fin n) F,
      Function.Injective σ ∧
      (∀ Z (v : primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a),
        Matrix.toLin' (σ Z : Matrix (Fin n) (Fin n) F) v =
          ((Matrix.toLin bs bs (Z : Matrix (Fin m) (Fin m) (AdjoinRoot a)) v :
            primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a) : Fin n → F)) ∧
      ∀ Z, ∀ b ∈ primaryFactors (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)), b ≠ a →
        ∀ v ∈ primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) b,
          Matrix.toLin' (σ Z : Matrix (Fin n) (Fin n) F) v = v := by
  classical
  let L := linearSpecialBlock (slGL n F g) a
  let e₁ : L ≃* _root_.SpecialLinearGroup (AdjoinRoot a)
      (primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a) :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict (slGL n F g) a)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq ha⟩
  have hmap : (L.comap (slGL n F)).map (slGL n F) = L := by
    rw [Subgroup.map_comap_eq, inf_eq_right]
    exact linearSpecialBlock_le_range_slGL hsq ha
  let eH := (Subgroup.equivMapOfInjective _ (slGL n F) slGL_injective).trans
    (MulEquiv.subgroupCongr hmap)
  let σ' := ((Matrix.SpecialLinearGroup.toLin_equiv bs).trans e₁.symm).trans eH.symm
  have hσ : ∀ Z, slGL n F (σ' Z : Matrix.SpecialLinearGroup (Fin n) F) =
      (e₁.symm (Matrix.SpecialLinearGroup.toLin_equiv bs Z) :
        LinearMap.GeneralLinearGroup F (Fin n → F)) :=
    fun Z => congrArg Subtype.val (eH.apply_symm_apply _)
  have hσv := fun Z v => congrArg
    (fun u : LinearMap.GeneralLinearGroup F (Fin n → F) => (u : Module.End F (Fin n → F)) v) (hσ Z)
  refine ⟨(L.comap (slGL n F)).subtype.comp σ'.toMonoidHom,
    (L.comap (slGL n F)).subtype_injective.comp σ'.injective, fun Z v => (hσv Z v).trans ?_,
    fun Z b hb hba v hv => (hσv Z v).trans ((e₁.symm _).2.2.1 b hb hba v hv)⟩
  exact congrArg (fun u : _root_.SpecialLinearGroup (AdjoinRoot a)
    (primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a) =>
      (u.1 v : Fin n → F)) (e₁.apply_symm_apply _)

private theorem linCore_sl2 {E : Type*} [Field E] [Finite E] [CharP E 2] {ζ : E}
    (hζ : IsPrimitiveRoot ζ 3) {k : ℕ} (hk : k = 2) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin k) E) ∧
      (∃ u w : Matrix.SpecialLinearGroup (Fin k) E, u * w ≠ w * u) ∧
      3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) E) := by
  subst hk
  have : Fintype E := Fintype.ofFinite E
  have h4 : 4 ≤ Nat.card E := by
    have h1 := hζ.dvd_of_pow_eq_one _
      (FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero (by norm_num)))
    have h2 : 1 < Fintype.card E := Fintype.one_lt_card_iff_nontrivial.2 inferInstance
    rw [Nat.card_eq_fintype_card]; omega
  refine ⟨?_, ⟨CFSG.Timmesfeld.RankOne.upperElt E 1, CFSG.Timmesfeld.RankOne.lowerElt E 1,
    fun h => ?_⟩, ?_⟩
  · haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (CFSG.Timmesfeld.RankOne.psl2EquivSL2 E).symm.isSimpleGroup
  · have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) E =>
      (g : Matrix (Fin 2) (Fin 2) E) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    simp [CFSG.Timmesfeld.RankOne.upperElt, CFSG.Timmesfeld.RankOne.lowerElt, Matrix.mul_apply,
      Fin.sum_univ_two] at this
  · have h6 : (ζ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    let t : Matrix.SpecialLinearGroup (Fin 2) E := ⟨Matrix.diagonal ![ζ, ζ ^ 2], by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp [← pow_succ', hζ.pow_eq_one]⟩
    have ht3 : t ^ 3 = 1 := by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_pow]
      change (Matrix.diagonal ![ζ, ζ ^ 2] ^ 3) i j = _
      rw [Matrix.diagonal_pow]
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hζ.pow_eq_one, h6]
    have ht1 : t ≠ 1 := fun h => hζ.ne_one (by norm_num) (by
      simpa [t] using congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) E =>
        (g : Matrix (Fin 2) (Fin 2) E) 0 0) h)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← orderOf_eq_prime ht3 ht1]
    exact orderOf_dvd_natCard t

theorem SG.exists_sl2_of_primaryBlock {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {Bt : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)} (hB3 : ∀ y ∈ Bt, y ^ 3 = 1)
    (hBc : ∀ y ∈ Bt, ∀ z ∈ Bt, y * z = z * y) {g d : Matrix.SpecialLinearGroup (Fin n) F}
    (hg : g ∈ Bt) (hd : d ∈ Bt) {a : F[X]}
    (ha : a ∈ primaryFactors (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)))
    (hm : 2 ≤ primaryMultiplicity (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a)
    {ζ : AdjoinRoot a} (hζ : IsPrimitiveRoot ζ 3) (c : AdjoinRoot a)
    (hc : ∀ v : primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a,
      Matrix.toLin' (d : Matrix (Fin n) (Fin n) F) v =
        ((c • v : primaryComponent (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) a) :
          Fin n → F)) :
    ∃ A Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) F), IsSimpleGroup A ∧
      (∃ u w : A, u * w ≠ w * u) ∧ 3 ∣ Nat.card A ∧ Y ≤ Bt ∧ d ∈ Y ∧ Y.relIndex Bt ≤ 3 ∧
      ∀ y ∈ Y, ∀ z ∈ A, y * z = z * y := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  haveI : Finite (AdjoinRoot a) := Module.finite_of_finite F
  haveI : CharP (AdjoinRoot a) 2 := charP_of_injective_algebraMap (algebraMap F _).injective 2
  set T := Matrix.toLin' (g : Matrix (Fin n) (Fin n) F) with hT
  set W := primaryComponent T a with hW
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hsq : Squarefree (minpoly F T) := squarefree_minpoly_slGL (p := 3)
    (by rw [Nat.cast_ofNat, show (3 : F) = 2 + 1 by norm_num, h2, zero_add]; exact one_ne_zero)
    (hB3 g hg)
  have hcT : ∀ y ∈ Bt, Commute (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F)) T := fun y hy =>
    (commute_iff_eq _ _).2 (LinearMap.ext fun v => by
      simp only [hT, Module.End.mul_apply, ← Matrix.toLin'_mul_apply,
        ← Matrix.SpecialLinearGroup.coe_mul, hBc y hy g hg])
  let φ : Bt →* Module.End (AdjoinRoot a) W :=
    { toFun := fun y => commutantRestrict a ⟨_, (mem_commutant T).2 (hcT y y.2)⟩
      map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
      map_mul' := fun y z => LinearMap.ext fun v => Subtype.ext (by
        simp [Matrix.toLin'_mul_apply]) }
  have hy3 : ∀ y : Bt, y ^ 3 = 1 := fun y => Subtype.ext (by simpa using hB3 _ y.2)
  obtain ⟨bs, χ, hχ⟩ := linCore_basis_char hζ φ (fun y z => by
    rw [commute_iff_eq, ← map_mul, ← map_mul,
      show y * z = z * y from Subtype.ext (hBc _ y.2 _ z.2)]) fun y => by
    rw [← map_pow, hy3, map_one]
  obtain ⟨σ, hσi, hσW, hσO⟩ := linCore_embed hsq ha bs
  have hm' : 2 ≤ finrank (AdjoinRoot a) W := hm
  let j0 : Fin (finrank (AdjoinRoot a) W) := ⟨0, by omega⟩
  let j1 : Fin (finrank (AdjoinRoot a) W) := ⟨1, by omega⟩
  have hj01 : j0 ≠ j1 := fun h => absurd (congrArg Fin.val h) (by simp [j0, j1])
  have hχ3 : ∀ j y, χ j y ^ 3 = 1 := fun j y => by rw [← map_pow, hy3, map_one]
  let ψ : Bt →* AdjoinRoot a := χ j0 * χ j1 * χ j1
  have hker : ∀ y : Bt, y ∈ ψ.toHomUnits.ker ↔ χ j0 y = χ j1 y := fun y => by
    rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one]
    simp only [ψ, MonoidHom.mul_apply]
    exact ⟨fun h => by linear_combination (-(χ j0 y)) * hχ3 j1 y + χ j1 y * h,
      fun h => by rw [h]; linear_combination hχ3 j1 y⟩
  have hχd : ∀ j, χ j ⟨d, hd⟩ = c := fun j => smul_left_injective (AdjoinRoot a) (bs.ne_zero j)
    (Subtype.ext ((congrArg Subtype.val (hχ ⟨d, hd⟩ j)).symm.trans (hc (bs j))))
  have hYK : (ψ.toHomUnits.ker.map Bt.subtype).subgroupOf Bt = ψ.toHomUnits.ker :=
    Subgroup.comap_map_eq_self_of_injective Bt.subtype_injective _
  have hidx : (ψ.toHomUnits.ker.map Bt.subtype).relIndex Bt ≤ 3 := by
    rw [Subgroup.relIndex, hYK, Subgroup.index_ker]
    refine le_trans (Subgroup.card_le_of_le (K := rootsOfUnity 3 (AdjoinRoot a)) ?_)
      (card_rootsOfUnity _ _)
    rintro _ ⟨y, rfl⟩
    rw [mem_rootsOfUnity', MonoidHom.coe_toHomUnits]
    simp only [ψ, MonoidHom.mul_apply]
    rw [mul_pow, mul_pow, hχ3, hχ3, one_mul, one_mul]
  let J : Finset (Fin (finrank (AdjoinRoot a) W)) := {j0, j1}
  have hρ : Function.Injective (σ.comp (blockSLOn (AdjoinRoot a) J)) :=
    hσi.comp (blockSLOn_injective J)
  let eA := MonoidHom.ofInjective hρ
  obtain ⟨hs, ⟨u, w, huw⟩, h3⟩ := linCore_sl2 hζ (k := J.card) (Finset.card_pair hj01)
  haveI := hs
  refine ⟨_, _, eA.symm.isSimpleGroup, ⟨eA u, eA w, fun h => huw (eA.injective (by
    rw [map_mul, map_mul]; exact h))⟩, (Nat.card_congr eA.toEquiv) ▸ h3,
    Subgroup.map_subtype_le _, ⟨⟨d, hd⟩, (hker _).2 ((hχd j0).trans (hχd j1).symm), rfl⟩, hidx,
    ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨X, rfl⟩
  have hJχ : ∀ i ∈ J, χ i y = χ j0 y := fun i hi => (Finset.mem_insert.1 hi).elim
    (fun h => h ▸ rfl) fun h => by rw [Finset.mem_singleton.1 h, (hker y).1 hy]
  set N := blockSLOn (AdjoinRoot a) J X with hN
  have hEc : (φ y).comp (Matrix.toLin bs bs (N : Matrix _ _ (AdjoinRoot a))) =
      (Matrix.toLin bs bs (N : Matrix _ _ (AdjoinRoot a))).comp (φ y) := by
    refine bs.ext fun j => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin_self, map_sum, map_smul, hχ, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    by_cases hij : i ∈ J ∧ j ∈ J
    · rw [hJχ i hij.1, hJχ j hij.2, mul_comm]
    · rw [hN, coe_blockSLOn, blockOn_apply_not_mem J _ (not_and_or.1 hij)]
      split_ifs with h <;> simp [h]
  apply slGL_injective (n := n) (k := F)
  rw [map_mul, map_mul]
  refine Units.ext (ext_primaryComponent hsq fun b hb v hv => ?_)
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  change Matrix.toLin' (y : Matrix (Fin n) (Fin n) F) (Matrix.toLin' (σ N : Matrix _ _ F) v) =
    Matrix.toLin' (σ N : Matrix _ _ F) (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F) v)
  by_cases hba : b = a
  · have hv' : v ∈ W := by rw [hW, ← hba]; exact hv
    have e1 : Matrix.toLin' (σ N : Matrix (Fin n) (Fin n) F) v =
        ((Matrix.toLin bs bs (N : Matrix _ _ (AdjoinRoot a)) ⟨v, hv'⟩ : W) : Fin n → F) :=
      hσW N ⟨v, hv'⟩
    rw [e1]
    exact (congrArg (fun f => ((f ⟨v, hv'⟩ : W) : Fin n → F)) hEc).trans
      (hσW N (φ y ⟨v, hv'⟩)).symm
  · rw [hσO N b hb hba v hv,
      hσO N b hb hba _ (apply_mem_primaryComponent (hcT y y.2) hv)]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
