module

public import CFSG.LocalAnalysis.LargeEvenClassification.EndCoordinateTransport

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def RankTwoBinaryResidue (_twist : ZMod 2) :=
  (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

@[expose] def rankTwoBinaryResidueAdd {twist : ZMod 2}
    (first second : RankTwoBinaryResidue twist) : RankTwoBinaryResidue twist :=
  ((first.1.1 + second.1.1, first.1.2 + second.1.2),
    (first.2.1 + second.2.1, first.2.2 + second.2.2))

instance rankTwoBinaryResidueAddInstance (twist : ZMod 2) : Add (RankTwoBinaryResidue twist) :=
  ⟨rankTwoBinaryResidueAdd⟩

instance rankTwoBinaryResidueZero (twist : ZMod 2) : Zero (RankTwoBinaryResidue twist) :=
  ⟨((0, 0), (0, 0))⟩

instance rankTwoBinaryResidueNeg (twist : ZMod 2) : Neg (RankTwoBinaryResidue twist) :=
  ⟨fun x => ((-x.1.1, -x.1.2), (-x.2.1, -x.2.2))⟩

instance rankTwoBinaryResidueOne (twist : ZMod 2) : One (RankTwoBinaryResidue twist) :=
  ⟨((1, 0), (0, 1))⟩

instance rankTwoBinaryResidueFintype (twist : ZMod 2) : Fintype (RankTwoBinaryResidue twist) :=
  inferInstanceAs (Fintype ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)))

instance rankTwoBinaryResidueDecidableEq (twist : ZMod 2) :
    DecidableEq (RankTwoBinaryResidue twist) :=
  inferInstanceAs (DecidableEq ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)))

@[expose] def rankTwoBinaryResidueProduct (twist : ZMod 2)
    (first second : RankTwoBinaryResidue twist) : RankTwoBinaryResidue twist :=
  ((first.1.1 * second.1.1 + twist * first.1.2 * second.2.1,
    first.1.1 * second.1.2 + first.1.2 * second.2.2),
    (first.2.1 * second.1.1 + first.2.2 * second.2.1,
      twist * first.2.1 * second.1.2 + first.2.2 * second.2.2))

instance rankTwoBinaryResidueMul (twist : ZMod 2) : Mul (RankTwoBinaryResidue twist) :=
  ⟨rankTwoBinaryResidueProduct twist⟩

instance rankTwoBinaryResidueRing (twist : ZMod 2) : Ring (RankTwoBinaryResidue twist) :=
  Ring.ofMinimalAxioms
    (by
      intro first second third
      change rankTwoBinaryResidueAdd (rankTwoBinaryResidueAdd first second) third =
        rankTwoBinaryResidueAdd first (rankTwoBinaryResidueAdd second third)
      apply Prod.ext <;> apply Prod.ext <;> simp only [rankTwoBinaryResidueAdd, add_assoc])
    (by
      intro x
      change rankTwoBinaryResidueAdd ((0, 0), (0, 0)) x = x
      apply Prod.ext <;> apply Prod.ext <;> simp only [rankTwoBinaryResidueAdd, zero_add])
    (by
      intro x
      let : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
      change rankTwoBinaryResidueAdd ((-x.1.1, -x.1.2), (-x.2.1, -x.2.2)) x = ((0, 0), (0, 0))
      apply Prod.ext <;> apply Prod.ext <;> simp only [rankTwoBinaryResidueAdd, _root_.neg_add_cancel])
    (by
      intro first second third
      change rankTwoBinaryResidueProduct twist (rankTwoBinaryResidueProduct twist first second) third =
        rankTwoBinaryResidueProduct twist first (rankTwoBinaryResidueProduct twist second third)
      apply Prod.ext <;> apply Prod.ext <;> dsimp only [rankTwoBinaryResidueProduct] <;> ring)
    (by
      intro x
      change rankTwoBinaryResidueProduct twist ((1, 0), (0, 1)) x = x
      apply Prod.ext <;> apply Prod.ext <;> simp [rankTwoBinaryResidueProduct])
    (by
      intro x
      change rankTwoBinaryResidueProduct twist x ((1, 0), (0, 1)) = x
      apply Prod.ext <;> apply Prod.ext <;> simp [rankTwoBinaryResidueProduct])
    (by
      intro first second third
      change rankTwoBinaryResidueProduct twist first (rankTwoBinaryResidueAdd second third) =
        rankTwoBinaryResidueAdd (rankTwoBinaryResidueProduct twist first second)
          (rankTwoBinaryResidueProduct twist first third)
      apply Prod.ext <;> apply Prod.ext <;>
        dsimp only [rankTwoBinaryResidueProduct, rankTwoBinaryResidueAdd] <;> ring)
    (by
      intro first second third
      change rankTwoBinaryResidueProduct twist (rankTwoBinaryResidueAdd first second) third =
        rankTwoBinaryResidueAdd (rankTwoBinaryResidueProduct twist first third)
          (rankTwoBinaryResidueProduct twist second third)
      apply Prod.ext <;> apply Prod.ext <;>
        dsimp only [rankTwoBinaryResidueProduct, rankTwoBinaryResidueAdd] <;> ring)

instance rankTwoBinaryResidueModule (twist : ZMod 2) : Module (ZMod 2) (RankTwoBinaryResidue twist) :=
  inferInstanceAs (Module (ZMod 2) ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)))

@[expose] def residueSquareCommutatorSpan {Residue : Type*} [Ring Residue]
    [Module (ZMod 2) Residue] (W : Submodule (ZMod 2) Residue) : Submodule (ZMod 2) Residue :=
  Submodule.span (ZMod 2) ({z | ∃ x ∈ W, z = x + x * x} ∪
    {z | ∃ x ∈ W, ∃ y ∈ W, z = x * y - y * x})

theorem residue_square_mem_span {Residue : Type*} [Ring Residue]
    [Module (ZMod 2) Residue] (W : Submodule (ZMod 2) Residue) {x : Residue} (hx : x ∈ W) :
    x + x * x ∈ residueSquareCommutatorSpan W :=
  Submodule.subset_span (Or.inl ⟨x, hx, rfl⟩)

theorem residue_commutator_mem_span {Residue : Type*} [Ring Residue]
    [Module (ZMod 2) Residue] (W : Submodule (ZMod 2) Residue)
    {x y : Residue} (hx : x ∈ W) (hy : y ∈ W) :
    x * y - y * x ∈ residueSquareCommutatorSpan W :=
  Submodule.subset_span (Or.inr ⟨x, hx, y, hy, rfl⟩)

theorem rankTwoBinaryResidue_card (twist : ZMod 2) : Nat.card (RankTwoBinaryResidue twist) = 16 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) = 16
  decide

theorem rankTwoBinaryResidue_finrank (twist : ZMod 2) :
    Module.finrank (ZMod 2) (RankTwoBinaryResidue twist) = 4 := by
  have hcard := FiniteField.pow_finrank_eq_natCard 2 (RankTwoBinaryResidue twist)
  rw [rankTwoBinaryResidue_card] at hcard
  change 2 ^ Module.finrank (ZMod 2) (RankTwoBinaryResidue twist) = 2 ^ 4 at hcard
  have hlog := congrArg (Nat.log 2) hcard
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hlog

theorem rankTwoBinaryResidue_idempotent_centralizer_card :
    ∀ (twist : ZMod 2) (x : RankTwoBinaryResidue twist),
      x * x = x → x ≠ 0 → x ≠ 1 →
        Fintype.card {y : RankTwoBinaryResidue twist // x * y = y * x} ≤ 4 := by
  decide

private theorem rankTwoBinaryResidue_two_scalar_card :
    ∀ twist : ZMod 2,
      Fintype.card {x : RankTwoBinaryResidue twist // x = 0 ∨ x = 1} = 2 := by
  decide

private theorem rankTwoBinaryResidue_zero_span_finrank (twist : ZMod 2)
    (W : Submodule (ZMod 2) (RankTwoBinaryResidue twist))
    (hzero : residueSquareCommutatorSpan W = ⊥) : Module.finrank (ZMod 2) W ≤ 2 := by
  by_contra hlarge
  have hcard : 4 < Nat.card W := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 W]
    have hpower := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ Module.finrank (ZMod 2) W by omega)
    norm_num at hpower
    omega
  have hidempotent (x : W) : (x : RankTwoBinaryResidue twist) * x = x := by
    have hsquare := residue_square_mem_span W x.property
    rw [hzero] at hsquare
    have heq : (x : RankTwoBinaryResidue twist) + x * x = 0 := hsquare
    have hneg : -(x : RankTwoBinaryResidue twist) = x := by
      have hbinary : ∀ (t : ZMod 2) (z : RankTwoBinaryResidue t), -z = z := by decide
      exact hbinary twist x
    exact (eq_neg_of_add_eq_zero_right heq).trans hneg
  have hcommute (x y : W) : (x : RankTwoBinaryResidue twist) * y = y * x := by
    have hcommutator := residue_commutator_mem_span W x.property y.property
    rw [hzero] at hcommutator
    exact sub_eq_zero.mp hcommutator
  have hexists : ∃ x : W, (x : RankTwoBinaryResidue twist) ≠ 0 ∧ (x : RankTwoBinaryResidue twist) ≠ 1 := by
    by_contra hnone
    push Not at hnone
    let scalar : W → {x : RankTwoBinaryResidue twist // x = 0 ∨ x = 1} :=
      fun x => ⟨x, by
        by_cases hx : (x : RankTwoBinaryResidue twist) = 0
        · exact Or.inl hx
        · exact Or.inr (hnone x hx)⟩
    have hinjective : Function.Injective scalar := by
      intro x y heq
      apply Subtype.ext
      exact congrArg (fun z => z.val) heq
    have hbound := Nat.card_le_card_of_injective scalar hinjective
    rw [Nat.card_eq_fintype_card (α := {x : RankTwoBinaryResidue twist // x = 0 ∨ x = 1}),
      rankTwoBinaryResidue_two_scalar_card] at hbound
    omega
  obtain ⟨x, hxzero, hxone⟩ := hexists
  let centralize : W → {y : RankTwoBinaryResidue twist // (x : RankTwoBinaryResidue twist) * y = y * x} :=
    fun y => ⟨y, hcommute x y⟩
  have hinjective : Function.Injective centralize := by
    intro y z heq
    apply Subtype.ext
    exact congrArg (fun z => z.val) heq
  have hbound := Nat.card_le_card_of_injective centralize hinjective
  rw [Nat.card_eq_fintype_card (α := {y : RankTwoBinaryResidue twist //
    (x : RankTwoBinaryResidue twist) * y = y * x})] at hbound
  have hcentralizer := rankTwoBinaryResidue_idempotent_centralizer_card twist x
    (hidempotent x) hxzero hxone
  omega

private theorem rankTwoBinaryResidue_top_span_finrank (twist : ZMod 2) :
    2 ≤ Module.finrank (ZMod 2)
      (residueSquareCommutatorSpan (⊤ : Submodule (ZMod 2) (RankTwoBinaryResidue twist))) := by
  let W : Submodule (ZMod 2) (RankTwoBinaryResidue twist) := ⊤
  let C := residueSquareCommutatorSpan W
  let upper : RankTwoBinaryResidue twist := ((0, 1), (0, 0))
  let lower : RankTwoBinaryResidue twist := ((0, 0), (1, 0))
  have hupper : upper + upper * upper = upper := by
    change rankTwoBinaryResidueAdd upper (rankTwoBinaryResidueProduct twist upper upper) = upper
    apply Prod.ext <;> apply Prod.ext <;>
      simp [rankTwoBinaryResidueAdd, rankTwoBinaryResidueProduct, upper]
  have hlower : lower + lower * lower = lower := by
    change rankTwoBinaryResidueAdd lower (rankTwoBinaryResidueProduct twist lower lower) = lower
    apply Prod.ext <;> apply Prod.ext <;>
      simp [rankTwoBinaryResidueAdd, rankTwoBinaryResidueProduct, lower]
  have hupperMem : upper ∈ C := hupper ▸ residue_square_mem_span W (x := upper) (by trivial)
  have hlowerMem : lower ∈ C := hlower ▸ residue_square_mem_span W (x := lower) (by trivial)
  let embed : ZMod 2 × ZMod 2 → C := fun z =>
    ⟨z.1 • upper + z.2 • lower, C.add_mem (C.smul_mem z.1 hupperMem) (C.smul_mem z.2 hlowerMem)⟩
  have hinjective : Function.Injective embed := by
    intro z v heq
    have hcoordinates := congrArg Subtype.val heq
    have hcalculation : ∀ (t : ZMod 2) (z v : ZMod 2 × ZMod 2),
        z.1 • (((0, 1), (0, 0)) : RankTwoBinaryResidue t) + z.2 • ((0, 0), (1, 0)) =
          v.1 • ((0, 1), (0, 0)) + v.2 • ((0, 0), (1, 0)) → z = v := by decide
    exact hcalculation twist z v hcoordinates
  have hbound := Nat.card_le_card_of_injective embed hinjective
  have hfour : Nat.card (ZMod 2 × ZMod 2) = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hfour, ← FiniteField.pow_finrank_eq_natCard 2 C] at hbound
  change 2 ≤ Module.finrank (ZMod 2) C
  by_contra hsmall
  have hpower := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show Module.finrank (ZMod 2) C ≤ 1 by omega)
  norm_num at hpower
  omega

theorem rankTwoBinaryResidue_square_commutator_bound (twist : ZMod 2)
    (W : Submodule (ZMod 2) (RankTwoBinaryResidue twist)) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) + 2 := by
  have hbound := Submodule.finrank_le W
  rw [rankTwoBinaryResidue_finrank] at hbound
  by_cases hfour : Module.finrank (ZMod 2) W = 4
  · have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by
      rw [rankTwoBinaryResidue_finrank]
      exact hfour)
    rw [htop, (Submodule.topEquiv (R := ZMod 2) (M := RankTwoBinaryResidue twist)).finrank_eq,
      rankTwoBinaryResidue_finrank]
    have htwo := rankTwoBinaryResidue_top_span_finrank twist
    omega
  · by_cases hzero : residueSquareCommutatorSpan W = ⊥
    · have hsmall := rankTwoBinaryResidue_zero_span_finrank twist W hzero
      omega
    · have hpositive : Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) ≠ 0 :=
        mt Submodule.finrank_eq_zero.mp hzero
      omega

@[expose] def ringMultipleIdeal (R : Type*) [Ring R] (n : ℕ) : Ideal R where
  carrier := {x | ∃ r : R, x = n • r}
  zero_mem' := ⟨0, (nsmul_zero n).symm⟩
  add_mem' := by
    rintro x y ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨r + s, (nsmul_add r s n).symm⟩
  smul_mem' := by
    rintro a x ⟨r, rfl⟩
    refine ⟨a * r, ?_⟩
    change a * (n • r) = n • (a * r)
    simp only [nsmul_eq_mul]
    calc
      a * ((n : R) * r) = (a * (n : R)) * r := (mul_assoc _ _ _).symm
      _ = ((n : R) * a) * r := by rw [Nat.cast_comm n a]
      _ = (n : R) * (a * r) := mul_assoc _ _ _

instance ringMultipleIdeal_twoSided (R : Type*) [Ring R] (n : ℕ) :
    (ringMultipleIdeal R n).IsTwoSided where
  mul_mem_of_left := by
    rintro x b ⟨r, rfl⟩
    refine ⟨r * b, ?_⟩
    rw [nsmul_eq_mul, nsmul_eq_mul, mul_assoc]

instance ringModuloTwoModule (R : Type*) [Ring R] :
    Module (ZMod 2) (R ⧸ ringMultipleIdeal R 2) :=
  AddCommGroup.zmodModule (fun x => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_nsmul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ⟨r, rfl⟩)

section BinaryCoordinates

variable (scale modulus : ℕ) [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)]
variable (htwo : 2 ∣ modulus)

@[expose] def cyclicPairSmallBinaryReduction : ZMod modulus →+* ZMod 2 :=
  ZMod.castHom htwo (ZMod 2)

@[expose] def cyclicPairLargeBinaryReduction : ZMod (scale * modulus) →+* ZMod 2 :=
  ZMod.castHom (htwo.trans (dvd_mul_left modulus scale)) (ZMod 2)

omit [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)] in
theorem cyclicPairLargeBinaryReduction_factor (x : ZMod (scale * modulus)) :
    cyclicPairSmallBinaryReduction modulus htwo (cyclicReduction scale modulus x) =
      cyclicPairLargeBinaryReduction scale modulus htwo x := by
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((cyclicPairSmallBinaryReduction modulus htwo).comp (cyclicReduction scale modulus))
    (cyclicPairLargeBinaryReduction scale modulus htwo)) x

omit [NeZero scale] [NeZero (scale * modulus)] in
theorem cyclicPairLargeBinaryReduction_inclusion (x : ZMod modulus) :
    cyclicPairLargeBinaryReduction scale modulus htwo (scaledCyclicInclusion scale modulus x) =
      (scale : ZMod 2) * cyclicPairSmallBinaryReduction modulus htwo x := by
  rw [scaledCyclicInclusion_apply, map_mul, map_natCast, map_natCast]
  congr 1
  exact ((congrArg (cyclicPairSmallBinaryReduction modulus htwo)
    (ZMod.natCast_zmod_val x).symm).trans (map_natCast _ _)).symm

@[expose] def cyclicPairBinaryCoefficientResidue (c : CyclicPairCoefficients scale modulus) :
    RankTwoBinaryResidue (scale : ZMod 2) :=
  ((cyclicPairLargeBinaryReduction scale modulus htwo c.1.1,
    cyclicPairSmallBinaryReduction modulus htwo c.1.2),
    (cyclicPairSmallBinaryReduction modulus htwo c.2.1,
      cyclicPairSmallBinaryReduction modulus htwo c.2.2))

@[expose] noncomputable def cyclicPairEndBinaryResidueHom :
    AddMonoid.End (CyclicPair scale modulus) →+* RankTwoBinaryResidue (scale : ZMod 2) where
  toFun := fun f => cyclicPairBinaryCoefficientResidue scale modulus htwo
    (cyclicPairEndCoefficients scale modulus f)
  map_zero' := by
    rw [cyclicPairEndCoefficients_zero]
    change ((_, _), (_, _)) = ((0, 0), (0, 0))
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
  map_one' := by
    rw [cyclicPairEndCoefficients_one]
    change ((_, _), (_, _)) = ((1, 0), (0, 1))
    simp only [map_zero, map_one]
  map_add' := by
    intro first second
    rw [cyclicPairEndCoefficients_add]
    change cyclicPairBinaryCoefficientResidue scale modulus htwo (_ + _) =
      rankTwoBinaryResidueAdd _ _
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [cyclicPairBinaryCoefficientResidue, rankTwoBinaryResidueAdd,
        Prod.fst_add, Prod.snd_add, map_add]
  map_mul' := by
    intro first second
    rw [cyclicPairEndCoefficients_mul]
    change cyclicPairBinaryCoefficientResidue scale modulus htwo (cyclicPairCoefficientProduct _ _ _ _) =
      rankTwoBinaryResidueProduct _ _ _
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [cyclicPairBinaryCoefficientResidue, cyclicPairCoefficientProduct,
        rankTwoBinaryResidueProduct, map_add, map_mul, map_natCast,
        cyclicPairLargeBinaryReduction_inclusion, cyclicPairLargeBinaryReduction_factor, mul_assoc]

omit [NeZero scale] [NeZero (scale * modulus)] in
theorem zmod_binary_reduction_zero (x : ZMod modulus) :
    cyclicPairSmallBinaryReduction modulus htwo x = 0 ↔
      ∃ r : ZMod modulus, x = 2 • r := by
  constructor
  · intro hzero
    have hcast : (x.val : ZMod 2) = 0 := by
      calc
        _ = cyclicPairSmallBinaryReduction modulus htwo (x.val : ZMod modulus) :=
          (map_natCast _ _).symm
        _ = 0 := by rw [ZMod.natCast_zmod_val, hzero]
    have hdivides : 2 ∣ x.val := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    refine ⟨(x.val / 2 : ℕ), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdivides, ZMod.natCast_zmod_val]
  · rintro ⟨r, rfl⟩
    rw [map_nsmul, nsmul_eq_mul]
    have htwoZero : (2 : ZMod 2) = 0 := by decide
    rw [Nat.cast_ofNat, htwoZero, zero_mul]

theorem cyclicPairEndBinaryResidueHom_zero (f : AddMonoid.End (CyclicPair scale modulus)) :
    cyclicPairEndBinaryResidueHom scale modulus htwo f = 0 ↔
      f ∈ ringMultipleIdeal (AddMonoid.End (CyclicPair scale modulus)) 2 := by
  constructor
  · intro hzero
    let c := cyclicPairEndCoefficients scale modulus f
    have hc : cyclicPairBinaryCoefficientResidue scale modulus htwo c = ((0, 0), (0, 0)) := hzero
    obtain ⟨a, ha⟩ := (zmod_binary_reduction_zero (scale * modulus)
      (htwo.trans (dvd_mul_left modulus scale)) c.1.1).mp
      (congrArg (fun z : RankTwoBinaryResidue (scale : ZMod 2) => z.1.1) hc)
    obtain ⟨b, hb⟩ := (zmod_binary_reduction_zero modulus htwo c.1.2).mp
      (congrArg (fun z : RankTwoBinaryResidue (scale : ZMod 2) => z.1.2) hc)
    obtain ⟨d, hd⟩ := (zmod_binary_reduction_zero modulus htwo c.2.1).mp
      (congrArg (fun z : RankTwoBinaryResidue (scale : ZMod 2) => z.2.1) hc)
    obtain ⟨e, he⟩ := (zmod_binary_reduction_zero modulus htwo c.2.2).mp
      (congrArg (fun z : RankTwoBinaryResidue (scale : ZMod 2) => z.2.2) hc)
    refine ⟨cyclicPairEndFromCoefficients scale modulus ((a, b), (d, e)), ?_⟩
    apply cyclicPairEndCoefficients_injective scale modulus
    rw [cyclicPairEndCoefficients_nsmul, cyclicPairEndCoefficients_from]
    change c = 2 • ((a, b), (d, e))
    apply Prod.ext <;> apply Prod.ext
    · exact ha
    · exact hb
    · exact hd
    · exact he
  · rintro ⟨r, rfl⟩
    rw [map_nsmul]
    have hzero : ∀ (t : ZMod 2) (x : RankTwoBinaryResidue t), 2 • x = 0 := by decide
    exact hzero _ _

theorem cyclicPairEndBinaryResidueHom_surjective :
    Function.Surjective (cyclicPairEndBinaryResidueHom scale modulus htwo) := by
  intro c
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective (htwo.trans (dvd_mul_left modulus scale)) c.1.1
  obtain ⟨b, hb⟩ := ZMod.castHom_surjective htwo c.1.2
  obtain ⟨d, hd⟩ := ZMod.castHom_surjective htwo c.2.1
  obtain ⟨e, he⟩ := ZMod.castHom_surjective htwo c.2.2
  refine ⟨cyclicPairEndFromCoefficients scale modulus ((a, b), (d, e)), ?_⟩
  change cyclicPairBinaryCoefficientResidue scale modulus htwo
    (cyclicPairEndCoefficients scale modulus (cyclicPairEndFromCoefficients scale modulus _)) = c
  rw [cyclicPairEndCoefficients_from]
  apply Prod.ext <;> apply Prod.ext
  · exact ha
  · exact hb
  · exact hd
  · exact he

noncomputable def cyclicPairEndBinaryResidueEquiv :
    (AddMonoid.End (CyclicPair scale modulus) ⧸
      ringMultipleIdeal (AddMonoid.End (CyclicPair scale modulus)) 2) ≃+*
        RankTwoBinaryResidue (scale : ZMod 2) :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift _ (cyclicPairEndBinaryResidueHom scale modulus htwo)
      (fun f hf => (cyclicPairEndBinaryResidueHom_zero scale modulus htwo f).mpr hf))
    ⟨(Ideal.injective_lift_iff _).mpr (by
      ext f
      exact cyclicPairEndBinaryResidueHom_zero scale modulus htwo f), by
      intro c
      obtain ⟨f, hf⟩ := cyclicPairEndBinaryResidueHom_surjective scale modulus htwo c
      exact ⟨Ideal.Quotient.mk _ f, hf⟩⟩

end BinaryCoordinates

@[expose] noncomputable def ringEquivBinaryLinearEquiv {R S : Type*} [Ring R] [Ring S]
    [Module (ZMod 2) R] [Module (ZMod 2) S] (f : R ≃+* S) : R ≃ₗ[ZMod 2] S :=
  LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap 2) f.bijective

theorem ringEquivBinaryLinearEquiv_apply {R S : Type*} [Ring R] [Ring S]
    [Module (ZMod 2) R] [Module (ZMod 2) S] (f : R ≃+* S) (x : R) :
    ringEquivBinaryLinearEquiv f x = f x := rfl

theorem residueSquareCommutatorSpan_map_le {R S : Type*} [Ring R] [Ring S]
    [Module (ZMod 2) R] [Module (ZMod 2) S] (f : R ≃+* S) (W : Submodule (ZMod 2) R) :
    residueSquareCommutatorSpan (W.map (ringEquivBinaryLinearEquiv f).toLinearMap) ≤
      (residueSquareCommutatorSpan W).map (ringEquivBinaryLinearEquiv f).toLinearMap := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, rfl⟩
  · obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨r + r * r, residue_square_mem_span W hr, ?_⟩
    change f (r + r * r) = f r + f r * f r
    rw [map_add, map_mul]
  · obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hy
    apply Submodule.mem_map.mpr
    refine ⟨r * s - s * r, residue_commutator_mem_span W hr hs, ?_⟩
    change f (r * s - s * r) = f r * f s - f s * f r
    rw [map_sub, map_mul, map_mul]

theorem residue_square_commutator_bound_of_rank_two_equiv {R : Type*} [Ring R]
    [Module (ZMod 2) R] {twist : ZMod 2} (f : R ≃+* RankTwoBinaryResidue twist)
    (W : Submodule (ZMod 2) R) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) + 2 := by
  let e := ringEquivBinaryLinearEquiv f
  have hmodel := rankTwoBinaryResidue_square_commutator_bound twist (W.map e.toLinearMap)
  have hle := Submodule.finrank_mono (residueSquareCommutatorSpan_map_le f W)
  rw [e.finrank_map_eq] at hmodel
  rw [e.finrank_map_eq] at hle
  exact hmodel.trans (Nat.add_le_add_right hle 2)

section NativeEndomorphisms

variable {Abelian : Type*} [AddCommGroup Abelian]
variable (scale modulus : ℕ) [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)]
variable (htwo : 2 ∣ modulus) (coordinates : Abelian ≃+ CyclicPair scale modulus)

@[expose] noncomputable def abelianEndBinaryResidueHom :
    AddMonoid.End Abelian →+* RankTwoBinaryResidue (scale : ZMod 2) :=
  (cyclicPairEndBinaryResidueHom scale modulus htwo).comp
    (addEndCoordinateTransport coordinates).toRingHom

theorem abelianEndBinaryResidueHom_zero (f : AddMonoid.End Abelian) :
    abelianEndBinaryResidueHom scale modulus htwo coordinates f = 0 ↔
      f ∈ ringMultipleIdeal (AddMonoid.End Abelian) 2 := by
  let e := addEndCoordinateTransport coordinates
  change cyclicPairEndBinaryResidueHom scale modulus htwo (e f) = 0 ↔ _
  rw [cyclicPairEndBinaryResidueHom_zero]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨e.symm r, ?_⟩
    have h := congrArg e.symm hr
    simpa only [e.symm_apply_apply, map_nsmul] using h
  · rintro ⟨r, rfl⟩
    exact ⟨e r, map_nsmul e 2 r⟩

theorem abelianEndBinaryResidueHom_surjective :
    Function.Surjective (abelianEndBinaryResidueHom scale modulus htwo coordinates) :=
  (cyclicPairEndBinaryResidueHom_surjective scale modulus htwo).comp
    (addEndCoordinateTransport coordinates).surjective

noncomputable def abelianEndBinaryResidueEquiv :
    (AddMonoid.End Abelian ⧸ ringMultipleIdeal (AddMonoid.End Abelian) 2) ≃+*
      RankTwoBinaryResidue (scale : ZMod 2) :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift _ (abelianEndBinaryResidueHom scale modulus htwo coordinates)
      (fun f hf => (abelianEndBinaryResidueHom_zero scale modulus htwo coordinates f).mpr hf))
    ⟨(Ideal.injective_lift_iff _).mpr (by
      ext f
      exact abelianEndBinaryResidueHom_zero scale modulus htwo coordinates f), by
      intro c
      obtain ⟨f, hf⟩ := abelianEndBinaryResidueHom_surjective scale modulus htwo coordinates c
      exact ⟨Ideal.Quotient.mk _ f, hf⟩⟩

include htwo coordinates in
theorem abelian_endomorphism_residue_square_commutator_bound
    (W : Submodule (ZMod 2)
      (AddMonoid.End Abelian ⧸ ringMultipleIdeal (AddMonoid.End Abelian) 2)) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) + 2 :=
  residue_square_commutator_bound_of_rank_two_equiv
    (abelianEndBinaryResidueEquiv scale modulus htwo coordinates) W

end NativeEndomorphisms

theorem rank_two_endomorphism_residue_square_commutator_bound
    {Abelian : Type*} [AddCommGroup Abelian] (upper lower : ℕ)
    (hle : lower ≤ upper) (hlower : 1 ≤ lower)
    (coordinates : Abelian ≃+ (ZMod (2 ^ upper) × ZMod (2 ^ lower)))
    (W : Submodule (ZMod 2)
      (AddMonoid.End Abelian ⧸ ringMultipleIdeal (AddMonoid.End Abelian) 2)) :
    Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) ≥ Module.finrank (ZMod 2) W - 2 := by
  have hperiod : 2 ^ (upper - lower) * 2 ^ lower = 2 ^ upper := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  let coordinates' : Abelian ≃+ CyclicPair (2 ^ (upper - lower)) (2 ^ lower) := by
    change Abelian ≃+ (ZMod (2 ^ (upper - lower) * 2 ^ lower) × ZMod (2 ^ lower))
    rw [hperiod]
    exact coordinates
  have htwo : 2 ∣ 2 ^ lower := dvd_pow_self 2 (by omega : lower ≠ 0)
  have hbound := abelian_endomorphism_residue_square_commutator_bound
    (2 ^ (upper - lower)) (2 ^ lower) htwo coordinates' W
  omega

end CFSG.LargeEvenClassification.Helpers
