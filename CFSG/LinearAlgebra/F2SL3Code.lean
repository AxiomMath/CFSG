module

public import CFSG.LinearAlgebra.F2NatMat
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Adjugate

public section

namespace CFSG.F2NatMat

open Matrix
open scoped MatrixGroups

theorem mulK_lt (n a b : ℕ) : mulK n a b < 2 ^ (n * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show 0 < 2 ^ (0 * 0)
    norm_num
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  have hj : p % n < n := Nat.mod_lt _ hn
  have hi : ¬ p / n < n := fun h => by
    have := idx_lt h hj
    rw [idx_eq] at this
    omega
  rw [← idx_eq (n := n) (p := p), mulK, testBit_mulAux hj, decide_eq_false hi, Bool.false_and]

@[expose] def invTab : ℕ :=
  10917923680927888706888049557473473384599485241734876393804252578545819149360102717975275706039517133754120982307849413025538703271502501893782844134080470862332112873009720998261353670662165718297118989135336490523916519833422809254886205478809246766331613849333218214828036703261474731440857574399136676266165761172256086503121152329171583740481931851916138320837237152674916679652392594871248004922336237367535317127399151392121915449266745399450138437668208910993219969668852075365688961821241178792514715096831533659656258117639614316535083992798869774833787121048773266114639956928072259658861663498313232971786270715397205796357414103894542193714490262327038428199483493873705811133374270603152152047508416419053093194037141100970344203657527081274524195948764412033753928468173453882278854700346125424267328410786292664442728413940671085889697227198345903551456143679478154051208294898933697472116760165231041482124068481123327273926810951513522893283995640438011904125995647539099786582450283202994671798457531059848902301322626725837779245315466871368712562856434192339229468596042695408690857126905403711422750551766606960458933718302158303653437434930409728632565308153714229370706637023344319632462844146239811598834040296344974489512359681506802234082273471239440310860813194913710470235297687446939837421120699591028051145427274459606362026409984

@[expose] def invL (c : ℕ) : ℕ := Nat.land (Nat.shiftRight invTab (Nat.mul 9 c)) 511

theorem invL_lt (c : ℕ) : invL c < 512 := by
  change (invTab >>> (9 * c)) &&& 511 < 512
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem invL_check : allBelow 512 (fun c => !det3K c || eqK 3 (mulK 3 c (invL c)) 273) = true := by
  decide +kernel

theorem dec_mul_invL {c : ℕ} (hc : c < 512) (hd : det3K c = true) :
    dec 3 c * dec 3 (invL c) = 1 := by
  have h := allBelow_spec invL_check c hc
  rw [hd, Bool.not_true, Bool.false_or, ← dec_eq_iff_eqK, dec_mulK] at h
  rw [h, ← dec_oneK]
  rfl

abbrev SL3c : Type := {c : Fin 512 // det3K c.1 = true}

namespace SL3c

@[expose] def toSL (x : SL3c) : SL(3, ZMod 2) :=
  ⟨dec 3 x.1.1, by rw [det_dec3, x.2]; rfl⟩

theorem toSL_val (x : SL3c) : (toSL x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = dec 3 x.1.1 := rfl

theorem toSL_injective : Function.Injective toSL := by
  intro x y h
  have h1 : dec 3 x.1.1 = dec 3 y.1.1 := congrArg Subtype.val h
  have hx : x.1.1 < 2 ^ (3 * 3) := x.1.2
  have hy : y.1.1 < 2 ^ (3 * 3) := y.1.2
  rw [dec_eq_dec_iff, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
  exact Subtype.ext (Fin.ext h1)

theorem det3K_of_det {c : ℕ} (h : (dec 3 c).det = 1) : det3K c = true := by
  rw [det_dec3, ent_eq_one] at h; exact h

instance : One SL3c := ⟨⟨⟨273, by norm_num⟩, by decide⟩⟩

instance : Mul SL3c := ⟨fun x y => ⟨⟨mulK 3 x.1.1 y.1.1, mulK_lt 3 _ _⟩, det3K_of_det (by
  rw [dec_mulK, Matrix.det_mul, ← toSL_val, ← toSL_val, (toSL x).2, (toSL y).2, mul_one])⟩⟩

instance : Inv SL3c := ⟨fun x => ⟨⟨invL x.1.1, invL_lt _⟩, det3K_of_det (by
  have h := congrArg Matrix.det (dec_mul_invL x.1.2 x.2)
  rwa [Matrix.det_mul, ← toSL_val, (toSL x).2, one_mul, Matrix.det_one] at h)⟩⟩

instance : Div SL3c := ⟨fun x y => x * y⁻¹⟩

instance : Pow SL3c ℕ := ⟨fun x n => npowRec n x⟩

instance : Pow SL3c ℤ := ⟨fun x n => zpowRec npowRec n x⟩

theorem toSL_one : toSL 1 = 1 := Subtype.ext (by rw [toSL_val]; decide)

theorem toSL_mul (x y : SL3c) : toSL (x * y) = toSL x * toSL y :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, toSL_val, toSL_val, toSL_val]; exact dec_mulK _ _ _)

theorem toSL_inv (x : SL3c) : toSL x⁻¹ = (toSL x)⁻¹ :=
  eq_inv_of_mul_eq_one_right (Subtype.ext (dec_mul_invL x.1.2 x.2))

theorem toSL_npow (x : SL3c) (n : ℕ) : toSL (x ^ n) = toSL x ^ n := by
  induction n with
  | zero => exact toSL_one
  | succ n ih =>
    change toSL (npowRec n x * x) = _
    rw [toSL_mul, pow_succ]
    exact congrArg (· * toSL x) ih

theorem toSL_zpow (x : SL3c) (n : ℤ) : toSL (x ^ n) = toSL x ^ n := by
  cases n with
  | ofNat n => exact (toSL_npow x n).trans (zpow_natCast _ _).symm
  | negSucc n =>
    change toSL (npowRec (n + 1) x)⁻¹ = _
    rw [toSL_inv, zpow_negSucc]
    exact congrArg (·⁻¹) (toSL_npow x (n + 1))

instance : Group SL3c :=
  toSL_injective.group toSL toSL_one toSL_mul toSL_inv (fun x y => by
    change toSL (x * y⁻¹) = _
    rw [toSL_mul, toSL_inv, div_eq_mul_inv]) toSL_npow toSL_zpow

theorem toSL_surjective : Function.Surjective toSL := by
  intro A
  obtain ⟨c, hc, h⟩ := exists_dec 3 (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hd : det3K c = true := det3K_of_det (by rw [h]; exact A.2)
  exact ⟨⟨⟨c, hc⟩, hd⟩, Subtype.ext h⟩

noncomputable def equiv : SL3c ≃* SL(3, ZMod 2) :=
  MulEquiv.ofBijective (MonoidHom.mk' toSL toSL_mul) ⟨toSL_injective, toSL_surjective⟩

theorem equiv_apply (x : SL3c) : equiv x = toSL x := MulEquiv.ofBijective_apply _ _ x

end SL3c

end CFSG.F2NatMat
