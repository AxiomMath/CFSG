module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoLift
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoHeisNF
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoCube
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveToralBasis
public import CFSG.RankThree.Classical2.CentralLiftCommutator
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveToral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoFactor
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoWeyl
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Timmesfeld.Steinberg
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Lifts

variable {L : Type} [Field L]

theorem lift_mul (Y U Y' U' : SL(5, L)) :
    (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      rhoSigmaE8A4 L e8VA (Y * Y') * rhoSigmaE8A4 L e8VB (U * U') := by
  have h := (rhoA_commute_rhoB Y' U).eq
  calc (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U')
      = rhoSigmaE8A4 L e8VA Y * (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U) *
        rhoSigmaE8A4 L e8VB U' := by rw [h]; group
    _ = rhoSigmaE8A4 L e8VA (Y * Y') * rhoSigmaE8A4 L e8VB (U * U') := by
      rw [map_mul, map_mul]; group

theorem lift_comm_iff {Y U Y' U' : SL(5, L)}
    (h : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)) :
    Y * Y' = Y' * Y ↔ U * U' = U' * U := by
  rw [lift_mul, lift_mul] at h
  constructor
  · intro hY
    rw [hY] at h
    exact rhoSigmaE8A4_injective (L := L) e8VB (mul_left_cancel h)
  · intro hU
    rw [hU] at h
    exact rhoSigmaE8A4_injective (L := L) e8VA (mul_right_cancel h)

theorem comm_lift_product_eq_one {Y U Y' U' : SL(5, L)}
    (h : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)) :
    rhoSigmaE8A4 L e8VA (Y * Y' * (Y' * Y)⁻¹) *
      rhoSigmaE8A4 L e8VB (U * U' * (U' * U)⁻¹) = 1 := by
  let f := (rhoSigmaE8A4 L e8VA).noncommCoprod
    (rhoSigmaE8A4 L e8VB) rhoA_commute_rhoB
  have h' : f ((Y, U) * (Y', U')) = f ((Y', U') * (Y, U)) := by
    simpa only [map_mul, f, MonoidHom.noncommCoprod_apply] using h
  have heq : f (((Y, U) * (Y', U')) * ((Y', U') * (Y, U))⁻¹) = 1 := by
    rw [map_mul, map_inv, h', mul_inv_cancel]
  exact heq

theorem comm_lift_B_eq_of_A_eq {Y U Y' U' V W V' W' : SL(5, L)}
    (h : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U))
    (h' : (rhoSigmaE8A4 L e8VA V * rhoSigmaE8A4 L e8VB W) *
        (rhoSigmaE8A4 L e8VA V' * rhoSigmaE8A4 L e8VB W') =
      (rhoSigmaE8A4 L e8VA V' * rhoSigmaE8A4 L e8VB W') *
        (rhoSigmaE8A4 L e8VA V * rhoSigmaE8A4 L e8VB W))
    (hA : Y * Y' * (Y' * Y)⁻¹ = V * V' * (V' * V)⁻¹) :
    U * U' * (U' * U)⁻¹ = W * W' * (W' * W)⁻¹ := by
  have hc := comm_lift_product_eq_one h
  have hc' := comm_lift_product_eq_one h'
  rw [hA] at hc
  exact rhoSigmaE8A4_injective (L := L) e8VB (mul_left_cancel (hc.trans hc'.symm))

theorem comm_lift_scalar {Y U Y' U' : SL(5, L)}
    (h : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)) :
    (∃ κ : L, ((Y * Y' * (Y' * Y)⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = κ • 1) ∧
      ∃ κ : L, ((U * U' * (U' * U)⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = κ • 1 := by
  exact scalar_of_rho_mul_eq_one (comm_lift_product_eq_one h)

end Lifts

section Tw

variable {L : Type} [Field L]

@[expose] def Tw (κ : L) (x y : Matrix (Fin 5) (Fin 5) L) : Prop := x * y = κ • (y * x)

theorem Tw.pow_right {κ : L} {x y : Matrix (Fin 5) (Fin 5) L} (h : Tw κ x y) (n : ℕ) :
    Tw (κ ^ n) x (y ^ n) := CFSG.LieType.SeitzGeneration.mat_mul_pow_eq_smul h n

theorem Tw.mul_right {κ κ' : L} {x y z : Matrix (Fin 5) (Fin 5) L} (h : Tw κ x y)
    (h' : Tw κ' x z) : Tw (κ * κ') x (y * z) := by
  unfold Tw at *
  calc x * (y * z) = (x * y) * z := by rw [Matrix.mul_assoc]
    _ = (κ • (y * x)) * z := by rw [h]
    _ = κ • (y * (x * z)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
    _ = κ • (y * (κ' • (z * x))) := by rw [h']
    _ = (κ * κ') • ((y * z) * x) := by
      rw [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]

theorem Tw.mul_left {κ κ' : L} {x y z : Matrix (Fin 5) (Fin 5) L} (h : Tw κ x z)
    (h' : Tw κ' y z) : Tw (κ * κ') (x * y) z := by
  unfold Tw at *
  calc (x * y) * z = x * (y * z) := by rw [Matrix.mul_assoc]
    _ = x * (κ' • (z * y)) := by rw [h']
    _ = κ' • ((x * z) * y) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = κ' • ((κ • (z * x)) * y) := by rw [h]
    _ = (κ * κ') • (z * (x * y)) := by
      rw [Matrix.smul_mul, smul_smul, mul_comm κ' κ, Matrix.mul_assoc]

theorem Tw.symm {κ : L} (hκ : κ ≠ 0) {x y : Matrix (Fin 5) (Fin 5) L} (h : Tw κ x y) :
    Tw κ⁻¹ y x := by
  unfold Tw at *
  rw [h, smul_smul, inv_mul_cancel₀ hκ, one_smul]

theorem Tw.pow_left {κ : L} (hκ : κ ≠ 0) {x y : Matrix (Fin 5) (Fin 5) L} (h : Tw κ x y)
    (n : ℕ) : Tw (κ ^ n) (x ^ n) y := by
  have h1 := (h.symm hκ).pow_right n
  have h2 := h1.symm (pow_ne_zero n (inv_ne_zero hκ))
  rwa [inv_pow, inv_inv] at h2

theorem Tw.one_of_commute {x y : Matrix (Fin 5) (Fin 5) L} (h : x * y = y * x) : Tw 1 x y := by
  unfold Tw
  rw [h, one_smul]

theorem Tw.commute_of_one {x y : Matrix (Fin 5) (Fin 5) L} (h : Tw 1 x y) : x * y = y * x := by
  unfold Tw at h
  rwa [one_smul] at h

theorem Tw.power_products {κ : L} (hκ : κ ≠ 0) {x y : Matrix (Fin 5) (Fin 5) L}
    (h : Tw κ x y) (a b c d : ℕ) :
    Tw (κ ^ (a * d) * (κ ^ (b * c))⁻¹) (x ^ a * y ^ b) (x ^ c * y ^ d) := by
  have hxx := Tw.one_of_commute (Commute.pow_pow_self x a c).eq
  have hyy := Tw.one_of_commute (Commute.pow_pow_self y b d).eq
  have hxy := (h.pow_left hκ a).pow_right d
  have hyx := ((h.symm hκ).pow_left (inv_ne_zero hκ) b).pow_right c
  simpa only [one_mul, mul_one, ← pow_mul, inv_pow] using
    (hxx.mul_right hxy).mul_left (hyx.mul_right hyy)

theorem Tw.unique {κ μ : L} {x y : Matrix (Fin 5) (Fin 5) L}
    (hx : IsUnit x) (hy : IsUnit y) (hκ : Tw κ x y) (hμ : Tw μ x y) : κ = μ := by
  have heq : κ • (y * x) = μ • (y * x) := (show x * y = κ • (y * x) from hκ).symm.trans hμ
  have hu : IsUnit (y * x).det := (Matrix.isUnit_iff_isUnit_det _).1 (hy.mul hx)
  have h := congrArg (fun M => (M * (y * x)⁻¹) 0 0) heq
  simpa only [Matrix.smul_mul, Matrix.mul_nonsing_inv _ hu, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] using h

theorem Tw.power_products_mod_five {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {x y : Matrix (Fin 5) (Fin 5) L} (hx : IsUnit x) (hy : IsUnit y)
    (h : Tw κ x y) (a b c d : ℕ)
    (hp : Tw κ (x ^ a * y ^ b) (x ^ c * y ^ d)) :
    a * d % 5 = (b * c + 1) % 5 := by
  have hκ0 : κ ≠ 0 := by
    intro hz
    simpa [hz] using hκ.pow_eq_one
  have ht := h.power_products hκ0 a b c d
  have heq := hp.unique ((hx.pow a).mul (hy.pow b)) ((hx.pow c).mul (hy.pow d)) ht
  have hrel : κ ^ (a * d) = κ ^ (b * c + 1) := by
    have hh : κ ^ (a * d) * (κ ^ (b * c))⁻¹ = κ := heq.symm
    calc κ ^ (a * d) = κ * κ ^ (b * c) :=
        (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hκ0)).mp hh
      _ = κ ^ (b * c + 1) := by rw [pow_succ']
  apply hκ.pow_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  rw [← pow_eq_pow_mod _ hκ.pow_eq_one, ← pow_eq_pow_mod _ hκ.pow_eq_one]
  exact hrel

end Tw

section Pair

variable {L : Type} [Field L]

theorem smul_one_eq_one_iff (κ : L) : κ • (1 : Matrix (Fin 5) (Fin 5) L) = 1 ↔ κ = 1 := by
  constructor
  · intro h
    have := congrFun (congrFun h 0) 0
    simpa using this
  · rintro rfl
    exact one_smul _ _

theorem tw_of_comm5 {Y Y' : SL(5, L)} {κ : L}
    (h : ((Y * Y' * (Y' * Y)⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = κ • 1) :
    Tw κ (Y : Matrix (Fin 5) (Fin 5) L) Y' := by
  unfold Tw
  have h1 : Y * Y' = (Y * Y' * (Y' * Y)⁻¹) * (Y' * Y) := by group
  calc (Y : Matrix (Fin 5) (Fin 5) L) * Y' = ((Y * Y' : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
    _ = (((Y * Y' * (Y' * Y)⁻¹) * (Y' * Y) : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) := by
        rw [← h1]
    _ = κ • ((Y' : Matrix (Fin 5) (Fin 5) L) * Y) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.smul_mul, Matrix.one_mul,
          Matrix.SpecialLinearGroup.coe_mul]

theorem pair_data {Y U Y' U' : SL(5, L)}
    (h : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)) :
    ∃ κ κ' : L, Tw κ (Y : Matrix (Fin 5) (Fin 5) L) Y' ∧ Tw κ' (U : Matrix (Fin 5) (Fin 5) L) U' ∧
      κ ^ 5 = 1 ∧ κ' ^ 5 = 1 ∧ (κ = 1 ↔ κ' = 1) := by
  obtain ⟨⟨κ, hκ⟩, ⟨κ', hκ'⟩⟩ := comm_lift_scalar h
  have hiff := lift_comm_iff h
  have hdet : ∀ {V V' : SL(5, L)} {c : L},
      ((V * V' * (V' * V)⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = c • 1 → c ^ 5 = 1 := by
    intro V V' c hc
    have h1 := (V * V' * (V' * V)⁻¹).2
    rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h1
    exact h1
  refine ⟨κ, κ', tw_of_comm5 hκ, tw_of_comm5 hκ', hdet hκ, hdet hκ', ?_⟩
  have key : ∀ {V V' : SL(5, L)} {c : L},
      ((V * V' * (V' * V)⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = c • 1 →
      (c = 1 ↔ V * V' = V' * V) := by
    intro V V' c hc
    rw [← smul_one_eq_one_iff, ← hc]
    constructor
    · intro h1
      have h2 : V * V' * (V' * V)⁻¹ = 1 := Subtype.ext h1
      exact mul_inv_eq_one.1 h2
    · intro h1
      rw [h1]
      simp
  rw [key hκ, key hκ']
  exact hiff

theorem pow_five_scalar {Y U : SL(5, L)}
    (h : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) ^ 5 = 1) :
    (∃ c : L, c ≠ 0 ∧ (Y : Matrix (Fin 5) (Fin 5) L) ^ 5 = c • 1) ∧
      ∃ c : L, c ≠ 0 ∧ (U : Matrix (Fin 5) (Fin 5) L) ^ 5 = c • 1 := by
  rw [(rhoA_commute_rhoB Y U).mul_pow, ← map_pow, ← map_pow] at h
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := scalar_of_rho_mul_eq_one h
  have hdet : ∀ {V : SL(5, L)} {c : L}, (V ^ 5 : SL(5, L)) = V ^ 5 →
      ((V ^ 5 : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = c • 1 → c ≠ 0 := by
    intro V c _ hc0 h0
    have h1 := (V ^ 5).2
    rw [hc0, h0] at h1
    simp at h1
  refine ⟨⟨c, hdet rfl hc, ?_⟩, ⟨c', hdet rfl hc', ?_⟩⟩
  · rw [← Matrix.SpecialLinearGroup.coe_pow]; exact hc
  · rw [← Matrix.SpecialLinearGroup.coe_pow]; exact hc'

end Pair

section Lift2

variable {L : Type} [Field L]

theorem rho_mem_adjointGroup (v : WeylGroup Tag.E8) (Y : SL(5, L)) :
    rhoSigmaE8A4 L v Y ∈ adjointGroup Tag.E8 L := by
  have h : (rhoSigmaE8A4 L v).range ≤ adjointGroup Tag.E8 L := by
    rw [rhoSigmaE8A4_range]
    exact iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ
  exact h ⟨Y, rfl⟩

theorem actsBy_lift_A (Y U : SL(5, L)) :
    ActsBy (rhoSigmaE8A4 L e8VA) (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)
      (Matrix.SpecialLinearGroup.toGL Y) := fun X => by
  rw [conjSLn_toGL']
  have h : rhoSigmaE8A4 L e8VB U * rhoSigmaE8A4 L e8VA X =
      rhoSigmaE8A4 L e8VA X * rhoSigmaE8A4 L e8VB U := (rhoA_commute_rhoB X U).eq.symm
  calc rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U * rhoSigmaE8A4 L e8VA X *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)⁻¹
      = rhoSigmaE8A4 L e8VA Y * (rhoSigmaE8A4 L e8VB U * rhoSigmaE8A4 L e8VA X) *
        (rhoSigmaE8A4 L e8VB U)⁻¹ * (rhoSigmaE8A4 L e8VA Y)⁻¹ := by group
    _ = rhoSigmaE8A4 L e8VA (Y * X * Y⁻¹) := by
      rw [h]; simp only [map_mul, map_inv]; group

theorem actsBy_lift_B (Y U : SL(5, L)) :
    ActsBy (rhoSigmaE8A4 L e8VB) (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)
      (Matrix.SpecialLinearGroup.toGL U) := fun X => by
  rw [conjSLn_toGL']
  have h : rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB X =
      rhoSigmaE8A4 L e8VB X * rhoSigmaE8A4 L e8VA Y := (rhoA_commute_rhoB Y X).eq
  calc rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U * rhoSigmaE8A4 L e8VB X *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)⁻¹
      = (rhoSigmaE8A4 L e8VA Y * (rhoSigmaE8A4 L e8VB U * rhoSigmaE8A4 L e8VB X *
          (rhoSigmaE8A4 L e8VB U)⁻¹)) * (rhoSigmaE8A4 L e8VA Y)⁻¹ := by group
    _ = rhoSigmaE8A4 L e8VB (U * X * U⁻¹) := by
      have h2 : rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB (U * X * U⁻¹) =
          rhoSigmaE8A4 L e8VB (U * X * U⁻¹) * rhoSigmaE8A4 L e8VA Y :=
        (rhoA_commute_rhoB Y (U * X * U⁻¹)).eq
      simp only [map_mul, map_inv] at h2 ⊢
      rw [h2]; group

theorem sl_scalar_central {Y : SL(5, L)} {c : L}
    (hY : (Y : Matrix (Fin 5) (Fin 5) L) = c • 1) (X : SL(5, L)) : Y * X = X * Y := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hY, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

open scoped commutatorElement in
theorem lift_product_ker_le_center :
    ((rhoSigmaE8A4 L e8VA).noncommCoprod
      (rhoSigmaE8A4 L e8VB) rhoA_commute_rhoB).ker ≤
      Subgroup.center (SL(5, L) × SL(5, L)) := by
  rintro ⟨Y, U⟩ h
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := scalar_of_rho_mul_eq_one h
  apply Subgroup.mem_center_iff.mpr
  rintro ⟨X, V⟩
  exact Prod.ext (sl_scalar_central hc X).symm (sl_scalar_central hd V).symm

theorem comm_lift_A_eq_of_lift_eq {Y U Y' U' V W V' W' : SL(5, L)}
    (h : rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U =
      rhoSigmaE8A4 L e8VA V * rhoSigmaE8A4 L e8VB W)
    (h' : rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U' =
      rhoSigmaE8A4 L e8VA V' * rhoSigmaE8A4 L e8VB W') :
    Y * Y' * (Y' * Y)⁻¹ = V * V' * (V' * V)⁻¹ := by
  let f := (rhoSigmaE8A4 L e8VA).noncommCoprod
    (rhoSigmaE8A4 L e8VB) rhoA_commute_rhoB
  have heq := CFSG.RankThree.Classical2.commutatorElement_eq_of_map_eq
    f lift_product_ker_le_center
    (x := (Y,U)) (x' := (V,W)) (y := (Y',U')) (y' := (V',W')) h h'
  have hA := congrArg Prod.fst heq
  simpa only [commutatorElement_def, Prod.fst_mul, Prod.fst_inv, _root_.mul_inv_rev,
    mul_assoc] using hA

theorem pow_z_of_scalar_lift {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {Y U : SL(5, L)} {c c' : L}
    (hY : (Y : Matrix (Fin 5) (Fin 5) L) = c • 1) (hU : (U : Matrix (Fin 5) (Fin 5) L) = c' • 1) :
    ∃ j : ℕ, rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U = griessZ hζ ^ j := by
  have hdiag : ∀ {V : SL(5, L)} {c : L}, (V : Matrix (Fin 5) (Fin 5) L) = c • 1 →
      ∀ i j : Fin 5, i ≠ j → (V : Matrix (Fin 5) (Fin 5) L) i j = 0 := by
    intro V c hV i j hij
    rw [hV]
    simp [Matrix.one_apply_ne hij]
  have hT : rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U ∈ torusGroup Tag.E8 L :=
    mul_mem (rhoSigmaE8A4_diagonal e8VA Y (hdiag hY)) (rhoSigmaE8A4_diagonal e8VB U (hdiag hU))
  obtain ⟨b, hb⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup hT
  have hcY := sl_scalar_central hY
  have hcU := sl_scalar_central hU
  obtain ⟨j, hj⟩ := eq_pow_z_of_trivial_action hζ (b := b)
    (fun X => by
      rw [hb]
      have h := (actsBy_lift_A Y U) X
      rw [h, conjSLn_toGL', show Y * X * Y⁻¹ = X by rw [hcY X]; group])
    (fun X => by
      rw [hb]
      have h := (actsBy_lift_B Y U) X
      rw [h, conjSLn_toGL', show U * X * U⁻¹ = X by rw [hcU X]; group])
  exact ⟨j, hb.symm.trans hj⟩

end Lift2

section Toral

variable {L : Type} [Field L]

theorem lift_inv (Y U : SL(5, L)) :
    (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)⁻¹ =
      rhoSigmaE8A4 L e8VA Y⁻¹ * rhoSigmaE8A4 L e8VB U⁻¹ := by
  have h := (rhoA_commute_rhoB Y⁻¹ U⁻¹).eq
  rw [map_inv, map_inv] at h
  rw [map_inv, map_inv, _root_.mul_inv_rev]
  exact h.symm

theorem conj_lift (SA SB Y U : SL(5, L)) :
    (rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB)⁻¹ *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB) =
      rhoSigmaE8A4 L e8VA (SA⁻¹ * Y * SA) * rhoSigmaE8A4 L e8VB (SB⁻¹ * U * SB) := by
  rw [lift_inv, lift_mul, lift_mul]

theorem conj_eq_diag_of_simul {Y S' : SL(5, L)} {S : GL (Fin 5) L} {d : Fin 5 → L} {μ : L}
    (hμ : μ ≠ 0) (hS : (Y : Matrix (Fin 5) (Fin 5) L) * (S : Matrix (Fin 5) (Fin 5) L) =
      (S : Matrix (Fin 5) (Fin 5) L) * diagonal d)
    (hSS' : (S : Matrix (Fin 5) (Fin 5) L) = μ • (S' : Matrix (Fin 5) (Fin 5) L)) :
    ((S'⁻¹ * Y * S' : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = diagonal d := by
  have h1 : (Y : Matrix (Fin 5) (Fin 5) L) * S' = S' * diagonal d := by
    rw [hSS', Matrix.mul_smul, Matrix.smul_mul] at hS
    exact smul_right_injective _ hμ hS
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_assoc, h1, ← Matrix.mul_assoc,
    Matrix.adjugate_mul, S'.2, one_smul, Matrix.one_mul]

theorem diag_conj_of_simul {Y S' : SL(5, L)} {S : GL (Fin 5) L} {d : Fin 5 → L} {μ : L}
    (hμ : μ ≠ 0) (hS : (Y : Matrix (Fin 5) (Fin 5) L) * (S : Matrix (Fin 5) (Fin 5) L) =
      (S : Matrix (Fin 5) (Fin 5) L) * diagonal d)
    (hSS' : (S : Matrix (Fin 5) (Fin 5) L) = μ • (S' : Matrix (Fin 5) (Fin 5) L)) :
    ∀ i j : Fin 5, i ≠ j → ((S'⁻¹ * Y * S' : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) i j = 0 := by
  intro i j hij
  rw [conj_eq_diag_of_simul hμ hS hSS']
  exact Matrix.diagonal_apply_ne _ hij

theorem toral_of_comm_lift_family [IsAlgClosed L] (h5 : (5 : L) ≠ 0) {ι : Type}
    (g : ι → ModGL Tag.E8 L) (Y U : ι → SL(5, L))
    (hg : ∀ i, g i = rhoSigmaE8A4 L e8VA (Y i) * rhoSigmaE8A4 L e8VB (U i))
    (hg5 : ∀ i, g i ^ 5 = 1) (hcomm : ∀ i j, g i * g j = g j * g i)
    (hY : ∀ i j, Y i * Y j = Y j * Y i) :
    ∃ x ∈ adjointGroup Tag.E8 L, ∀ i, x⁻¹ * g i * x ∈ torusGroup Tag.E8 L := by
  classical
  have hU : ∀ i j, U i * U j = U j * U i := fun i j => by
    have h := hcomm i j
    rw [hg i, hg j] at h
    exact (lift_comm_iff h).1 (hY i j)
  have hpow : ∀ i, (∃ c : L, c ≠ 0 ∧ (Y i : Matrix (Fin 5) (Fin 5) L) ^ 5 = c • 1) ∧
      ∃ c : L, c ≠ 0 ∧ (U i : Matrix (Fin 5) (Fin 5) L) ^ 5 = c • 1 := fun i => by
    have h := hg5 i
    rw [hg i] at h
    exact pow_five_scalar h
  choose cY hcY hYp using fun i => (hpow i).1
  choose cU hcU hUp using fun i => (hpow i).2
  obtain ⟨SA, hSA⟩ := exists_simul_diag h5 (fun i => (Y i : Matrix (Fin 5) (Fin 5) L))
    (fun i j => by
      simp only [← Matrix.SpecialLinearGroup.coe_mul, hY i j]) hcY hYp
  obtain ⟨SB, hSB⟩ := exists_simul_diag h5 (fun i => (U i : Matrix (Fin 5) (Fin 5) L))
    (fun i j => by
      simp only [← Matrix.SpecialLinearGroup.coe_mul, hU i j]) hcU hUp
  obtain ⟨SA', μA, hμA, hSA'⟩ := exists_sl_of_gl SA
  obtain ⟨SB', μB, hμB, hSB'⟩ := exists_sl_of_gl SB
  refine ⟨rhoSigmaE8A4 L e8VA SA' * rhoSigmaE8A4 L e8VB SB',
    mul_mem (rho_mem_adjointGroup _ _) (rho_mem_adjointGroup _ _), fun i => ?_⟩
  obtain ⟨dA, hdA⟩ := hSA i
  obtain ⟨dB, hdB⟩ := hSB i
  rw [hg i, conj_lift]
  exact mul_mem (rhoSigmaE8A4_diagonal e8VA _ (diag_conj_of_simul hμA hdA hSA'))
    (rhoSigmaE8A4_diagonal e8VB _ (diag_conj_of_simul hμB hdB hSB'))

theorem fin3_comm {G : Type*} [Mul G] {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (i j : Fin 3) :
    (![a, b, c] : Fin 3 → G) i * (![a, b, c] : Fin 3 → G) j =
      (![a, b, c] : Fin 3 → G) j * (![a, b, c] : Fin 3 → G) i := by
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact hab
    | exact hab.symm
    | exact hac
    | exact hac.symm
    | exact hbc
    | exact hbc.symm

theorem toral_closure_of_comm_lifts [IsAlgClosed L] (h5 : (5 : L) ≠ 0)
    {a b c : ModGL Tag.E8 L} {Ya Ua Yb Ub Yc Uc : SL(5, L)}
    (hae : a = rhoSigmaE8A4 L e8VA Ya * rhoSigmaE8A4 L e8VB Ua)
    (hbe : b = rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub)
    (hce : c = rhoSigmaE8A4 L e8VA Yc * rhoSigmaE8A4 L e8VB Uc)
    (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1) (hc5 : c ^ 5 = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hYab : Ya * Yb = Yb * Ya) (hYac : Ya * Yc = Yc * Ya) (hYbc : Yb * Yc = Yc * Yb) :
    ∃ x ∈ adjointGroup Tag.E8 L,
      ∀ e ∈ Subgroup.closure ({a, b, c} : Set (ModGL Tag.E8 L)),
        x⁻¹ * e * x ∈ torusGroup Tag.E8 L := by
  obtain ⟨x, hx, hxt⟩ := toral_of_comm_lift_family h5 (ι := Fin 3) ![a, b, c] ![Ya, Yb, Yc]
    ![Ua, Ub, Uc] (fun i => by fin_cases i <;> simpa using ‹_›)
    (fun i => by fin_cases i <;> simpa using ‹_›) (fin3_comm hab hac hbc) (fin3_comm hYab hYac hYbc)
  refine ⟨x, hx, fun e he => ?_⟩
  have hle : Subgroup.closure ({a, b, c} : Set (ModGL Tag.E8 L)) ≤
      (torusGroup Tag.E8 L).comap (MulAut.conj x⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro e he
    rcases he with rfl | rfl | rfl
    · simpa [MulAut.conj_apply] using hxt 0
    · simpa [MulAut.conj_apply] using hxt 1
    · simpa [MulAut.conj_apply] using hxt 2
  simpa [MulAut.conj_apply] using hle he

end Toral

section Radical

variable {L : Type} [Field L]

theorem lift_pow (Y U : SL(5, L)) (n : ℕ) :
    (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) ^ n =
      rhoSigmaE8A4 L e8VA (Y ^ n) * rhoSigmaE8A4 L e8VB (U ^ n) := by
  rw [(rhoA_commute_rhoB Y U).mul_pow, map_pow, map_pow]

theorem sl_isUnit (Y : SL(5, L)) : IsUnit (Y : Matrix (Fin 5) (Fin 5) L) :=
  (Matrix.SpecialLinearGroup.toGL Y).isUnit

theorem isPrimitiveRoot_five_of_ne_one {κ : L} (h5 : κ ^ 5 = 1) (h1 : κ ≠ 1) :
    IsPrimitiveRoot κ 5 := by
  have hord : orderOf κ = 5 := orderOf_eq_prime h5 h1
  have := IsPrimitiveRoot.orderOf κ
  rwa [hord] at this

theorem exists_pow_eq_of_pow_five {κ ξ : L} (hκ : IsPrimitiveRoot κ 5) (hξ : ξ ^ 5 = 1) :
    ∃ n : ℕ, κ ^ n = ξ := by
  obtain ⟨n, -, hn⟩ := hκ.eq_pow_of_pow_eq_one hξ
  exact ⟨n, hn⟩

theorem sl_comm_iff {Y Y' : SL(5, L)} :
    Y * Y' = Y' * Y ↔ (Y : Matrix (Fin 5) (Fin 5) L) * Y' = Y' * Y := by
  constructor
  · intro h
    simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg Subtype.val h
  · intro h
    exact Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using h)

theorem radical_pair_normal_form [IsAlgClosed L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b c : ModGL Tag.E8 L} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (hb5 : b ^ 5 = 1) {Ya Ua Yb Ub Yc Uc : SL(5, L)}
    (hae : a = rhoSigmaE8A4 L e8VA Ya * rhoSigmaE8A4 L e8VB Ua)
    (hbe : b = rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub)
    (hce : c = rhoSigmaE8A4 L e8VA Yc * rhoSigmaE8A4 L e8VB Uc)
    (hnc : Ya * Yb ≠ Yb * Ya) :
    ∃ j i k : ℕ, c * a ^ i * b ^ k = griessZ hζ ^ j := by
  classical
  obtain ⟨κ, κ', hκ, hκ', hκ5, hκ'5, hiff⟩ := pair_data (Y := Ya) (U := Ua) (Y' := Yb)
    (U' := Ub) (show _ = _ by rw [← hae, ← hbe]; exact hab.eq)
  have hκ1 : κ ≠ 1 := fun h1 => hnc (sl_comm_iff.2 (Tw.commute_of_one (h1 ▸ hκ)))
  have hκprim : IsPrimitiveRoot κ 5 := isPrimitiveRoot_five_of_ne_one hκ5 hκ1
  have hκ'prim : IsPrimitiveRoot κ' 5 :=
    isPrimitiveRoot_five_of_ne_one hκ'5 fun h => hκ1 (hiff.2 h)
  obtain ⟨κ₁, κ₁', hκ₁, -, hκ₁5, -, -⟩ := pair_data (Y := Yc) (U := Uc) (Y' := Ya) (U' := Ua)
    (show _ = _ by rw [← hce, ← hae]; exact hac.symm.eq)
  obtain ⟨κ₂, κ₂', hκ₂, -, hκ₂5, -, -⟩ := pair_data (Y := Yc) (U := Uc) (Y' := Yb) (U' := Ub)
    (show _ = _ by rw [← hce, ← hbe]; exact hbc.symm.eq)
  obtain ⟨k, hk⟩ := exists_pow_eq_of_pow_five hκprim hκ₁5
  obtain ⟨i, hi⟩ := exists_pow_eq_of_pow_five hκprim
    (show κ₂⁻¹ ^ 5 = 1 by rw [inv_pow, hκ₂5, inv_one])
  have hκne : κ ≠ 0 := hκprim.ne_zero (by norm_num)
  have hκ₂ne : κ₂ ≠ 0 := by
    intro h0
    rw [h0] at hκ₂5
    simp at hκ₂5
  have hra : Tw 1 (((Yc : Matrix (Fin 5) (Fin 5) L) * (Ya : Matrix (Fin 5) (Fin 5) L) ^ i) *
      (Yb : Matrix (Fin 5) (Fin 5) L) ^ k) (Ya : Matrix (Fin 5) (Fin 5) L) := by
    have h1 := ((hκ₁.mul_left (Tw.one_of_commute
      ((Commute.refl (Ya : Matrix (Fin 5) (Fin 5) L)).pow_left i).eq)).mul_left
      ((hκ.symm hκne).pow_left (inv_ne_zero hκne) k))
    have h2 : κ₁ * 1 * κ⁻¹ ^ k = 1 := by
      rw [← hk, mul_one, inv_pow, mul_inv_cancel₀ (pow_ne_zero k hκne)]
    rwa [h2] at h1
  have hrb : Tw 1 (((Yc : Matrix (Fin 5) (Fin 5) L) * (Ya : Matrix (Fin 5) (Fin 5) L) ^ i) *
      (Yb : Matrix (Fin 5) (Fin 5) L) ^ k) (Yb : Matrix (Fin 5) (Fin 5) L) := by
    have h1 := ((hκ₂.mul_left (hκ.pow_left hκne i)).mul_left (Tw.one_of_commute
      ((Commute.refl (Yb : Matrix (Fin 5) (Fin 5) L)).pow_left k).eq))
    have h2 : κ₂ * κ ^ i * 1 = 1 := by
      rw [hi, mul_one, mul_inv_cancel₀ hκ₂ne]
    rwa [h2] at h1
  set Yr : SL(5, L) := Yc * Ya ^ i * Yb ^ k with hYr
  set Ur : SL(5, L) := Uc * Ua ^ i * Ub ^ k with hUr
  have hrlift : c * a ^ i * b ^ k = rhoSigmaE8A4 L e8VA Yr * rhoSigmaE8A4 L e8VB Ur := by
    rw [hce, hae, hbe, lift_pow, lift_pow, lift_mul, lift_mul]
  have hMr : (Yr : Matrix (Fin 5) (Fin 5) L) = (Yc : Matrix (Fin 5) (Fin 5) L) *
      (Ya : Matrix (Fin 5) (Fin 5) L) ^ i * (Yb : Matrix (Fin 5) (Fin 5) L) ^ k := by
    simp [hYr, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
  have hYra : Yr * Ya = Ya * Yr := sl_comm_iff.2 (by rw [hMr]; exact Tw.commute_of_one hra)
  have hYrb : Yr * Yb = Yb * Yr := sl_comm_iff.2 (by rw [hMr]; exact Tw.commute_of_one hrb)
  have hca : Commute c a := hac.symm
  have hcb : Commute c b := hbc.symm
  have hba : Commute b a := hab.symm
  have hrea : (c * a ^ i * b ^ k) * a = a * (c * a ^ i * b ^ k) :=
    ((hca.mul_left ((Commute.refl a).pow_left i)).mul_left (hba.pow_left k)).eq
  have hreb : (c * a ^ i * b ^ k) * b = b * (c * a ^ i * b ^ k) :=
    ((hcb.mul_left (hab.pow_left i)).mul_left ((Commute.refl b).pow_left k)).eq
  have hUra : Ur * Ua = Ua * Ur := by
    have h := hrea
    rw [hrlift, hae] at h
    exact (lift_comm_iff h).1 hYra
  have hUrb : Ur * Ub = Ub * Ur := by
    have h := hreb
    rw [hrlift, hbe] at h
    exact (lift_comm_iff h).1 hYrb
  have hb5 : (rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub) ^ 5 = 1 := by
    rw [← hbe]; exact hb5
  obtain ⟨cA, -, hcA⟩ := (pow_five_scalar hb5).1
  obtain ⟨cB, -, hcB⟩ := (pow_five_scalar hb5).2
  obtain ⟨nA, hnA⟩ := heis_schur hκprim (sl_isUnit Ya) (sl_isUnit Yb) hκ hcA
    (sl_comm_iff.1 hYra) (sl_comm_iff.1 hYrb)
  obtain ⟨nB, hnB⟩ := heis_schur hκ'prim (sl_isUnit Ua) (sl_isUnit Ub) hκ' hcB
    (sl_comm_iff.1 hUra) (sl_comm_iff.1 hUrb)
  obtain ⟨j, hj⟩ := pow_z_of_scalar_lift hζ hnA hnB
  exact ⟨j, i, k, by rw [hrlift, hj]⟩

theorem radical_aux [IsAlgClosed L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b c : ModGL Tag.E8 L} (hb : CubeBasis a b c) {Ya Ua Yb Ub Yc Uc : SL(5, L)}
    (hae : a = rhoSigmaE8A4 L e8VA Ya * rhoSigmaE8A4 L e8VB Ua)
    (hbe : b = rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub)
    (hce : c = rhoSigmaE8A4 L e8VA Yc * rhoSigmaE8A4 L e8VB Uc)
    (hnc : Ya * Yb ≠ Yb * Ya) :
    ∃ j i k : ℕ, ¬ 5 ∣ j ∧ c * a ^ i * b ^ k = griessZ hζ ^ j := by
  obtain ⟨j, i, k, hj⟩ := radical_pair_normal_form hζ hb.comm_ab hb.comm_ac hb.comm_bc
    hb.pow_b hae hbe hce hnc
  refine ⟨j, i, k, ?_, hj⟩
  rintro ⟨m, rfl⟩
  have hr1 : c * a ^ i * b ^ k = 1 := by
    rw [hj, pow_mul, griessZ_pow_five hζ, one_pow]
  have h0 := @hb.inj (⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩,
    ⟨1, by norm_num⟩) (0, 0, 0) (by
      simp only [pow_zero, mul_one, pow_one]
      rw [← pow_eq_pow_mod _ hb.pow_a, ← pow_eq_pow_mod _ hb.pow_b]
      calc a ^ i * b ^ k * c = a ^ i * (b ^ k * c) := by rw [mul_assoc]
        _ = a ^ i * (c * b ^ k) := by rw [(hb.comm_bc.pow_left k).eq]
        _ = (a ^ i * c) * b ^ k := by rw [← mul_assoc]
        _ = (c * a ^ i) * b ^ k := by rw [(hb.comm_ac.pow_left i).eq]
        _ = 1 := hr1)
  simp [Prod.ext_iff] at h0

theorem closure_eq_of_radical {G : Type*} [Group G] {z a b c : G} {i k j : ℕ} (hz5 : z ^ 5 = 1)
    (hj : ¬ 5 ∣ j) (hr : c * a ^ i * b ^ k = z ^ j) :
    z ∈ Subgroup.closure ({a, b, c} : Set G) ∧
      Subgroup.closure ({z, a, b} : Set G) = Subgroup.closure ({a, b, c} : Set G) := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hj).symm (by norm_num : 1 < 5)
  have hma : a ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
  have hmb : b ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
  have hmc : c ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
  have hzr : z = (c * a ^ i * b ^ k) ^ m := by
    rw [hr, ← pow_mul, pow_eq_pow_mod _ hz5, hm, pow_one]
  have hzmem : z ∈ Subgroup.closure ({a, b, c} : Set G) := by
    rw [hzr]
    exact pow_mem (mul_mem (mul_mem hmc (pow_mem hma _)) (pow_mem hmb _)) _
  refine ⟨hzmem, le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hzmem
    · exact hma
    · exact hmb
  · rw [Subgroup.closure_le]
    have hza : a ∈ Subgroup.closure ({z, a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hzb : b ∈ Subgroup.closure ({z, a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hzz : z ∈ Subgroup.closure ({z, a, b} : Set G) := Subgroup.subset_closure (by simp)
    rintro x (rfl | rfl | rfl)
    · exact hza
    · exact hzb
    · have : x = z ^ j * (b ^ k)⁻¹ * (a ^ i)⁻¹ := by
        rw [← hr]; group
      rw [this]
      exact mul_mem (mul_mem (pow_mem hzz _) (inv_mem (pow_mem hzb _))) (inv_mem (pow_mem hza _))

theorem exists_central_shear_of_noncommuting_A_lifts {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b : ModGL Tag.E8 L} {Y U Y' U' : SL(5, L)}
    (ha : a = rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)
    (hb : b = rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U')
    (hcomm : a * b = b * a) (hYnc : Y * Y' ≠ Y' * Y) (n : ℕ) :
    ∃ γ ∈ mulSub L,
      γ * griessZ hζ * γ⁻¹ = griessZ hζ ∧
      γ * a * γ⁻¹ = a ∧
      γ * b * γ⁻¹ = griessZ hζ ^ n * b := by
  have hcomm' : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) := by
    simpa only [ha, hb] using hcomm
  obtain ⟨⟨c, hC⟩, -⟩ := comm_lift_scalar hcomm'
  obtain ⟨j, hzj⟩ := pow_z_of_scalar_lift (L := L) hζ
    (Y := Y * Y' * (Y' * Y)⁻¹) (U := 1) (c := c) (c' := 1) hC (by simp)
  have hzj' : rhoSigmaE8A4 L e8VA (Y * Y' * (Y' * Y)⁻¹) = griessZ hζ ^ j := by
    simpa using hzj
  have hρC_ne : rhoSigmaE8A4 L e8VA (Y * Y' * (Y' * Y)⁻¹) ≠ 1 := by
    intro h
    apply hYnc
    have hC1 : Y * Y' * (Y' * Y)⁻¹ = 1 :=
      rhoSigmaE8A4_injective (L := L) e8VA (by simpa using h)
    exact mul_inv_eq_one.1 hC1
  have hzj_ne : griessZ hζ ^ j ≠ 1 := by
    intro h
    exact hρC_ne (by rw [hzj']; exact h)
  have h5j : ¬ 5 ∣ j := by
    rintro ⟨m, rfl⟩
    exact hzj_ne (by rw [pow_mul, griessZ_pow_five hζ, one_pow])
  have hconj_b0 : (rhoSigmaE8A4 L e8VA Y) * b * (rhoSigmaE8A4 L e8VA Y)⁻¹ =
      rhoSigmaE8A4 L e8VA (Y * Y' * Y⁻¹) * rhoSigmaE8A4 L e8VB U' := by
    rw [hb]
    simpa using
      (conj_lift (L := L) (SA := Y⁻¹) (SB := 1) (Y := Y') (U := U'))
  have hCY : Y * Y' * Y⁻¹ = (Y * Y' * (Y' * Y)⁻¹) * Y' := by group
  have hconj_b : (rhoSigmaE8A4 L e8VA Y) * b * (rhoSigmaE8A4 L e8VA Y)⁻¹ =
      griessZ hζ ^ j * b := by
    rw [hconj_b0, hCY, map_mul, hzj', hb]
    group
  have hcz : Commute (rhoSigmaE8A4 L e8VA Y) (griessZ hζ ^ j) :=
    Commute.pow_right ((griessZ_comm_rhoA hζ Y).symm) j
  have hconj_pow : ∀ k : ℕ,
      (rhoSigmaE8A4 L e8VA Y) ^ k * b * ((rhoSigmaE8A4 L e8VA Y) ^ k)⁻¹ =
        (griessZ hζ ^ j) ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hczk : (rhoSigmaE8A4 L e8VA Y) ^ k * (griessZ hζ ^ j) =
            (griessZ hζ ^ j) * (rhoSigmaE8A4 L e8VA Y) ^ k :=
          (Commute.pow_left hcz k).eq
        calc (rhoSigmaE8A4 L e8VA Y) ^ (k + 1) * b *
              ((rhoSigmaE8A4 L e8VA Y) ^ (k + 1))⁻¹
            = (rhoSigmaE8A4 L e8VA Y) ^ k *
                ((rhoSigmaE8A4 L e8VA Y) * b * (rhoSigmaE8A4 L e8VA Y)⁻¹) *
                ((rhoSigmaE8A4 L e8VA Y) ^ k)⁻¹ := by group
          _ = (rhoSigmaE8A4 L e8VA Y) ^ k * (griessZ hζ ^ j * b) *
                ((rhoSigmaE8A4 L e8VA Y) ^ k)⁻¹ := by rw [hconj_b]
          _ = (rhoSigmaE8A4 L e8VA Y) ^ k * (griessZ hζ ^ j) * b *
                ((rhoSigmaE8A4 L e8VA Y) ^ k)⁻¹ := by group
          _ = (griessZ hζ ^ j) * (rhoSigmaE8A4 L e8VA Y) ^ k * b *
                ((rhoSigmaE8A4 L e8VA Y) ^ k)⁻¹ := by rw [hczk]
          _ = (griessZ hζ ^ j) *
                ((rhoSigmaE8A4 L e8VA Y) ^ k * b *
                  ((rhoSigmaE8A4 L e8VA Y) ^ k)⁻¹) := by group
          _ = (griessZ hζ ^ j) * ((griessZ hζ ^ j) ^ k * b) := by rw [ih]
          _ = (griessZ hζ ^ j) ^ (k + 1) * b := by rw [pow_succ']; group
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_of_coprime n
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5j).symm (by norm_num : 5 ≠ 0)
  let γ : ModGL Tag.E8 L := (rhoSigmaE8A4 L e8VA Y) ^ k
  have hγmem : γ ∈ mulSub L := by
    refine ⟨Y ^ k, 1, ?_⟩
    dsimp only [γ]
    rw [map_pow, map_one, mul_one]
  have hγz : γ * griessZ hζ * γ⁻¹ = griessZ hζ := by
    have hcommγz : Commute γ (griessZ hζ) := by
      dsimp only [γ]
      exact Commute.pow_left ((griessZ_comm_rhoA hζ Y).symm) k
    calc γ * griessZ hζ * γ⁻¹ = griessZ hζ * γ * γ⁻¹ := by rw [hcommγz.eq]
      _ = griessZ hζ := by simp
  have hγa : γ * a * γ⁻¹ = a := by
    have hcommγa : Commute γ a := by
      rw [ha]
      dsimp only [γ]
      exact ((Commute.refl (rhoSigmaE8A4 L e8VA Y)).pow_left k).mul_right
        ((rhoA_commute_rhoB Y U).pow_left k)
    calc γ * a * γ⁻¹ = a * γ * γ⁻¹ := by rw [hcommγa.eq]
      _ = a := by simp
  have hzpow : (griessZ hζ ^ j) ^ k = griessZ hζ ^ n := by
    rw [← pow_mul]
    calc griessZ hζ ^ (j * k) = griessZ hζ ^ ((j * k) % 5) :=
          pow_eq_pow_mod (j * k) (griessZ_pow_five hζ)
      _ = griessZ hζ ^ (n % 5) := by rw [hk]
      _ = griessZ hζ ^ n := (pow_eq_pow_mod n (griessZ_pow_five hζ)).symm
  have hγb : γ * b * γ⁻¹ = griessZ hζ ^ n * b := by
    dsimp only [γ]
    rw [hconj_pow k, hzpow]
  exact ⟨γ, hγmem, hγz, hγa, hγb⟩

end Radical

section Main

variable {L : Type} [Field L] [IsAlgClosed L]

theorem z_basis_of_nontoral (h5 : (5 : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b c : ModGL Tag.E8 L} (hb : CubeBasis a b c) (ha : a ∈ mulSub L) (hbm : b ∈ mulSub L)
    (hc : c ∈ mulSub L)
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ e ∈ Subgroup.closure ({a, b, c} : Set (ModGL Tag.E8 L)),
        g⁻¹ * e * g ∈ torusGroup Tag.E8 L) :
    ∃ e e' : ModGL Tag.E8 L, griessZ hζ ∈ Subgroup.closure ({a, b, c} : Set (ModGL Tag.E8 L)) ∧
      Subgroup.closure ({griessZ hζ, e, e'} : Set (ModGL Tag.E8 L)) =
        Subgroup.closure ({a, b, c} : Set (ModGL Tag.E8 L)) := by
  obtain ⟨Ya, Ua, hae⟩ := ha
  obtain ⟨Yb, Ub, hbe⟩ := hbm
  obtain ⟨Yc, Uc, hce⟩ := hc
  by_cases hab : Ya * Yb = Yb * Ya
  · by_cases hac : Ya * Yc = Yc * Ya
    · by_cases hbc : Yb * Yc = Yc * Yb
      · exact absurd (toral_closure_of_comm_lifts h5 hae hbe hce hb.pow_a hb.pow_b hb.pow_c
          hb.comm_ab.eq hb.comm_ac.eq hb.comm_bc.eq hab hac hbc) hnt
      ·
        obtain ⟨j, i, k, hj, hr⟩ := radical_aux hζ (hb.swap.swap') hbe hce hae hbc
        obtain ⟨hzm, hcl⟩ := closure_eq_of_radical (griessZ_pow_five hζ) hj hr
        refine ⟨b, c, ?_, ?_⟩
        · have : ({b, c, a} : Set (ModGL Tag.E8 L)) = {a, b, c} := by
            ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
          rwa [this] at hzm
        · have : ({b, c, a} : Set (ModGL Tag.E8 L)) = {a, b, c} := by
            ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
          rwa [this] at hcl
    ·
      obtain ⟨j, i, k, hj, hr⟩ := radical_aux hζ hb.swap' hae hce hbe hac
      obtain ⟨hzm, hcl⟩ := closure_eq_of_radical (griessZ_pow_five hζ) hj hr
      refine ⟨a, c, ?_, ?_⟩
      · have : ({a, c, b} : Set (ModGL Tag.E8 L)) = {a, b, c} := by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rwa [this] at hzm
      · have : ({a, c, b} : Set (ModGL Tag.E8 L)) = {a, b, c} := by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rwa [this] at hcl
  ·
    obtain ⟨j, i, k, hj, hr⟩ := radical_aux hζ hb hae hbe hce hab
    obtain ⟨hzm, hcl⟩ := closure_eq_of_radical (griessZ_pow_five hζ) hj hr
    exact ⟨a, b, hzm, hcl⟩

theorem nc_lifts_of_nontoral (h5 : (5 : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {e e' : ModGL Tag.E8 L} (he : e ∈ mulSub L) (he' : e' ∈ mulSub L)
    (hcomm : e * e' = e' * e) (he5 : e ^ 5 = 1) (he'5 : e' ^ 5 = 1)
    (hze : griessZ hζ * e = e * griessZ hζ) (hze' : griessZ hζ * e' = e' * griessZ hζ)
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, e, e'} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L) :
    ∃ Ye Ue Ye' Ue' : SL(5, L), e = rhoSigmaE8A4 L e8VA Ye * rhoSigmaE8A4 L e8VB Ue ∧
      e' = rhoSigmaE8A4 L e8VA Ye' * rhoSigmaE8A4 L e8VB Ue' ∧ Ye * Ye' ≠ Ye' * Ye := by
  obtain ⟨Ye, Ue, hee⟩ := he
  obtain ⟨Ye', Ue', hee'⟩ := he'
  obtain ⟨Yz, hYz⟩ := z_mem_range_rhoA hζ
  have hzA : ∀ X : SL(5, L), Yz * X = X * Yz := fun X => by
    apply rhoSigmaE8A4_injective (L := L) e8VA
    rw [map_mul, map_mul, hYz]
    exact griessZ_comm_rhoA hζ X
  have hzlift : griessZ hζ = rhoSigmaE8A4 L e8VA Yz * rhoSigmaE8A4 L e8VB 1 := by
    rw [map_one, mul_one, hYz]
  refine ⟨Ye, Ue, Ye', Ue', hee, hee', fun hnc => hnt ?_⟩
  exact toral_closure_of_comm_lifts h5 hzlift hee hee' (griessZ_pow_five hζ) he5 he'5
    hze hze' hcomm (hzA Ye) (hzA Ye') hnc

theorem heisShape_of_nontoral (h5 : (5 : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {e e' : ModGL Tag.E8 L} (he : e ∈ mulSub L) (he' : e' ∈ mulSub L)
    (hcomm : e * e' = e' * e) (he5 : e ^ 5 = 1) (he'5 : e' ^ 5 = 1)
    (hze : griessZ hζ * e = e * griessZ hζ) (hze' : griessZ hζ * e' = e' * griessZ hζ)
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, e, e'} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L) :
    HeisShape (rhoSigmaE8A4 L e8VA) (griessZ hζ) e e' ∧
      HeisShape (rhoSigmaE8A4 L e8VB) (griessZ hζ) e e' := by
  obtain ⟨Ye, Ue, Ye', Ue', hee, hee', hnc⟩ :=
    nc_lifts_of_nontoral h5 hζ he he' hcomm he5 he'5 hze hze' hnt
  obtain ⟨κ, κ', hκ, hκ', hκ5, hκ'5, hiff⟩ := pair_data (Y := Ye) (U := Ue) (Y' := Ye')
    (U' := Ue') (show _ = _ by rw [← hee, ← hee']; exact hcomm)
  have hκ1 : κ ≠ 1 := fun h1 => hnc (sl_comm_iff.2 (Tw.commute_of_one (h1 ▸ hκ)))
  have hκprim : IsPrimitiveRoot κ 5 := isPrimitiveRoot_five_of_ne_one hκ5 hκ1
  have hκ'prim : IsPrimitiveRoot κ' 5 :=
    isPrimitiveRoot_five_of_ne_one hκ'5 fun h => hκ1 (hiff.2 h)
  have he5' : (rhoSigmaE8A4 L e8VA Ye * rhoSigmaE8A4 L e8VB Ue) ^ 5 = 1 := by rw [← hee]; exact he5
  have he'5' : (rhoSigmaE8A4 L e8VA Ye' * rhoSigmaE8A4 L e8VB Ue') ^ 5 = 1 := by
    rw [← hee']; exact he'5
  obtain ⟨c₀, -, hc₀⟩ := (pow_five_scalar he5').1
  obtain ⟨d₀, -, hd₀⟩ := (pow_five_scalar he5').2
  obtain ⟨c₁, -, hc₁⟩ := (pow_five_scalar he'5').1
  obtain ⟨d₁, -, hd₁⟩ := (pow_five_scalar he'5').2
  refine ⟨⟨actsBy_z_A hζ, Matrix.SpecialLinearGroup.toGL Ye, Matrix.SpecialLinearGroup.toGL Ye', κ,
    c₀, c₁, hκprim, ?_, ?_, hκ, ?_, ?_⟩,
    ⟨actsBy_z_B hζ, Matrix.SpecialLinearGroup.toGL Ue, Matrix.SpecialLinearGroup.toGL Ue', κ',
    d₀, d₁, hκ'prim, ?_, ?_, hκ', ?_, ?_⟩⟩
  · rw [hee]; exact actsBy_lift_A Ye Ue
  · rw [hee']; exact actsBy_lift_A Ye' Ue'
  · rw [Units.val_pow_eq_pow_val]; exact hc₀
  · rw [Units.val_pow_eq_pow_val]; exact hc₁
  · rw [hee]; exact actsBy_lift_B Ye Ue
  · rw [hee']; exact actsBy_lift_B Ye' Ue'
  · rw [Units.val_pow_eq_pow_val]; exact hd₀
  · rw [Units.val_pow_eq_pow_val]; exact hd₁

theorem mulSub_comm_z {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {g : ModGL Tag.E8 L}
    (hg : g ∈ mulSub L) : g * griessZ hζ = griessZ hζ * g := by
  obtain ⟨Y, U, rfl⟩ := hg
  have hA := (griessZ_comm_rhoA hζ Y).symm
  have hB : rhoSigmaE8A4 L e8VB U * griessZ hζ = griessZ hζ * rhoSigmaE8A4 L e8VB U := by
    have := (actsBy_z_B hζ).comm (A := U) (M := 1) (by simp)
    exact this.symm
  calc rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U * griessZ hζ
      = rhoSigmaE8A4 L e8VA Y * (rhoSigmaE8A4 L e8VB U * griessZ hζ) := by rw [mul_assoc]
    _ = rhoSigmaE8A4 L e8VA Y * (griessZ hζ * rhoSigmaE8A4 L e8VB U) := by rw [hB]
    _ = (rhoSigmaE8A4 L e8VA Y * griessZ hζ) * rhoSigmaE8A4 L e8VB U := by rw [← mul_assoc]
    _ = (griessZ hζ * rhoSigmaE8A4 L e8VA Y) * rhoSigmaE8A4 L e8VB U := by rw [hA]
    _ = griessZ hζ * (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) := by rw [mul_assoc]

theorem card_le_five_cube_of_nontoral_le_mulSub {ζ : L} (h5 : (5 : L) ≠ 0)
    (hζ : IsPrimitiveRoot ζ 5) (E : Subgroup (ModGL Tag.E8 L)) (hE : E ≤ mulSub L)
    (hE5 : CFSG.Open.IsElemAbelian 5 E)
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ e ∈ E, g⁻¹ * e * g ∈ torusGroup Tag.E8 L) :
    Nat.card E ≤ 5 ^ 3 := by
  classical
  let Y : E → SL(5, L) := fun e => (mem_mulSub.mp (hE e.2)).choose
  let U : E → SL(5, L) := fun e => (mem_mulSub.mp (hE e.2)).choose_spec.choose
  have hYU : ∀ e : E, (e : ModGL Tag.E8 L) =
      rhoSigmaE8A4 L e8VA (Y e) * rhoSigmaE8A4 L e8VB (U e) :=
    fun e => (mem_mulSub.mp (hE e.2)).choose_spec.choose_spec
  have hpowE : ∀ e : E, (e : ModGL Tag.E8 L) ^ 5 = 1 :=
    fun e => hE5.2 (e : ModGL Tag.E8 L) e.2
  have hcommE : ∀ x y : E, x * y = y * x :=
    fun x y => hE5.1.is_comm.comm x y
  have hcommG : ∀ x y : E,
      (x : ModGL Tag.E8 L) * (y : ModGL Tag.E8 L) =
        (y : ModGL Tag.E8 L) * (x : ModGL Tag.E8 L) :=
    fun x y => by
      simpa using congrArg (fun z : E => (z : ModGL Tag.E8 L)) (hcommE x y)
  by_cases hYall : ∀ e e' : E, Y e * Y e' = Y e' * Y e
  ·
    obtain ⟨x, hx, hxt⟩ := toral_of_comm_lift_family (L := L) h5
      (fun e : E => (e : ModGL Tag.E8 L)) Y U hYU hpowE hcommG hYall
    exact (hnt ⟨x, hx, fun e he => hxt ⟨e, he⟩⟩).elim
  ·
    have hYnc : ∃ a b : E, Y a * Y b ≠ Y b * Y a := by
      by_contra h
      apply hYall
      intro a b
      by_contra hab
      exact h ⟨a, b, hab⟩
    obtain ⟨a, b, hnc⟩ := hYnc
    set z : ModGL Tag.E8 L := griessZ hζ with hz
    have hz5 : z ^ 5 = 1 := by rw [hz]; exact griessZ_pow_five hζ
    have hza : Commute z (a : ModGL Tag.E8 L) := by
      rw [hz]
      exact (mulSub_comm_z (L := L) hζ (hE a.2)).symm
    have hzb : Commute z (b : ModGL Tag.E8 L) := by
      rw [hz]
      exact (mulSub_comm_z (L := L) hζ (hE b.2)).symm
    have hab : Commute (a : ModGL Tag.E8 L) (b : ModGL Tag.E8 L) := hcommG a b
    have hEclosure : E ≤ Subgroup.closure
        ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) := by
      intro c hc
      have hc_mem : (c : ModGL Tag.E8 L) ∈ Subgroup.closure
          ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) := by
        obtain ⟨j, i, k, hjk⟩ := radical_pair_normal_form (L := L) hζ
          (hcommG a b) (hcommG a ⟨c, hc⟩) (hcommG b ⟨c, hc⟩) (hpowE b)
          (hYU a) (hYU b) (by simpa using hYU ⟨c, hc⟩) hnc
        have hc_eq : (c : ModGL Tag.E8 L) =
            z ^ j * ((b : ModGL Tag.E8 L) ^ k)⁻¹ *
              ((a : ModGL Tag.E8 L) ^ i)⁻¹ := by
          rw [hz, ← hjk]
          group
        have hzmem : z ∈ Subgroup.closure
            ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) :=
          Subgroup.subset_closure (by simp)
        have hamem : (a : ModGL Tag.E8 L) ∈ Subgroup.closure
            ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) :=
          Subgroup.subset_closure (by simp)
        have hbmem : (b : ModGL Tag.E8 L) ∈ Subgroup.closure
            ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) :=
          Subgroup.subset_closure (by simp)
        rw [hc_eq]
        exact mul_mem (mul_mem (pow_mem hzmem j) (inv_mem (pow_mem hbmem k)))
          (inv_mem (pow_mem hamem i))
      simpa using hc_mem
    have hcard : Nat.card E ≤ 5 ^ 3 := by
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      let F : (Fin 5 × Fin 5 × Fin 5) →
          Subgroup.closure ({z, (a : ModGL Tag.E8 L),
            (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) :=
        fun v => ⟨z ^ (v.1 : ℕ) * (a : ModGL Tag.E8 L) ^ (v.2.1 : ℕ) *
            (b : ModGL Tag.E8 L) ^ (v.2.2 : ℕ),
          (mem_closure_triple_iff (p := 5) hza hzb hab hz5 (hpowE a) (hpowE b) _).2
            ⟨v, rfl⟩⟩
      have hsurj : Function.Surjective F := by
        intro x
        obtain ⟨v, hv⟩ := (mem_closure_triple_iff (p := 5) hza hzb hab hz5
          (hpowE a) (hpowE b) (x : ModGL Tag.E8 L)).1 x.2
        exact ⟨v, Subtype.ext hv⟩
      haveI : Finite (Subgroup.closure
          ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L))) :=
        Finite.of_surjective F hsurj
      have hcl : Nat.card (Subgroup.closure
          ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L))) ≤ 5 ^ 3 := by
        calc Nat.card (Subgroup.closure
              ({z, (a : ModGL Tag.E8 L), (b : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)))
            ≤ Nat.card (Fin 5 × Fin 5 × Fin 5) := Nat.card_le_card_of_surjective F hsurj
          _ = 5 ^ 3 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod,
              Fintype.card_fin]
            norm_num
      exact (Subgroup.card_le_of_le hEclosure).trans hcl
    exact hcard

theorem exists_z_cube_of_nontoral_le_mulSub {ζ : L} (h5 : (5 : L) ≠ 0)
    (hζ : IsPrimitiveRoot ζ 5) (E : Subgroup (ModGL Tag.E8 L)) (hE : E ≤ mulSub L)
    (hE5 : CFSG.Open.IsElemAbelian 5 E) (hcard : 5 ^ 3 ≤ Nat.card E)
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ e ∈ E, g⁻¹ * e * g ∈ torusGroup Tag.E8 L) :
    ∃ e ∈ E, ∃ e' ∈ E, griessZ hζ ∈ E ∧ CubeBasis (griessZ hζ) e e' ∧
      Subgroup.closure ({griessZ hζ, e, e'} : Set (ModGL Tag.E8 L)) = E := by
  have hcardeq : Nat.card E = 5 ^ 3 :=
    Nat.le_antisymm (card_le_five_cube_of_nontoral_le_mulSub h5 hζ E hE hE5 hnt) hcard
  obtain ⟨a, ha, b, hb, c, hc, hgen⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3.exists_three_gen_of_card_cube
      (by norm_num : Nat.Prime 5) E hcardeq hE5.2
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, Commute x y := by
    intro x hx y hy
    exact congrArg (fun t : E => (t : ModGL Tag.E8 L))
      (hE5.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcardgen : Nat.card (Subgroup.closure ({a, b, c} : Set (ModGL Tag.E8 L))) = 5 ^ 3 := by
    rw [← hgen]
    exact hcardeq
  have hbas : CubeBasis a b c := CubeBasis.of_card
    (hcomm a ha b hb) (hcomm a ha c hc) (hcomm b hb c hc)
    (hE5.2 a ha) (hE5.2 b hb) (hE5.2 c hc) hcardgen
  have hntgen : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({a, b, c} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L := by
    rw [← hgen]
    exact hnt
  obtain ⟨e, e', hz, hcl⟩ := z_basis_of_nontoral h5 hζ hbas (hE ha) (hE hb) (hE hc) hntgen
  rw [← hgen] at hz hcl
  have he : e ∈ E := hcl ▸ Subgroup.subset_closure (by simp)
  have he' : e' ∈ E := hcl ▸ Subgroup.subset_closure (by simp)
  refine ⟨e, he, e', he', hz, ?_, hcl⟩
  apply CubeBasis.of_card (hcomm _ hz _ he) (hcomm _ hz _ he') (hcomm _ he _ he')
    (griessZ_pow_five hζ) (hE5.2 e he) (hE5.2 e' he')
  rw [hcl]
  exact hcardeq

theorem mulSub_le_adjointGroup : mulSub L ≤ adjointGroup Tag.E8 L := by
  rintro _ ⟨Y, U, rfl⟩
  exact mul_mem (rho_mem_adjointGroup _ _) (rho_mem_adjointGroup _ _)

theorem centralizer_nontoral_cube_eq
    {ζ : L} (h5 : (5 : L) ≠ 0) (hζ : IsPrimitiveRoot ζ 5)
    {a b : ModGL Tag.E8 L} (hbasis : CubeBasis (griessZ hζ) a b)
    (ha : a ∈ mulSub L) (hb : b ∈ mulSub L)
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L) :
    Subgroup.centralizer (Subgroup.closure
      ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) : Set (ModGL Tag.E8 L)) ⊓
      adjointGroup Tag.E8 L = Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) := by
  let E : Subgroup (ModGL Tag.E8 L) := Subgroup.closure {griessZ hζ, a, b}
  have hzE : griessZ hζ ∈ E := Subgroup.subset_closure (by simp)
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  obtain ⟨Y, U, Y', U', hYa, hYb, hnc⟩ := nc_lifts_of_nontoral h5 hζ ha hb
    hbasis.comm_bc.eq hbasis.pow_b hbasis.pow_c hbasis.comm_ab.eq hbasis.comm_ac.eq hnt
  have hEmul : E ≤ mulSub L := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact rhoA_le_mulSub (z_mem_range_rhoA hζ)
    · exact ha
    · exact hb
  have : IsMulCommutative E := Subgroup.isMulCommutative_closure (by
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) _ <;>
      first | exact Commute.refl _ | exact hbasis.comm_ab | exact hbasis.comm_ac |
        exact hbasis.comm_bc | exact hbasis.comm_ab.symm | exact hbasis.comm_ac.symm |
        exact hbasis.comm_bc.symm)
  apply le_antisymm
  · rintro c ⟨hcC, hcAd⟩
    have hc := Subgroup.mem_centralizer_iff.mp hcC
    have hcmul : c ∈ mulSub L := centralizer_le_mulSub hζ hcAd (hc _ hzE).symm
    obtain ⟨Yc, Uc, hYc⟩ := mem_mulSub.mp hcmul
    obtain ⟨j, i, k, heq⟩ := radical_pair_normal_form hζ hbasis.comm_bc
      (show Commute a c from hc _ haE) (show Commute b c from hc _ hbE)
      hbasis.pow_c hYa hYb hYc hnc
    have hceq : c = griessZ hζ ^ j * (b ^ k)⁻¹ * (a ^ i)⁻¹ := by
      rw [← heq]; group
    rw [hceq]
    exact E.mul_mem (E.mul_mem (E.pow_mem hzE _) (E.inv_mem (E.pow_mem hbE _)))
      (E.inv_mem (E.pow_mem haE _))
  · exact le_inf (Subgroup.le_centralizer E) (hEmul.trans mulSub_le_adjointGroup)

theorem exists_sl2_action_of_noncommuting_A_lifts {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b : ModGL Tag.E8 L} {Y U Y' U' : SL(5, L)}
    (ha : a = rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)
    (hb : b = rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U')
    (hcomm : a * b = b * a) (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1)
    (hYnc : Y * Y' ≠ Y' * Y) (M : SL(2, ZMod 5)) :
    ∃ γ ∈ mulSub L,
      γ * griessZ hζ * γ⁻¹ = griessZ hζ ∧
      γ * a * γ⁻¹ = a ^ (M 0 0).val * b ^ (M 1 0).val ∧
      γ * b * γ⁻¹ = a ^ (M 0 1).val * b ^ (M 1 1).val := by
  have hcomm' : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') =
      (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) := by
    simpa only [ha, hb] using hcomm
  obtain ⟨κ, κ', hTwA, hTwB, hκ5, hκ'5, hiff⟩ :=
    pair_data (Y := Y) (U := U) (Y' := Y') (U' := U') hcomm'
  have hκ1 : κ ≠ 1 := by
    intro h1
    apply hYnc
    exact sl_comm_iff.2 (Tw.commute_of_one (h1 ▸ hTwA))
  have hκ'1 : κ' ≠ 1 := fun h1 => hκ1 (hiff.2 h1)
  have hκprim : IsPrimitiveRoot κ 5 := isPrimitiveRoot_five_of_ne_one hκ5 hκ1
  have hκ'prim : IsPrimitiveRoot κ' 5 := isPrimitiveRoot_five_of_ne_one hκ'5 hκ'1
  have hκ0 : κ ≠ 0 := hκprim.ne_zero (by norm_num)
  have hκ'0 : κ' ≠ 0 := hκ'prim.ne_zero (by norm_num)
  let jA : ℕ := (M 0 0).val
  let kA : ℕ := (M 1 0).val
  let jB : ℕ := (M 0 1).val
  let kB : ℕ := (M 1 1).val
  have hdet : ((M : Matrix (Fin 2) (Fin 2) (ZMod 5)).det) = 1 := M.2
  have hdet' : (M 0 0 : ZMod 5) * M 1 1 = (M 1 0 : ZMod 5) * M 0 1 + 1 := by
    rw [Matrix.det_fin_two] at hdet
    calc (M 0 0 : ZMod 5) * M 1 1
        = ((M 0 0 : ZMod 5) * M 1 1 - M 0 1 * M 1 0) + M 0 1 * M 1 0 := by ring
      _ = 1 + M 0 1 * M 1 0 := by rw [hdet]
      _ = M 1 0 * M 0 1 + 1 := by ring
  have hcast : ((jA * kB : ℕ) : ZMod 5) = ((kA * jB + 1 : ℕ) : ZMod 5) := by
    dsimp only [jA, kA, jB, kB]
    push_cast
    rw [ZMod.natCast_zmod_val (M 0 0), ZMod.natCast_zmod_val (M 1 1),
      ZMod.natCast_zmod_val (M 1 0), ZMod.natCast_zmod_val (M 0 1)]
    exact hdet'
  have hmod : (jA * kB) % 5 = (kA * jB + 1) % 5 :=
    (ZMod.natCast_eq_natCast_iff' (jA * kB) (kA * jB + 1) 5).mp hcast
  have hκpow : κ ^ (jA * kB) * (κ ^ (kA * jB))⁻¹ = κ := by
    have heq : κ ^ (jA * kB) = κ ^ (kA * jB + 1) := by
      rw [pow_eq_pow_mod (jA * kB) hκ5, pow_eq_pow_mod (kA * jB + 1) hκ5, hmod]
    rw [heq, pow_succ']
    field_simp [hκ0]
  have hκ'pow : κ' ^ (jA * kB) * (κ' ^ (kA * jB))⁻¹ = κ' := by
    have heq : κ' ^ (jA * kB) = κ' ^ (kA * jB + 1) := by
      rw [pow_eq_pow_mod (jA * kB) hκ'5, pow_eq_pow_mod (kA * jB + 1) hκ'5, hmod]
    rw [heq, pow_succ']
    field_simp [hκ'0]
  let Y₁ : SL(5, L) := Y ^ jA * Y' ^ kA
  let Y₂ : SL(5, L) := Y ^ jB * Y' ^ kB
  let U₁ : SL(5, L) := U ^ jA * U' ^ kA
  let U₂ : SL(5, L) := U ^ jB * U' ^ kB
  have hTwA' : Tw κ (Y₁ : Matrix (Fin 5) (Fin 5) L) (Y₂ : Matrix (Fin 5) (Fin 5) L) := by
    have h := hTwA.power_products hκ0 jA kA jB kB
    rw [hκpow] at h
    simpa only [Y₁, Y₂, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow] using h
  have hTwB' : Tw κ' (U₁ : Matrix (Fin 5) (Fin 5) L) (U₂ : Matrix (Fin 5) (Fin 5) L) := by
    have h := hTwB.power_products hκ'0 jA kA jB kB
    rw [hκ'pow] at h
    simpa only [U₁, U₂, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow] using h
  have hpow_lift : ∀ j k : ℕ,
      a ^ j * b ^ k =
        rhoSigmaE8A4 L e8VA (Y ^ j * Y' ^ k) *
          rhoSigmaE8A4 L e8VB (U ^ j * U' ^ k) := by
    intro j k
    rw [ha, hb, lift_pow, lift_pow, lift_mul]
  have hb5_lift : (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U') ^ 5 = 1 := by
    rw [← hb]
    exact hb5
  obtain ⟨⟨cY', -, hY'5⟩, ⟨cU', -, hU'5⟩⟩ := pow_five_scalar hb5_lift
  have htrans5 : (a ^ jB * b ^ kB) ^ 5 = 1 := by
    have hcommC : Commute a b := hcomm
    have hcommB : Commute (a ^ jB) (b ^ kB) := (hcommC.pow_left jB).pow_right kB
    rw [hcommB.mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm jB 5, Nat.mul_comm kB 5,
      pow_mul, pow_mul, ha5, hb5]
    simp
  have htrans_lift : (rhoSigmaE8A4 L e8VA Y₂ * rhoSigmaE8A4 L e8VB U₂) ^ 5 = 1 := by
    rw [← hpow_lift jB kB]
    exact htrans5
  obtain ⟨⟨cY₂, -, hY₂5⟩, ⟨cU₂, -, hU₂5⟩⟩ := pow_five_scalar htrans_lift
  obtain ⟨SA, hSA0, hSA1⟩ := exists_sl_conj_heis_pairs hκprim
    (M₀ := (Y : Matrix (Fin 5) (Fin 5) L)) (M₁ := (Y' : Matrix (Fin 5) (Fin 5) L))
    (N₀ := (Y₁ : Matrix (Fin 5) (Fin 5) L)) (N₁ := (Y₂ : Matrix (Fin 5) (Fin 5) L))
    (sl_isUnit Y) (sl_isUnit Y') (sl_isUnit Y₁) (sl_isUnit Y₂)
    hTwA hTwA' hY'5 hY₂5 Y.2 Y'.2 Y₁.2 Y₂.2
  obtain ⟨SB, hSB0, hSB1⟩ := exists_sl_conj_heis_pairs hκ'prim
    (M₀ := (U : Matrix (Fin 5) (Fin 5) L)) (M₁ := (U' : Matrix (Fin 5) (Fin 5) L))
    (N₀ := (U₁ : Matrix (Fin 5) (Fin 5) L)) (N₁ := (U₂ : Matrix (Fin 5) (Fin 5) L))
    (sl_isUnit U) (sl_isUnit U') (sl_isUnit U₁) (sl_isUnit U₂)
    hTwB hTwB' hU'5 hU₂5 U.2 U'.2 U₁.2 U₂.2
  have hSA0' : Y₁ * SA = SA * Y := Subtype.ext hSA0
  have hSA1' : Y₂ * SA = SA * Y' := Subtype.ext hSA1
  have hSB0' : U₁ * SB = SB * U := Subtype.ext hSB0
  have hSB1' : U₂ * SB = SB * U' := Subtype.ext hSB1
  have hSAY : SA * Y * SA⁻¹ = Y₁ := by
    rw [← hSA0']
    group
  have hSAY' : SA * Y' * SA⁻¹ = Y₂ := by
    rw [← hSA1']
    group
  have hSBU : SB * U * SB⁻¹ = U₁ := by
    rw [← hSB0']
    group
  have hSBU' : SB * U' * SB⁻¹ = U₂ := by
    rw [← hSB1']
    group
  let γ : ModGL Tag.E8 L := rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB
  have hγmem : γ ∈ mulSub L := ⟨SA, SB, rfl⟩
  have hconj_forward : ∀ X V : SL(5, L),
      (rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB) *
          (rhoSigmaE8A4 L e8VA X * rhoSigmaE8A4 L e8VB V) *
          (rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB)⁻¹ =
        rhoSigmaE8A4 L e8VA (SA * X * SA⁻¹) *
          rhoSigmaE8A4 L e8VB (SB * V * SB⁻¹) := by
    intro X V
    have h := conj_lift (L := L) (SA := SA⁻¹) (SB := SB⁻¹) (Y := X) (U := V)
    rw [lift_inv] at h
    rw [inv_inv, inv_inv] at h
    rw [← lift_inv SA SB] at h
    exact h
  have hγz : γ * griessZ hζ * γ⁻¹ = griessZ hζ := by
    calc γ * griessZ hζ * γ⁻¹ = griessZ hζ * γ * γ⁻¹ := by
          rw [mulSub_comm_z (L := L) hζ hγmem]
      _ = griessZ hζ := by simp
  have hγa : γ * a * γ⁻¹ = a ^ jA * b ^ kA := by
    conv_lhs => rw [ha]
    rw [hconj_forward Y U, hSAY, hSBU]
    simpa only [Y₁, U₁] using (hpow_lift jA kA).symm
  have hγb : γ * b * γ⁻¹ = a ^ jB * b ^ kB := by
    conv_lhs => rw [hb]
    rw [hconj_forward Y' U', hSAY', hSBU']
    simpa only [Y₂, U₂] using (hpow_lift jB kB).symm
  refine ⟨γ, hγmem, hγz, ?_, ?_⟩
  · simpa only [jA, kA] using hγa
  · simpa only [jB, kB] using hγb

end Main

namespace FixZDet

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
open scoped MatrixGroups

variable {L : Type} [Field L]

private theorem scalar_factors_twist_iff {κ a b : L} (ha : a ≠ 0) (hb : b ≠ 0)
    {X Y : SL(5, L)} :
    Tw κ (((a • 1 : Matrix (Fin 5) (Fin 5) L) * (X : Matrix (Fin 5) (Fin 5) L)))
      (((b • 1 : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L))) ↔
      Tw κ (X : Matrix (Fin 5) (Fin 5) L) (Y : Matrix (Fin 5) (Fin 5) L) := by
  have hmul : ∀ c d : L, ∀ A B : SL(5, L),
      ((c • 1 : Matrix (Fin 5) (Fin 5) L) * (A : Matrix (Fin 5) (Fin 5) L)) *
          ((d • 1 : Matrix (Fin 5) (Fin 5) L) * (B : Matrix (Fin 5) (Fin 5) L)) =
        (c * d) • ((A : Matrix (Fin 5) (Fin 5) L) * (B : Matrix (Fin 5) (Fin 5) L)) := by
    intro c d A B
    calc
      ((c • 1 : Matrix (Fin 5) (Fin 5) L) * (A : Matrix (Fin 5) (Fin 5) L)) *
          ((d • 1 : Matrix (Fin 5) (Fin 5) L) * (B : Matrix (Fin 5) (Fin 5) L))
          = (c • (A : Matrix (Fin 5) (Fin 5) L)) *
              (d • (B : Matrix (Fin 5) (Fin 5) L)) := by
            simp only [Matrix.smul_mul, Matrix.one_mul]
      _ = (c * d) • ((A : Matrix (Fin 5) (Fin 5) L) * (B : Matrix (Fin 5) (Fin 5) L)) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm d c]
  constructor
  · intro h
    unfold Tw at h
    rw [hmul a b X Y, hmul b a Y X] at h
    have h' : (a * b) • ((X : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L)) =
        (a * b) • (κ • ((Y : Matrix (Fin 5) (Fin 5) L) * (X : Matrix (Fin 5) (Fin 5) L))) := by
      calc (a * b) • ((X : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L))
          = κ • ((b * a) • ((Y : Matrix (Fin 5) (Fin 5) L) * (X : Matrix (Fin 5) (Fin 5) L))) := h
        _ = κ • ((a * b) • ((Y : Matrix (Fin 5) (Fin 5) L) * (X : Matrix (Fin 5) (Fin 5) L))) := by rw [mul_comm b a]
        _ = (a * b) • (κ • ((Y : Matrix (Fin 5) (Fin 5) L) * (X : Matrix (Fin 5) (Fin 5) L))) := by
            rw [smul_smul, mul_comm, ← smul_smul]
    exact smul_right_injective _ (mul_ne_zero ha hb) h'
  · intro h
    unfold Tw at h ⊢
    rw [hmul a b X Y, hmul b a Y X, h, smul_smul, smul_smul, mul_comm b a,
      mul_comm κ (a * b)]

variable {L : Type} [Field L]

theorem point_stabilizer_det_eq_one {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b : ModGL Tag.E8 L} {Y U Y' U' : SL(5, L)}
    (ha : a = rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)
    (hb : b = rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U')
    (hab : a * b = b * a) (hnc : Y * Y' ≠ Y' * Y)
    {γ : ModGL Tag.E8 L} (hγ : γ ∈ mulSub L)
    {i j k i' j' k' : ℕ}
    (hconja : γ * a * γ⁻¹ = griessZ hζ ^ i * a ^ j * b ^ k)
    (hconjb : γ * b * γ⁻¹ = griessZ hζ ^ i' * a ^ j' * b ^ k') :
    (j : ZMod 5) * (k' : ZMod 5) - (k : ZMod 5) * (j' : ZMod 5) = 1 := by
  classical
  obtain ⟨κ, κ', hκ, hκ', hκ5, hκ'5, hiff⟩ := pair_data (Y := Y) (U := U) (Y' := Y')
    (U' := U') (by simpa [ha, hb] using hab)
  have hκ1 : κ ≠ 1 := fun h1 => hnc (sl_comm_iff.2 (Tw.commute_of_one (h1 ▸ hκ)))
  have hκprim : IsPrimitiveRoot κ 5 := isPrimitiveRoot_five_of_ne_one hκ5 hκ1
  obtain ⟨SA, SB, hγlift⟩ := mem_mulSub.mp hγ
  obtain ⟨Z, hZ⟩ := z_mem_range_rhoA (L := L) hζ
  have hZcomm : ∀ X : SL(5, L), Z * X = X * Z := by
    intro X
    apply rhoSigmaE8A4_injective (L := L) e8VA
    rw [map_mul, map_mul, hZ]
    exact griessZ_comm_rhoA hζ X
  obtain ⟨c, hZc⟩ := scalar_of_central hZcomm
  have hc0 : c ≠ 0 := by
    have hdet : (Z : Matrix (Fin 5) (Fin 5) L).det = 1 := Z.2
    have hc5 : c ^ 5 = 1 := by
      rw [hZc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at hdet
      simpa using hdet
    intro hc
    rw [hc, zero_pow (by norm_num : 5 ≠ 0)] at hc5
    exact zero_ne_one hc5
  have hγinv : γ⁻¹ = rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹ := by
    rw [hγlift, lift_inv]
  have hsinv : rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB =
      (rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹)⁻¹ := by
    rw [lift_inv]
    simp
  have hconj_a_lift : γ * a * γ⁻¹ =
      rhoSigmaE8A4 L e8VA (SA * Y * SA⁻¹) *
        rhoSigmaE8A4 L e8VB (SB * U * SB⁻¹) := by
    calc γ * a * γ⁻¹
        = (rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB) * a *
            (rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹) := by
            rw [hγinv, hγlift]
      _ = (rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹)⁻¹ * a *
            (rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹) := by rw [hsinv]
      _ = rhoSigmaE8A4 L e8VA (SA * Y * SA⁻¹) *
            rhoSigmaE8A4 L e8VB (SB * U * SB⁻¹) := by
            rw [ha]
            simpa using conj_lift (L := L) SA⁻¹ SB⁻¹ Y U
  have hconj_b_lift : γ * b * γ⁻¹ =
      rhoSigmaE8A4 L e8VA (SA * Y' * SA⁻¹) *
        rhoSigmaE8A4 L e8VB (SB * U' * SB⁻¹) := by
    calc γ * b * γ⁻¹
        = (rhoSigmaE8A4 L e8VA SA * rhoSigmaE8A4 L e8VB SB) * b *
            (rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹) := by
            rw [hγinv, hγlift]
      _ = (rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹)⁻¹ * b *
            (rhoSigmaE8A4 L e8VA SA⁻¹ * rhoSigmaE8A4 L e8VB SB⁻¹) := by rw [hsinv]
      _ = rhoSigmaE8A4 L e8VA (SA * Y' * SA⁻¹) *
            rhoSigmaE8A4 L e8VB (SB * U' * SB⁻¹) := by
            rw [hb]
            simpa using conj_lift (L := L) SA⁻¹ SB⁻¹ Y' U'
  have hzpow : ∀ n : ℕ, griessZ hζ ^ n = rhoSigmaE8A4 L e8VA (Z ^ n) := by
    intro n
    rw [← hZ, map_pow]
  have hRHSa : griessZ hζ ^ i * a ^ j * b ^ k =
      rhoSigmaE8A4 L e8VA (Z ^ i * (Y ^ j * Y' ^ k)) *
        rhoSigmaE8A4 L e8VB (U ^ j * U' ^ k) := by
    rw [hzpow, ha, hb, lift_pow, lift_pow, mul_assoc, lift_mul, ← mul_assoc, ← map_mul]
  have hRHSb : griessZ hζ ^ i' * a ^ j' * b ^ k' =
      rhoSigmaE8A4 L e8VA (Z ^ i' * (Y ^ j' * Y' ^ k')) *
        rhoSigmaE8A4 L e8VB (U ^ j' * U' ^ k') := by
    rw [hzpow, ha, hb, lift_pow, lift_pow, mul_assoc, lift_mul, ← mul_assoc, ← map_mul]
  have hpairA :
      (SA * Y * SA⁻¹) * (SA * Y' * SA⁻¹) *
          ((SA * Y' * SA⁻¹) * (SA * Y * SA⁻¹))⁻¹ =
        (Z ^ i * (Y ^ j * Y' ^ k)) * (Z ^ i' * (Y ^ j' * Y' ^ k')) *
          ((Z ^ i' * (Y ^ j' * Y' ^ k')) * (Z ^ i * (Y ^ j * Y' ^ k)))⁻¹ := by
    exact comm_lift_A_eq_of_lift_eq
      (Y := SA * Y * SA⁻¹) (U := SB * U * SB⁻¹)
      (Y' := SA * Y' * SA⁻¹) (U' := SB * U' * SB⁻¹)
      (V := Z ^ i * (Y ^ j * Y' ^ k)) (W := U ^ j * U' ^ k)
      (V' := Z ^ i' * (Y ^ j' * Y' ^ k')) (W' := U ^ j' * U' ^ k')
      (by rw [← hconj_a_lift, hconja]; exact hRHSa)
      (by rw [← hconj_b_lift, hconjb]; simpa using hRHSb)
  let C : SL(5, L) := Y * Y' * (Y' * Y)⁻¹
  let D : SL(5, L) := ⟨κ • 1, by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact hκ5⟩
  have hκD : Y * Y' = D * (Y' * Y) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [show (D : Matrix (Fin 5) (Fin 5) L) = κ • 1 from rfl,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.smul_mul, Matrix.one_mul]
    simpa only [Tw] using hκ
  have hCeq : C = D := by
    dsimp [C]
    calc Y * Y' * (Y' * Y)⁻¹ = D * (Y' * Y) * (Y' * Y)⁻¹ := by rw [hκD]
      _ = D := by group
  have hCmat : (C : Matrix (Fin 5) (Fin 5) L) = κ • 1 := by
    rw [hCeq]
  have hleft : (SA * Y * SA⁻¹) * (SA * Y' * SA⁻¹) *
        ((SA * Y' * SA⁻¹) * (SA * Y * SA⁻¹))⁻¹ =
      SA * C * SA⁻¹ := by
    dsimp [C]
    group
  have hCcomm : C * SA = SA * C := sl_scalar_central hCmat SA
  have hconjC : SA * C * SA⁻¹ = C := by
    rw [← hCcomm]
    group
  have hleft_scalar :
      (((SA * C * SA⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L)) = κ • 1 := by
    rw [hconjC]
    exact hCmat
  have hcommA_scalar :
      (((Z ^ i * (Y ^ j * Y' ^ k)) * (Z ^ i' * (Y ^ j' * Y' ^ k')) *
          ((Z ^ i' * (Y ^ j' * Y' ^ k')) * (Z ^ i * (Y ^ j * Y' ^ k)))⁻¹ :
        SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = κ • 1 := by
    rw [← hpairA, hleft]
    exact hleft_scalar
  have hTwZ : Tw κ
      (((Z ^ i * (Y ^ j * Y' ^ k) : SL(5, L)) : Matrix (Fin 5) (Fin 5) L))
      (((Z ^ i' * (Y ^ j' * Y' ^ k') : SL(5, L)) : Matrix (Fin 5) (Fin 5) L)) :=
    tw_of_comm5 hcommA_scalar
  have hZpow_mat : ∀ n : ℕ,
      (((Z ^ n : SL(5, L)) : Matrix (Fin 5) (Fin 5) L)) = (c ^ n) • 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, hZc, Matrix.smul_mul,
          Matrix.one_mul, smul_smul, pow_succ]
  have hTwZ' : Tw κ
      (((c ^ i • 1 : Matrix (Fin 5) (Fin 5) L) *
        ((Y ^ j * Y' ^ k : SL(5, L)) : Matrix (Fin 5) (Fin 5) L)))
      (((c ^ i' • 1 : Matrix (Fin 5) (Fin 5) L) *
        ((Y ^ j' * Y' ^ k' : SL(5, L)) : Matrix (Fin 5) (Fin 5) L))) := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, hZpow_mat i, hZpow_mat i'] using hTwZ
  have hTwA : Tw κ (((Y ^ j * Y' ^ k : SL(5, L)) : Matrix (Fin 5) (Fin 5) L))
      (((Y ^ j' * Y' ^ k' : SL(5, L)) : Matrix (Fin 5) (Fin 5) L)) :=
    (scalar_factors_twist_iff (κ := κ) (a := c ^ i) (b := c ^ i')
      (pow_ne_zero i hc0) (pow_ne_zero i' hc0)
      (X := Y ^ j * Y' ^ k) (Y := Y ^ j' * Y' ^ k')).1 hTwZ'
  have hTwA' : Tw κ ((Y : Matrix (Fin 5) (Fin 5) L) ^ j * (Y' : Matrix (Fin 5) (Fin 5) L) ^ k)
      ((Y : Matrix (Fin 5) (Fin 5) L) ^ j' * (Y' : Matrix (Fin 5) (Fin 5) L) ^ k') := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using hTwA
  have hmod := Tw.power_products_mod_five hκprim (sl_isUnit Y) (sl_isUnit Y') hκ j k j' k' hTwA'
  have hcast : ((j * k' : ℕ) : ZMod 5) = ((k * j' + 1 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff' _ _ 5).2 hmod
  have hcast' : (j : ZMod 5) * (k' : ZMod 5) = (k : ZMod 5) * (j' : ZMod 5) + 1 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcast
  rw [hcast']
  ring

end FixZDet

section Basic

variable {L : Type} [Field L]

theorem comm5_of_tw {Y Y' : SL(5, L)} {κ : L}
    (h : Tw κ (Y : Matrix (Fin 5) (Fin 5) L) (Y' : Matrix (Fin 5) (Fin 5) L)) :
    ((Y * Y' * (Y' * Y)⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = κ • 1 := by
  have hdet : ((Y' : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L)).det = 1 := by
    rw [Matrix.det_mul, Y'.2, Y.2, mul_one]
  calc ((Y * Y' * (Y' * Y)⁻¹ : SL(5, L)) : Matrix (Fin 5) (Fin 5) L)
      = ((Y : Matrix (Fin 5) (Fin 5) L) * (Y' : Matrix (Fin 5) (Fin 5) L)) *
          Matrix.adjugate ((Y' : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L)) := by
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
          Matrix.adjugate_mul_distrib]
    _ = (κ • ((Y' : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L))) *
          Matrix.adjugate ((Y' : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L)) := by
        rw [h]
    _ = κ • (((Y' : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L)) *
          Matrix.adjugate ((Y' : Matrix (Fin 5) (Fin 5) L) * (Y : Matrix (Fin 5) (Fin 5) L))) := by
        rw [Matrix.smul_mul]
    _ = κ • 1 := by
        rw [Matrix.mul_adjugate, hdet, one_smul]

end Basic

section Pair

variable {L : Type} [Field L] [IsAlgClosed L]

local notation "lift" => (fun (Y U : SL(5, L)) =>
  rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U)

theorem conj_lift_left (SA SB Y U : SL(5, L)) :
    lift SA SB * lift Y U * (lift SA SB)⁻¹ =
      lift (SA * Y * SA⁻¹) (SB * U * SB⁻¹) := by
  have hleft : lift SA SB = (lift SA⁻¹ SB⁻¹)⁻¹ := by
    rw [lift_inv SA⁻¹ SB⁻¹]
    simp
  have hright : (lift SA SB)⁻¹ = lift SA⁻¹ SB⁻¹ := lift_inv SA SB
  rw [hright, hleft, conj_lift SA⁻¹ SB⁻¹ Y U]
  simp

theorem exists_conj_comm_lift_pair
    {Y U Y' U' V W V' W' : SL(5, L)}
    (h : lift Y U * lift Y' U' = lift Y' U' * lift Y U)
    (h0 : lift V W * lift V' W' = lift V' W' * lift V W)
    (hg'5 : (lift Y' U') ^ 5 = 1)
    (hg0'5 : (lift V' W') ^ 5 = 1)
    (hA : Y * Y' * (Y' * Y)⁻¹ = V * V' * (V' * V)⁻¹)
    (hYnc : Y * Y' ≠ Y' * Y) :
    ∃ SA SB : SL(5, L),
      V * SA = SA * Y ∧ V' * SA = SA * Y' ∧
      W * SB = SB * U ∧ W' * SB = SB * U' ∧
      lift SA SB * lift Y U * (lift SA SB)⁻¹ = lift V W ∧
      lift SA SB * lift Y' U' * (lift SA SB)⁻¹ = lift V' W' := by
  classical
  obtain ⟨κA, hκA⟩ := (comm_lift_scalar h).1
  obtain ⟨κB0, hκB0⟩ := (comm_lift_scalar h).2
  obtain ⟨κ, κB, hTwκ, hTwκB, hκ5, hκB5, hiff⟩ := pair_data h
  have hκAeq : κA = κ :=
    Tw.unique (sl_isUnit Y) (sl_isUnit Y') (tw_of_comm5 hκA) hTwκ
  have hκBeq : κB0 = κB :=
    Tw.unique (sl_isUnit U) (sl_isUnit U') (tw_of_comm5 hκB0) hTwκB
  have hκ1 : κ ≠ 1 := by
    intro h1
    exact hYnc (sl_comm_iff.2 (Tw.commute_of_one (by simpa [h1] using hTwκ)))
  have hκprim : IsPrimitiveRoot κ 5 := isPrimitiveRoot_five_of_ne_one hκ5 hκ1
  have hκB1 : κB ≠ 1 := fun h1 => hκ1 (hiff.2 h1)
  have hκBprim : IsPrimitiveRoot κB 5 := isPrimitiveRoot_five_of_ne_one hκB5 hκB1
  have hκAcomm : ((Y * Y' * (Y' * Y)⁻¹ : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) = κ • 1 := by
    rw [← hκAeq]
    exact hκA
  have hκVcomm : ((V * V' * (V' * V)⁻¹ : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) = κ • 1 := by
    rw [← hA]
    exact hκAcomm
  have hκBcomm : ((U * U' * (U' * U)⁻¹ : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) = κB • 1 := by
    rw [← hκBeq]
    exact hκB0
  have hBtarget : (U * U' * (U' * U)⁻¹ : SL(5, L)) = W * W' * (W' * W)⁻¹ :=
    comm_lift_B_eq_of_A_eq (Y := Y) (U := U) (Y' := Y') (U' := U')
      (V := V) (W := W) (V' := V') (W' := W') h h0 hA
  have hBtarget_mat : ((W * W' * (W' * W)⁻¹ : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) = ((U * U' * (U' * U)⁻¹ : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) := congrArg Subtype.val hBtarget.symm
  have hκWcomm : ((W * W' * (W' * W)⁻¹ : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) = κB • 1 := by
    rw [hBtarget_mat]
    exact hκBcomm
  obtain ⟨cY, hcY0, hY'pow⟩ := (pow_five_scalar hg'5).1
  obtain ⟨cU, hcU0, hU'pow⟩ := (pow_five_scalar hg'5).2
  obtain ⟨cV, hcV0, hV'pow⟩ := (pow_five_scalar hg0'5).1
  obtain ⟨cW, hcW0, hW'pow⟩ := (pow_five_scalar hg0'5).2
  obtain ⟨SA, hSA0, hSA1⟩ :=
    exists_sl_conj_heis_pairs hκprim (sl_isUnit Y) (sl_isUnit Y') (sl_isUnit V) (sl_isUnit V')
      (tw_of_comm5 hκAcomm) (tw_of_comm5 hκVcomm) hY'pow hV'pow Y.2 Y'.2 V.2 V'.2
  obtain ⟨SB, hSB0, hSB1⟩ :=
    exists_sl_conj_heis_pairs hκBprim (sl_isUnit U) (sl_isUnit U') (sl_isUnit W) (sl_isUnit W')
      (tw_of_comm5 hκBcomm) (tw_of_comm5 hκWcomm) hU'pow hW'pow U.2 U'.2 W.2 W'.2
  have hSA0' : V * SA = SA * Y :=
    Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hSA0)
  have hSA1' : V' * SA = SA * Y' :=
    Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hSA1)
  have hSB0' : W * SB = SB * U :=
    Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hSB0)
  have hSB1' : W' * SB = SB * U' :=
    Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hSB1)
  have hSAY : SA * Y * SA⁻¹ = V := by
    calc SA * Y * SA⁻¹ = (V * SA) * SA⁻¹ := by rw [← hSA0']
      _ = V := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hSAY' : SA * Y' * SA⁻¹ = V' := by
    calc SA * Y' * SA⁻¹ = (V' * SA) * SA⁻¹ := by rw [← hSA1']
      _ = V' := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hSBU : SB * U * SB⁻¹ = W := by
    calc SB * U * SB⁻¹ = (W * SB) * SB⁻¹ := by rw [← hSB0']
      _ = W := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hSBU' : SB * U' * SB⁻¹ = W' := by
    calc SB * U' * SB⁻¹ = (W' * SB) * SB⁻¹ := by rw [← hSB1']
      _ = W' := by rw [mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨SA, SB, hSA0', hSA1', hSB0', hSB1', ?_, ?_⟩
  · rw [conj_lift_left SA SB Y U, hSAY, hSBU]
  · rw [conj_lift_left SA SB Y' U', hSAY', hSBU']

theorem exists_conj_cube_of_basis
    (h5 : (5 : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {a b a' b' : ModGL Tag.E8 L}
    (ha : a ∈ mulSub L) (hb : b ∈ mulSub L)
    (ha' : a' ∈ mulSub L) (hb' : b' ∈ mulSub L)
    (hbas : CubeBasis (griessZ hζ) a b) (hbas' : CubeBasis (griessZ hζ) a' b')
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L)
    (hnt' : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, a', b'} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L) :
    ∃ γ ∈ mulSub L,
      Subgroup.map (MulAut.conj γ).toMonoidHom
        (Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L))) =
      Subgroup.closure ({griessZ hζ, a', b'} : Set (ModGL Tag.E8 L)) := by
  classical
  obtain ⟨Ya, Ua, Yb, Ub, hae, hbe, hncsrc⟩ :=
    nc_lifts_of_nontoral h5 hζ ha hb hbas.comm_bc.eq hbas.pow_b hbas.pow_c
      (mulSub_comm_z hζ ha).symm (mulSub_comm_z hζ hb).symm hnt
  obtain ⟨Ya', Ua', Yb', Ub', hae', hbe', hnctgt⟩ :=
    nc_lifts_of_nontoral h5 hζ ha' hb' hbas'.comm_bc.eq hbas'.pow_b hbas'.pow_c
      (mulSub_comm_z hζ ha').symm (mulSub_comm_z hζ hb').symm hnt'
  have hae_u : ((rhoSigmaE8A4 L e8VA) Ya * (rhoSigmaE8A4 L e8VB) Ua) = a := by
    simpa only using hae.symm
  have hbe_u : ((rhoSigmaE8A4 L e8VA) Yb * (rhoSigmaE8A4 L e8VB) Ub) = b := by
    simpa only using hbe.symm
  have hae'_u : ((rhoSigmaE8A4 L e8VA) Ya' * (rhoSigmaE8A4 L e8VB) Ua') = a' := by
    simpa only using hae'.symm
  have hbe'_u : ((rhoSigmaE8A4 L e8VA) Yb' * (rhoSigmaE8A4 L e8VB) Ub') = b' := by
    simpa only using hbe'.symm
  have hcomm_lift : lift Ya Ua * lift Yb Ub = lift Yb Ub * lift Ya Ua := by
    change ((rhoSigmaE8A4 L e8VA) Ya * (rhoSigmaE8A4 L e8VB) Ua) *
        ((rhoSigmaE8A4 L e8VA) Yb * (rhoSigmaE8A4 L e8VB) Ub) =
      ((rhoSigmaE8A4 L e8VA) Yb * (rhoSigmaE8A4 L e8VB) Ub) *
        ((rhoSigmaE8A4 L e8VA) Ya * (rhoSigmaE8A4 L e8VB) Ua)
    rw [hae_u, hbe_u]
    exact hbas.comm_bc.eq
  have hcomm_lift' : lift Ya' Ua' * lift Yb' Ub' = lift Yb' Ub' * lift Ya' Ua' := by
    change ((rhoSigmaE8A4 L e8VA) Ya' * (rhoSigmaE8A4 L e8VB) Ua') *
        ((rhoSigmaE8A4 L e8VA) Yb' * (rhoSigmaE8A4 L e8VB) Ub') =
      ((rhoSigmaE8A4 L e8VA) Yb' * (rhoSigmaE8A4 L e8VB) Ub') *
        ((rhoSigmaE8A4 L e8VA) Ya' * (rhoSigmaE8A4 L e8VB) Ua')
    rw [hae'_u, hbe'_u]
    exact hbas'.comm_bc.eq
  obtain ⟨κ, κB, hTwκ, hTwκB, hκ5, hκB5, hiff⟩ :=
    pair_data (Y := Ya) (U := Ua) (Y' := Yb) (U' := Ub) hcomm_lift
  obtain ⟨κ', κB', hTwκ', hTwκB', hκ'5, hκB'5, hiff'⟩ :=
    pair_data (Y := Ya') (U := Ua') (Y' := Yb') (U' := Ub') hcomm_lift'
  have hκ1 : κ ≠ 1 := by
    intro h1
    exact hncsrc (sl_comm_iff.2 (Tw.commute_of_one (by simpa [h1] using hTwκ)))
  have hκprim : IsPrimitiveRoot κ 5 := isPrimitiveRoot_five_of_ne_one hκ5 hκ1
  have hκ'1 : κ' ≠ 1 := by
    intro h1
    exact hnctgt (sl_comm_iff.2 (Tw.commute_of_one (by simpa [h1] using hTwκ')))
  have hκ'prim : IsPrimitiveRoot κ' 5 := isPrimitiveRoot_five_of_ne_one hκ'5 hκ'1
  obtain ⟨i, hi⟩ := exists_pow_eq_of_pow_five hκprim hκ'5
  have hi5 : ¬ 5 ∣ i := by
    intro hdiv
    obtain ⟨q, rfl⟩ := hdiv
    have h1 : κ' = 1 := by rw [← hi, pow_mul, hκ5, one_pow]
    exact hκ'1 h1
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hi5).symm (by norm_num : 1 < 5)
  set c : ModGL Tag.E8 L := b ^ i with hc
  have hb_eq : b = c ^ m := by
    rw [hc, ← pow_mul, pow_eq_pow_mod _ hbas.pow_c, hm, pow_one]
  have hm1z : griessZ hζ ∈ ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) :=
    Set.mem_insert _ _
  have hm1a : a ∈ ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hm1b : b ∈ ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hm2z : griessZ hζ ∈ ({griessZ hζ, a, c} : Set (ModGL Tag.E8 L)) :=
    Set.mem_insert _ _
  have hm2a : a ∈ ({griessZ hζ, a, c} : Set (ModGL Tag.E8 L)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hm2c : c ∈ ({griessZ hζ, a, c} : Set (ModGL Tag.E8 L)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hcl_eq : Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) =
      Subgroup.closure ({griessZ hζ, a, c} : Set (ModGL Tag.E8 L)) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact Subgroup.subset_closure hm2z
      · exact Subgroup.subset_closure hm2a
      · rw [hb_eq]
        exact pow_mem (Subgroup.subset_closure hm2c) m
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact Subgroup.subset_closure hm1z
      · exact Subgroup.subset_closure hm1a
      · rw [hc]
        exact pow_mem (Subgroup.subset_closure hm1b) i
  have hb_i_lift : b ^ i = lift (Yb ^ i) (Ub ^ i) := by
    rw [hbe, lift_pow]
  have hb_i_lift_u : ((rhoSigmaE8A4 L e8VA) (Yb ^ i) *
      (rhoSigmaE8A4 L e8VB) (Ub ^ i)) = b ^ i := by
    simpa only using hb_i_lift.symm
  have hbpow5 : (b ^ i) ^ 5 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hbas.pow_c, one_pow]
  have hg'5 : (lift (Yb ^ i) (Ub ^ i)) ^ 5 = 1 := by
    change (((rhoSigmaE8A4 L e8VA) (Yb ^ i) * (rhoSigmaE8A4 L e8VB) (Ub ^ i)) ^ 5) = 1
    rw [hb_i_lift_u]
    exact hbpow5
  have hg0'5 : (lift Yb' Ub') ^ 5 = 1 := by
    change (((rhoSigmaE8A4 L e8VA) Yb' * (rhoSigmaE8A4 L e8VB) Ub') ^ 5) = 1
    rw [hbe'_u]
    exact hbas'.pow_c
  have hcomm_mod : lift Ya Ua * lift (Yb ^ i) (Ub ^ i) =
      lift (Yb ^ i) (Ub ^ i) * lift Ya Ua := by
    change ((rhoSigmaE8A4 L e8VA) Ya * (rhoSigmaE8A4 L e8VB) Ua) *
        ((rhoSigmaE8A4 L e8VA) (Yb ^ i) * (rhoSigmaE8A4 L e8VB) (Ub ^ i)) =
      ((rhoSigmaE8A4 L e8VA) (Yb ^ i) * (rhoSigmaE8A4 L e8VB) (Ub ^ i)) *
        ((rhoSigmaE8A4 L e8VA) Ya * (rhoSigmaE8A4 L e8VB) Ua)
    rw [hae_u, hb_i_lift_u]
    exact (hbas.comm_bc.pow_right i).eq
  have hcomm_tgt : lift Ya' Ua' * lift Yb' Ub' = lift Yb' Ub' * lift Ya' Ua' := by
    change ((rhoSigmaE8A4 L e8VA) Ya' * (rhoSigmaE8A4 L e8VB) Ua') *
        ((rhoSigmaE8A4 L e8VA) Yb' * (rhoSigmaE8A4 L e8VB) Ub') =
      ((rhoSigmaE8A4 L e8VA) Yb' * (rhoSigmaE8A4 L e8VB) Ub') *
        ((rhoSigmaE8A4 L e8VA) Ya' * (rhoSigmaE8A4 L e8VB) Ua')
    rw [hae'_u, hbe'_u]
    exact hbas'.comm_bc.eq
  have hTwκi : Tw (κ ^ i) (Ya : Matrix (Fin 5) (Fin 5) L) ((Yb ^ i : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) := by
    simpa [Matrix.SpecialLinearGroup.coe_pow] using hTwκ.pow_right i
  have hTwκ'i : Tw κ' (Ya : Matrix (Fin 5) (Fin 5) L) ((Yb ^ i : SL(5, L)) :
      Matrix (Fin 5) (Fin 5) L) := by
    simpa [hi] using hTwκi
  have hA : Ya * (Yb ^ i) * ((Yb ^ i) * Ya)⁻¹ =
      Ya' * Yb' * (Yb' * Ya')⁻¹ := by
    apply Subtype.ext
    rw [comm5_of_tw hTwκ'i, comm5_of_tw hTwκ']
  have hYnc_mod : Ya * (Yb ^ i) ≠ (Yb ^ i) * Ya := by
    intro hc
    have hTw1 : Tw 1 (Ya : Matrix (Fin 5) (Fin 5) L) ((Yb ^ i : SL(5, L)) :
        Matrix (Fin 5) (Fin 5) L) :=
      Tw.one_of_commute (by
        simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg Subtype.val hc)
    have heq : κ' = 1 := Tw.unique (sl_isUnit Ya) (sl_isUnit (Yb ^ i)) hTwκ'i hTw1
    exact hκ'1 heq
  obtain ⟨SA, SB, hSA0, hSA1, hSB0, hSB1, hconj_a, hconj_bi⟩ :=
    exists_conj_comm_lift_pair hcomm_mod hcomm_tgt hg'5 hg0'5 hA hYnc_mod
  let γ : ModGL Tag.E8 L := lift SA SB
  have hγmem : γ ∈ mulSub L := ⟨SA, SB, rfl⟩
  have hγz : γ * griessZ hζ * γ⁻¹ = griessZ hζ := by
    rw [show γ * griessZ hζ = griessZ hζ * γ from mulSub_comm_z hζ hγmem]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hγa : γ * a * γ⁻¹ = a' := by
    rw [← hae_u, ← hae'_u]
    exact hconj_a
  have hγbi : γ * (b ^ i) * γ⁻¹ = b' := by
    rw [← hb_i_lift_u, ← hbe'_u]
    exact hconj_bi
  have hγc : γ * c * γ⁻¹ = b' := by
    rw [hc]
    exact hγbi
  have hmap_i : Subgroup.map (MulAut.conj γ).toMonoidHom
      (Subgroup.closure ({griessZ hζ, a, c} : Set (ModGL Tag.E8 L))) =
      Subgroup.closure ({griessZ hζ, a', b'} : Set (ModGL Tag.E8 L)) := by
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hγz, hγa, hγc]
  refine ⟨γ, hγmem, ?_⟩
  calc Subgroup.map (MulAut.conj γ).toMonoidHom
        (Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)))
      = Subgroup.map (MulAut.conj γ).toMonoidHom
        (Subgroup.closure ({griessZ hζ, a, c} : Set (ModGL Tag.E8 L))) := by
        rw [hcl_eq]
    _ = Subgroup.closure ({griessZ hζ, a', b'} : Set (ModGL Tag.E8 L)) := hmap_i

end Pair

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
