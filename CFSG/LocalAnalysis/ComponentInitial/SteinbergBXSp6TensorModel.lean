module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbits
public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsAut
public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsLocal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel

open Subgroup Matrix
open CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3 unitri unitriGL sylowT unitri_mul)
open CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

abbrev tS : S := unitriGL 0 1 0

theorem coe_tS : ((tS : S) : Mat3) = unitri 0 1 0 := rfl

theorem tS_ne_one : tS ≠ 1 := fun h => by
  have := congrArg (fun g : S => (g : Mat3) 0 2) h
  revert this
  decide

set_option maxRecDepth 100000 in
theorem commute_tS_check : ∀ m₀₀ m₀₁ m₀₂ m₁₀ m₁₁ m₁₂ m₂₀ m₂₁ m₂₂ : ZMod 2,
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] * unitri 0 1 0 =
      unitri 0 1 0 * !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    m₀₀ * m₁₁ * m₂₂ - m₀₀ * m₁₂ * m₂₁ - m₀₁ * m₁₀ * m₂₂ + m₀₁ * m₁₂ * m₂₀ + m₀₂ * m₁₀ * m₂₁ -
      m₀₂ * m₁₁ * m₂₀ = 1 →
    IsUT !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] := by
  decide +kernel

theorem commute_tS_iff (g : S) : g * tS = tS * g ↔ g ∈ U3 := by
  constructor
  · intro h
    rw [mem_U3_iff]
    have h' : (g : Mat3) * unitri 0 1 0 = unitri 0 1 0 * (g : Mat3) := congrArg Units.val h
    have hdet := det_eq_one g
    rw [Matrix.det_fin_three] at hdet
    rw [Matrix.eta_fin_three (g : Mat3)] at h' ⊢
    exact commute_tS_check _ _ _ _ _ _ _ _ _ h' hdet
  · rintro ⟨a, b, c, rfl⟩
    apply Units.ext
    change unitri a b c * unitri 0 1 0 = unitri 0 1 0 * unitri a b c
    rw [unitri_mul, unitri_mul]
    congr 1 <;> ring

@[expose] def invS (M : Mat3) (h : M * M = 1) : S := ⟨M, M, h, h⟩

theorem exists_conj_unitri_tS : ∀ a b c : ZMod 2, unitri a b c * unitri a b c = 1 →
    unitri a b c ≠ 1 → ∃ h : S, (h : Mat3) * unitri a b c = unitri 0 1 0 * (h : Mat3) := by
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · intro _ h; exact absurd (by decide) h
  · intro _ _
    exact ⟨invS !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by decide), by decide⟩
  · intro _ _
    exact ⟨1, by decide⟩
  · intro _ _
    exact ⟨invS !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by decide), by decide⟩
  · intro _ _
    exact ⟨invS !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by decide), by decide⟩
  · intro h; exact absurd h (by decide)
  · intro _ _
    exact ⟨invS !![1, 0, 0; 0, 1, 0; 0, 1, 1] (by decide), by decide⟩
  · intro h; exact absurd h (by decide)

theorem exists_conj_eq_tS {x : S} (hx : x * x = 1) (h1 : x ≠ 1) : ∃ g : S, g * x * g⁻¹ = tS := by
  have hP : IsPGroup 2 (zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq, hx]) h1
  obtain ⟨g, hg⟩ := CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.exists_conj_le_sylowT hP
  obtain ⟨a, b, c, habc⟩ := hg x (mem_zpowers x)
  have hu : unitri a b c * unitri a b c = 1 := by
    have h2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
      rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group, hx]
      group
    rw [habc] at h2
    exact congrArg Units.val h2
  have hu1 : unitri a b c ≠ 1 := by
    intro h
    apply h1
    have h2 : g⁻¹ * x * g = 1 := by rw [habc]; exact Units.ext h
    rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group, h2]
    group
  obtain ⟨h, hh⟩ := exists_conj_unitri_tS a b c hu hu1
  refine ⟨h * g⁻¹, ?_⟩
  have hh' : h * (g⁻¹ * x * g) = tS * h := by
    rw [habc]
    exact Units.ext hh
  calc h * g⁻¹ * x * (h * g⁻¹)⁻¹ = h * (g⁻¹ * x * g) * h⁻¹ := by group
    _ = tS := by rw [hh']; group

theorem not_commute_U3 : unitriGL 1 0 0 * unitriGL 0 0 1 ≠ unitriGL 0 0 1 * unitriGL 1 0 0 :=
  fun h => absurd (congrArg Units.val h) (by decide)

theorem card_le_four_of_elementary {E : Subgroup S} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have hP : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq, hsq x x.2, Subgroup.coe_one])⟩
  obtain ⟨g, hg⟩ := CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.exists_conj_le_sylowT hP
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'T : E' ≤ U3 := by
    rintro _ ⟨x, hx, rfl⟩
    change g⁻¹ * x * g⁻¹⁻¹ ∈ U3
    rw [inv_inv]
    exact hg x hx
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hdvd : Nat.card E ∣ 8 := by
    rw [← hcard, ← card_U3]
    exact Subgroup.card_dvd_of_le hE'T
  have h8 : Nat.card E ≠ 8 := by
    intro h8
    have hEq : E' = U3 := Subgroup.eq_of_le_of_card_ge hE'T (by rw [hcard, h8, card_U3])
    have hc' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    exact not_commute_U3 (hc' _ (hEq ▸ ⟨1, 0, 0, rfl⟩) _ (hEq ▸ ⟨0, 0, 1, rfl⟩))
  have h8' : Nat.card E ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card E <;> simp_all

@[expose] def repM : Representation (ZMod 2) K Mat3 where
  toFun k :=
    { toFun := fun X => (k.1 : Mat3) * X * (k.2 : Mat3)ᵀ
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        rfl }
  map_one' := by
    ext X : 1
    simp
  map_mul' k k' := by
    ext X : 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, Prod.fst_mul, Prod.snd_mul,
      Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem repM_apply (k : K) (X : Mat3) : repM k X = (k.1 : Mat3) * X * (k.2 : Mat3)ᵀ := rfl

@[expose] def transM : Mat3 →ₗ[ZMod 2] Mat3 :=
  (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) (ZMod 2) (ZMod 2)).toLinearMap

theorem transM_apply (X : Mat3) : transM X = Xᵀ := rfl

theorem transM_transM (X : Mat3) : transM (transM X) = X := Matrix.transpose_transpose X

theorem transM_mul_transM : transM * transM = 1 := LinearMap.ext transM_transM

theorem transM_repM (k : K) (X : Mat3) : transM (repM k X) = repM k.swap (transM X) := by
  rw [transM_apply, transM_apply, repM_apply, repM_apply, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rfl

theorem transM_mul_repM (k : K) : transM * repM k = repM k.swap * transM :=
  LinearMap.ext (transM_repM k)

theorem mult_two_cases (x : Multiplicative (ZMod 2)) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  induction x using Multiplicative.rec with
  | ofAdd a =>
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem prodComm_mul_self : (MulEquiv.prodComm : MulAut K) * MulEquiv.prodComm = 1 :=
  MulEquiv.ext fun _ => rfl

@[expose] def swapAct : Multiplicative (ZMod 2) →* MulAut K where
  toFun ε := if Multiplicative.toAdd ε = 0 then 1 else MulEquiv.prodComm
  map_one' := by simp
  map_mul' ε ε' := by
    rcases mult_two_cases ε with rfl | rfl <;> rcases mult_two_cases ε' with rfl | rfl
    · simp
    · simp
    · simp
    · rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd 1) = 0 from rfl, ite_eq_left rfl,
        ite_eq_right (show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 0 by decide),
        prodComm_mul_self]

theorem swapAct_one_apply (k : K) : swapAct 1 k = k := rfl

theorem swapAct_s_apply (k : K) : swapAct (Multiplicative.ofAdd 1) k = k.swap := rfl

abbrev Ehat : Type := K ⋊[swapAct] Multiplicative (ZMod 2)

instance finite_Ehat : Finite Ehat :=
  Finite.of_injective (fun e : Ehat => (e.left, e.right)) fun _ _ h =>
    SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

abbrev sE : Ehat := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[expose] def transPow (ε : Multiplicative (ZMod 2)) : Module.End (ZMod 2) Mat3 :=
  if Multiplicative.toAdd ε = 0 then 1 else transM

theorem transPow_one : transPow 1 = 1 := rfl

theorem transPow_s : transPow (Multiplicative.ofAdd 1) = transM := rfl

theorem transPow_mul (ε ε' : Multiplicative (ZMod 2)) :
    transPow (ε * ε') = transPow ε * transPow ε' := by
  rcases mult_two_cases ε with rfl | rfl <;> rcases mult_two_cases ε' with rfl | rfl
  · rfl
  · simp [transPow_one]
  · simp [transPow_one]
  · rw [show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 from rfl,
      transPow_one, transPow_s, transM_mul_transM]

theorem transPow_mul_repM (ε : Multiplicative (ZMod 2)) (k : K) :
    transPow ε * repM k = repM (swapAct ε k) * transPow ε := by
  rcases mult_two_cases ε with rfl | rfl
  · rw [transPow_one, one_mul, mul_one]
    rfl
  · rw [transPow_s, transM_mul_repM]
    rfl

@[expose] def repE : Representation (ZMod 2) Ehat Mat3 where
  toFun e := repM e.left * transPow e.right
  map_one' := by
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, map_one, transPow_one, mul_one]
  map_mul' e e' := by
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul, transPow_mul,
      mul_assoc (repM e.left) (transPow e.right), ← mul_assoc (transPow e.right),
      transPow_mul_repM]
    simp only [mul_assoc]

theorem repE_inl (k : K) : repE (SemidirectProduct.inl k) = repM k := by
  change repM k * transPow 1 = repM k
  rw [transPow_one, mul_one]

theorem repE_inl_apply (k : K) (X : Mat3) :
    repE (SemidirectProduct.inl k) X = (k.1 : Mat3) * X * (k.2 : Mat3)ᵀ := by
  rw [repE_inl, repM_apply]

theorem repE_sE_apply (X : Mat3) : repE sE X = Xᵀ := by
  change (1 : Mat3) * transM X * ((1 : S) : Mat3)ᵀ = Xᵀ
  rw [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, transM_apply]

theorem repE_mul_apply (e e' : Ehat) (X : Mat3) : repE (e * e') X = repE e (repE e' X) := by
  rw [map_mul]
  rfl

theorem repE_inv_apply_apply (e : Ehat) (X : Mat3) : repE e⁻¹ (repE e X) = X := by
  rw [← repE_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem repE_apply_inv_apply (e : Ehat) (X : Mat3) : repE e (repE e⁻¹ X) = X := by
  rw [← repE_mul_apply, mul_inv_cancel, map_one]
  rfl

abbrev FixM (T : Set Ehat) : Type := {X : Mat3 // ∀ b ∈ T, repE b X = X}

theorem card_fixM_anti {T T' : Set Ehat} (h : T ⊆ T') :
    Nat.card (FixM T') ≤ Nat.card (FixM T) :=
  Nat.card_le_card_of_injective (fun X => ⟨X.1, fun b hb => X.2 b (h hb)⟩)
    fun X Y hXY => by simpa [Subtype.ext_iff] using hXY

theorem card_fixM_conj (e : Ehat) (T : Set Ehat) :
    Nat.card (FixM ((fun b => e * b * e⁻¹) '' T)) = Nat.card (FixM T) := by
  refine Nat.card_congr
    { toFun := fun X => ⟨repE e⁻¹ X.1, fun b hb => ?_⟩
      invFun := fun X => ⟨repE e X.1, ?_⟩
      left_inv := fun X => Subtype.ext (repE_apply_inv_apply e X.1)
      right_inv := fun X => Subtype.ext (repE_inv_apply_apply e X.1) }
  · have h := X.2 _ ⟨b, hb, rfl⟩
    rw [repE_mul_apply, repE_mul_apply] at h
    rw [← repE_inv_apply_apply e (repE b _), h]
  · rintro _ ⟨b, hb, rfl⟩
    rw [repE_mul_apply, repE_mul_apply, repE_inv_apply_apply, X.2 b hb]

theorem card_le_of_recon {P : Mat3 → Prop} {n : ℕ} (f : Mat3 → Fin n → ZMod 2)
    (Φ : (Fin n → ZMod 2) → Mat3) (h : ∀ X, P X → X = Φ (f X)) :
    Nat.card {X // P X} ≤ 2 ^ n := by
  calc Nat.card {X // P X} ≤ Nat.card (Fin n → ZMod 2) :=
        Nat.card_le_card_of_injective (fun X => f X.1) fun X Y hXY =>
          Subtype.ext ((h X.1 X.2).trans ((congrArg Φ hXY).trans (h Y.1 Y.2).symm))
    _ = 2 ^ n := by simp [Nat.card_eq_fintype_card, ZMod.card]

set_option maxRecDepth 100000 in
theorem fix_t1_check : ∀ m₀₀ m₀₁ m₀₂ m₁₀ m₁₁ m₁₂ m₂₀ m₂₁ m₂₂ : ZMod 2,
    unitri 0 1 0 * !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; 0, 0, 0] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_tt_check : ∀ m₀₀ m₀₁ m₀₂ m₁₀ m₁₁ m₁₂ m₂₀ m₂₁ m₂₂ : ZMod 2,
    unitri 0 1 0 * !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] * (unitri 0 1 0)ᵀ =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, 0; m₀₂, 0, 0] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_t1_1t_check : ∀ m₀₀ m₀₁ m₀₂ m₁₀ m₁₁ m₁₂ m₂₀ m₂₁ m₂₂ : ZMod 2,
    unitri 0 1 0 * !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] * (unitri 0 1 0)ᵀ =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] = !![m₀₀, m₀₁, 0; m₁₀, m₁₁, 0; 0, 0, 0] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_s_check : ∀ m₀₀ m₀₁ m₀₂ m₁₀ m₁₁ m₁₂ m₂₀ m₂₁ m₂₂ : ZMod 2,
    (!![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂])ᵀ =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] =
      !![m₀₀, m₀₁, m₀₂; m₀₁, m₁₁, m₁₂; m₀₂, m₁₂, m₂₂] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_s_tt_check : ∀ m₀₀ m₀₁ m₀₂ m₁₀ m₁₁ m₁₂ m₂₀ m₂₁ m₂₂ : ZMod 2,
    (!![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂])ᵀ =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    unitri 0 1 0 * !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] * (unitri 0 1 0)ᵀ =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] →
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] =
      !![m₀₀, m₀₁, m₀₂; m₀₁, m₁₁, 0; m₀₂, 0, 0] := by
  decide +kernel

theorem fixM_singleton_iff (b : Ehat) (X : Mat3) : (∀ b' ∈ ({b} : Set Ehat), repE b' X = X) ↔
    repE b X = X := by simp

theorem fixM_pair_iff (b c : Ehat) (X : Mat3) : (∀ b' ∈ ({b, c} : Set Ehat), repE b' X = X) ↔
    repE b X = X ∧ repE c X = X := by simp

theorem card_fixM_t1 : Nat.card (FixM {SemidirectProduct.inl ((tS, 1) : K)}) ≤ 64 := by
  have h := card_le_of_recon (P := fun X => ∀ b' ∈ ({SemidirectProduct.inl ((tS, 1) : K)} :
      Set Ehat), repE b' X = X)
    (fun X => ![X 0 0, X 0 1, X 0 2, X 1 0, X 1 1, X 1 2])
    (fun v => !![v 0, v 1, v 2; v 3, v 4, v 5; 0, 0, 0]) fun X hX => by
      rw [fixM_singleton_iff, repE_inl_apply, coe_tS, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one] at hX
      rw [Matrix.eta_fin_three X] at hX ⊢
      exact fix_t1_check _ _ _ _ _ _ _ _ _ hX
  exact le_of_le_of_eq h (by norm_num)

theorem card_fixM_tt : Nat.card (FixM {SemidirectProduct.inl ((tS, tS) : K)}) ≤ 32 := by
  have h := card_le_of_recon (P := fun X => ∀ b' ∈ ({SemidirectProduct.inl ((tS, tS) : K)} :
      Set Ehat), repE b' X = X)
    (fun X => ![X 0 0, X 0 1, X 0 2, X 1 0, X 1 1])
    (fun v => !![v 0, v 1, v 2; v 3, v 4, 0; v 2, 0, 0]) fun X hX => by
      rw [fixM_singleton_iff, repE_inl_apply, coe_tS] at hX
      rw [Matrix.eta_fin_three X] at hX ⊢
      exact fix_tt_check _ _ _ _ _ _ _ _ _ hX
  exact le_of_le_of_eq h (by norm_num)

theorem card_fixM_t1_1t :
    Nat.card (FixM {SemidirectProduct.inl ((tS, 1) : K), SemidirectProduct.inl ((1, tS) : K)}) ≤
      16 := by
  have h := card_le_of_recon (P := fun X => ∀ b' ∈ ({SemidirectProduct.inl ((tS, 1) : K),
      SemidirectProduct.inl ((1, tS) : K)} : Set Ehat), repE b' X = X)
    (fun X => ![X 0 0, X 0 1, X 1 0, X 1 1])
    (fun v => !![v 0, v 1, 0; v 2, v 3, 0; 0, 0, 0]) fun X hX => by
      rw [fixM_pair_iff, repE_inl_apply, repE_inl_apply, coe_tS, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul] at hX
      rw [Matrix.eta_fin_three X] at hX ⊢
      exact fix_t1_1t_check _ _ _ _ _ _ _ _ _ hX.1 hX.2
  exact le_of_le_of_eq h (by norm_num)

theorem card_fixM_s : Nat.card (FixM {sE}) ≤ 64 := by
  have h := card_le_of_recon (P := fun X => ∀ b' ∈ ({sE} : Set Ehat), repE b' X = X)
    (fun X => ![X 0 0, X 0 1, X 0 2, X 1 1, X 1 2, X 2 2])
    (fun v => !![v 0, v 1, v 2; v 1, v 3, v 4; v 2, v 4, v 5]) fun X hX => by
      rw [fixM_singleton_iff, repE_sE_apply] at hX
      rw [Matrix.eta_fin_three X] at hX ⊢
      exact fix_s_check _ _ _ _ _ _ _ _ _ hX
  exact le_of_le_of_eq h (by norm_num)

theorem card_fixM_s_tt :
    Nat.card (FixM {sE, SemidirectProduct.inl ((tS, tS) : K)}) ≤ 16 := by
  have h := card_le_of_recon (P := fun X => ∀ b' ∈ ({sE, SemidirectProduct.inl ((tS, tS) : K)} :
      Set Ehat), repE b' X = X)
    (fun X => ![X 0 0, X 0 1, X 0 2, X 1 1])
    (fun v => !![v 0, v 1, v 2; v 1, v 3, 0; v 2, 0, 0]) fun X hX => by
      rw [fixM_pair_iff, repE_sE_apply, repE_inl_apply, coe_tS] at hX
      rw [Matrix.eta_fin_three X] at hX ⊢
      exact fix_s_tt_check _ _ _ _ _ _ _ _ _ hX.1 hX.2
  exact le_of_le_of_eq h (by norm_num)

theorem inl_conj_inl (k k' : K) :
    (SemidirectProduct.inl k : Ehat) * SemidirectProduct.inl k' * (SemidirectProduct.inl k)⁻¹ =
      SemidirectProduct.inl (k * k' * k⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem sE_conj_inl (k : K) :
    sE * (SemidirectProduct.inl k : Ehat) * sE⁻¹ = SemidirectProduct.inl k.swap := by
  rw [show sE⁻¹ = SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ from
    (map_inv _ _).symm, ← SemidirectProduct.inl_aut]
  rfl

theorem conj_mul_conj (a b x : Ehat) : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
  group

theorem exists_conj_std {k : K} (hk : k * k = 1) (h1 : k ≠ 1) :
    ∃ e : Ehat, e * SemidirectProduct.inl k * e⁻¹ = SemidirectProduct.inl ((tS, 1) : K) ∨
      e * SemidirectProduct.inl k * e⁻¹ = SemidirectProduct.inl ((tS, tS) : K) := by
  obtain ⟨x, y⟩ := k
  have hx2 : x * x = 1 := congrArg Prod.fst hk
  have hy2 : y * y = 1 := congrArg Prod.snd hk
  by_cases hx : x = 1
  · subst hx
    have hy : y ≠ 1 := fun hy => h1 (by rw [hy]; rfl)
    obtain ⟨h, hh⟩ := exists_conj_eq_tS hy2 hy
    refine ⟨SemidirectProduct.inl ((h, 1) : K) * sE, Or.inl ?_⟩
    rw [conj_mul_conj, sE_conj_inl, inl_conj_inl]
    congr 1
    exact Prod.ext hh (by simp)
  · obtain ⟨g, hg⟩ := exists_conj_eq_tS hx2 hx
    by_cases hy : y = 1
    · subst hy
      refine ⟨SemidirectProduct.inl ((g, 1) : K), Or.inl ?_⟩
      rw [inl_conj_inl]
      congr 1
      exact Prod.ext hg (by simp)
    · obtain ⟨h, hh⟩ := exists_conj_eq_tS hy2 hy
      refine ⟨SemidirectProduct.inl ((g, h) : K), Or.inr ?_⟩
      rw [inl_conj_inl]
      congr 1
      exact Prod.ext hg hh

theorem left_conj_cond (e : Ehat) (k : K) :
    e ∈ centralizer {(SemidirectProduct.inl k : Ehat)} ↔
      e.left * swapAct e.right k = k * e.left := by
  rw [mem_centralizer_singleton_iff, SemidirectProduct.ext_iff]
  simp

theorem mem_centralizer_t1_iff (e : Ehat) :
    e ∈ centralizer {(SemidirectProduct.inl ((tS, 1) : K) : Ehat)} ↔
      e.left.1 ∈ U3 ∧ e.right = 1 := by
  rw [left_conj_cond]
  rcases mult_two_cases e.right with h | h
  · rw [h, swapAct_one_apply, Prod.ext_iff]
    simp only [Prod.fst_mul, Prod.snd_mul, mul_one, one_mul, and_true]
    exact commute_tS_iff _
  · rw [h, swapAct_s_apply, Prod.ext_iff]
    simp only [Prod.swap_prod_mk, Prod.fst_mul, Prod.snd_mul, mul_one, one_mul]
    constructor
    · rintro ⟨-, h2⟩
      exact absurd (mul_eq_left.1 h2) tS_ne_one
    · rintro ⟨-, h2⟩
      exact absurd h2 (by decide)

theorem mem_centralizer_tt_iff (e : Ehat) :
    e ∈ centralizer {(SemidirectProduct.inl ((tS, tS) : K) : Ehat)} ↔
      e.left.1 ∈ U3 ∧ e.left.2 ∈ U3 := by
  rw [left_conj_cond]
  have hsw : swapAct e.right ((tS, tS) : K) = (tS, tS) := by
    rcases mult_two_cases e.right with h | h
    · rw [h, swapAct_one_apply]
    · rw [h, swapAct_s_apply]
      rfl
  rw [hsw, Prod.ext_iff]
  simp only [Prod.fst_mul, Prod.snd_mul]
  exact and_congr (commute_tS_iff _) (commute_tS_iff _)

theorem card_mult_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_centralizer_t1 :
    Nat.card (centralizer {(SemidirectProduct.inl ((tS, 1) : K) : Ehat)}) = 1344 := by
  have e : centralizer {(SemidirectProduct.inl ((tS, 1) : K) : Ehat)} ≃ U3 × S :=
    { toFun := fun x => (⟨x.1.left.1, ((mem_centralizer_t1_iff x.1).1 x.2).1⟩, x.1.left.2)
      invFun := fun p => ⟨⟨(p.1.1, p.2), 1⟩, (mem_centralizer_t1_iff _).2 ⟨p.1.2, rfl⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply SemidirectProduct.ext
        · rfl
        · exact ((mem_centralizer_t1_iff x.1).1 x.2).2.symm
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_U3,
    CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3]

theorem card_centralizer_tt :
    Nat.card (centralizer {(SemidirectProduct.inl ((tS, tS) : K) : Ehat)}) = 128 := by
  have e : centralizer {(SemidirectProduct.inl ((tS, tS) : K) : Ehat)} ≃
      (U3 × U3) × Multiplicative (ZMod 2) :=
    { toFun := fun x => ((⟨x.1.left.1, ((mem_centralizer_tt_iff x.1).1 x.2).1⟩,
        ⟨x.1.left.2, ((mem_centralizer_tt_iff x.1).1 x.2).2⟩), x.1.right)
      invFun := fun p => ⟨⟨(p.1.1.1, p.1.2.1), p.2⟩,
        (mem_centralizer_tt_iff _).2 ⟨p.1.1.2, p.1.2.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, card_U3, card_mult_two]

abbrev c7M : Mat3 := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def c7S : S :=
  ⟨c7M, c7M * c7M * c7M * c7M * c7M * c7M, by decide, by decide⟩

theorem c7S_pow_seven : c7S ^ 7 = 1 := Units.ext (by
  rw [Units.val_pow_eq_pow_val]
  decide)

set_option maxRecDepth 100000 in
theorem fix_t1_c7_check : ∀ m₀₀ m₀₁ m₀₂ m₁₀ m₁₁ m₁₂ m₂₀ m₂₁ m₂₂ : ZMod 2,
    (unitri 0 1 0 * !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] ∧
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] * c7Mᵀ =
      !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂]) →
    !![m₀₀, m₀₁, m₀₂; m₁₀, m₁₁, m₁₂; m₂₀, m₂₁, m₂₂] = !![0, 0, 0; 0, 0, 0; 0, 0, 0] := by
  decide +kernel

theorem eq_zero_of_fix_t1_c7 (X : Mat3) (h1 : repE (SemidirectProduct.inl ((tS, 1) : K)) X = X)
    (h2 : repE (SemidirectProduct.inl ((1, c7S) : K)) X = X) : X = 0 := by
  rw [repE_inl_apply, coe_tS, Units.val_one, Matrix.transpose_one, Matrix.mul_one] at h1
  rw [repE_inl_apply, Units.val_one, Matrix.one_mul] at h2
  change X * c7Mᵀ = X at h2
  rw [Matrix.eta_fin_three X] at h1 h2 ⊢
  have := fix_t1_c7_check _ _ _ _ _ _ _ _ _ ⟨h1, h2⟩
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem image_conj_singleton (e b : Ehat) :
    (fun x => e * x * e⁻¹) '' ({b} : Set Ehat) = {e * b * e⁻¹} := Set.image_singleton

theorem image_conj_pair (e b c : Ehat) :
    (fun x => e * x * e⁻¹) '' ({b, c} : Set Ehat) = {e * b * e⁻¹, e * c * e⁻¹} :=
  Set.image_pair _ _ _

theorem card_fixM_inl_le {k : K} (hk : k * k = 1) (h1 : k ≠ 1) :
    Nat.card (FixM {SemidirectProduct.inl k}) ≤ 64 := by
  obtain ⟨e, he⟩ := exists_conj_std hk h1
  rw [← card_fixM_conj e, image_conj_singleton]
  rcases he with he | he
  · rw [he]
    exact card_fixM_t1
  · rw [he]
    exact card_fixM_tt.trans (by norm_num)

theorem card_fixM_pair_le {x y : S} (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1)
    (hy1 : y ≠ 1) :
    Nat.card (FixM {SemidirectProduct.inl ((x, 1) : K), SemidirectProduct.inl ((1, y) : K)}) ≤
      16 := by
  obtain ⟨g, hg⟩ := exists_conj_eq_tS hx hx1
  obtain ⟨h, hh⟩ := exists_conj_eq_tS hy hy1
  rw [← card_fixM_conj (SemidirectProduct.inl ((g, h) : K)), image_conj_pair, inl_conj_inl,
    inl_conj_inl]
  have e1 : ((g, h) : K) * (x, 1) * (g, h)⁻¹ = (tS, 1) := Prod.ext hg (by simp)
  have e2 : ((g, h) : K) * (1, y) * (g, h)⁻¹ = (1, tS) := Prod.ext (by simp) hh
  rw [e1, e2]
  exact card_fixM_t1_1t

theorem exists_conj_eq_sE {b : Ehat} (hb : b.right ≠ 1) (hb2 : b * b = 1) :
    ∃ c : Ehat, c * b * c⁻¹ = sE := by
  obtain ⟨⟨g, h⟩, ε⟩ := b
  have hε : ε = Multiplicative.ofAdd 1 := (mult_two_cases ε).resolve_left hb
  subst hε
  have hl : (((g, h) : K) * ((g, h) : K).swap) = 1 := by
    have := congrArg SemidirectProduct.left hb2
    rwa [SemidirectProduct.mul_left, swapAct_s_apply] at this
  have hgh : h = g⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Prod.fst hl)
  subst hgh
  refine ⟨SemidirectProduct.inl ((g⁻¹, 1) : K), ?_⟩
  apply SemidirectProduct.ext
  · simp [swapAct_s_apply]
  · simp

theorem card_fixM_s_diag_le {h : S} (hh : h * h = 1) (h1 : h ≠ 1) :
    Nat.card (FixM {sE, SemidirectProduct.inl ((h, h) : K)}) ≤ 16 := by
  obtain ⟨g, hg⟩ := exists_conj_eq_tS hh h1
  rw [← card_fixM_conj (SemidirectProduct.inl ((g, g) : K)), image_conj_pair, inl_conj_inl]
  have e1 : (SemidirectProduct.inl ((g, g) : K) : Ehat) * sE *
      (SemidirectProduct.inl ((g, g) : K))⁻¹ = sE := by
    apply SemidirectProduct.ext
    · simp [swapAct_s_apply]
    · simp
  have e2 : ((g, g) : K) * (h, h) * (g, g)⁻¹ = (tS, tS) := Prod.ext hg hg
  rw [e1, e2]
  exact card_fixM_s_tt

theorem exists_ne_one_map_eq_one {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Nat.card f.range < Nat.card G) : ∃ g : G, g ≠ 1 ∧ f g = 1 := by
  by_contra h
  push Not at h
  have hker : f.ker = ⊥ := eq_bot_iff.2 fun g hg => by
    by_contra hg1
    exact h g hg1 hg
  have := Subgroup.card_ker_mul_card_range f
  rw [hker, Subgroup.card_bot, one_mul] at this
  omega

theorem exists_ne_one_of_ne_bot {G : Type*} [Group G] {B : Subgroup G} (hB : B ≠ ⊥) :
    ∃ b ∈ B, b ≠ 1 := by
  by_contra h
  push Not at h
  exact hB (eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (h x hx))

theorem card_fixM_mul_card_lt (B : Subgroup Ehat) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hB : B ≠ ⊥) : Nat.card (FixM B) * Nat.card B < 512 := by
  classical
  by_cases hK : ∀ b ∈ B, b.right = 1
  ·
    set B' : Subgroup K := B.comap SemidirectProduct.inl with hB'
    have hinl : ∀ b ∈ B, SemidirectProduct.inl b.left = b := fun b hb =>
      SemidirectProduct.ext rfl (hK b hb).symm
    have hmemB' : ∀ b ∈ B, b.left ∈ B' := fun b hb => by
      change SemidirectProduct.inl b.left ∈ B
      rw [hinl b hb]
      exact hb
    have hcardB : Nat.card B = Nat.card B' := Nat.card_congr
      { toFun := fun b => ⟨b.1.left, hmemB' b.1 b.2⟩
        invFun := fun k => ⟨SemidirectProduct.inl k.1, k.2⟩
        left_inv := fun b => Subtype.ext (hinl b.1 b.2)
        right_inv := fun k => rfl }
    have hB'sq : ∀ k ∈ B', k * k = 1 := fun k hk =>
      SemidirectProduct.inl_injective (by rw [map_mul, map_one]; exact hsq _ hk)
    have hB'comm : ∀ k ∈ B', ∀ k' ∈ B', k * k' = k' * k := fun k hk k' hk' =>
      SemidirectProduct.inl_injective (by rw [map_mul, map_mul]; exact hcomm _ hk _ hk')
    have hP₁ : Nat.card (B'.map (MonoidHom.fst S S)) ≤ 4 :=
      card_le_four_of_elementary (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact congrArg Prod.fst (hB'comm x hx y hy)) (by
        rintro _ ⟨x, hx, rfl⟩
        exact congrArg Prod.fst (hB'sq x hx))
    have hP₂ : Nat.card (B'.map (MonoidHom.snd S S)) ≤ 4 :=
      card_le_four_of_elementary (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact congrArg Prod.snd (hB'comm x hx y hy)) (by
        rintro _ ⟨x, hx, rfl⟩
        exact congrArg Prod.snd (hB'sq x hx))
    have hB'le : Nat.card B' ≤ 16 := by
      have h := Nat.card_le_card_of_injective
        (fun k : B' => ((⟨k.1.1, k.1, k.2, rfl⟩ : B'.map (MonoidHom.fst S S)),
          (⟨k.1.2, k.1, k.2, rfl⟩ : B'.map (MonoidHom.snd S S))))
        (fun k k' hkk' => Subtype.ext (Prod.ext (congrArg (fun p => (p.1 : S)) hkk')
          (congrArg (fun p => (p.2 : S)) hkk')))
      rw [Nat.card_prod] at h
      exact h.trans ((Nat.mul_le_mul hP₁ hP₂).trans (by norm_num))
    obtain ⟨b, hbB, hb1⟩ := exists_ne_one_of_ne_bot hB
    by_cases h4 : Nat.card B' ≤ 4
    · have hk1 : b.left ≠ 1 := fun h => hb1 (by rw [← hinl b hbB, h, map_one])
      have hfix : Nat.card (FixM B) ≤ 64 := by
        refine (card_fixM_anti (T := {SemidirectProduct.inl b.left}) ?_).trans
          (card_fixM_inl_le (hB'sq _ (hmemB' b hbB)) hk1)
        rw [Set.singleton_subset_iff, hinl b hbB]
        exact hbB
      calc Nat.card (FixM B) * Nat.card B ≤ 64 * 4 := Nat.mul_le_mul hfix (hcardB ▸ h4)
        _ < 512 := by norm_num
    · push Not at h4
      have hlt₂ : Nat.card ((MonoidHom.snd S S).domRestrict B').range < Nat.card B' := by
        rw [MonoidHom.domRestrict_range]
        omega
      have hlt₁ : Nat.card ((MonoidHom.fst S S).domRestrict B').range < Nat.card B' := by
        rw [MonoidHom.domRestrict_range]
        omega
      obtain ⟨k, hk1, hk⟩ := exists_ne_one_map_eq_one _ hlt₂
      obtain ⟨k', hk'1, hk'⟩ := exists_ne_one_map_eq_one _ hlt₁
      have hk2 : (k : K).2 = 1 := hk
      have hk'2 : (k' : K).1 = 1 := hk'
      have hx1 : (k : K).1 ≠ 1 := fun h => hk1 (Subtype.ext (Prod.ext h hk2))
      have hy1 : (k' : K).2 ≠ 1 := fun h => hk'1 (Subtype.ext (Prod.ext hk'2 h))
      have hkx : ((k : K).1, (1 : S)) = (k : K) := Prod.ext rfl hk2.symm
      have hky : ((1 : S), (k' : K).2) = (k' : K) := Prod.ext hk'2.symm rfl
      have hfix : Nat.card (FixM B) ≤ 16 := by
        refine (card_fixM_anti (T := {SemidirectProduct.inl (((k : K).1, 1) : K),
          SemidirectProduct.inl ((1, (k' : K).2) : K)}) ?_).trans
          (card_fixM_pair_le (congrArg Prod.fst (hB'sq _ k.2)) hx1
            (congrArg Prod.snd (hB'sq _ k'.2)) hy1)
        rw [Set.insert_subset_iff, Set.singleton_subset_iff, hkx, hky]
        exact ⟨k.2, k'.2⟩
      calc Nat.card (FixM B) * Nat.card B ≤ 16 * 16 := Nat.mul_le_mul hfix (hcardB ▸ hB'le)
        _ < 512 := by norm_num
  ·
    push Not at hK
    obtain ⟨b, hbB, hbr⟩ := hK
    obtain ⟨c, hc⟩ := exists_conj_eq_sE hbr (hsq b hbB)
    set B'' := B.map (MulAut.conj c).toMonoidHom with hB''
    have hcoe : (B'' : Set Ehat) = (fun x => c * x * c⁻¹) '' (B : Set Ehat) := by
      ext x
      simp [hB'', MulAut.conj_apply]
    have hfixB : Nat.card (FixM B'') = Nat.card (FixM B) := by
      rw [hcoe]
      exact card_fixM_conj c B
    have hcardB : Nat.card B'' = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have hsE : sE ∈ B'' := ⟨b, hbB, hc⟩
    have hcomm'' : ∀ x ∈ B'', ∀ y ∈ B'', x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    have hsq'' : ∀ x ∈ B'', x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hsq x hx, map_one]
    have hdiag : ∀ x ∈ B'', x.right = 1 → x = SemidirectProduct.inl ((x.left.1, x.left.1) : K) := by
      intro x hx hxr
      have hxl : SemidirectProduct.inl x.left = x := SemidirectProduct.ext rfl hxr.symm
      have h1 : sE * x * sE⁻¹ = x := by
        rw [hcomm'' sE hsE x hx, mul_inv_cancel_right]
      rw [← hxl, sE_conj_inl] at h1
      have h2 : x.left.swap = x.left := SemidirectProduct.inl_injective h1
      calc x = SemidirectProduct.inl x.left := hxl.symm
        _ = SemidirectProduct.inl ((x.left.1, x.left.1) : K) :=
          congrArg _ (Prod.ext rfl (congrArg Prod.snd h2).symm)
    set f := (SemidirectProduct.rightHom : Ehat →* Multiplicative (ZMod 2)).domRestrict B''
    have hrange : Nat.card f.range ≤ 2 := (Subgroup.card_le_card_group _).trans card_mult_two.le
    have hcardker := Subgroup.card_ker_mul_card_range f
    let g₀ : f.ker →* S :=
      { toFun := fun x => (x : B'').1.left.1
        map_one' := rfl
        map_mul' := fun x y => by
          have hx : ((x : B'') : Ehat).right = 1 := x.2
          change (((x : B'') : Ehat) * ((y : B'') : Ehat)).left.1 = _
          rw [SemidirectProduct.mul_left, hx, swapAct_one_apply]
          rfl }
    have hg₀ : Function.Injective g₀ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxr : ((x : B'') : Ehat).right = 1 := x.2
      have h1 := hdiag _ (x : B'').2 hxr
      have hx' : ((x : B'') : Ehat).left.1 = 1 := hx
      rw [hx'] at h1
      exact Subtype.ext (Subtype.ext (h1.trans (by
        rw [show ((1, 1) : K) = 1 from rfl, map_one]
        rfl)))
    have hker4 : Nat.card f.ker ≤ 4 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hg₀).toEquiv]
      refine card_le_four_of_elementary ?_ ?_
      · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subtype.ext (hcomm'' _ (x : B'').2 _ (y : B'').2))
      · rintro _ ⟨x, rfl⟩
        rw [← map_mul, show x * x = 1 from Subtype.ext (Subtype.ext (hsq'' _ (x : B'').2)),
          map_one]
    by_cases hk1 : ∃ x : f.ker, x ≠ 1
    · obtain ⟨x, hx1⟩ := hk1
      have hxr : ((x : B'') : Ehat).right = 1 := x.2
      have h1 := hdiag _ (x : B'').2 hxr
      set h := ((x : B'') : Ehat).left.1
      have hh1 : h ≠ 1 := fun hh => hx1 (hg₀ (by rw [map_one]; exact hh))
      have hhh : h * h = 1 := by
        have := congrArg (fun y : Ehat => y.left.1) (hsq'' _ (x : B'').2)
        rwa [SemidirectProduct.mul_left, hxr, swapAct_one_apply] at this
      have hfix : Nat.card (FixM B'') ≤ 16 := by
        refine (card_fixM_anti (T := {sE, SemidirectProduct.inl ((h, h) : K)}) ?_).trans
          (card_fixM_s_diag_le hhh hh1)
        rw [Set.insert_subset_iff, Set.singleton_subset_iff, ← h1]
        exact ⟨hsE, (x : B'').2⟩
      calc Nat.card (FixM B) * Nat.card B = Nat.card (FixM B'') * Nat.card B'' := by
            rw [hfixB, hcardB]
        _ ≤ 16 * (4 * 2) := Nat.mul_le_mul hfix (by
            rw [← hcardker]
            exact Nat.mul_le_mul hker4 hrange)
        _ < 512 := by norm_num
    · push Not at hk1
      have hker1 : Nat.card f.ker ≤ 1 := by
        rw [Finite.card_le_one_iff_subsingleton]
        exact ⟨fun x y => (hk1 x).trans (hk1 y).symm⟩
      have hfix : Nat.card (FixM B'') ≤ 64 := by
        refine (card_fixM_anti (T := {sE}) ?_).trans card_fixM_s
        rw [Set.singleton_subset_iff]
        exact hsE
      calc Nat.card (FixM B) * Nat.card B = Nat.card (FixM B'') * Nat.card B'' := by
            rw [hfixB, hcardB]
        _ ≤ 64 * (1 * 2) := Nat.mul_le_mul hfix (by
            rw [← hcardker]
            exact Nat.mul_le_mul hker1 hrange)
        _ < 512 := by norm_num

@[expose] noncomputable def tensorMat : TensorProduct (ZMod 2) N N ≃ₗ[ZMod 2] Mat3 :=
  ((TensorProduct.piScalarRight (ZMod 2) (ZMod 2) N (Fin 3)).trans
    (Matrix.ofLinearEquiv (ZMod 2))).trans
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) (ZMod 2) (ZMod 2))

theorem tensorMat_tmul (v w : N) : tensorMat (v ⊗ₜ w) = Matrix.vecMulVec v w := by
  ext i j
  simp [tensorMat, Matrix.transposeLinearEquiv_apply, TensorProduct.piScalarRight_apply,
    Matrix.vecMulVec_apply, mul_comm]

theorem vecMulVec_vecMul (A B : Mat3) (v w : Fin 3 → ZMod 2) :
    Matrix.vecMulVec (v ᵥ* A) (w ᵥ* B) = Aᵀ * Matrix.vecMulVec v w * B := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_three]
  ring

theorem tensorMat_map (A B : Mat3) (x : TensorProduct (ZMod 2) N N) :
    tensorMat (TensorProduct.map (Matrix.vecMulLinear A) (Matrix.vecMulLinear B) x) =
      Aᵀ * tensorMat x * B := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    rw [TensorProduct.map_tmul, tensorMat_tmul, tensorMat_tmul]
    exact vecMulVec_vecMul A B v w
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.mul_add, Matrix.add_mul]

theorem repN_eq (g : S) : repN g = Matrix.vecMulLinear ((g⁻¹ : S) : Mat3) :=
  LinearMap.ext fun v => repN_apply g v

theorem repNd_eq (g : S) : repNd g = Matrix.vecMulLinear ((tau g⁻¹ : S) : Mat3) :=
  LinearMap.ext fun f => repNd_apply g f

theorem transpose_inv_val (g : S) : ((g⁻¹ : S) : Mat3)ᵀ = (tau g : Mat3) :=
  (tau_apply_val g).symm

theorem inv_val_eq (g : S) : ((g⁻¹ : S) : Mat3) = ((tau g : S) : Mat3)ᵀ := by
  rw [tau_apply_val, Matrix.transpose_transpose]

theorem tau_inv_val' (g : S) : ((tau g⁻¹ : S) : Mat3) = (g : Mat3)ᵀ := by
  rw [tau_apply_val, inv_inv]

theorem tensorMat_outer_NdNd (k : K) (x : TensorProduct (ZMod 2) Nd Nd) :
    tensorMat (outer repNd repNd k x) = repM k (tensorMat x) := by
  rw [outer_apply, repNd_eq, repNd_eq, tensorMat_map, tau_inv_val', tau_inv_val',
    Matrix.transpose_transpose, repM_apply]

theorem tensorMat_outer_NN (k : K) (x : TensorProduct (ZMod 2) N N) :
    tensorMat (outer repN repN k x) = repM (tau k.1, tau k.2) (tensorMat x) := by
  rw [outer_apply, repN_eq, repN_eq, tensorMat_map, transpose_inv_val, inv_val_eq, repM_apply]

theorem tensorMat_outer_NNd (k : K) (x : TensorProduct (ZMod 2) N Nd) :
    tensorMat (outer repN repNd k x) = repM (tau k.1, k.2) (tensorMat x) := by
  rw [outer_apply, repN_eq, repNd_eq, tensorMat_map, transpose_inv_val, tau_inv_val', repM_apply]

theorem tensorMat_outer_NdN (k : K) (x : TensorProduct (ZMod 2) Nd N) :
    tensorMat (outer repNd repN k x) = repM (k.1, tau k.2) (tensorMat x) := by
  rw [outer_apply, repNd_eq, repN_eq, tensorMat_map, tau_inv_val', Matrix.transpose_transpose,
    inv_val_eq, repM_apply]

@[expose] noncomputable def equivNdNd : (outer repNd repNd).Equiv repM :=
  equivOf tensorMat tensorMat_outer_NdNd

theorem absIrr_repM : AbsIrr repM :=
  AbsIrr.of_equiv equivNdNd.symm (repNd_absIrr.outer repNd_absIrr)

theorem repM_end (F : Module.End (ZMod 2) Mat3) (hF : ∀ k, F * repM k = repM k * F) :
    ∃ c : ZMod 2, F = c • 1 :=
  absIrr_repM.eq_smul F hF

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem repM_end_cases (F : Module.End (ZMod 2) Mat3) (hF : ∀ k, F * repM k = repM k * F) :
    F = 0 ∨ F = 1 := by
  obtain ⟨c, hc⟩ := repM_end F hF
  rcases zmod2_cases c with rfl | rfl
  · left
    rw [hc, zero_smul]
  · right
    rw [hc, one_smul]

theorem repM_tau_left_one (g : S) : repM (tau g, g) 1 = 1 := by
  rw [repM_apply, Matrix.mul_one, ← transpose_inv_val, ← Matrix.transpose_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem repM_tau_right_one (g : S) : repM (g, tau g) 1 = 1 := by
  rw [repM_apply, Matrix.mul_one, ← inv_val_eq, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel
