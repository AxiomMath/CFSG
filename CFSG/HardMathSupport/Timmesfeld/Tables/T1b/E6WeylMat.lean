module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylCheck
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.Timmesfeld.Orders.ExceptionalWeyl
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding.R3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Timmesfeld.ExceptionalOrders
open scoped Matrix

@[expose] def e6Idx : Fin 6 ≃ Fin Tag.E6.rank := finCongr rfl

@[simp] theorem e6Idx_val (k : Fin 6) : (e6Idx k).val = k.val := rfl

@[simp] theorem e6Idx_symm_val (k : Fin Tag.E6.rank) : (e6Idx.symm k).val = k.val := rfl

@[expose] noncomputable def e6WeylEntry (w : WeylGroup Tag.E6) (k j : Fin 6) : ZMod 3 :=
  (((w⁻¹ • (Pi.single (e6Idx k) 1 : Fin Tag.E6.rank → ℤ)) (e6Idx j) : ℤ) : ZMod 3)

theorem e6WeylEntry_one (k j : Fin 6) :
    e6WeylEntry 1 k j = (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) k j := by
  simp only [e6WeylEntry, inv_one, one_smul, Matrix.one_apply, Pi.single_apply,
    e6Idx.injective.eq_iff]
  split_ifs <;> simp_all

theorem e6WeylEntry_mul (w w' : WeylGroup Tag.E6) (k j : Fin 6) :
    e6WeylEntry (w * w') k j = ∑ l : Fin 6, e6WeylEntry w k l * e6WeylEntry w' l j := by
  simp only [e6WeylEntry, mul_inv_rev, mul_smul]
  rw [smul_eq_sum_single w'⁻¹ (w⁻¹ • Pi.single (e6Idx k) 1)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  exact (Fintype.sum_equiv e6Idx _ _ fun l => rfl).symm

@[expose] noncomputable def e6WeylMat : WeylGroup Tag.E6 →* Matrix (Fin 6) (Fin 6) (ZMod 3) where
  toFun w := Matrix.of fun k j => e6WeylEntry w k j
  map_one' := Matrix.ext fun k j => by rw [Matrix.of_apply, e6WeylEntry_one]
  map_mul' w w' := Matrix.ext fun k j => by
    rw [Matrix.of_apply, e6WeylEntry_mul, Matrix.mul_apply]
    rfl

theorem e6WeylMat_apply (w : WeylGroup Tag.E6) (k j : Fin 6) :
    e6WeylMat w k j = e6WeylEntry w k j := rfl

@[expose] def e6ReflMat (i : Fin Tag.E6.rank) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun k j =>
    (((reflect Tag.E6 i (Pi.single (e6Idx k) 1)) (e6Idx j) : ℤ) : ZMod 3)

theorem e6ReflL_eq (i : Fin Tag.E6.rank) : toMatL 3 6 (e6ReflL.getD i.val []) = e6ReflMat i := by
  fin_cases i <;> decide

theorem e6WeylMat_simple (i : Fin Tag.E6.rank) :
    e6WeylMat (simple Tag.E6 i) = toMatL 3 6 (e6ReflL.getD i.val []) := by
  rw [e6ReflL_eq]
  ext k j
  rw [e6WeylMat_apply, e6WeylEntry, CoxeterSystem.inv_simple, simple_smul]
  rfl

theorem e6WordL_nil : e6WordL [] = midL 3 6 := rfl

theorem e6WordL_cons (i : ℕ) (ω : List ℕ) :
    e6WordL (i :: ω) = mmulL 3 6 (e6ReflL.getD i []) (e6WordL ω) := rfl

theorem e6WeylMat_wordProd (ω : List (Fin Tag.E6.rank)) :
    e6WeylMat ((coxeterSystem Tag.E6).wordProd ω) = toMatL 3 6 (e6WordL (ω.map Fin.val)) := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, map_one, List.map_nil, e6WordL_nil, toMatL_midL]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, e6WeylMat_simple, List.map_cons, e6WordL_cons,
      toMatL_mmulL]

theorem rootList_E6_eq_of_modEq :
    ∀ β ∈ rootList Tag.E6, ∀ i : Fin Tag.E6.rank,
      (∀ j : Fin Tag.E6.rank, ((β j : ℤ) : ZMod 3) =
        (((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j : ℤ) : ZMod 3)) → β = Pi.single i 1 := by
  decide

theorem e6WeylMat_injective : Function.Injective e6WeylMat := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hfix : ∀ k : Fin Tag.E6.rank,
      w⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) = Pi.single k 1 := by
    intro k
    have hroot : IsRoot Tag.E6 (w⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) :=
      CFSG.LieType.Chevalley.IsRoot.smul (IsRoot.basis k) w⁻¹
    refine rootList_E6_eq_of_modEq _ (mem_rootList.2 hroot) k fun j => ?_
    have h := congrFun (congrFun hw (e6Idx.symm k)) (e6Idx.symm j)
    rw [e6WeylMat_apply, e6WeylEntry, Matrix.one_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at h
    rw [h]
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hne : e6Idx.symm k ≠ e6Idx.symm j := fun h' => hjk (e6Idx.symm.injective h').symm
      simp [hne, hjk]
  have h1 : w⁻¹ = 1 := ext_single fun k => by rw [hfix k, one_smul]
  exact inv_eq_one.1 h1

variable {K : Type} [Field K]

@[expose] def cubeTuple (ζ : Kˣ) (v : Fin 6 → ZMod 3) : Fin Tag.E6.rank → Kˣ :=
  fun i => ζ ^ (v (e6Idx.symm i)).val

theorem zpow_eq_of_intCast_eq {ζ : Kˣ} (hζ : orderOf ζ = 3) {m n : ℤ}
    (h : (m : ZMod 3) = (n : ZMod 3)) : ζ ^ m = ζ ^ n := by
  rw [zpow_eq_zpow_iff_modEq, hζ]
  exact (ZMod.intCast_eq_intCast_iff m n 3).1 h

theorem weylAct_cubeTuple {ζ : Kˣ} (hζ : orderOf ζ = 3) (w : WeylGroup Tag.E6)
    (v : Fin 6 → ZMod 3) : weylAct w (cubeTuple ζ v) = cubeTuple ζ (e6WeylMat w *ᵥ v) := by
  funext k
  have hL : weylAct w (cubeTuple ζ v) k = ζ ^ (∑ j : Fin Tag.E6.rank,
      ((v (e6Idx.symm j)).val : ℤ) * (w⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) j) := by
    simp only [weylAct, cubeTuple, rootChar]
    rw [← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
  rw [hL, cubeTuple, ← zpow_natCast]
  apply zpow_eq_of_intCast_eq hζ
  rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id', id, Matrix.mulVec, dotProduct,
    Int.cast_sum]
  refine (Fintype.sum_equiv e6Idx _ _ fun l => ?_).symm
  rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id', id, mul_comm,
    e6WeylMat_apply, e6WeylEntry, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem cubeTuple_injective {ζ : Kˣ} (hζ : orderOf ζ = 3) : Function.Injective (cubeTuple ζ) := by
  intro v v' h
  funext k
  have h1 := congrFun h (e6Idx k)
  simp only [cubeTuple, Equiv.symm_apply_apply] at h1
  rw [pow_eq_pow_iff_modEq, hζ] at h1
  have h2 : (v k).val = (v' k).val := by
    have := (v k).val_lt
    have := (v' k).val_lt
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt (by assumption), Nat.mod_eq_of_lt (by assumption)] at h1
  exact ZMod.val_injective _ h2

theorem mem_zpowers_of_pow_three' [Finite K] {ζ : Kˣ} (hζ : orderOf ζ = 3)
    (h3 : 3 ∣ Nat.card K - 1) {y : Kˣ} (hy : y ^ 3 = 1) : y ∈ Subgroup.zpowers ζ := by
  have hle : Subgroup.zpowers ζ ≤ (powMonoidHom 3 : Kˣ →* Kˣ).ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker, powMonoidHom_apply, ← hζ]
    exact pow_orderOf_eq_one ζ
  have hcard : Nat.card (powMonoidHom 3 : Kˣ →* Kˣ).ker ≤ Nat.card (Subgroup.zpowers ζ) := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_eq_right h3,
      Nat.card_zpowers, hζ]
  have := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [this, MonoidHom.mem_ker, powMonoidHom_apply]
  exact hy

theorem exists_cubeTuple [Finite K] {ζ : Kˣ} (hζ : orderOf ζ = 3) (h3 : 3 ∣ Nat.card K - 1)
    {a : Fin Tag.E6.rank → Kˣ} (ha : ∀ i, a i ^ 3 = 1) : ∃ v, a = cubeTuple ζ v := by
  have hex : ∀ i, ∃ m : ℤ, ζ ^ m = a i := fun i =>
    Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_three' hζ h3 (ha i))
  choose m hm using hex
  refine ⟨fun k => (m (e6Idx k) : ZMod 3), funext fun i => ?_⟩
  rw [cubeTuple, Equiv.apply_symm_apply, ← hm, ← zpow_natCast]
  apply zpow_eq_of_intCast_eq hζ
  rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id', id]

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
