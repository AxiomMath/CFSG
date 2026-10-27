module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisCoord
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup
open scoped Matrix

variable {p : ℕ} {G : Type*} [Group G]

structure HeisCoordData (p : ℕ) {G : Type*} [Group G] (Q : Subgroup G) where
  x : Q
  y : Q
  gen : Subgroup.closure ({x, y} : Set Q) = ⊤
  π : Q →* Multiplicative (Fin 2 → ZMod p)
  π_x : π x = Multiplicative.ofAdd (![1, 0] : Fin 2 → ZMod p)
  π_y : π y = Multiplicative.ofAdd (![0, 1] : Fin 2 → ZMod p)
  ker_eq : π.ker = Subgroup.center Q
  surj : Function.Surjective π

open scoped commutatorElement

theorem yzpow_mul_x (x y : G) (hzy : Commute ⁅x, y⁆ y) (k : ℤ) :
    y ^ k * x * (y ^ k)⁻¹ = ⁅x, y⁆ ^ (-k) * x := by
  have hy : y * x * y⁻¹ = ⁅x, y⁆⁻¹ * x := by
    rw [commutatorElement_def]; group
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : y ^ ((k : ℤ) + 1) * x * (y ^ ((k : ℤ) + 1))⁻¹ =
        y * (y ^ (k : ℤ) * x * (y ^ (k : ℤ))⁻¹) * y⁻¹ := by
      rw [zpow_add_one, mul_inv_rev]; group
    rw [e, ih]
    have : y * (⁅x, y⁆ ^ (-(k : ℤ)) * x) * y⁻¹ = ⁅x, y⁆ ^ (-(k : ℤ)) * (y * x * y⁻¹) := by
      have hc : y * ⁅x, y⁆ ^ (-(k : ℤ)) = ⁅x, y⁆ ^ (-(k : ℤ)) * y :=
        ((hzy.zpow_left (-(k : ℤ))).symm).eq
      calc y * (⁅x, y⁆ ^ (-(k : ℤ)) * x) * y⁻¹ = (y * ⁅x, y⁆ ^ (-(k : ℤ))) * x * y⁻¹ := by group
        _ = ⁅x, y⁆ ^ (-(k : ℤ)) * y * x * y⁻¹ := by rw [hc]
        _ = _ := by group
    rw [this, hy]
    rw [show -((k : ℤ) + 1) = -(k : ℤ) + -1 by ring, zpow_add, zpow_neg_one]
    group
  | pred k ih =>
    have hyi : y⁻¹ * x * y = ⁅x, y⁆ * x := by
      have hc : y⁻¹ * ⁅x, y⁆ = ⁅x, y⁆ * y⁻¹ := (hzy.inv_right.symm).eq
      have h1 : y⁻¹ * ⁅x, y⁆ * y = ⁅x, y⁆ := by rw [hc]; group
      calc y⁻¹ * x * y = (y⁻¹ * ⁅x, y⁆ * y) * x := by
            rw [commutatorElement_def]; group
        _ = _ := by rw [h1]
    have e : y ^ (-(k : ℤ) - 1) * x * (y ^ (-(k : ℤ) - 1))⁻¹ =
        y⁻¹ * (y ^ (-(k : ℤ)) * x * (y ^ (-(k : ℤ)))⁻¹) * y := by
      rw [zpow_sub_one, mul_inv_rev, inv_inv]; group
    rw [e, ih]
    have hc : y⁻¹ * ⁅x, y⁆ ^ (-(-(k : ℤ))) = ⁅x, y⁆ ^ (-(-(k : ℤ))) * y⁻¹ :=
      ((hzy.inv_right.zpow_left (-(-(k : ℤ)))).symm).eq
    calc y⁻¹ * (⁅x, y⁆ ^ (-(-(k : ℤ))) * x) * y
        = (y⁻¹ * ⁅x, y⁆ ^ (-(-(k : ℤ)))) * x * y := by group
      _ = ⁅x, y⁆ ^ (-(-(k : ℤ))) * (y⁻¹ * x * y) := by rw [hc]; group
      _ = _ := by
        rw [hyi, show -(-(k : ℤ) - 1) = -(-(k : ℤ)) + 1 by ring, zpow_add_one]; group

theorem xzpow_mul_y (x y : G) (hzx : Commute ⁅x, y⁆ x) (a : ℤ) :
    x ^ a * y * (x ^ a)⁻¹ = ⁅x, y⁆ ^ a * y := by
  have hx : x * y * x⁻¹ = ⁅x, y⁆ * y := by
    rw [commutatorElement_def]; group
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : x ^ ((k : ℤ) + 1) * y * (x ^ ((k : ℤ) + 1))⁻¹ =
        x * (x ^ (k : ℤ) * y * (x ^ (k : ℤ))⁻¹) * x⁻¹ := by
      rw [zpow_add_one, mul_inv_rev]; group
    rw [e, ih]
    have hc : x * ⁅x, y⁆ ^ (k : ℤ) = ⁅x, y⁆ ^ (k : ℤ) * x :=
      ((hzx.zpow_left (k : ℤ)).symm).eq
    calc x * (⁅x, y⁆ ^ (k : ℤ) * y) * x⁻¹ = (x * ⁅x, y⁆ ^ (k : ℤ)) * y * x⁻¹ := by group
      _ = ⁅x, y⁆ ^ (k : ℤ) * (x * y * x⁻¹) := by rw [hc]; group
      _ = _ := by rw [hx, zpow_add_one]; group
  | pred k ih =>
    have hxi : x⁻¹ * y * x = ⁅x, y⁆⁻¹ * y := by
      have h1 : x⁻¹ * ⁅x, y⁆⁻¹ * x = ⁅x, y⁆⁻¹ := by
        have h := hzx.inv_left.symm.eq
        calc x⁻¹ * ⁅x, y⁆⁻¹ * x = x⁻¹ * (⁅x, y⁆⁻¹ * x) := by group
          _ = ⁅x, y⁆⁻¹ := by rw [← h]; group
      calc x⁻¹ * y * x = (x⁻¹ * ⁅x, y⁆⁻¹ * x) * y := by
            rw [commutatorElement_def]; group
        _ = _ := by rw [h1]
    have e : x ^ (-(k : ℤ) - 1) * y * (x ^ (-(k : ℤ) - 1))⁻¹ =
        x⁻¹ * (x ^ (-(k : ℤ)) * y * (x ^ (-(k : ℤ)))⁻¹) * x := by
      rw [zpow_sub_one, mul_inv_rev, inv_inv]; group
    rw [e, ih]
    have hc : x⁻¹ * ⁅x, y⁆ ^ (-(k : ℤ)) = ⁅x, y⁆ ^ (-(k : ℤ)) * x⁻¹ :=
      ((hzx.inv_right.zpow_left (-(k : ℤ))).symm).eq
    calc x⁻¹ * (⁅x, y⁆ ^ (-(k : ℤ)) * y) * x
        = (x⁻¹ * ⁅x, y⁆ ^ (-(k : ℤ))) * y * x := by group
      _ = ⁅x, y⁆ ^ (-(k : ℤ)) * (x⁻¹ * y * x) := by rw [hc]; group
      _ = _ := by
        rw [hxi, show -(k : ℤ) - 1 = -(k : ℤ) + -1 by ring, zpow_add, zpow_neg_one]; group

theorem commute_inv_mul_of_conj_eq {n q x : G} (h : n * x * n⁻¹ = q * x * q⁻¹) :
    Commute (q⁻¹ * n) x := by
  show q⁻¹ * n * x = x * (q⁻¹ * n)
  have : n * x = q * x * q⁻¹ * n := by rw [← h]; group
  calc q⁻¹ * n * x = q⁻¹ * (n * x) := by group
    _ = q⁻¹ * (q * x * q⁻¹ * n) := by rw [this]
    _ = x * (q⁻¹ * n) := by group

theorem commute_of_conj_gens (x y n : G) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (s r : ℤ) (hnx : n * x * n⁻¹ = ⁅x, y⁆ ^ s * x) (hny : n * y * n⁻¹ = ⁅x, y⁆ ^ r * y) :
    Commute ((x ^ r * y ^ (-s))⁻¹ * n) x ∧ Commute ((x ^ r * y ^ (-s))⁻¹ * n) y := by
  have h1 : (x ^ r * y ^ (-s)) * x * (x ^ r * y ^ (-s))⁻¹ = ⁅x, y⁆ ^ s * x := by
    have e : (x ^ r * y ^ (-s)) * x * (x ^ r * y ^ (-s))⁻¹ =
        x ^ r * (y ^ (-s) * x * (y ^ (-s))⁻¹) * (x ^ r)⁻¹ := by group
    rw [e, yzpow_mul_x x y hzy (-s), neg_neg]
    have hc : Commute (⁅x, y⁆ ^ s) (x ^ r) := (hzx.zpow_left s).zpow_right r
    calc x ^ r * (⁅x, y⁆ ^ s * x) * (x ^ r)⁻¹ = (x ^ r * ⁅x, y⁆ ^ s) * x * (x ^ r)⁻¹ := by group
      _ = (⁅x, y⁆ ^ s * x ^ r) * x * (x ^ r)⁻¹ := by rw [← hc.eq]
      _ = ⁅x, y⁆ ^ s * x := by group
  have h2 : (x ^ r * y ^ (-s)) * y * (x ^ r * y ^ (-s))⁻¹ = ⁅x, y⁆ ^ r * y := by
    have e : (x ^ r * y ^ (-s)) * y * (x ^ r * y ^ (-s))⁻¹ =
        x ^ r * y * (x ^ r)⁻¹ := by group
    rw [e, xzpow_mul_y x y hzx r]
  exact ⟨commute_inv_mul_of_conj_eq (hnx.trans h1.symm), commute_inv_mul_of_conj_eq (hny.trans h2.symm)⟩

variable {Q : Subgroup G}

namespace HeisCoordData

variable (D : HeisCoordData p Q)

@[expose] def gen2 : Fin 2 → Q := ![D.x, D.y]

@[expose] def actMat (n : normalizer (Q : Set G)) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  Matrix.of fun i j => Multiplicative.toAdd (D.π (Q.normalizerMonoidHom n (D.gen2 j))) i

theorem π_conj (n : normalizer (Q : Set G)) (q : Q) :
    Multiplicative.toAdd (D.π (Q.normalizerMonoidHom n q)) =
      D.actMat n *ᵥ Multiplicative.toAdd (D.π q) := by
  let f₂ : Q →* Multiplicative (Fin 2 → ZMod p) :=
    (AddMonoidHom.toMultiplicative (Matrix.mulVecLin (D.actMat n)).toAddMonoidHom).comp D.π
  have h : D.π.comp (Q.normalizerMonoidHom n).toMonoidHom = f₂ := by
    apply MonoidHom.eq_of_eqOn_top
    rw [← D.gen]
    apply MonoidHom.eqOn_closure
    rintro _ (rfl | rfl)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, f₂, D.π_x]
      apply Multiplicative.toAdd.injective
      ext i
      simp [actMat, gen2, Matrix.vecHead]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, f₂, D.π_y]
      apply Multiplicative.toAdd.injective
      ext i
      simp [actMat, gen2, Matrix.vecHead, Matrix.vecTail]
  have := congrArg (fun f : Q →* Multiplicative (Fin 2 → ZMod p) => Multiplicative.toAdd (f q)) h
  simpa [f₂] using this

theorem actMat_one : D.actMat 1 = 1 := by
  ext i j
  fin_cases j <;> fin_cases i <;> simp [actMat, gen2, D.π_x, D.π_y]

theorem actMat_mul (n n' : normalizer (Q : Set G)) :
    D.actMat (n * n') = D.actMat n * D.actMat n' := by
  ext i j
  rw [Matrix.mul_apply]
  have h := congrFun (D.π_conj n (Q.normalizerMonoidHom n' (D.gen2 j))) i
  simp only [actMat, Matrix.of_apply, map_mul, MulAut.mul_apply]
  rw [h]
  simp [Matrix.mulVec, dotProduct, actMat]

@[expose] def actHom : normalizer (Q : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  MonoidHom.toHomUnits ⟨⟨D.actMat, D.actMat_one⟩, D.actMat_mul⟩

theorem coe_actHom (n : normalizer (Q : Set G)) :
    ((D.actHom n : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      D.actMat n := by
  simp [actHom]

theorem actMat_eq_one_iff (n : normalizer (Q : Set G)) :
    D.actMat n = 1 ↔ ∀ q : Q, D.π (Q.normalizerMonoidHom n q) = D.π q := by
  constructor
  · intro h q
    apply Multiplicative.toAdd.injective
    rw [D.π_conj, h, Matrix.one_mulVec]
  · intro h
    rw [← D.actMat_one]
    ext i j
    simp [actMat, h]

theorem actMat_of_mem (q₀ : Q) :
    D.actMat ⟨q₀, Subgroup.le_normalizer q₀.2⟩ = 1 := by
  rw [actMat_eq_one_iff]
  intro q
  have : (Q.normalizerMonoidHom ⟨q₀, Subgroup.le_normalizer q₀.2⟩ q) = q₀ * q * q₀⁻¹ :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_mul, map_inv, mul_comm (D.π q₀) (D.π q), mul_assoc, mul_inv_cancel,
    mul_one]

theorem exists_mul_mem_centralizer (hZ : Subgroup.center Q = Subgroup.zpowers ⁅D.x, D.y⁆)
    (n : normalizer (Q : Set G)) (h : D.actMat n = 1) :
    ∃ q₀ : Q, (q₀ : G)⁻¹ * (n : G) ∈ Subgroup.centralizer (Q : Set G) := by
  have hker := (D.actMat_eq_one_iff n).1 h
  have hzc : ⁅D.x, D.y⁆ ∈ Subgroup.center Q := by rw [hZ]; exact Subgroup.mem_zpowers _
  have hzx : Commute (⁅(D.x : G), (D.y : G)⁆) (D.x : G) := by
    have := Subgroup.mem_center_iff.1 hzc D.x
    exact congrArg Subtype.val this.symm
  have hzy : Commute (⁅(D.x : G), (D.y : G)⁆) (D.y : G) := by
    have := Subgroup.mem_center_iff.1 hzc D.y
    exact congrArg Subtype.val this.symm
  have key : ∀ g : Q, ∃ s : ℤ, (n : G) * g * (n : G)⁻¹ = (⁅(D.x : G), (D.y : G)⁆) ^ s * g := by
    intro g
    have hm : (Q.normalizerMonoidHom n g) * g⁻¹ ∈ D.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hker g, mul_inv_cancel]
    rw [D.ker_eq, hZ] at hm
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 hm
    refine ⟨s, ?_⟩
    have hs' : Q.normalizerMonoidHom n g = ⁅D.x, D.y⁆ ^ s * g := by
      rw [hs]; group
    have h2 : (n : G) * g * (n : G)⁻¹ = ((Q.normalizerMonoidHom n g : Q) : G) := by simp
    rw [h2, hs']
    simp [commutatorElement_def]
  obtain ⟨s, hs⟩ := key D.x
  obtain ⟨r, hr⟩ := key D.y
  obtain ⟨hcx, hcy⟩ := commute_of_conj_gens (D.x : G) (D.y : G) (n : G) hzx hzy s r hs hr
  refine ⟨D.x ^ r * D.y ^ (-s), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hP : ∀ a : Q, a ∈ Subgroup.closure ({D.x, D.y} : Set Q) →
      Commute (a : G) (((D.x ^ r * D.y ^ (-s) : Q) : G)⁻¹ * (n : G)) := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · simpa using hcx.symm
      · simpa using hcy.symm
    | one => exact Commute.one_left _
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  have hP' := hP ⟨g, hg⟩ (by rw [D.gen]; trivial)
  exact hP'.eq

end HeisCoordData

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
