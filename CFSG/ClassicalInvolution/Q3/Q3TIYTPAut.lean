module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.Q3.Q3T6
open scoped MatrixGroups

theorem gl2Three_comm_of_comm_order_four :
    ∀ (g : GL (Fin 2) (ZMod 3)) (s : SL(2, ZMod 3)), s * s = -1 →
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g →
      (∀ b : SL(2, ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g * g * b =
        b * ((g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g * g)) →
      ∀ b : SL(2, ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * b =
        (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g := by
  decide +kernel

theorem sl2Three_mulAut_eq_one_of_odd_fix (α : MulAut SL(2, ZMod 3)) {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1) {s : SL(2, ZMod 3)} (hs : s * s = -1) (hαs : α s = s) : α = 1 := by
  have h24 : α ^ 24 = 1 := by
    have := pow_card_eq_one' (G := MulAut SL(2, ZMod 3)) (x := α)
    rwa [sl2Three_card_mulAut] at this
  have hgcd : Nat.gcd m 24 ∣ 3 := by
    have h1 : Nat.gcd m 24 ∣ 8 * 3 := Nat.gcd_dvd_right m 24
    have h2 : Nat.Coprime (Nat.gcd m 24) 8 := by
      have hodd : Odd (Nat.gcd m 24) := hm.of_dvd_nat (Nat.gcd_dvd_left m 24)
      have : Nat.Coprime (Nat.gcd m 24) 2 := hodd.coprime_two_right
      simpa using this.pow_right 3
    exact h2.dvd_of_dvd_mul_left h1
  have h3 : α ^ 3 = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hαm, h24⟩
    obtain ⟨c, hc⟩ := hgcd
    calc α ^ 3 = α ^ (m.gcd 24 * c) := congrArg (α ^ ·) hc
      _ = (α ^ m.gcd 24) ^ c := pow_mul _ _ _
      _ = 1 := by rw [this, one_pow]
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj α
  set M : Matrix (Fin 2) (Fin 2) (ZMod 3) := (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) with hM
  set Mi : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    ((g⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) with hMi
  have hMiM : Mi * M = 1 := by rw [hMi, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMMi : M * Mi = 1 := by rw [hMi, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hL : ∀ X : Matrix (Fin 2) (Fin 2) (ZMod 3), Mi * (M * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hMiM, Matrix.one_mul]
  have hcen : ∀ b : SL(2, ZMod 3), M * M * M * b = b * (M * M * M) := by
    intro b
    have e1 : (α ^ 3) b = b := by rw [h3]; rfl
    have e2 : (α ^ 3) b = α (α (α b)) := by
      rw [pow_succ, pow_succ, pow_one]
      rfl
    rw [e2] at e1
    have e3 := congrArg (fun x : SL(2, ZMod 3) => (x : Matrix (Fin 2) (Fin 2) (ZMod 3))) e1
    simp only [hg] at e3
    have key : M * M * M * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (M * (M * (M * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) * Mi) * Mi) * Mi) * (M * M * M) := by
      simp only [Matrix.mul_assoc, hL, hMiM, Matrix.mul_one]
    rw [key, e3]
  have hcomm : M * (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) * M := by
    have h1 := congrArg (fun x : SL(2, ZMod 3) => (x : Matrix (Fin 2) (Fin 2) (ZMod 3))) hαs
    simp only [hg] at h1
    calc M * (s : Matrix (Fin 2) (Fin 2) (ZMod 3))
        = (M * (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) * Mi) * M := by
          simp only [Matrix.mul_assoc, hMiM, Matrix.mul_one]
      _ = _ := by rw [h1]
  have hall := gl2Three_comm_of_comm_order_four g s hs hcomm hcen
  refine MulEquiv.ext fun b => ?_
  rw [MulAut.one_apply]
  apply Subtype.ext
  rw [hg b]
  calc M * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) * Mi
      = ((b : Matrix (Fin 2) (Fin 2) (ZMod 3)) * M) * Mi := by rw [hall b]
    _ = b := by rw [Matrix.mul_assoc, hMMi, Matrix.mul_one]

section Fpf

variable {G : Type} [Group G]

theorem inv_of_fixedPointFree {P : Subgroup G} [Finite P] {t : G} (ht2 : t * t = 1)
    (hnorm : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hfix : ∀ x ∈ P, t * x = x * t → x = 1) :
    ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv] at hnorm ⊢
  have tt : ∀ g : G, t * (t * g) = g := fun g => by rw [← mul_assoc, ht2, one_mul]
  have tt' : ∀ g : G, g * t * t = g := fun g => by rw [mul_assoc, ht2, mul_one]
  have hinvt : ∀ g : G, (t * g * t)⁻¹ = t * g⁻¹ * t := fun g => by
    rw [mul_inv_rev, mul_inv_rev, htinv]
    simp only [mul_assoc]
  let f : P → P := fun x => ⟨(x : G)⁻¹ * (t * x * t), P.mul_mem (P.inv_mem x.2) (hnorm x x.2)⟩
  have hf : Function.Injective f := by
    intro x y h
    have h1 : (x : G)⁻¹ * (t * x * t) = (y : G)⁻¹ * (t * y * t) := congrArg Subtype.val h
    have h2 : (y : G) * (x : G)⁻¹ * (t * x * t) = t * y * t := by
      calc (y : G) * (x : G)⁻¹ * (t * x * t) = (y : G) * ((x : G)⁻¹ * (t * x * t)) := by
            rw [mul_assoc]
        _ = (y : G) * ((y : G)⁻¹ * (t * y * t)) := by rw [h1]
        _ = t * y * t := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    have h3 : (y : G) * (x : G)⁻¹ = t * ((y : G) * (x : G)⁻¹) * t := by
      calc (y : G) * (x : G)⁻¹ = ((y : G) * (x : G)⁻¹ * (t * x * t)) * (t * x * t)⁻¹ := by
            rw [mul_assoc _ _ (t * x * t)⁻¹, mul_inv_cancel, mul_one]
        _ = (t * y * t) * (t * (x : G)⁻¹ * t) := by rw [h2, hinvt]
        _ = t * ((y : G) * (x : G)⁻¹) * t := by
            simp only [mul_assoc, tt]
    have h4 : t * ((y : G) * (x : G)⁻¹) = ((y : G) * (x : G)⁻¹) * t := by
      calc t * ((y : G) * (x : G)⁻¹) = t * ((y : G) * (x : G)⁻¹) * t * t := by rw [tt']
        _ = ((y : G) * (x : G)⁻¹) * t := by rw [← h3]
    have h5 := hfix _ (P.mul_mem y.2 (P.inv_mem x.2)) h4
    exact Subtype.ext (mul_inv_eq_one.mp h5).symm
  have hs : Function.Surjective f := Finite.surjective_of_injective hf
  intro x hx
  obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
  have hxy : x = (y : G)⁻¹ * (t * y * t) := congrArg Subtype.val hy.symm
  rw [hxy, mul_inv_rev, hinvt]
  simp only [mul_assoc, inv_inv, tt']

end Fpf

end CFSG.ClassicalInvolution.Q3.Q3TIY
