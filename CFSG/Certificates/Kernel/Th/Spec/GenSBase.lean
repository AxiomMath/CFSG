
module

public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Sporadic.Th.Max3.DataBase
import CFSG.Certificates.Kernel.Th.Max3S.BasicBase
public import CFSG.Certificates.Kernel.Th.Gen.Wrap

@[expose] public section

namespace CFSG.KC.Th.Spec.GenS

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.KC.Th.Spec

section Defs

variable {G : Type} [Group G] (a b : G)

def t3 : G := a * b
def t4 : G := t3 a b * b
def t5 : G := t3 a b * t4 a b
def t6 : G := t3 a b * t5 a b
def t7 : G := a * t6 a b
def t8 : G := t6 a b * a
def u : G := (t8 a b)⁻¹ * t7 a b
def s8 : G := t6 a b * t5 a b
def s9 : G := t3 a b * s8 a b
def s10 : G := s9 a b * t4 a b
def s7 : G := a * s10 a b
def s8' : G := s10 a b * a
def v : G := (s8' a b)⁻¹ * s7 a b
def x : G := v a b ^ 14
def y : G := t7 a b * u a b ^ 9
def wordProd (w : List CFSG.Sporadic.Th.Max3.Gen) : G :=
  (w.map (CFSG.Sporadic.Th.Max3.Gen.eval (x a b) (y a b))).prod
def abLetter (i : ℕ) : G := if i = 1 then a else b
def abProd (w : List ℕ) : G := (w.map (abLetter a b)).prod
def fusionConj (w : List ℕ) (r : G) : G :=
  ((abProd a b w)⁻¹ * r * abProd a b w * a) ^ 9 * (abProd a b w)⁻¹
def genPair (c : G) : Set G :=
  {x a b * (c⁻¹ * (x a b * c)), y a b * (c⁻¹ * (y a b * c))}
def GenFact (w : List ℕ) (r : G) : Prop :=
  fusionConj a b w r * r * (fusionConj a b w r)⁻¹ = a ∧
    a ∈ Subgroup.closure (genPair a b (fusionConj a b w r)) ∧
      b ∈ Subgroup.closure (genPair a b (fusionConj a b w r))
end Defs

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

section Regs

variable (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
variable {G : Type} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2))
include hk

theorem mulR {P Q R : ℕ} {g h : G} (hl : Gen.eqN (mulB c rm P Q) R = true) (hP : pkMat P = φ g)
    (hQ : pkMat Q = φ h) : pkMat R = φ (g * h) := by
  rw [← CFSG.KC.Th.Max3S.eq_of_eqN hl, pkMat_mulB hk, hP, hQ, map_mul]

omit hk in
theorem phi_mul (g h : G) : φ (g * h) = φ g * φ h := map_mul φ g h

omit hk in
theorem phi_one : φ 1 = 1 := map_one φ

theorem invR {P Pi : ℕ} {g : G} (hl : Gen.eqN (mulB c rm P Pi) ONE = true) (hP : pkMat P = φ g) :
    pkMat Pi = φ g⁻¹ := by
  have e : φ g * pkMat Pi = 1 := by
    rw [← hP, ← pkMat_mulB hk, CFSG.KC.Th.Max3S.eq_of_eqN hl, pkMat_one hk]
  have e3 : φ g⁻¹ * φ g = 1 := by
    rw [← phi_mul φ g⁻¹ g, inv_mul_cancel, phi_one φ]
  calc pkMat Pi = 1 * pkMat Pi := (Matrix.one_mul _).symm
    _ = (φ g⁻¹ * φ g) * pkMat Pi := by rw [e3]
    _ = φ g⁻¹ * (φ g * pkMat Pi) := Matrix.mul_assoc _ _ _
    _ = φ g⁻¹ * 1 := by rw [e]
    _ = φ g⁻¹ := Matrix.mul_one _

theorem powR {P R e nb : ℕ} {g : G} (hl : Gen.eqN (BigS.powB c rm ONE P e nb) R = true)
    (he : e < 2 ^ nb) (hP : pkMat P = φ g) : pkMat R = φ (g ^ e) := by
  rw [← CFSG.KC.Th.Max3S.eq_of_eqN hl, pkMat_powB hk P e nb he, hP, map_pow]

omit hk in
theorem abProd_map (a b : G) : ∀ w : List ℕ,
    φ (abProd a b w) = (w.map fun i => if i = 1 then φ a else φ b).prod
  | [] => by
    show φ 1 = 1
    exact phi_one φ
  | i :: w => by
    show φ (abLetter a b i * abProd a b w) =
      (if i = 1 then φ a else φ b) * (w.map fun i => if i = 1 then φ a else φ b).prod
    rw [phi_mul, abProd_map a b w]
    unfold abLetter
    split_ifs <;> rfl

end Regs

theorem digits0 : (List.range 5).map (fun i => BigS.bitsN 276 (2 * i) 2) = [0, 1, 1, 0, 1] := by
  decide

theorem digits1 : (List.range 13).map (fun i => BigS.bitsN 17896517 (2 * i) 2) =
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] := by
  decide

end CFSG.KC.Th.Spec.GenS

end
