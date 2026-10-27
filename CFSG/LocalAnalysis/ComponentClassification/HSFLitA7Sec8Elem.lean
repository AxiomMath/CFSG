module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

variable {G : Type*} [Group G]

noncomputable def invHom (g : G) (hg : g * g = 1) : Multiplicative (ZMod 2) →* G where
  toFun a := g ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have hg2 : g ^ 2 = 1 := by rw [pow_two, hg]
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg2).symm

theorem invHom_one (g : G) (hg : g * g = 1) : invHom g hg (Multiplicative.ofAdd 1) = g := by
  change g ^ (1 : ZMod 2).val = g
  rw [ZMod.val_one, pow_one]

theorem exists_evHom {n : ℕ} (g : Fin n → G) (hc : ∀ i j, g i * g j = g j * g i)
    (hs : ∀ i, g i * g i = 1) :
    ∃ φ : (Fin n → Multiplicative (ZMod 2)) →* G,
      ∀ i, φ (Pi.mulSingle i (Multiplicative.ofAdd 1)) = g i := by
  classical
  have hcomm : Pairwise fun i j => ∀ (x y : Multiplicative (ZMod 2)),
      Commute (invHom (g i) (hs i) x) (invHom (g j) (hs j) y) := by
    intro i j _ x y
    exact Commute.pow_pow (hc i j) _ _
  refine ⟨MonoidHom.noncommPiCoprod (fun i => invHom (g i) (hs i)) hcomm, fun i => ?_⟩
  rw [MonoidHom.noncommPiCoprod_mulSingle, invHom_one]

abbrev e4 (i : Fin 4) : Fin 4 → Multiplicative (ZMod 2) := Pi.mulSingle i (Multiplicative.ofAdd 1)

theorem exists_evHom4 {a b c d : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (had : a * d = d * a) (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1) :
    ∃ φ : (Fin 4 → Multiplicative (ZMod 2)) →* G,
      φ (e4 0) = a ∧ φ (e4 1) = b ∧ φ (e4 2) = c ∧ φ (e4 3) = d := by
  obtain ⟨φ, hφ⟩ := exists_evHom ![a, b, c, d] (by
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all) (by
    intro i
    fin_cases i <;> simp_all)
  exact ⟨φ, hφ 0, hφ 1, hφ 2, hφ 3⟩

abbrev e3 (i : Fin 3) : Fin 3 → Multiplicative (ZMod 2) := Pi.mulSingle i (Multiplicative.ofAdd 1)

theorem exists_evHom3 {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    ∃ φ : (Fin 3 → Multiplicative (ZMod 2)) →* G, φ (e3 0) = a ∧ φ (e3 1) = b ∧ φ (e3 2) = c := by
  obtain ⟨φ, hφ⟩ := exists_evHom ![a, b, c] (by
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all) (by
    intro i
    fin_cases i <;> simp_all)
  exact ⟨φ, hφ 0, hφ 1, hφ 2⟩

macro "elem_eq " φ:term:max e0:term:max e1:term:max e2:term:max e3:term:max : tactic =>
  `(tactic| (
    try rw [← $e0:term]
    try rw [← $e1:term]
    try rw [← $e2:term]
    try rw [← $e3:term]
    try rw [← map_one $φ:term]
    try simp only [← map_mul]
    congr 1
    decide))

end CFSG.ComponentClassification.HSFLit.Sec8
