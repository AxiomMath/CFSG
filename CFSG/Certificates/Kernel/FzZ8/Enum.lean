module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef

public section

namespace CFSG.KC.FzZ8

open Certificates.FzR10A CFSG.OddStandard.SmallF3.FritzII

@[expose] def lsA : List Mat := [⟨0,1,1,0⟩, ⟨0,3,3,0⟩, ⟨0,5,5,0⟩, ⟨0,7,7,0⟩, ⟨1,0,1,7⟩, ⟨1,7,0,7⟩,
  ⟨3,0,3,5⟩, ⟨3,5,0,5⟩, ⟨5,0,5,3⟩, ⟨5,3,0,3⟩, ⟨7,0,7,1⟩, ⟨7,1,0,1⟩]

@[expose] def cMat (a c : Nat) : Mat := ⟨a, (8 - c) % 8, c, (a + 8 - c) % 8⟩

@[expose] def iMat (a c : Nat) : Mat := ⟨a, (c + 8 - a) % 8, c, (8 - a) % 8⟩

@[expose] def tPair (a c : Nat) : Bool :=
  a == 1 && c == 4 || a == 5 && c == 0 || a == 5 && c == 4

@[expose] def sPair (a c : Nat) : Bool := (a == 3 || a == 7) && (c == 0 || c == 4)

@[expose] def lPair (a c : Nat) : Bool :=
  a == 0 && (c == 1 || c == 3 || c == 5 || c == 7) ||
    (a == 1 || a == 3 || a == 5 || a == 7) && (c == 0 || c == a)

theorem comm_rho0 {a b c d : Nat} (ha : a < 8) (hb : b < 8) (hc : c < 8) (hd : d < 8)
    (h : (Mat.mk a b c d).mul rho0 = rho0.mul ⟨a, b, c, d⟩) :
    b = (8 - c) % 8 ∧ d = (a + 8 - c) % 8 := by
  simp only [Mat.mul, rho0, Mat.mk.injEq] at h
  omega

theorem inv_rho0 {a b c d : Nat} (ha : a < 8) (hb : b < 8) (hc : c < 8) (hd : d < 8)
    (h : (Mat.mk a b c d).mul rho0 = (rho0.mul rho0).mul ⟨a, b, c, d⟩) :
    b = (c + 8 - a) % 8 ∧ d = (8 - a) % 8 := by
  simp only [Mat.mul, rho0, Mat.mk.injEq] at h
  omega

theorem candT_comm {m : Mat} (h : candT m = true) : m.mul rho0 = rho0.mul m := by
  simp only [candT, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

theorem candS_comm {t m : Mat} (h : candS t m = true) : m.mul rho0 = rho0.mul m := by
  simp only [candS, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.2

theorem candL_inv {t m : Mat} (h : candL t m = true) : m.mul rho0 = (rho0.mul rho0).mul m := by
  simp only [candL, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

theorem beq_mat (m n : Mat) :
    (m == n) = (m.a == n.a && m.b == n.b && m.c == n.c && m.d == n.d) := by
  cases m
  cases n
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Bool.and_eq_true, Mat.mk.injEq, and_assoc]

theorem enumT : ∀ a < 8, ∀ c < 8, candT (cMat a c) = true → tPair a c = true := by
  simp only [candT, beq_mat]
  decide +kernel

theorem enumL14 : ∀ a < 8, ∀ c < 8, candL (cMat 1 4) (iMat a c) = false := by
  simp only [candL, beq_mat]
  decide +kernel

theorem enumL54 : ∀ a < 8, ∀ c < 8, candL (cMat 5 4) (iMat a c) = false := by
  simp only [candL, beq_mat]
  decide +kernel

theorem enumS : ∀ a < 8, ∀ c < 8,
    candS (cMat 5 0) (cMat a c) = true → sPair a c = true := by
  simp only [candS, beq_mat]
  decide +kernel

theorem sPair_cases {a c : Nat} (h : sPair a c = true) : (a = 3 ∨ a = 7) ∧ (c = 0 ∨ c = 4) := by
  simp only [sPair, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h

theorem enumL : ∀ a < 8, ∀ c < 8,
    candL (cMat 5 0) (iMat a c) = true →
      lPair a c = true := by
  simp only [candL, beq_mat]
  decide +kernel

theorem enumSL34 : ∀ al < 8, ∀ cl < 8, lPair al cl = true →
    ((cMat 3 4).mul (iMat al cl) == (iMat al cl).mul (cMat 3 4)) = false := by
  simp only [beq_mat]
  decide +kernel

theorem enumSL74 : ∀ al < 8, ∀ cl < 8, lPair al cl = true →
    ((cMat 7 4).mul (iMat al cl) == (iMat al cl).mul (cMat 7 4)) = false := by
  simp only [beq_mat]
  decide +kernel

theorem lPair_any : ∀ a < 8, ∀ c < 8, lPair a c = true →
    (lsA.any fun n => n == iMat a c) = true := by
  simp only [beq_mat]
  decide +kernel

theorem lPair_mem {a c : Nat} (ha : a < 8) (hc : c < 8) (h : lPair a c = true) :
    iMat a c ∈ lsA := by
  obtain ⟨n, hn, he⟩ := List.any_eq_true.1 (lPair_any a ha c hc h)
  rw [beq_iff_eq] at he
  exact he ▸ hn

theorem enumA {Mt Ms Ml : Mat} (hMt : FzR10AMatLt Mt) (hMs : FzR10AMatLt Ms) (hMl : FzR10AMatLt Ml)
    (hT : candT Mt = true) (hS : candS Mt Ms = true) (hL : candL Mt Ml = true)
    (hSL : (Ms.mul Ml == Ml.mul Ms) = true) :
    Mt = ⟨5, 0, 0, 5⟩ ∧ (Ms = ⟨3, 0, 0, 3⟩ ∨ Ms = ⟨7, 0, 0, 7⟩) ∧ Ml ∈ lsA := by
  obtain ⟨a, b, c, d⟩ := Mt
  obtain ⟨ha, hb, hc, hd⟩ : a < 8 ∧ b < 8 ∧ c < 8 ∧ d < 8 := hMt
  obtain ⟨rfl, rfl⟩ := comm_rho0 ha hb hc hd (candT_comm hT)
  obtain ⟨as, bs, cs, ds⟩ := Ms
  obtain ⟨has, hbs, hcs, hds⟩ : as < 8 ∧ bs < 8 ∧ cs < 8 ∧ ds < 8 := hMs
  obtain ⟨rfl, rfl⟩ := comm_rho0 has hbs hcs hds (candS_comm hS)
  obtain ⟨al, bl, cl, dl⟩ := Ml
  obtain ⟨hal, hbl, hcl, hdl⟩ : al < 8 ∧ bl < 8 ∧ cl < 8 ∧ dl < 8 := hMl
  obtain ⟨rfl, rfl⟩ := inv_rho0 hal hbl hcl hdl (candL_inv hL)
  have ht := enumT a ha c hc hT
  simp only [tPair, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ht
  rcases ht with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
  · have h := (enumL14 al hal cl hcl).symm.trans hL
    exact absurd h Bool.false_ne_true
  swap
  · have h := (enumL54 al hal cl hcl).symm.trans hL
    exact absurd h Bool.false_ne_true
  have hl := enumL al hal cl hcl hL
  refine ⟨rfl, ?_, lPair_mem hal hcl hl⟩
  obtain ⟨hsa, hsc⟩ := sPair_cases (enumS as has cs hcs hS)
  rcases hsc with rfl | rfl
  · rcases hsa with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rcases hsa with rfl | rfl
    · have h := (enumSL34 al hal cl hcl hl).symm.trans hSL
      exact absurd h Bool.false_ne_true
    · have h := (enumSL74 al hal cl hcl hl).symm.trans hSL
      exact absurd h Bool.false_ne_true

end CFSG.KC.FzZ8
