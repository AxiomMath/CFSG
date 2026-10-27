module

public import CFSG.Quasithin.Recognition.CertF8

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

open CFSG.Quasithin

structure GF512 where
  c0 : GF8
  c1 : GF8
  c2 : GF8

namespace GF512

instance instDecidableEq : DecidableEq GF512 := fun a b =>
  if h : a.c0 = b.c0 ∧ a.c1 = b.c1 ∧ a.c2 = b.c2 then
    isTrue (by cases a; cases b; simp_all)
  else isFalse (fun e => h (by subst e; exact ⟨rfl, rfl, rfl⟩))

theorem ext {a b : GF512} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) :
    a = b := by
  cases a; cases b; simp_all

@[expose] def xg : GF8 := GF8.ofNat' 2

instance instZero : Zero GF512 := ⟨⟨0, 0, 0⟩⟩

instance instOne : One GF512 := ⟨⟨1, 0, 0⟩⟩

instance instAdd : Add GF512 := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩

instance instNeg : Neg GF512 := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2⟩⟩

@[expose] def mul (a b : GF512) : GF512 :=
  ⟨a.c0 * b.c0 + xg * (a.c1 * b.c2 + a.c2 * b.c1),
    (a.c0 * b.c1 + a.c1 * b.c0) + (a.c1 * b.c2 + a.c2 * b.c1) + xg * (a.c2 * b.c2),
    (a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0) + a.c2 * b.c2⟩

instance instMul : Mul GF512 := ⟨mul⟩

@[expose] def cof0 (a : GF512) : GF8 := (a.c0 + a.c2) * (a.c0 + a.c2) + (xg * a.c2 + a.c1) * a.c1

@[expose] def cof1 (a : GF512) : GF8 := a.c1 * (a.c0 + a.c2) + (xg * a.c2 + a.c1) * a.c2

@[expose] def cof2 (a : GF512) : GF8 := a.c1 * a.c1 + (a.c0 + a.c2) * a.c2

@[expose] def norm (a : GF512) : GF8 := a.c0 * cof0 a + xg * a.c2 * cof1 a + xg * a.c1 * cof2 a

instance instInv : Inv GF512 :=
  ⟨fun a => ⟨(norm a)⁻¹ * cof0 a, (norm a)⁻¹ * cof1 a, (norm a)⁻¹ * cof2 a⟩⟩

instance instFintype : Fintype GF512 :=
  Fintype.ofEquiv (GF8 × GF8 × GF8) ⟨fun p => ⟨p.1, p.2.1, p.2.2⟩, fun a => (a.c0, a.c1, a.c2),
    fun _ => rfl, fun _ => rfl⟩

theorem c0_mul (a b : GF512) :
    (a * b).c0 = a.c0 * b.c0 + xg * (a.c1 * b.c2 + a.c2 * b.c1) := rfl

theorem c1_mul (a b : GF512) :
    (a * b).c1 = (a.c0 * b.c1 + a.c1 * b.c0) + (a.c1 * b.c2 + a.c2 * b.c1) +
      xg * (a.c2 * b.c2) := rfl

theorem c2_mul (a b : GF512) :
    (a * b).c2 = (a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0) + a.c2 * b.c2 := rfl

theorem c0_one : (1 : GF512).c0 = 1 := rfl

theorem c1_one : (1 : GF512).c1 = 0 := rfl

theorem c2_one : (1 : GF512).c2 = 0 := rfl

theorem c0_add (a b : GF512) : (a + b).c0 = a.c0 + b.c0 := rfl

theorem c1_add (a b : GF512) : (a + b).c1 = a.c1 + b.c1 := rfl

theorem c2_add (a b : GF512) : (a + b).c2 = a.c2 + b.c2 := rfl

theorem mul_inv_cancel_aux :
    ∀ u v w : GF8, (⟨u, v, w⟩ : GF512) ≠ 0 → (⟨u, v, w⟩ : GF512) * ⟨u, v, w⟩⁻¹ = 1 := by
  decide +kernel

instance instField : Field GF512 :=
  Field.ofMinimalAxioms GF512
    (fun a b c => ext (add_assoc _ _ _) (add_assoc _ _ _) (add_assoc _ _ _))
    (fun a => ext (zero_add _) (zero_add _) (zero_add _))
    (fun a => ext (neg_add_cancel _) (neg_add_cancel _) (neg_add_cancel _))
    (fun a b c => ext (by simp only [c0_mul, c1_mul, c2_mul]; ring)
      (by simp only [c0_mul, c1_mul, c2_mul]; ring)
      (by simp only [c0_mul, c1_mul, c2_mul]; ring))
    (fun a b => ext (by simp only [c0_mul]; ring) (by simp only [c1_mul]; ring)
      (by simp only [c2_mul]; ring))
    (fun a => ext (by simp only [c0_mul, c0_one, c1_one, c2_one]; ring)
      (by simp only [c1_mul, c0_one, c1_one, c2_one]; ring)
      (by simp only [c2_mul, c0_one, c1_one, c2_one]; ring))
    (fun a ha => by
      obtain ⟨u, v, w⟩ := a
      exact mul_inv_cancel_aux u v w ha)
    (by decide)
    (fun a b c => ext (by simp only [c0_mul, c0_add, c1_add, c2_add]; ring)
      (by simp only [c1_mul, c0_add, c1_add, c2_add]; ring)
      (by simp only [c2_mul, c0_add, c1_add, c2_add]; ring))
    ⟨0, 1, by decide⟩

end GF512

end CFSG.AGLEmbedding.ChevOuterD48
