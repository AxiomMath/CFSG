module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowCount

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

variable {D : Type*}

@[expose] def wr (a b : D) (q : Z2) : D ≀ᵣ Z2 := ⟨fun x => if x = 1 then a else b, q⟩

@[simp] theorem wr_left_one (a b : D) (q : Z2) : (wr a b q).left 1 = a := by simp [wr]

@[simp] theorem wr_left_z2 (a b : D) (q : Z2) : (wr a b q).left z2 = b := by
  simp [wr, z2_ne_one]

@[simp] theorem wr_right (a b : D) (q : Z2) : (wr a b q).right = q := rfl

theorem wr_eta (x : D ≀ᵣ Z2) : wr (x.left 1) (x.left z2) x.right = x := by
  refine RegularWreathProduct.ext ?_ rfl
  funext z
  rcases z2_cases z with rfl | rfl <;> simp

theorem wr_inj {a b a' b' : D} {q q' : Z2} :
    wr a b q = wr a' b' q' ↔ a = a' ∧ b = b' ∧ q = q' := by
  constructor
  · intro h
    have h1 := congrArg (fun x => x.left 1) h
    have h2 := congrArg (fun x => x.left z2) h
    have h3 := congrArg RegularWreathProduct.right h
    simp at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

variable [Group D]

theorem wr_mul_one (a b c d : D) (q : Z2) : wr a b 1 * wr c d q = wr (a * c) (b * d) q := by
  rw [RegularWreathProduct.mul_def]
  refine RegularWreathProduct.ext ?_ (by simp [wr])
  funext z
  rcases z2_cases z with rfl | rfl <;> simp [wr, z2_ne_one]

theorem wr_mul_z2 (a b c d : D) (q : Z2) :
    wr a b z2 * wr c d q = wr (a * d) (b * c) (z2 * q) := by
  rw [RegularWreathProduct.mul_def]
  refine RegularWreathProduct.ext ?_ (by simp [wr])
  funext z
  rcases z2_cases z with rfl | rfl <;> simp [wr, z2_ne_one, z2_inv, z2_mul_self]

omit [Group D] in
theorem diag_eq_wr (g : D) : diag g = wr g g 1 := by
  refine RegularWreathProduct.ext ?_ rfl
  funext z
  simp [diag, wr]

theorem wr_one : wr (1 : D) 1 1 = 1 := by
  refine RegularWreathProduct.ext ?_ rfl
  funext z
  simp [wr]

omit [Group D] in
@[expose] def wrEquiv : D × D × Z2 ≃ D ≀ᵣ Z2 where
  toFun p := wr p.1 p.2.1 p.2.2
  invFun x := (x.left 1, x.left z2, x.right)
  left_inv p := by simp
  right_inv x := wr_eta x

end CFSG.OddStandard.AltStdSec.SylowSn
