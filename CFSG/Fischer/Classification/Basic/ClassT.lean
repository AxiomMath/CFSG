module

public import CFSG.Fischer.Uniq.Graph

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

section Product

theorem Pair.not_commute_mul (hP : Pair X E) {e f y : X} (he : e ∈ E) (hf : f ∈ E) (hy : y ∈ E)
    (hef : e * f = f * e) (hne : e ≠ f) (hye : y * e ≠ e * y) (hyf : y * f ≠ f * y) :
    y * (e * f) ≠ e * f * y := by
  intro h
  have h1 := Pair.triality_adj hP he hf hy hef hne hye hyf
  rw [← h, mul_inv_cancel_right] at h1
  exact h1.2.1 rfl

end Product

end CFSG.Fischer.Classification
