module

public import CFSG.ClassicalInvolution.Asc77.AscC5O1G

public section

namespace CFSG.ClassicalInvolution.Asc77.C25G

theorem mul_comm_sq_eq_one {M : Type*} [Group M] {a b : M} (hc : b * a = a * b)
    (ha : a * a = 1) (hb : b * b = 1) : a * b * a * b = 1 := by
  calc a * b * a * b = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b) * b := by rw [hc]
    _ = (a * a) * (b * b) := by simp only [mul_assoc]
    _ = 1 := by rw [ha, hb, mul_one]

theorem exists_conj_comm_lift {X : Type} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (hO : Odd (Nat.card O)) {ζ : X} (hζ : ζ * ζ = 1) (y₀ : X)
    (hc : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) : X ⧸ O) * QuotientGroup.mk ζ =
      QuotientGroup.mk ζ * QuotientGroup.mk (y₀ * ζ * y₀⁻¹)) :
    ∃ g : X, (g * ζ * g⁻¹) * ζ = ζ * (g * ζ * g⁻¹) ∧
      (QuotientGroup.mk (g * ζ * g⁻¹) : X ⧸ O) = QuotientGroup.mk (y₀ * ζ * y₀⁻¹) := by
  have hx2 : (y₀ * ζ * y₀⁻¹) * (y₀ * ζ * y₀⁻¹) = 1 := by
    calc (y₀ * ζ * y₀⁻¹) * (y₀ * ζ * y₀⁻¹) = y₀ * (ζ * ζ) * y₀⁻¹ := by group
      _ = 1 := by rw [hζ]; group
  have hq : (QuotientGroup.mk (ζ * (y₀ * ζ * y₀⁻¹) * ζ * (y₀ * ζ * y₀⁻¹)) : X ⧸ O) = 1 := by
    have hmz : (QuotientGroup.mk ζ : X ⧸ O) * QuotientGroup.mk ζ = 1 := by
      rw [← QuotientGroup.mk_mul, hζ, QuotientGroup.mk_one]
    have hmx : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) : X ⧸ O) *
        QuotientGroup.mk (y₀ * ζ * y₀⁻¹) = 1 := by
      rw [← QuotientGroup.mk_mul, hx2, QuotientGroup.mk_one]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact mul_comm_sq_eq_one hc hmz hmx
  obtain ⟨o, ho, hoc⟩ :=
    C5O.exists_conj_comm_of_odd hO hζ hx2
      ((QuotientGroup.eq_one_iff (ζ * (y₀ * ζ * y₀⁻¹) * ζ * (y₀ * ζ * y₀⁻¹))).mp hq)
  have e : (o * y₀) * ζ * (o * y₀)⁻¹ = o * (y₀ * ζ * y₀⁻¹) * o⁻¹ := by group
  refine ⟨o * y₀, ?_, ?_⟩
  · rw [e]
    exact hoc
  · have hmo : (QuotientGroup.mk o : X ⧸ O) = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [e]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmo]

end CFSG.ClassicalInvolution.Asc77.C25G
