module

public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.ClassicalInvolution.PhanG

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary

variable {F : Type*} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem mulSingle_mem_detKer {a k : Fin m} (s : normOne σ) :
    (Pi.mulSingle a s * Pi.mulSingle k s⁻¹ : Fin m → normOne σ) ∈ detKer σ m := by
  rw [mem_detKer]
  simp only [Pi.mul_apply]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ x : Fin m, (Pi.mulSingle a s : Fin m → normOne σ) x = s := by
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.mulSingle_eq_of_ne hb]
    · simp
  have h2 : ∏ x : Fin m, (Pi.mulSingle k s⁻¹ : Fin m → normOne σ) x = s⁻¹ := by
    rw [Finset.prod_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.mulSingle_eq_of_ne hb]
    · simp
  rw [h1, h2, mul_inv_cancel]

theorem eq_torus_of_comm_torus (hs : ∃ s : normOne σ, (s : Fˣ) ≠ 1) (hm : 3 ≤ m) {g : SUid σ m}
    (h : ∀ t ∈ torus σ m, g * t = t * g) : g ∈ torus σ m := by
  obtain ⟨s, hs1⟩ := hs
  rw [mem_torus_iff]
  intro a b hab
  have hcard : ({a, b} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Finset.card_le_two) (by omega)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hka, hkb⟩ := hk
  have hd := mulSingle_mem_detKer (σ := σ) (a := a) (k := k) s
  have hc := h _ (diagSU_mem_torus _ hd)
  have hc' := congrArg
    (fun x : SUid σ m => (((x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) a b) hc
  simp only [Subgroup.coe_mul, Units.val_mul, coe_coe_diagSU, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at hc'
  have hbv : (Pi.mulSingle a s * Pi.mulSingle k s⁻¹ : Fin m → normOne σ) b = 1 := by
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hab.symm, Pi.mulSingle_eq_of_ne (Ne.symm hkb),
      mul_one]
  have hav : (Pi.mulSingle a s * Pi.mulSingle k s⁻¹ : Fin m → normOne σ) a = s := by
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hka), mul_one]
  rw [hbv, hav] at hc'
  have h1 : ((((1 : normOne σ) : Fˣ)) : F) = 1 := rfl
  rw [h1, mul_one] at hc'
  have : (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) a b) * (1 - (((s : normOne σ) : Fˣ) : F))
      = 0 := by
    linear_combination hc'
  rcases mul_eq_zero.mp this with h0 | h0
  · exact h0
  · exact absurd (Units.ext (sub_eq_zero.mp h0).symm) hs1

end CFSG.ClassicalInvolution.PhanG
