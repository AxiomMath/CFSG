module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

variable {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)]

@[expose] noncomputable def disp (t : MulAut S) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range ((binaryLin t : Additive S →ₗ[ZMod 2] Additive S) - 1))

theorem disp_conj (g t : MulAut S) : disp (g * t * g⁻¹) = disp t :=
  finrank_range_sub_one_conj (binaryLin : MulAut S →* (Additive S ≃ₗ[ZMod 2] Additive S)) g t

theorem disp_mul_le (t y : MulAut S) : disp (t * y) ≤ disp y + disp t :=
  finrank_range_sub_one_mul_le (binaryLin : MulAut S →* (Additive S ≃ₗ[ZMod 2] Additive S)) t y

theorem card_eq_fixV_zpowers_mul (t : MulAut S) :
    Nat.card S = Nat.card (fixV (Subgroup.zpowers t)) * 2 ^ disp t := by
  let δ : S →* S :=
    { toFun := fun v => t v * v⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hker : δ.ker = fixV (Subgroup.zpowers t) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV]
    constructor
    · intro h x hx
      have h1 : t v = v := by
        have : t v * v⁻¹ = 1 := h
        exact mul_inv_eq_one.mp this
      have h2 : t⁻¹ v = v := by
        have := congrArg (fun z => t⁻¹ z) h1
        simpa using this.symm
      have hk : ∀ k : ℤ, (t ^ k) v = v := by
        intro k
        induction k using Int.induction_on with
        | zero => simp
        | succ k ih => rw [zpow_add_one, MulAut.mul_apply, h1, ih]
        | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, h2, ih]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact hk k
    · intro h
      have := h t (Subgroup.mem_zpowers t)
      show t v * v⁻¹ = 1
      rw [this, mul_inv_cancel]
  have hrange : Nat.card δ.range = 2 ^ disp t := by
    have h0 := card_range_displacement t
    unfold disp
    rw [← h0]
    rfl
  have h := Subgroup.card_ker_mul_card_range δ
  rw [hker, hrange] at h
  exact h.symm

theorem two_pow_disp_le_card {A : Subgroup (MulAut S)} {t : MulAut S} (ht : t ∈ A)
    (hoff : Nat.card S ≤ Nat.card A * Nat.card (fixV A)) : 2 ^ disp t ≤ Nat.card A := by
  have h1 := card_eq_fixV_zpowers_mul t
  have h2 : fixV A ≤ fixV (Subgroup.zpowers t) := fun v hv x hx => hv x ((Subgroup.zpowers_le).2 ht hx)
  have h3 : Nat.card (fixV A) ≤ Nat.card (fixV (Subgroup.zpowers t)) :=
    Subgroup.card_le_of_le h2
  have hpos : 0 < Nat.card (fixV (Subgroup.zpowers t)) := Nat.card_pos
  have h4 : Nat.card (fixV (Subgroup.zpowers t)) * 2 ^ disp t ≤
      Nat.card A * Nat.card (fixV (Subgroup.zpowers t)) := by
    rw [← h1]
    exact hoff.trans (Nat.mul_le_mul_left _ h3)
  rw [mul_comm (Nat.card A)] at h4
  exact Nat.le_of_mul_le_mul_left h4 hpos

end CFSG.HardMathSupport.U4FF
