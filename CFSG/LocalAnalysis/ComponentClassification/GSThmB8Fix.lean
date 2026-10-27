module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Local

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Eight

variable {Y : Type*} [Group Y]

theorem oddBarAut_mk (σ : MulAut Y) (y : Y) :
    oddBarAut Y σ (y : Y ⧸ pPrimeCore 2 Y) = ((σ y : Y) : Y ⧸ pPrimeCore 2 Y) := rfl

theorem fixSubgroup_oddBarAut [Finite Y] (σ : MulAut Y) (hσ : IsPGroup 2 (zpowers σ)) :
    fixSubgroup (oddBarAut Y σ) = (fixSubgroup σ).map (QuotientGroup.mk' (pPrimeCore 2 Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro ybar hy
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ybar
    rw [mem_fixSubgroup] at hy
    have hpow : ∀ (t : MulAut Y), t ∈ zpowers σ → ∀ w : Y,
        ((w : Y ⧸ pPrimeCore 2 Y) = (y : Y ⧸ pPrimeCore 2 Y)) →
          ((t w : Y) : Y ⧸ pPrimeCore 2 Y) = (y : Y ⧸ pPrimeCore 2 Y) := by
      intro t ht w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
      have h1 : ((σ ^ k) w : Y ⧸ pPrimeCore 2 Y) = oddBarAut Y (σ ^ k) (w : Y ⧸ pPrimeCore 2 Y) :=
        rfl
      rw [h1, map_zpow, hw]
      have h2 : ∀ n : ℤ, (oddBarAut Y σ ^ n) (y : Y ⧸ pPrimeCore 2 Y) =
          (y : Y ⧸ pPrimeCore 2 Y) := by
        intro n
        induction n using Int.induction_on with
        | zero => rfl
        | succ n ih =>
          rw [zpow_add_one, MulAut.mul_apply, hy, ih]
        | pred n ih =>
          rw [zpow_sub_one, MulAut.mul_apply]
          conv_rhs => rw [← ih]
          congr 1
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
          exact hy.symm
      exact h2 k
    let F : SubMulAction ↥(zpowers σ) Y :=
      { carrier := {w | (w : Y ⧸ pPrimeCore 2 Y) = (y : Y ⧸ pPrimeCore 2 Y)}
        smul_mem' := fun t w hw => hpow t t.2 w hw }
    have hF : Nat.card F = Nat.card (pPrimeCore 2 Y) := by
      let e : F ≃ pPrimeCore 2 Y :=
        { toFun := fun w => ⟨y⁻¹ * w, by
            have := (QuotientGroup.eq (s := pPrimeCore 2 Y)).mp w.2.symm
            exact this⟩
          invFun := fun o => ⟨y * o, by
            show ((y * o : Y) : Y ⧸ pPrimeCore 2 Y) = (y : Y ⧸ pPrimeCore 2 Y)
            rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (o : Y)).mpr o.2, mul_one]⟩
          left_inv := fun w => by
            apply Subtype.ext
            simp
          right_inv := fun o => by
            apply Subtype.ext
            simp }
      exact Nat.card_congr e
    have hnd : ¬ 2 ∣ Nat.card F := by
      rw [hF]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    obtain ⟨w, hw⟩ := hσ.nonempty_fixed_point_of_prime_not_dvd_card F hnd
    refine ⟨w.1, ?_, w.2⟩
    show w.1 ∈ fixSubgroup σ
    rw [mem_fixSubgroup]
    have := congrArg Subtype.val (hw ⟨σ, mem_zpowers σ⟩)
    exact this
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_fixSubgroup]
    change oddBarAut Y σ (w : Y ⧸ pPrimeCore 2 Y) = (w : Y ⧸ pPrimeCore 2 Y)
    rw [oddBarAut_mk, (mem_fixSubgroup.mp hw)]

end Eight

end CFSG.ComponentClassification.GSThmB
