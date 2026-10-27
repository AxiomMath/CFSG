module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)

abbrev SL2 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

abbrev Gm : Type := SL2 × SL2

@[expose] def act (γ : Gm) (m : M2) : M2 := (γ.1 : M2) * m * (γ.2 : M2).transpose

theorem act_one (m : M2) : act 1 m = m := by
  simp [act]

theorem act_mul (γ δ : Gm) (m : M2) : act (γ * δ) m = act γ (act δ m) := by
  simp only [act, Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

theorem act_add (γ : Gm) (m m' : M2) : act γ (m + m') = act γ m + act γ m' := by
  simp [act, Matrix.mul_add, Matrix.add_mul]

theorem act_smul (γ : Gm) (c : ZMod 2) (m : M2) : act γ (c • m) = c • act γ m := by
  simp [act]

@[expose] def actEquiv (γ : Gm) : M2 ≃ₗ[ZMod 2] M2 where
  toFun := act γ
  invFun := act γ⁻¹
  map_add' := act_add γ
  map_smul' := act_smul γ
  left_inv m := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv m := by rw [← act_mul, mul_inv_cancel, act_one]

@[expose] def ρ₀ : Gm →* (M2 ≃ₗ[ZMod 2] M2) where
  toFun := actEquiv
  map_one' := LinearEquiv.ext act_one
  map_mul' γ δ := LinearEquiv.ext (act_mul γ δ)

@[simp] theorem ρ₀_apply (γ : Gm) (m : M2) : ρ₀ γ m = act γ m := rfl

@[expose] def qf (m : M2) : ZMod 2 := m 0 0 * m 1 1 + m 0 1 * m 1 0

@[expose] def b₀ : LinearMap.BilinForm (ZMod 2) M2 :=
  LinearMap.mk₂ (ZMod 2) (fun m m' => m 0 0 * m' 1 1 + m 0 1 * m' 1 0)
    (fun m₁ m₂ m' => by simp only [Matrix.add_apply]; ring)
    (fun c m m' => by simp only [Matrix.smul_apply, smul_eq_mul]; ring)
    (fun m m'₁ m'₂ => by simp only [Matrix.add_apply]; ring)
    (fun c m m' => by simp only [Matrix.smul_apply, smul_eq_mul]; ring)

@[expose] def q₀ : QuadraticForm (ZMod 2) M2 := b₀.toQuadraticMap

theorem q₀_apply (m : M2) : q₀ m = qf m := rfl

@[expose] def pf (m m' : M2) : ZMod 2 :=
  m 0 0 * m' 1 1 + m' 0 0 * m 1 1 + m 0 1 * m' 1 0 + m' 0 1 * m 1 0

theorem polar_q₀ (m m' : M2) : polar q₀ m m' = pf m m' := by
  simp only [polar, q₀_apply, qf, pf, Matrix.add_apply]
  ring

theorem q₀_nondegenerate : q₀.polarBilin.Nondegenerate := by
  have key : ∀ m : M2, (∀ m' : M2, pf m m' = 0) → m = 0 := by decide +kernel
  refine ⟨fun m hm => key m fun m' => ?_, fun m hm => key m fun m' => ?_⟩
  · rw [← polar_q₀]
    exact hm m'
  · have := hm m'
    rw [polarBilin_apply_apply, polar_q₀] at this
    rwa [show pf m m' = pf m' m by simp only [pf]; ring]

instance : Finite (M2 ≃ₗ[ZMod 2] M2) :=
  Finite.of_injective (fun e => (e : M2 → M2)) fun _ _ h => LinearEquiv.ext (congrFun h)

theorem qf_act : ∀ (γ : Gm) (m : M2), qf (act γ m) = qf m := by decide +kernel

theorem ρ₀_mem_orthogonalGroup (γ : Gm) : ρ₀ γ ∈ TauCeti.QuadraticMap.orthogonalGroup q₀ :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun m => qf_act γ m

theorem fixCount : ∀ γ : Gm, Fintype.card {m : M2 // act γ m = m} = 1 ∨
    Fintype.card {m : M2 // act γ m = m} = 4 ∨ Fintype.card {m : M2 // act γ m = m} = 16 := by
  decide +kernel

theorem finrank_M2 : finrank (ZMod 2) M2 = 4 := by
  rw [Module.finrank_matrix, Module.finrank_self]
  simp

theorem even_finrank_commSpace_ρ₀ (γ : Gm) : Even (finrank (ZMod 2) (commSpace (ρ₀ γ))) := by
  have h1 := finrank_commSpace_add_finrank_fixSpace (K := ZMod 2) (ρ₀ γ)
  rw [finrank_M2] at h1
  have h2 : Nat.card (fixSpace (ρ₀ γ)) = 2 ^ finrank (ZMod 2) (fixSpace (ρ₀ γ)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 : Nat.card (fixSpace (ρ₀ γ)) = Fintype.card {m : M2 // act γ m = m} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun m => by rw [mem_fixSpace]; rfl)
  rw [h3] at h2
  have hle := Submodule.finrank_le (fixSpace (ρ₀ γ))
  rw [finrank_M2] at hle
  rcases fixCount γ with h | h | h <;> rw [h] at h2
  · have : finrank (ZMod 2) (fixSpace (ρ₀ γ)) = 0 :=
      Nat.pow_right_injective le_rfl (h2.symm.trans (by norm_num))
    exact ⟨2, by omega⟩
  · have : finrank (ZMod 2) (fixSpace (ρ₀ γ)) = 2 :=
      Nat.pow_right_injective le_rfl (h2.symm.trans (by norm_num))
    exact ⟨1, by omega⟩
  · have : finrank (ZMod 2) (fixSpace (ρ₀ γ)) = 4 :=
      Nat.pow_right_injective le_rfl (h2.symm.trans (by norm_num))
    exact ⟨0, by omega⟩

theorem act_injective : ∀ γ δ : Gm, (∀ m : M2, act γ m = act δ m) → γ = δ := by
  decide +kernel

theorem ρ₀_injective : Function.Injective ρ₀ := fun γ δ h =>
  act_injective γ δ fun m => LinearEquiv.congr_fun h m

theorem card_Gm : Nat.card Gm = 36 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def plusEquiv : (Fin 2 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] M2 where
  toFun v := !![v (.inl 0), v (.inl 1); v (.inr 1), v (.inr 0)]
  invFun m := Sum.elim ![m 0 0, m 0 1] ![m 1 1, m 1 0]
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  left_inv v := by
    funext j
    rcases j with i | i <;> fin_cases i <;> rfl
  right_inv m := by ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem q₀_plusEquiv (v : Fin 2 ⊕ Fin 2 → ZMod 2) :
    q₀ (plusEquiv v) = CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2) v := by
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply, q₀_apply, Fin.sum_univ_two]
  simp only [qf, plusEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]

theorem card_orthogonalGroup_q₀ :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup q₀) = 72 := by
  have e : (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)).IsometryEquiv q₀ :=
    { plusEquiv with map_app' := q₀_plusEquiv }
  rw [← CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr e]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := ZMod 2) 1
  have h72 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2))) : ℤ) = 72 := by
    rw [h, Nat.card_zmod]
    norm_num [Finset.Icc_self]
  exact_mod_cast h72

theorem card_omegaGroup_q₀ : Nat.card (omegaGroup q₀ q₀_nondegenerate) = 36 := by
  have h1 := relIndex_omegaGroup q₀ q₀_nondegenerate
  have h2 := Subgroup.relIndex_mul_card (omegaGroup q₀ q₀_nondegenerate)
    (TauCeti.QuadraticMap.orthogonalGroup q₀)
  rw [h1, card_orthogonalGroup_q₀, inf_eq_left.mpr (omegaGroup_le q₀ q₀_nondegenerate)] at h2
  omega

theorem range_ρ₀ : ρ₀.range = omegaGroup q₀ q₀_nondegenerate := by
  have hle : ρ₀.range ≤ omegaGroup q₀ q₀_nondegenerate := by
    rintro _ ⟨γ, rfl⟩
    exact ⟨ρ₀_mem_orthogonalGroup γ, even_finrank_commSpace_ρ₀ γ⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_omegaGroup_q₀, ← card_Gm]
  exact (Nat.card_congr (MonoidHom.ofInjective ρ₀_injective).toEquiv).le

@[expose, irreducible] def E00 : M2 := !![1, 0; 0, 0]

theorem E00_ne_zero : E00 ≠ 0 := by decide +kernel

theorem exists_act_eq_E00 : ∀ m : M2, m ≠ 0 → qf m = 0 → ∃ γ : Gm, act γ m = E00 := by
  decide +kernel

end CFSG.LargeExtraspecial.S10
