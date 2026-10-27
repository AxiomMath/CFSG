module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieTorus

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.Quasithin.H13.F431.L3.P3
open CFSG.QuasithinUnique.Fin257.L3
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem unit_pow_three_of_card_four {F : Type} [Field F] [Finite F] (hq : Nat.card F = 4)
    (t : Fˣ) : t ^ 3 = 1 := by
  have h3 : Nat.card Fˣ = 3 := by
    have := Nat.card_units F
    omega
  have h := pow_card_eq_one' (G := Fˣ) (x := t)
  rwa [h3] at h

@[expose] def diagUnitsHom (F : Type) [Field F] : Fˣ →* Fˣ × Fˣ where
  toFun t := (t, t)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diagUnitsHom_injective (F : Type) [Field F] :
    Function.Injective (diagUnitsHom F) := by
  intro a b h
  exact congrArg Prod.fst h

theorem ker_dHom_eq {F : Type} [Field F] [Finite F] (hq : Nat.card F = 4) :
    (dHom F).ker = (diagUnitsHom F).range := by
  ext ⟨t₁, t₂⟩
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro h
    have hp : proj 3 F (dMat t₁ t₂) = 1 := h
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hp)
    have e0 : (t₁ : F) = c := by
      have := congrFun (congrFun hc 0) 0
      simpa [coe_dMat, Matrix.scalar_apply] using this
    have e1 : (t₂ : F) = c := by
      have := congrFun (congrFun hc 1) 1
      simpa [coe_dMat, Matrix.scalar_apply] using this
    exact ⟨t₁, Prod.ext rfl (Units.ext (e0.trans e1.symm))⟩
  · rintro ⟨t, ht⟩
    have h1 : t = t₁ := congrArg Prod.fst ht
    have h2 : t = t₂ := congrArg Prod.snd ht
    rw [← h1, ← h2]
    have htt : (t * t)⁻¹ = t :=
      inv_eq_of_mul_eq_one_right ((pow_three' t).symm.trans (unit_pow_three_of_card_four hq t))
    have hmat : (dMat t t : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (t : F) := by
      rw [coe_dMat, htt, Matrix.scalar_apply]
      congr 1
      funext i
      fin_cases i <;> first | rfl | simp
    show proj 3 F (dMat t t) = 1
    exact proj_eq_one_iff.mpr (mem_scalars.mpr ⟨t, unit_pow_three_of_card_four hq t, hmat⟩)

theorem card_ker_dHom {F : Type} [Field F] [Finite F] (hq : Nat.card F = 4) :
    Nat.card (dHom F).ker = 3 := by
  rw [ker_dHom_eq hq, ← Nat.card_congr (MonoidHom.ofInjective (diagUnitsHom_injective F)).toEquiv]
  have := Nat.card_units F
  omega

theorem card_torus3 {F : Type} [Field F] [Finite F] (hq : Nat.card F = 4) :
    Nat.card (CFSG.Quasithin.H13.F431.L3.P3.torus3 F) = 3 := by
  have hmul := Subgroup.card_ker_mul_card_range (dHom F)
  rw [card_ker_dHom hq, Nat.card_prod] at hmul
  have hU := Nat.card_units F
  have h3 : Nat.card Fˣ = 3 := by omega
  rw [h3] at hmul
  show Nat.card (dHom F).range = 3
  omega

theorem projUnitriangular_inf_torus3 {F : Type} [Field F] :
    projUnitriangular 3 F ⊓ torus3 F = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgU, hgT⟩
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hgU
  obtain ⟨t₁, t₂, h⟩ := mem_torus3.mp hgT
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  have hD : (dMat t₁ t₂ : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [Matrix.scalar_apply] at hD
  have hAij : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
    intro i j hij
    have hz : (dMat t₁ t₂ : Matrix (Fin 3) (Fin 3) F) i j = 0 := isDiag_dMat t₁ t₂ hij
    have h2 : (A : Matrix (Fin 3) (Fin 3) F) i j * (c : F) = 0 := by
      have := congrFun (congrFun hD i) j
      rw [hz] at this
      simpa [Matrix.mul_diagonal] using this.symm
    exact (mul_eq_zero.mp h2).resolve_right (Units.ne_zero c)
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext i j
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq]
      exact hA.2 j
    · rw [Matrix.one_apply_ne hij]
      exact hAij i j hij
  rw [Subgroup.mem_bot, hA1, map_one]

theorem normalizer_U_eq_sup_torus3 {F : Type} [Field F] [CharP F 2] [Finite F] :
    Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) = projUnitriangular 3 F ⊔ torus3 F := by
  refine le_antisymm ?_ (sup_le Subgroup.le_normalizer torus3_le_normalizer)
  intro h hh
  obtain ⟨u, hu, b, hb, rfl⟩ := torus3_mul hh
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hb)

end CFSG.GH74.QTGen4.DSGen4.L34

end
