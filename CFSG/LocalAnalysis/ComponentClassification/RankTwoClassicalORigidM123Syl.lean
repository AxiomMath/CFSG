module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidChar

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Unipotent

variable (K : Type) [Field K]

theorem slTr_zero : slTr (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slTr]

theorem slTr_add (a b : K) : slTr (a + b) = slTr a * slTr b := by
  apply Subtype.ext
  change (1 + single 0 1 (a + b) : Matrix (Fin 2) (Fin 2) K) =
    (1 + single 0 1 a) * (1 + single 0 1 b)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, single_apply, add_comm]

variable {K} in
theorem slTr_injective : Function.Injective (slTr (K := K)) := fun a b h => by
  have h1 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [slTr] using h1

@[expose] def slTrHom : Multiplicative K →* SL(2, K) where
  toFun c := slTr c.toAdd
  map_one' := by
    rw [toAdd_one]
    exact slTr_zero K
  map_mul' a b := by
    rw [toAdd_mul]
    exact slTr_add K _ _

theorem slTrHom_injective : Function.Injective (slTrHom K) := fun _ _ h =>
  Multiplicative.toAdd.injective (slTr_injective h)

end Unipotent

section Levi

variable (K : Type) [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)

@[expose] noncomputable def oRhoTwoU : Subgroup (GL ι K) :=
  ((oRhoTwoGL oe).comp (slTrHom K)).range

variable {K}

@[expose] noncomputable def oSylLevi (S₂ : Subgroup (GL ι₂ K)) : Subgroup (GL ι K) :=
  oRhoTwoU K oe ⊔ S₂.map (oKappaGL oe)

theorem oRhoTwoGL_injective : Function.Injective (oRhoTwoGL (K := K) oe) := fun A A' h => by
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
  simp only [coe_oRhoTwoGL] at h1
  have h2 := (oblk_injective h1).2
  rw [rhoTwoMat_apply, rhoTwoMat_apply, fromBlocks_inj] at h2
  exact Subtype.ext h2.1

theorem oKappaGL_injective : Function.Injective (oKappaGL (K := K) oe) := fun Y Y' h => by
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
  simp only [coe_oKappaGL] at h1
  exact Units.ext (oblk_injective h1).1

theorem card_oRhoTwoU : Nat.card (oRhoTwoU K oe) = Nat.card K := by
  have hinj : Function.Injective ((oRhoTwoGL oe).comp (slTrHom K)) := fun _ _ h =>
    slTrHom_injective K (oRhoTwoGL_injective oe h)
  rw [oRhoTwoU, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr Multiplicative.toAdd

theorem map_oKappaGL_le_centralizer (S₂ : Subgroup (GL ι₂ K)) :
    S₂.map (oKappaGL oe) ≤ centralizer (oRhoTwoU K oe : Set (GL ι K)) := by
  rintro _ ⟨Y, -, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨c, rfl⟩
  exact (commute_oKappaGL_oRhoTwoGL Y _).symm.eq

theorem oRhoTwoU_inf_map_oKappaGL (S₂ : Subgroup (GL ι₂ K)) :
    oRhoTwoU K oe ⊓ S₂.map (oKappaGL oe) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨c, rfl⟩, ⟨Y, -, hY⟩⟩
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) hY
  simp only [coe_oKappaGL, MonoidHom.comp_apply, coe_oRhoTwoGL] at h1
  have hY1 : Y = 1 := Units.ext (oblk_injective h1).1
  rw [mem_bot, ← hY, hY1, map_one]

theorem card_oSylLevi (S₂ : Subgroup (GL ι₂ K)) :
    Nat.card (oSylLevi oe S₂) = Nat.card K * Nat.card S₂ := by
  rw [oSylLevi, CFSG.ComponentClassification.AS76b.card_sup_eq_mul
    ((map_oKappaGL_le_centralizer oe S₂).trans (centralizer_le_normalizer _))
    (oRhoTwoU_inf_map_oKappaGL oe S₂), card_oRhoTwoU,
    Subgroup.card_map_of_injective (oKappaGL_injective oe)]

variable [CharP K 2]

theorem isPGroup_oRhoTwoU : IsPGroup 2 (oRhoTwoU K oe) := by
  rintro ⟨_, c, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hc : c ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← map_pow, hc, map_one]

theorem isPGroup_oSylLevi {S₂ : Subgroup (GL ι₂ K)} (hS₂p : IsPGroup 2 S₂) :
    IsPGroup 2 (oSylLevi oe S₂) :=
  (isPGroup_oRhoTwoU oe).to_sup_of_normal_left' (hS₂p.map _)
    ((map_oKappaGL_le_centralizer oe S₂).trans (centralizer_le_normalizer _))

end Levi

section Param

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι] [DecidableEq ι]
  (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

theorem qEGL_eq_mul (u : Fin 2 → ι₂ → K) (c : K) :
    qEGL oe Q₂ u c = qEGL oe Q₂ u 0 * qEGL oe Q₂ 0 c := by
  apply Units.ext
  rw [Units.val_mul, coe_qEGL, coe_qEGL, coe_qEGL, qE_mul]
  congr 1 <;> simp

theorem qEGL_injective :
    Function.Injective fun p : (Fin 2 → ι₂ → K) × K => qEGL oe Q₂ p.1 p.2 := by
  rintro ⟨u, c⟩ ⟨u', c'⟩ h
  have hu : u = u' := eq_of_qEGL_eq oe Q₂ h
  subst hu
  have h1 : qEGL oe Q₂ u c = qEGL oe Q₂ u c' := h
  rw [qEGL_eq_mul oe Q₂ u c, qEGL_eq_mul oe Q₂ u c'] at h1
  exact Prod.ext rfl (eq_of_qEGL_zero_eq oe Q₂ (mul_left_cancel h1))

theorem card_oQE [Fintype ι₂] : Nat.card (oQE oe Q₂) = Nat.card K ^ (2 * Fintype.card ι₂ + 1) := by
  have h1 : Nat.card (oQE oe Q₂) =
      Nat.card (Set.range fun p : (Fin 2 → ι₂ → K) × K => qEGL oe Q₂ p.1 p.2) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [h1, Nat.card_range_of_injective (qEGL_injective oe Q₂), Nat.card_prod, Nat.card_fun,
    Nat.card_fun, Nat.card_eq_fintype_card (α := ι₂), Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin]
  ring

end Param

section Step

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

@[expose] noncomputable def oSylStep (S₂ : Subgroup (GL ι₂ K)) : Subgroup (GL ι K) :=
  oQE oe Q₂ ⊔ oSylLevi oe S₂

variable {oe Q₂} {S₂ : Subgroup (GL ι₂ K)}

omit [CharP K 2] in
theorem oSylLevi_le_oL₀ (hS₂ : S₂ ≤ StatedOmega ⇑Q₂) : oSylLevi oe S₂ ≤ oL₀ oe Q₂ := by
  refine sup_le ?_ (le_sup_of_le_right (map_mono hS₂))
  rintro _ ⟨c, rfl⟩
  exact mem_sup_left ⟨slTrHom K c, rfl⟩

theorem oSylStep_le_oXt (hS₂ : S₂ ≤ StatedOmega ⇑Q₂) : oSylStep oe Q₂ S₂ ≤ oXt oe Q₂ :=
  sup_le_sup_left (oSylLevi_le_oL₀ hS₂) _

variable {Q : QuadraticForm K (ι → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem oSylLevi_le_normalizer (hS₂ : S₂ ≤ StatedOmega ⇑Q₂) :
    oSylLevi oe S₂ ≤ normalizer (oQE oe Q₂ : Set (GL ι K)) :=
  (oSylLevi_le_oL₀ hS₂).trans (le_sup_right.trans (oXt_le_normalizer_oQE hQ))

theorem isPGroup_oSylStep (hS₂ : S₂ ≤ StatedOmega ⇑Q₂) (hS₂p : IsPGroup 2 S₂) :
    IsPGroup 2 (oSylStep oe Q₂ S₂) :=
  isPGroup_oQE.to_sup_of_normal_left' (isPGroup_oSylLevi oe hS₂p)
    (oSylLevi_le_normalizer hQ hS₂)

theorem card_oSylStep (hS₂ : S₂ ≤ StatedOmega ⇑Q₂) :
    Nat.card (oSylStep oe Q₂ S₂) = Nat.card K ^ (2 * Fintype.card ι₂ + 2) * Nat.card S₂ := by
  have hinf : oQE oe Q₂ ⊓ oSylLevi oe S₂ = ⊥ := by
    rw [eq_bot_iff, ← oL₀_inf_oQE (oe := oe) (Q₂ := Q₂)]
    exact fun g hg => ⟨oSylLevi_le_oL₀ hS₂ hg.2, hg.1⟩
  rw [oSylStep, CFSG.ComponentClassification.AS76b.card_sup_eq_mul
    (oSylLevi_le_normalizer hQ hS₂) hinf, card_oQE, card_oSylLevi]
  ring

end Step

end CFSG.ComponentClassification.RankTwoClassical.ORigid
