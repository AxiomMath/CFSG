module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitSplitting

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule Matrix

variable (hV : e6Data.Valid) {K : Type*} [Field K] [CharP K 2]

@[expose] def fixSub (A : Subgroup (hV.minGroup K)) : Submodule K (Fin e6Data.d →₀ K) where
  carrier := {v | ∀ a ∈ A, hV.endo K a v = v}
  add_mem' := fun hv hw a ha => by rw [map_add, hv a ha, hw a ha]
  zero_mem' := fun _ _ => map_zero _
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

theorem v0_mem_fixSub {A : Subgroup (hV.minGroup K)} (hA : A ≤ F4in27 hV K) :
    v0 K ∈ fixSub hV A := fun _ ha => endo_v0 hV (hA ha)

theorem fixSub_eq_sup {A : Subgroup (hV.minGroup K)} (hA : A ≤ F4in27 hV K) :
    fixSub hV A = Submodule.span K {v0 K} ⊔ (fixSub hV A ⊓ M26 hV K) := by
  refine le_antisymm (fun w hw => ?_) (sup_le ?_ inf_le_left)
  · have h1 : w - fT K w • v0 K ∈ M26 hV K := by
      rw [M26_eq_ker hV, LinearMap.mem_ker, map_sub, map_smul, fT_v0, smul_eq_mul, mul_one,
        sub_self]
    have h2 : w - fT K w • v0 K ∈ fixSub hV A :=
      Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (v0_mem_fixSub hV hA))
    have h3 : fT K w • v0 K ∈ Submodule.span K {v0 K} :=
      Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have := Submodule.add_mem_sup h3 (Submodule.mem_inf.2 ⟨h2, h1⟩)
    rwa [add_sub_cancel] at this
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact v0_mem_fixSub hV hA

theorem natCard_fixSub {A : Subgroup (hV.minGroup K)} (hA : A ≤ F4in27 hV K) :
    Nat.card (fixSub hV A) = Nat.card K * Nat.card ↥(fixSub hV A ⊓ M26 hV K) := by
  rw [Module.natCard_eq_pow_finrank (K := K), Module.natCard_eq_pow_finrank (K := K) (V := ↥(fixSub hV A ⊓ M26 hV K)),
    ← pow_succ']
  congr 1
  have hdisj : Submodule.span K {v0 K} ⊓ (fixSub hV A ⊓ M26 hV K) = ⊥ := by
    have := (isCompl_v0_M26 hV (K := K)).inf_eq_bot
    rw [eq_bot_iff] at this ⊢
    exact le_trans (inf_le_inf_left _ inf_le_right) this
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {v0 K})
    (fixSub hV A ⊓ M26 hV K)
  rw [← fixSub_eq_sup hV hA, hdisj, finrank_bot, finrank_span_singleton v0_ne_zero] at h
  omega

theorem offender_transfer_one [Finite K]
    (H : ∀ A : Subgroup (hV.minGroup K), A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixSub hV A) ≤ Nat.card K ^ 26)
    {A : Subgroup (hV.minGroup K)} (hA : A ≤ F4in27 hV K) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card ↥(fixSub hV A ⊓ M26 hV K) ≤ Nat.card K ^ 25 := by
  have h := H A hne hel
  rw [natCard_fixSub hV hA, ← mul_assoc, mul_comm (Nat.card A), mul_assoc,
    show Nat.card K ^ 26 = Nat.card K * Nat.card K ^ 25 by ring] at h
  exact Nat.le_of_mul_le_mul_left h Nat.card_pos

theorem offender_transfer_two [Finite K]
    (H : ∀ A : Subgroup (hV.minGroup K), A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A ^ 2 * Nat.card (fixSub hV A) ≤ Nat.card K ^ 42)
    {A : Subgroup (hV.minGroup K)} (hA : A ≤ F4in27 hV K) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ^ 2 * Nat.card ↥(fixSub hV A ⊓ M26 hV K) ≤ Nat.card K ^ 41 := by
  have h := H A hne hel
  rw [natCard_fixSub hV hA, ← mul_assoc, mul_comm (Nat.card A ^ 2), mul_assoc,
    show Nat.card K ^ 42 = Nat.card K * Nat.card K ^ 41 by ring] at h
  exact Nat.le_of_mul_le_mul_left h Nat.card_pos

theorem offender_transfer [Finite K]
    (H : ∀ A : Subgroup (hV.minGroup K), A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixSub hV A) ≤ Nat.card K ^ 26 ∧
        Nat.card A ^ 2 * Nat.card (fixSub hV A) ≤ Nat.card K ^ 42)
    {A : Subgroup (hV.minGroup K)} (hA : A ≤ F4in27 hV K) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card ↥(fixSub hV A ⊓ M26 hV K) ≤ Nat.card K ^ 25 ∧
      Nat.card A ^ 2 * Nat.card ↥(fixSub hV A ⊓ M26 hV K) ≤ Nat.card K ^ 41 :=
  ⟨offender_transfer_one hV (fun A h1 h2 => (H A h1 h2).1) hA hne hel,
    offender_transfer_two hV (fun A h1 h2 => (H A h1 h2).2) hA hne hel⟩

theorem endo_mul_apply (g h : hV.minGroup K) (v : Fin e6Data.d →₀ K) :
    hV.endo K (g * h) v = hV.endo K g (hV.endo K h v) := by
  rw [MinData.Valid.endo_mul, Module.End.mul_apply]

theorem endo_inv_apply (g : hV.minGroup K) (v : Fin e6Data.d →₀ K) :
    hV.endo K g⁻¹ (hV.endo K g v) = v := by
  rw [← Module.End.mul_apply, MinData.Valid.endo_inv_mul, Module.End.one_apply]

theorem endo_apply_inv (g : hV.minGroup K) (v : Fin e6Data.d →₀ K) :
    hV.endo K g (hV.endo K g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, MinData.Valid.endo_mul_inv, Module.End.one_apply]

theorem fixSub_map_conj (A : Subgroup (hV.minGroup K)) (g : hV.minGroup K) :
    fixSub hV (A.map (MulAut.conj g).toMonoidHom) = (fixSub hV A).map (hV.endo K g) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨hV.endo K g⁻¹ v, fun a ha => ?_, endo_apply_inv hV g v⟩
    have h := hv (g * a * g⁻¹) ⟨a, ha, by simp [MulAut.conj_apply]⟩
    calc hV.endo K a (hV.endo K g⁻¹ v)
        = hV.endo K (a * g⁻¹) v := (endo_mul_apply hV a g⁻¹ v).symm
      _ = hV.endo K (g⁻¹ * (g * a * g⁻¹)) v := by rw [show a * g⁻¹ = g⁻¹ * (g * a * g⁻¹) by group]
      _ = hV.endo K g⁻¹ (hV.endo K (g * a * g⁻¹) v) := endo_mul_apply hV _ _ _
      _ = hV.endo K g⁻¹ v := by rw [h]
  · rintro ⟨w, hw, rfl⟩ a' ⟨a, ha, rfl⟩
    have h := hw a ha
    calc hV.endo K ((MulAut.conj g).toMonoidHom a) (hV.endo K g w)
        = hV.endo K (g * a) w := by
          rw [← endo_mul_apply]; congr 1; simp [MulAut.conj_apply]
      _ = hV.endo K g (hV.endo K a w) := endo_mul_apply hV _ _ _
      _ = hV.endo K g w := by rw [h]

theorem natCard_fixSub_map_conj (A : Subgroup (hV.minGroup K)) (g : hV.minGroup K) :
    Nat.card (fixSub hV (A.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixSub hV A) := by
  rw [fixSub_map_conj]
  have hinj : Function.Injective (hV.endo K g) :=
    Function.LeftInverse.injective (endo_inv_apply hV g)
  exact (Nat.card_congr (Submodule.equivMapOfInjective (hV.endo K g) hinj (fixSub hV A)).toEquiv).symm

theorem natCard_map_conj (A : Subgroup (hV.minGroup K)) (g : hV.minGroup K) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  (Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm

theorem offender_transfer_of_conj [Finite K] (U : Subgroup (hV.minGroup K))
    (hconj : ∀ A : Subgroup (hV.minGroup K), (∀ a ∈ A, a ^ 2 = 1) →
      ∃ g : hV.minGroup K, A.map (MulAut.conj g).toMonoidHom ≤ U)
    (H : ∀ A : Subgroup (hV.minGroup K), A ≤ U → A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixSub hV A) ≤ Nat.card K ^ 26 ∧
        Nat.card A ^ 2 * Nat.card (fixSub hV A) ≤ Nat.card K ^ 42)
    {A : Subgroup (hV.minGroup K)} (hA : A ≤ F4in27 hV K) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card ↥(fixSub hV A ⊓ M26 hV K) ≤ Nat.card K ^ 25 ∧
      Nat.card A ^ 2 * Nat.card ↥(fixSub hV A ⊓ M26 hV K) ≤ Nat.card K ^ 41 := by
  refine offender_transfer hV (fun B hB hBel => ?_) hA hne hel
  obtain ⟨g, hg⟩ := hconj B hBel
  have hBne : B.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun h => hB (by
    rw [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at h
    exact h)
  have hBel' : ∀ a ∈ B.map (MulAut.conj g).toMonoidHom, a ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hBel b hb, map_one]
  have h := H _ hg hBne hBel'
  rwa [natCard_map_conj, natCard_fixSub_map_conj] at h

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
