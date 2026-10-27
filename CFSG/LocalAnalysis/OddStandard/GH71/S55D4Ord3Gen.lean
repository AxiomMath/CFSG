module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Cover

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

variable {Y Γ : Type*} [Group Y] [Group Γ]

@[expose] def MovesAbelianTwo (b : MulAut Y) : Prop :=
  ∃ E : Subgroup Y, IsPGroup 2 E ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
    E.map b.toMonoidHom = E ∧ ∃ x ∈ E, b x ≠ x

@[expose] def Ord3Alt (r : ℕ) (b : MulAut Y) : Prop :=
  NormalizesPSub r b ∨ MovesAbelianTwo b

theorem movesAbelianTwo_of_congr (e : Y ≃* Γ) {b : MulAut Y}
    (h : MovesAbelianTwo (MulAut.congr e b)) : MovesAbelianTwo b := by
  obtain ⟨E, hEp, hEc, hEb, x, hxE, hx⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, hEp.map _, ?_, ?_, e.symm x, ⟨x, hxE, rfl⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    change e.symm a * e.symm c = e.symm c * e.symm a
    rw [← map_mul, ← map_mul, hEc a ha c hc]
  · have hc : b.toMonoidHom.comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp (MulAut.congr e b).toMonoidHom := by
      ext y
      change b (e.symm y) = e.symm (e (b (e.symm y)))
      rw [e.symm_apply_apply]
    rw [Subgroup.map_map, hc, ← Subgroup.map_map, hEb]
  · intro h'
    apply hx
    change e (b (e.symm x)) = x
    rw [h', e.apply_symm_apply]

theorem ord3Alt_of_congr (e : Y ≃* Γ) {r : ℕ} {b : MulAut Y}
    (h : Ord3Alt r (MulAut.congr e b)) : Ord3Alt r b :=
  h.imp (normalizesPSub_of_congr e) (movesAbelianTwo_of_congr e)

theorem ord3Alt_of_conj {r : ℕ} {b : MulAut Y} (γ : MulAut Y) (h : Ord3Alt r (γ * b * γ⁻¹)) :
    Ord3Alt r b :=
  ord3Alt_of_congr γ h

theorem map_eq_of_map_inv_eq {b : MulAut Y} {E : Subgroup Y}
    (h : E.map (b⁻¹).toMonoidHom = E) : E.map b.toMonoidHom = E := by
  conv_lhs => rw [← h]
  rw [Subgroup.map_map]
  convert Subgroup.map_id E
  ext y
  exact b.apply_symm_apply y

theorem ord3Alt_of_inv {r : ℕ} {b : MulAut Y} (h : Ord3Alt r b⁻¹) : Ord3Alt r b := by
  rcases h with ⟨R, hR1, hRp, hRb⟩ | ⟨E, hEp, hEc, hEb, x, hxE, hx⟩
  · exact Or.inl ⟨R, hR1, hRp, map_eq_of_map_inv_eq hRb⟩
  · refine Or.inr ⟨E, hEp, hEc, map_eq_of_map_inv_eq hEb, b⁻¹ x, ?_, fun h' => hx ?_⟩
    · rw [← hEb]
      exact ⟨x, hxE, rfl⟩
    · rw [MulAut.apply_inv_self] at h'
      exact h'.symm

theorem ord3_disj_of_alt {Y : Type} [Group Y] {r : ℕ} {b : MulAut Y} (hNoR : NoR 2 Y)
    (h : Ord3Alt r b) :
    (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
      ∃ s : ℕ, HHObsAt 3 s Y b ∧ (s = 2 → NoR 2 Y) := by
  have hmem : ∀ {E : Subgroup Y}, E.map b.toMonoidHom = E → ∀ x ∈ E, b x ∈ E :=
    fun {E} hE x hx => by
      have h1 := Subgroup.mem_map_of_mem b.toMonoidHom hx
      rwa [hE] at h1
  rcases h with ⟨R, hR1, hRp, hRb⟩ | ⟨E, hEp, hEc, hEb, x, hxE, hx⟩
  · exact Or.inl ⟨R, hR1, hRp, hmem hRb⟩
  · exact Or.inr ⟨2, ⟨Nat.prime_two, by decide, E, hEp, fun _ => hEc, hmem hEb, x, hxE, hx⟩,
      fun _ => hNoR⟩


theorem noR_two_of_lieModel_D4 {Y : Type} [Group Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hm : CFSG.Blueprint.LieModel Y .trialityD4 0 r f) : NoR 2 Y := by
  intro K _ _ hK ⟨e⟩
  have hmK := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  have hZ := CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_center_eq_bot hK hr hr2 hf hmK
  rw [hZ, Subgroup.card_bot]
  decide

end CFSG.OddStandard.GH71.S55
