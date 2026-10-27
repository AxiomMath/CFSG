module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition
public import CFSG.CGT.Timmesfeld75.Sec4TwoStruct

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a w : G}

theorem Sec4ActsTriv.mem_normalizer (hw : Sec4ActsTriv T T₁ T₂ w) :
    w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) :=
  mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le
    (conjSubgroup_le_of_forall_mem fun _ hm => hw.conj_mem hm))

@[expose] def sec4Ker (T T₁ T₂ : Subgroup G) : Subgroup G where
  carrier := {g | Sec4ActsTriv T T₁ T₂ g}
  mul_mem' {g h} hg hh := fun y hy => by
    have e : ⁅g * h, y⁆ = (g * ⁅h, y⁆ * g⁻¹) * ⁅g, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (sec4N T T₁ T₂).mul_mem (Sec4ActsTriv.conj_mem hg (hh y hy)) (hg y hy)
  one_mem' := fun y _ => by
    simp [commutatorElement_def]
  inv_mem' {g} hg := fun y hy => by
    have e : ⁅g⁻¹, y⁆ = g⁻¹ * ⁅g, y⁆⁻¹ * g := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hginv := (Subgroup.normalizer (sec4N T T₁ T₂ : Set G)).inv_mem
      (Sec4ActsTriv.mem_normalizer hg)
    have := (Subgroup.mem_normalizer_iff.1 hginv _).1
      ((sec4N T T₁ T₂).inv_mem (hg y hy))
    simpa using this

theorem mem_sec4Ker : w ∈ sec4Ker T T₁ T₂ ↔ Sec4ActsTriv T T₁ T₂ w := Iff.rfl

theorem Sec4Hyp.sec4N_le_sec4Ker (h : Sec4Hyp T T₁ a T₂) :
    sec4N T T₁ T₂ ≤ sec4Ker T T₁ T₂ := fun m hm y hy => by
  have e : ⁅m, y⁆ = m * (y * m⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (sec4N T T₁ T₂).mul_mem hm
    ((Subgroup.mem_normalizer_iff.1 (h.sec4Y_le_normalizer hy) _).1 ((sec4N T T₁ T₂).inv_mem hm))

theorem Sec4Hyp.conj_mem_sec4Ker (h : Sec4Hyp T T₁ a T₂) {g y : G}
    (hg : g ∈ sec4Ker T T₁ T₂) (hy : y ∈ sec4Y T T₁ T₂) : y * g * y⁻¹ ∈ sec4Ker T T₁ T₂ :=
  fun y' hy' => by
    have hy'' : y⁻¹ * y' * y ∈ sec4Y T T₁ T₂ :=
      (sec4Y T T₁ T₂).mul_mem ((sec4Y T T₁ T₂).mul_mem ((sec4Y T T₁ T₂).inv_mem hy) hy') hy
    have e : ⁅y * g * y⁻¹, y'⁆ = y * ⁅g, y⁻¹ * y' * y⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (h.sec4Y_le_normalizer hy) _).1 (hg _ hy'')

theorem Sec4Hyp.inf_sec4Ker_eq (h : Sec4Hyp T T₁ a T₂) :
    T ⊓ sec4Ker T T₁ T₂ = normIn T T₁ := by
  have := h.normal_sec4N
  apply le_antisymm
  · rintro t ⟨htT, htK⟩
    have hTZ := h.img_inf_center_eq_bot_of_le (K := sec4Y T T₁ T₂) le_rfl
      h.sec4Y_le_normalizer left_le_sec4Y
    obtain ⟨t', ht'⟩ : ∃ t' : ↥(sec4Y T T₁ T₂), (t' : G) = t :=
      ⟨⟨t, left_le_sec4Y htT⟩, rfl⟩
    have hz : (QuotientGroup.mk t' : ↥(sec4Y T T₁ T₂) ⧸
        (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ∈
        (T.subgroupOf (sec4Y T T₁ T₂)).map
          (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) ⊓
          Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) := by
      refine ⟨⟨t', Subgroup.mem_subgroupOf.2 (ht' ▸ htT), rfl⟩,
        Subgroup.mem_center_iff.2 fun g => ?_⟩
      induction g using QuotientGroup.induction_on with
      | H y' =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        refine Subgroup.mem_subgroupOf.2 ?_
        have h1 : ⁅t⁻¹, (y' : G)⁻¹⁆ ∈ sec4N T T₁ T₂ :=
          (sec4Ker T T₁ T₂).inv_mem htK _ ((sec4Y T T₁ T₂).inv_mem y'.2)
        have e : (((y' * t')⁻¹ * (t' * y') : ↥(sec4Y T T₁ T₂)) : G) = ⁅t⁻¹, (y' : G)⁻¹⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, ht']
          group
        rw [e]
        exact h1
    rw [hTZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz
    rw [← h.inf_sec4N_eq]
    exact ⟨htT, ht' ▸ Subgroup.mem_subgroupOf.1 hz⟩
  · intro l hl
    exact ⟨normIn_le _ _ hl, h.sec4N_le_sec4Ker (normIn_le_sec4N_left hl)⟩

end CFSG.CGT.Timmesfeld75
