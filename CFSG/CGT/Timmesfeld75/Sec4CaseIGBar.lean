module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIPlus

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

@[expose] def sec4A (T T₁ T₂ : Subgroup G) : Subgroup (NQuot T) :=
  barSub T (sec4R T T₁ T₂)

omit [Finite G] in
theorem sec4A_eq : sec4A T T₁ T₂ = barSub T (sec4N T T₁ T₂) := by
  apply le_antisymm
  · refine barSub_le_of_le_sup sec4N_le_normalizer_left fun u hu _ => ?_
    have hu' : u ∈ T ⊔ sec4N T T₁ T₂ := hu
    rwa [sup_comm] at hu'
  · refine barSub_le_of_le_sup sec4R_le_normalizer_left fun u hu _ => ?_
    exact Subgroup.mem_sup_left (show u ∈ sec4R T T₁ T₂ from Subgroup.mem_sup_right hu)

theorem Sec4Hyp.isElemAbelian_sec4A (h : Sec4Hyp T T₁ a T₂) :
    IsElemAbelian 2 (sec4A T T₁ T₂) := by
  rw [sec4A_eq]
  exact isElemAbelian_barSub h.isElemAbelian_sec4N

theorem exists_eq_barElt_mul_of_mem_sec4A (h : Sec4Hyp T T₁ a T₂) {x : NQuot T}
    (hx : x ∈ sec4A T T₁ T₂) :
    ∃ (a' b' : G) (ha : a' ∈ normIn T₁ T) (hb : b' ∈ normIn T₂ T),
      x = barElt T (mem_normIn.1 ha).2 * barElt T (mem_normIn.1 hb).2 := by
  rw [sec4A_eq] at hx
  obtain ⟨n, hnN, hnmem, rfl⟩ := exists_eq_barElt_of_mem_barSub hx
  have hcomm : ∀ x ∈ sec4N T T₁ T₂, ∀ y ∈ sec4N T T₁ T₂, x * y = y * x := fun x hx y hy =>
    elemAbelian_mul_comm h.isElemAbelian_sec4N hx hy
  obtain ⟨l, hl, a', ha', b', hb', rfl⟩ := exists_mul_mul_of_mem_sup
    (A := normIn T T₁) (B := normIn T₁ T) (C := normIn T₂ T)
    (fun x hx y hy => hcomm x (normIn_le_sec4N_left hx) y (normIn_le_sec4N_mid hy))
    (fun x hx y hy => hcomm x (normIn_le_sec4N_left hx) y (normIn_le_sec4N_right hy))
    (fun x hx y hy => hcomm x (normIn_le_sec4N_mid hx) y (normIn_le_sec4N_right hy)) hnmem
  refine ⟨a', b', ha', hb', ?_⟩
  have hlT : l ∈ T := normIn_le _ _ hl
  have hl1 : barElt T (Subgroup.le_normalizer hlT) = 1 := (barElt_eq_one_iff _).2 hlT
  have e : barElt T hnN = barElt T (Subgroup.le_normalizer hlT) *
      barElt T (mem_normIn.1 ha').2 * barElt T (mem_normIn.1 hb').2 := rfl
  rw [e, hl1, one_mul]

theorem Sec4Hyp.sec4A_stronglyClosed (h : Sec4Hyp T T₁ a T₂) (hP : Sec4PlusHolds T T₁ T₂)
    {S : Subgroup (NQuot T)} (hS : IsPGroup 2 S) (hAS : sec4A T T₁ T₂ ≤ S)
    {x : NQuot T} (hx : x ∈ sec4A T T₁ T₂) (g : NQuot T) (hg : g⁻¹ * x * g ∈ S) :
    g⁻¹ * x * g ∈ sec4A T T₁ T₂ := by
  have hTP : IsPGroup 2 T := isPGroup_two_of_isElemAbelian h.pair.wc.1
  obtain ⟨a', b', ha', hb', rfl⟩ := exists_eq_barElt_mul_of_mem_sec4A h hx
  obtain ⟨gg, rfl⟩ := QuotientGroup.mk_surjective g
  have hgg : (gg : G) ∈ Subgroup.normalizer (T : Set G) := gg.2
  have hab : a' * b' ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem (mem_normIn.1 ha').2 (mem_normIn.1 hb').2
  have hz : (gg : G)⁻¹ * (a' * b') * (gg : G) ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem ((Subgroup.normalizer (T : Set G)).inv_mem hgg)
        hab) hgg
  have hzbar : barElt T hz = (QuotientGroup.mk gg : NQuot T)⁻¹ *
      (barElt T (mem_normIn.1 ha').2 * barElt T (mem_normIn.1 hb').2) *
        (QuotientGroup.mk gg : NQuot T) := rfl
  have hzS : barElt T hz ∈ S := hzbar ▸ hg
  have hzF : (gg : G)⁻¹ * (a' * b') * (gg : G) ∈ sec4F T T₁ T₂ :=
    ⟨(gg : G)⁻¹, (Subgroup.normalizer (T : Set G)).inv_mem hgg, a', ha', b', hb', by simp⟩
  have hRS : sec4R T T₁ T₂ ≤ preBar T S :=
    (le_preBar_barSub sec4R_le_normalizer_left).trans (preBar_mono hAS)
  have hzR := hP (preBar T S) (isPGroup_preBar hTP hS) hRS (preBar_le_normalizer S) _
    ⟨mem_preBar.2 ⟨hz, hzS⟩, hzF⟩
  rw [← hzbar]
  exact barElt_mem_barSub hz hzR

theorem Sec4Hyp.conjSubgroup_normIn_eq (h : Sec4Hyp T T₁ a T₂) {g : G}
    (hgT : g ∈ Subgroup.normalizer (T : Set G))
    (hgR : g ∈ Subgroup.normalizer (sec4R T T₁ T₂ : Set G)) :
    conjSubgroup g (normIn T T₁) = normIn T T₁ := by
  have hgN := h.mem_normalizer_sec4N hgR hgT
  have h1 := conjSubgroup_inf g T (sec4N T T₁ T₂)
  rw [h.inf_sec4N_eq, mem_normalizer_iff_conjSubgroup_eq.1 hgT,
    mem_normalizer_iff_conjSubgroup_eq.1 hgN, h.inf_sec4N_eq] at h1
  exact h1

end CFSG.CGT.Timmesfeld75
