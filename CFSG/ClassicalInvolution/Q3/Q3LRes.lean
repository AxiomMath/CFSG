module

public import CFSG.ClassicalInvolution.Q3.Q3LTrick
public import CFSG.ClassicalInvolution.Q3.Q3MOdd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped commutatorElement

theorem le_sup_centralizer_of_sup_ne_top (hM : M11Facts) {Y : Type} [Group Y] [Finite Y]
    (hBelow : CIT3Below (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥) {z : Y}
    {L : Subgroup Y} (hz : IsClassicalMember3 L z) {T : Subgroup Y} (hT : IsComponentOf T ⊤)
    (hTL : T ⊔ L ≠ ⊤) : L ≤ T ⊔ Subgroup.centralizer (T : Set Y) := by
  by_cases hLc : L ≤ Subgroup.centralizer (T : Set Y)
  · exact le_sup_of_le_right hLc
  set Y₁ : Subgroup Y := T ⊔ L with hY₁
  have hTY : T ≤ Y₁ := le_sup_left
  have hLY : L ≤ Y₁ := le_sup_right
  have hcard : Nat.card Y₁ < Nat.card Y :=
    lt_of_le_of_ne (Subgroup.card_le_card_group Y₁)
      (fun h => hTL ((Subgroup.card_eq_iff_eq_top Y₁).mp h))
  set TG : Subgroup Y₁ := T.subgroupOf Y₁ with hTG
  set LG : Subgroup Y₁ := L.subgroupOf Y₁ with hLG
  have hzG : IsClassicalMember3 LG ⟨z, hLY hz.mem⟩ := hz.subgroupOf hLY
  have hTGc : IsComponentOf TG ⊤ := LocalComponents.of_overgroup hT hTY
  have hsupG : TG ⊔ LG = ⊤ := by
    apply Subgroup.map_injective Y₁.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTY,
      Subgroup.map_subgroupOf_eq_of_le hLY, Subgroup.map_top, Subgroup.range_subtype]
  have hTL' : ¬ ⁅TG, LG⁆ = ⊥ := by
    intro h
    apply hLc
    have h1 := congrArg (Subgroup.map Y₁.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTY,
      Subgroup.map_subgroupOf_eq_of_le hLY, Subgroup.map_bot] at h1
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h1
  set N : Subgroup Y₁ := Subgroup.normalClosure (LG : Set Y₁) with hN
  have hNtop : N = ⊤ := by
    rcases LocalComponents.normal_contains_or_commutes TG N hTGc with h | h
    · rw [eq_top_iff, ← hsupG]
      exact sup_le h (fun x hx => Subgroup.subset_normalClosure hx)
    · exact absurd (le_bot_iff.mp ((Subgroup.commutator_mono (le_refl TG)
        (fun x hx => Subgroup.subset_normalClosure hx)).trans h.le)) hTL'
  set Λ : Set (Subgroup Y₁) := Set.range (fun g : Y₁ => conjSub g LG) with hΛdef
  have hΛ : InClass3 Λ :=
    { nonempty := ⟨LG, 1, conjSub_one LG⟩
      conjInvariant := by
        rintro n K ⟨g, rfl⟩
        exact ⟨n * g, conjSub_mul n g LG⟩
      generated := by
        rw [eq_top_iff, ← hNtop]
        change Subgroup.closure (Group.conjugatesOfSet (LG : Set Y₁)) ≤ _
        refine (Subgroup.closure_le _).mpr fun x hx => ?_
        obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
        obtain ⟨c, hc⟩ := isConj_iff.mp hconj
        have hxK : x ∈ conjSub c LG := by
          rw [← hc]
          exact conj_mem_conjSub ha
        exact (le_iSup₂ (f := fun (K : Subgroup Y₁) (_ : K ∈ Λ) => K) (conjSub c LG)
          ⟨c, rfl⟩) hxK
      classical := by
        rintro _ ⟨g, rfl⟩
        exact ⟨_, hzG.conj g⟩ }
  have hLie : LieSystemMod3 Λ := hBelow Y₁ hcard Λ hΛ
  have hTO : TG ⊓ classicalInvolutionOddCore Y₁ = ⊥ := by
    set O₁ : Subgroup Y := (classicalInvolutionOddCore Y₁).map Y₁.subtype with hO₁
    have hnormT : ((T ⊓ O₁).subgroupOf T).Normal := by
      refine ⟨fun x hx t => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxT, y, hy, hyx⟩ := hx
      refine ⟨T.mul_mem (T.mul_mem t.2 hxT) (T.inv_mem t.2), ?_⟩
      refine ⟨⟨t, hTY t.2⟩ * y * ⟨t, hTY t.2⟩⁻¹, ?_, ?_⟩
      · exact (inferInstance : (classicalInvolutionOddCore Y₁).Normal).conj_mem y hy _
      · simpa using hyx
    have hsub : IsSubnormal (T ⊓ O₁) ⊤ :=
      isSubnormal_trans (isSubnormal_of_normal_subgroupOf inf_le_left hnormT) hT.2.1
    have hodd : Odd (Nat.card (T ⊓ O₁ : Subgroup Y)) := by
      have h1 : Odd (Nat.card O₁) := by
        rw [hO₁, Subgroup.card_map_of_injective Y₁.subtype_injective]
        exact CFSG.ComponentClassification.OddCore.odd_card Y₁
      exact h1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hbot : T ⊓ O₁ = ⊥ := M.eq_bot_of_isSubnormal_odd hO hsub hodd
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxT : (x : Y) ∈ T := hx.1
    have hxO : (x : Y) ∈ O₁ := ⟨x, hx.2, rfl⟩
    have : (x : Y) ∈ T ⊓ O₁ := ⟨hxT, hxO⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hLGΛ : LG ∈ Λ := ⟨1, conjSub_one LG⟩
  have hres := le_sup_centralizer_of_lieSystemMod3 hM hLie hLGΛ hTGc hTO
  have h2 := Subgroup.map_mono (f := Y₁.subtype) hres
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLY,
    Subgroup.map_subgroupOf_eq_of_le hTY] at h2
  refine h2.trans (sup_le_sup_left ?_ _)
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have := Subgroup.mem_centralizer_iff.mp hc ⟨t, hTY ht⟩ ht
  exact congrArg Subtype.val this

end CFSG.ClassicalInvolution.Q3
