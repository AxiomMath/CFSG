module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs

public section

open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open Equiv Equiv.Perm

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Alt

theorem eq_top_of_isPreprimitive_of_isThreeCycle_mem {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (alternatingGroup α)) [hG' : MulAction.IsPreprimitive G α]
    {c : alternatingGroup α} (hc : (c : Perm α).IsThreeCycle) (hcG : c ∈ G) : G = ⊤ := by
  rw [eq_top_iff, ← Subgroup.map_subtype_le_map_subtype, Subgroup.map_top, Subgroup.range_subtype]
  apply Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem (g := (c : Perm α)) _ hc
  · exact ⟨c, hcG, rfl⟩
  · let φ := (alternatingGroup α).subtype.subgroupMap G
    let f : α →ₑ[φ] α := { toFun := id, map_smul' _ _ := rfl }
    rwa [← MulAction.isPreprimitive_congr (f := f)
      ((alternatingGroup α).subtype.subgroupMap_surjective G) Function.bijective_id]

theorem exists_three_fixed {V₄ : Subgroup ↥(alternatingGroup (Fin 7))} (hV₄ : IsRootFour V₄) :
    ∃ x y z : Fin 7, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      ∀ i : Fin 7, (∀ v ∈ V₄, (v : Perm (Fin 7)) i = i) ↔ (i = x ∨ i = y ∨ i = z) := by
  classical
  have h4 := hV₄.2.2
  have h1 : (Finset.univ.filter fun i : Fin 7 => ¬ ∀ v ∈ V₄, (v : Perm (Fin 7)) i = i).card = 4 := by
    rw [← h4, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
    (fun i : Fin 7 => ∀ v ∈ V₄, (v : Perm (Fin 7)) i = i)
  have h3 : (Finset.univ.filter fun i : Fin 7 => ∀ v ∈ V₄, (v : Perm (Fin 7)) i = i).card = 3 := by
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨x, y, z, hxy, hxz, hyz, hF⟩ := Finset.card_eq_three.1 h3
  refine ⟨x, y, z, hxy, hxz, hyz, fun i => ?_⟩
  have := congrArg (fun F : Finset (Fin 7) => i ∈ F) hF
  simpa using this

theorem a7_gen_A5_aux {V₄ : Subgroup ↥(alternatingGroup (Fin 7))} (hV₄ : IsRootFour V₄) :
    ∃ B : Subgroup ↥(alternatingGroup (Fin 7)), V₄ ≤ B ∧
      Nonempty (↥B ≃* ↥(alternatingGroup (Fin 5))) ∧
      ∀ H : Subgroup ↥(alternatingGroup (Fin 7)), B ≤ H →
        Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))) ≤ H → H = ⊤ := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hfix⟩ := exists_three_fixed hV₄
  set s : Finset (Fin 7) := ({y, z} : Finset (Fin 7))ᶜ with hs
  have hscard : s.card = 5 := by
    rw [hs, Finset.card_compl, Finset.card_pair hyz]
    simp
  have hmems : ∀ i, i ∈ s ↔ i ≠ y ∧ i ≠ z := by
    intro i; simp [hs]
  refine ⟨(alternatingGroup.ofSubtype s).range, ?_, ?_, ?_⟩
  · intro v hv
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    intro i hi
    rw [Equiv.Perm.mem_support] at hi
    rw [hmems]
    refine ⟨fun hiy => hi ?_, fun hiz => hi ?_⟩
    · subst hiy; exact (hfix _).2 (Or.inr (Or.inl rfl)) v hv
    · subst hiz; exact (hfix _).2 (Or.inr (Or.inr rfl)) v hv
  · let e5 : ↥s ≃ Fin 5 := s.equivFinOfCardEq hscard
    exact ⟨(MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm.trans
      (Equiv.altCongrHom e5)⟩
  · intro H hBH hNH
    have h3 : (swap x y * swap x z : Perm (Fin 7)).IsThreeCycle :=
      isThreeCycle_swap_mul_swap_same hxy hxz hyz
    let c : ↥(alternatingGroup (Fin 7)) := ⟨swap x y * swap x z, h3.mem_alternatingGroup⟩
    have hcomm : ∀ u ∈ V₄, c * u * c⁻¹ = u := by
      intro u hu
      have hd : Disjoint (swap x y * swap x z : Perm (Fin 7)) (u : Perm (Fin 7)) := by
        intro a
        by_cases ha : a = x ∨ a = y ∨ a = z
        · right; exact (hfix a).2 ha u hu
        · left
          push_neg at ha
          rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha.1 ha.2.2, swap_apply_of_ne_of_ne ha.1 ha.2.1]
      have h1 : c * u = u * c := Subtype.ext hd.commute.eq
      rw [h1, mul_inv_cancel_right]
    have hcN : c ∈ Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro v
      constructor
      · intro hv; rw [hcomm v hv]; exact hv
      · intro hv
        have h2 := hcomm _ hv
        have h4 : c⁻¹ * (c * v * c⁻¹) * c = v := by group
        have h5 : c⁻¹ * (c * v * c⁻¹) * c = c * v * c⁻¹ := by
          have := congrArg (fun w => c⁻¹ * w * c) h2
          simpa [mul_assoc] using this.symm
        rw [← h4, h5]
        exact hv
    have hcH : c ∈ H := hNH hcN
    have hcx : (c : Perm (Fin 7)) x = z := by
      show (swap x y * swap x z) x = z
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hxz.symm hyz.symm]
    have hcz : (c : Perm (Fin 7)) z = y := by
      show (swap x y * swap x z) z = y
      rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
    have hxorb : ∀ a : Fin 7, ∃ g : ↥(alternatingGroup (Fin 7)), g ∈ H ∧ (g : Perm (Fin 7)) x = a := by
      intro a
      by_cases hax : a = x
      · exact ⟨1, H.one_mem, by simp [hax]⟩
      by_cases haz : a = z
      · exact ⟨c, hcH, by rw [hcx, haz]⟩
      by_cases hay : a = y
      · refine ⟨c * c, H.mul_mem hcH hcH, ?_⟩
        show (c : Perm (Fin 7)) ((c : Perm (Fin 7)) x) = a
        rw [hcx, hcz, hay]
      have has : a ∈ s := (hmems a).2 ⟨hay, haz⟩
      have hxs : x ∈ s := (hmems x).2 ⟨hxy, hxz⟩
      obtain ⟨p, hps, hpxa⟩ : ∃ p ∈ s, p ∉ ({x, a} : Finset (Fin 7)) := by
        apply Finset.exists_mem_notMem_of_card_lt_card
        calc ({x, a} : Finset (Fin 7)).card ≤ 2 := Finset.card_le_two
          _ < s.card := by rw [hscard]; norm_num
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpxa
      obtain ⟨hpx, hpa⟩ := hpxa
      have h3' : (swap x p * swap x a : Perm (Fin 7)).IsThreeCycle :=
        isThreeCycle_swap_mul_swap_same (Ne.symm hpx) (Ne.symm hax) hpa
      let g : ↥(alternatingGroup (Fin 7)) := ⟨swap x p * swap x a, h3'.mem_alternatingGroup⟩
      have hgB : g ∈ (alternatingGroup.ofSubtype s).range := by
        rw [alternatingGroup.mem_range_ofSubtype_iff]
        intro i hi
        by_contra hi'
        rw [Equiv.Perm.mem_support] at hi
        apply hi
        have hix : i ≠ x := fun h' => hi' (h' ▸ hxs)
        have hip : i ≠ p := fun h' => hi' (h' ▸ hps)
        have hia : i ≠ a := fun h' => hi' (h' ▸ has)
        show (swap x p * swap x a) i = i
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hix hia, swap_apply_of_ne_of_ne hix hip]
      refine ⟨g, hBH hgB, ?_⟩
      show (swap x p * swap x a) x = a
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hax (fun h => hpa h.symm)]
    haveI : MulAction.IsPretransitive H (Fin 7) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨g₁, hg₁, hg₁x⟩ := hxorb a
      obtain ⟨g₂, hg₂, hg₂x⟩ := hxorb b
      refine ⟨⟨g₂ * g₁⁻¹, H.mul_mem hg₂ (H.inv_mem hg₁)⟩, ?_⟩
      have e1 : g₁ • x = a := hg₁x
      have e2 : g₂ • x = b := hg₂x
      show (g₂ * g₁⁻¹) • a = b
      rw [mul_smul, inv_smul_eq_iff.2 e1.symm, e2]
    haveI : MulAction.IsPreprimitive H (Fin 7) :=
      MulAction.IsPreprimitive.of_prime_card
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact eq_top_of_isPreprimitive_of_isThreeCycle_mem H h3 hcH
end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Alt

