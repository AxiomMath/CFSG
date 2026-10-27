module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import CFSG.ClassicalInvolution.Q3.AE.Models

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem memBar_ne_of_disjoint {α β : Finset (Fin n)} {h : α.card = 4}
    {h' : β.card = 4} (hd : Disjoint α β) (b c : Bool) : memBar α h b ≠ memBar β h' c := by
  classical
  intro heq
  obtain ⟨k, hk, hkp⟩ : ∃ k ∈ (bif b then kList else kStarList), k.perm 0 ≠ 0 := by
    cases b
    · exact ⟨⟨vec4 [0, 3], d₁⟩, by decide +kernel, by decide⟩
    · exact ⟨⟨vec4 [0, 2], d₁⟩, by decide +kernel, by decide⟩
  have hmem : mkQ n (embed (emb α h) k) ∈ memBar α h b := by
    refine ⟨_, ?_, rfl⟩
    cases b
    · exact ⟨k, hk, rfl⟩
    · exact ⟨k, hk, rfl⟩
  rw [heq] at hmem
  obtain ⟨a, ha, he⟩ := hmem
  have hsa := supportedOn_of_mem_memAt ha
  have hperm : a.perm = (embed (emb α h) k).perm := by
    rcases mkQ_eq_iff.mp he with h1 | h1
    · rw [inv_mul_eq_one.mp h1]
    · have h2 := congrArg Wr.perm h1
      rw [mul_perm, inv_perm] at h2
      have h3 : a.perm⁻¹ * (embed (emb α h) k).perm = 1 := h2
      rw [inv_mul_eq_one] at h3
      exact h3
  have hx : emb α h 0 ∉ Set.range (emb β h') := by
    rw [range_emb]
    intro hxβ
    have hxα : emb α h 0 ∈ (α : Set (Fin n)) := by
      rw [← range_emb α h]
      exact Set.mem_range_self 0
    exact Finset.disjoint_left.mp hd hxα hxβ
  have hfix := (hsa _ hx).2
  rw [hperm, embed_perm, embedPerm_apply] at hfix
  exact hkp ((emb α h).injective hfix)

theorem zBar_compl (α : Finset (Fin 8)) (h : α.card = 4) (h' : αᶜ.card = 4) :
    zBar α h = zBar αᶜ h' := by
  classical
  rw [zBar, zBar, mkQ_eq_iff]
  right
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [mul_vec, zOf_inv, zOf_perm]
    show (zOf (emb α h)).vec x + (zOf (emb αᶜ h')).vec ((1 : Equiv.Perm (Fin 8)).symm x) = 1
    rw [show (1 : Equiv.Perm (Fin 8)).symm x = x from rfl, zOf_vec_apply, zOf_vec_apply]
    have e1 : x ∈ Set.range (emb α h) ↔ x ∈ α := by rw [range_emb]; rfl
    have e2 : x ∈ Set.range (emb αᶜ h') ↔ x ∈ αᶜ := by rw [range_emb]; rfl
    by_cases hx : x ∈ α
    · have hx' : x ∉ αᶜ := Finset.notMem_compl.mpr hx
      rw [ite_eq_left (e1.mpr hx), ite_eq_right (fun h2 => hx' (e2.mp h2)), add_zero]
    · have hx' : x ∈ αᶜ := Finset.mem_compl.mpr hx
      rw [ite_eq_right (fun h2 => hx (e1.mp h2)), ite_eq_left (e2.mpr hx'), zero_add]
  · rw [mul_perm, inv_perm, zOf_perm, zOf_perm, inv_one, one_mul]
    rfl

theorem affinePlanes_compl : ∀ β ∈ affinePlanes, βᶜ ∈ affinePlanes := by decide +kernel

theorem affinePlanes_eq_compl_of_disjoint : ∀ β ∈ affinePlanes, ∀ β' ∈ affinePlanes,
    Disjoint β β' → β' = βᶜ := by
  decide +kernel

theorem e29Sets_compl {α : Finset (Fin 8)} (hα : α ∈ e29Sets) : αᶜ ∈ e29Sets :=
  affinePlanes_compl α hα

theorem e29Sets_eq_compl_of_disjoint {β β' : Finset (Fin 8)} (hβ : β ∈ e29Sets)
    (hβ' : β' ∈ e29Sets) (hd : Disjoint β β') : β' = βᶜ :=
  affinePlanes_eq_compl_of_disjoint β hβ β' hβ' hd

end CFSG.ClassicalInvolution.Q3.AE
