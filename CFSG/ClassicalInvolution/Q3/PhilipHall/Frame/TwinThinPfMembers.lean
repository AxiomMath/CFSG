module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

@[expose] def extIn (β : Finset (Fin n)) (q : Equiv.Perm {x : Fin n // x ∈ β}) (x : Fin n) :
    Fin n :=
  if h : x ∈ β then (q ⟨x, h⟩).1 else x

theorem d_fpf : ∀ d ∈ [d₁, d₂, d₃], (∀ i, d i ≠ i) ∧ d * d = 1 := by decide +kernel

theorem perm_cases_kList : ∀ a ∈ kList, a.perm = 1 ∨ a.perm = d₁ ∨ a.perm = d₂ ∨ a.perm = d₃ := by
  decide +kernel

theorem perm_cases_kStarList :
    ∀ a ∈ kStarList, a.perm = 1 ∨ a.perm = d₁ ∨ a.perm = d₂ ∨ a.perm = d₃ := by decide +kernel

theorem e64_ext_dec : ∀ ℓ ∈ fanoLines, ∀ q : Equiv.Perm {x : Fin 7 // x ∈ ℓᶜ},
    (∀ x, q x ≠ x) → q * q = 1 → ∀ s ∈ fanoLines, s.image (extIn ℓᶜ q) ∈ fanoLines := by
  decide +kernel

theorem e29_ext_dec : ∀ α ∈ affinePlanes, ∀ q : Equiv.Perm {x : Fin 8 // x ∈ α},
    (∀ x, q x ≠ x) → q * q = 1 → ∀ s ∈ affinePlanes, s.image (extIn α q) ∈ affinePlanes := by
  decide +kernel

theorem embedPerm_mem_stab {F : List (Finset (Fin n))} {β : Finset (Fin n)} (h : β.card = 4)
    (hdec : ∀ q : Equiv.Perm {x : Fin n // x ∈ β}, (∀ x, q x ≠ x) → q * q = 1 →
      ∀ s ∈ F, s.image (extIn β q) ∈ F) {d : Equiv.Perm (Fin 4)} (hd : d ∈ [d₁, d₂, d₃]) :
    embedPerm (emb β h) d ∈ stabFamily F := by
  obtain ⟨hfp, hdd⟩ := d_fpf d hd
  set ι := emb β h with hι
  set p := embedPerm ι d with hp
  have hmem : ∀ x, x ∈ β ↔ x ∈ Set.range ι := fun x => by rw [hι, range_emb]; rfl
  have hpβ : ∀ x, p x ∈ β ↔ x ∈ β := by
    intro x
    constructor
    · intro hx
      by_contra hxn
      have : p x = x := embedPerm_of_not_mem ι d (fun hr => hxn ((hmem x).mpr hr))
      exact hxn (this ▸ hx)
    · intro hx
      obtain ⟨i, rfl⟩ := (hmem x).mp hx
      rw [hp, embedPerm_apply]
      exact (hmem _).mpr (Set.mem_range_self _)
  set q := p.subtypePerm (p := fun y => y ∈ β) hpβ with hq
  have hpp : p * p = 1 := by
    rw [hp, ← embedPerm_mul, hdd, embedPerm_one]
  have hext : ∀ x, extIn β q x = p x := by
    intro x
    unfold extIn
    by_cases hx : x ∈ β
    · simp [hx, hq]
    · have := embedPerm_of_not_mem ι d (fun hr => hx ((hmem x).mpr hr))
      simp only [hx, dite_false]
      exact this.symm
  have hq1 : ∀ x, q x ≠ x := by
    intro x hx
    obtain ⟨i, hi⟩ := (hmem x.1).mp x.2
    have h1 : p (ι i) = ι (d i) := embedPerm_apply ι d i
    have h2 : (q x : Fin n) = p x := rfl
    rw [← hi] at h2
    have h3 : (q x : Fin n) = x := congrArg Subtype.val hx
    rw [h2, h1, ← hi] at h3
    exact hfp i (ι.injective h3)
  have hq2 : q * q = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    show p (p x) = x
    have := congrArg (fun r => r x.1) hpp
    exact this
  have hinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
  intro s hs
  have hs' := hdec q hq1 hq2 s hs
  have : s.map p.toEmbedding = s.image (extIn β q) := by
    rw [Finset.map_eq_image]
    congr 1
    exact funext fun x => (hext x).symm
  refine ⟨?_, ?_⟩
  · rw [this]; exact hs'
  · rw [hinv, this]; exact hs'

theorem memBar_le_aeBarOver {F : List (Finset (Fin n))} {β : Finset (Fin n)} (h : β.card = 4)
    (hdec : ∀ q : Equiv.Perm {x : Fin n // x ∈ β}, (∀ x, q x ≠ x) → q * q = 1 →
      ∀ s ∈ F, s.image (extIn β q) ∈ F) (b : Bool) :
    memBar β h b ≤ aeBarOver (stabFamily F) := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨k, ?_, rfl⟩
  have hperm : ∀ a : Wr 4, (a.perm = 1 ∨ a.perm = d₁ ∨ a.perm = d₂ ∨ a.perm = d₃) →
      embedPerm (emb β h) a.perm ∈ stabFamily F := by
    intro a ha
    rcases ha with ha | ha | ha | ha
    · rw [ha, embedPerm_one]; exact (stabFamily F).one_mem
    · rw [ha]; exact embedPerm_mem_stab h hdec (by simp)
    · rw [ha]; exact embedPerm_mem_stab h hdec (by simp)
    · rw [ha]; exact embedPerm_mem_stab h hdec (by simp)
  cases b
  · obtain ⟨a, ha, rfl⟩ := hk
    exact ⟨embed_mem_aeSub _ (kStarList_even a ha), by
      show (embed (emb β h) a).perm ∈ stabFamily F
      rw [embed_perm]; exact hperm a (perm_cases_kStarList a ha)⟩
  · obtain ⟨a, ha, rfl⟩ := hk
    exact ⟨embed_mem_aeSub _ (kList_even a ha), by
      show (embed (emb β h) a).perm ∈ stabFamily F
      rw [embed_perm]; exact hperm a (perm_cases_kList a ha)⟩

theorem memBar_le_e64 : ∀ β ∈ e64Sets, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ e64Sub := by
  rintro β ⟨ℓ, hℓ, rfl⟩ hβ b
  exact memBar_le_aeBarOver hβ (e64_ext_dec ℓ hℓ) b

theorem memBar_le_e29 : ∀ β ∈ e29Sets, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ e29Sub := by
  intro β hβ h4 b
  exact memBar_le_aeBarOver h4 (e29_ext_dec β hβ) b

theorem center_e64_eq_bot : Subgroup.center ↥e64Sub = ⊥ := center_e64 memBar_le_e64

theorem center_e29_eq_bot : Subgroup.center ↥e29Sub = ⊥ := center_e29 memBar_le_e29

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
