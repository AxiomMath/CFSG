module

public import CFSG.ClassicalInvolution.Q3.AE.E64

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

open CFSG.ClassicalInvolution.Q3.AE

variable {m : ℕ}

@[expose] def Adj4 (α β : Finset (Fin m)) : Prop :=
  (α ∩ β).card = 2 ∨ Disjoint α β

theorem inter_union_eq {α A B : Finset (Fin m)} (hA : A ⊆ α) (hB : Disjoint B α) :
    α ∩ (A ∪ B) = A := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hx, hxA | hxB⟩
    · exact hxA
    · exact absurd hx (Finset.disjoint_left.mp hB hxB)
  · intro hx
    exact ⟨hA hx, Or.inl hx⟩

theorem exists_mid (hm : 6 ≤ m) {α β : Finset (Fin m)} (hα : α.card = 4) (hβ : β.card = 4) :
    ∃ γ : Finset (Fin m), γ.card = 4 ∧ (γ = α ∨ Adj4 α γ) ∧ (γ = β ∨ Adj4 γ β) := by
  classical
  have hsd : (α \ β).card + (α ∩ β).card = 4 := by rw [Finset.card_sdiff_add_card_inter, hα]
  have hsd' : (β \ α).card + (α ∩ β).card = 4 := by
    rw [Finset.inter_comm, Finset.card_sdiff_add_card_inter, hβ]
  have hle : (α ∩ β).card ≤ 4 := by omega
  interval_cases hk : (α ∩ β).card
  ·
    exact ⟨β, hβ, Or.inr (Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.card_eq_zero.mp hk))), Or.inl rfl⟩
  ·
    obtain ⟨A, hAs, hA2⟩ := Finset.exists_subset_card_eq (show 2 ≤ (α \ β).card by omega)
    obtain ⟨B, hBs, hB2⟩ := Finset.exists_subset_card_eq (show 2 ≤ (β \ α).card by omega)
    have hAα : A ⊆ α := hAs.trans Finset.sdiff_subset
    have hBβ : B ⊆ β := hBs.trans Finset.sdiff_subset
    have hAβ : Disjoint A β := Finset.disjoint_of_subset_left hAs Finset.sdiff_disjoint
    have hBα : Disjoint B α := Finset.disjoint_of_subset_left hBs Finset.sdiff_disjoint
    have hAB : Disjoint A B := Finset.disjoint_of_subset_right hBβ hAβ
    refine ⟨A ∪ B, by rw [Finset.card_union_of_disjoint hAB, hA2, hB2], Or.inr (Or.inl ?_),
      Or.inr (Or.inl ?_)⟩
    · rw [inter_union_eq hAα hBα, hA2]
    · rw [Finset.inter_comm, Finset.union_comm, inter_union_eq hBβ hAβ, hB2]
  ·
    exact ⟨β, hβ, Or.inr (Or.inl hk), Or.inl rfl⟩
  ·
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (show (α \ β).card = 1 by omega)
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (show (β \ α).card = 1 by omega)
    obtain ⟨s, hs⟩ : (α ∩ β).Nonempty := Finset.card_pos.mp (by omega)
    have ha' : a ∈ α \ β := by rw [ha]; exact Finset.mem_singleton_self a
    have hb' : b ∈ β \ α := by rw [hb]; exact Finset.mem_singleton_self b
    obtain ⟨haα, haβ⟩ := Finset.mem_sdiff.mp ha'
    obtain ⟨hbβ, hbα⟩ := Finset.mem_sdiff.mp hb'
    obtain ⟨hsα, hsβ⟩ := Finset.mem_inter.mp hs
    have hcard : (α ∪ β).card < (Finset.univ : Finset (Fin m)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_union_add_card_inter α β
      omega
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hcα : c ∉ α := fun h => hc (Finset.mem_union_left _ h)
    have hcβ : c ∉ β := fun h => hc (Finset.mem_union_right _ h)
    have hsa : s ≠ a := fun h => haβ (h ▸ hsβ)
    have hsb : s ≠ b := fun h => hbα (h ▸ hsα)
    have hbc : b ≠ c := fun h => hcβ (h ▸ hbβ)
    have hA : ({s, a} : Finset (Fin m)) ⊆ α := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hB : Disjoint ({b, c} : Finset (Fin m)) α := by
      rw [Finset.disjoint_left]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hA' : ({s, b} : Finset (Fin m)) ⊆ β := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hB' : Disjoint ({a, c} : Finset (Fin m)) β := by
      rw [Finset.disjoint_left]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have heq : ({s, a} ∪ {b, c} : Finset (Fin m)) = {s, b} ∪ {a, c} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    refine ⟨{s, a} ∪ {b, c}, ?_, Or.inr (Or.inl ?_), Or.inr (Or.inl ?_)⟩
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left hA hB.symm),
        Finset.card_pair hsa, Finset.card_pair hbc]
    · rw [inter_union_eq hA hB, Finset.card_pair hsa]
    · rw [heq, Finset.inter_comm, inter_union_eq hA' hB', Finset.card_pair hsb]
  ·
    have h1 : α ∩ β = α :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hk, hα])
    have h2 : α = β := Finset.eq_of_subset_of_card_le (h1 ▸ Finset.inter_subset_right)
      (by rw [hα, hβ])
    exact ⟨α, hα, Or.inl rfl, Or.inl h2⟩

theorem fanoLines_compl_inter_card : ∀ ℓ ∈ fanoLines, ∀ ℓ' ∈ fanoLines, ℓ ≠ ℓ' →
    (ℓᶜ ∩ ℓ'ᶜ).card = 2 := by
  decide +kernel

theorem adj4_of_mem_e64Sets {α β : Finset (Fin 7)} (hα : α ∈ e64Sets) (hβ : β ∈ e64Sets)
    (hne : α ≠ β) : Adj4 α β := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  obtain ⟨ℓ', hℓ', rfl⟩ := hβ
  exact Or.inl (fanoLines_compl_inter_card ℓ hℓ ℓ' hℓ' fun h => hne (by rw [h]))

theorem card_of_mem_e64Sets {α : Finset (Fin 7)} (hα : α ∈ e64Sets) : α.card = 4 := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  exact fanoLines_compl_card ℓ hℓ

theorem affinePlanes_inter : ∀ α ∈ affinePlanes, ∀ β ∈ affinePlanes, α ≠ β →
    (α ∩ β).card = 2 ∨ α ∩ β = ∅ := by
  decide +kernel

theorem affinePlanes_card : ∀ α ∈ affinePlanes, α.card = 4 := by
  decide +kernel

theorem adj4_of_mem_e29Sets {α β : Finset (Fin 8)} (hα : α ∈ e29Sets) (hβ : β ∈ e29Sets)
    (hne : α ≠ β) : Adj4 α β := by
  rcases affinePlanes_inter α hα β hβ hne with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr h)

theorem card_of_mem_e29Sets {α : Finset (Fin 8)} (hα : α ∈ e29Sets) : α.card = 4 :=
  affinePlanes_card α hα

end CFSG.ClassicalInvolution.Q3.TL4.SecIdE2
