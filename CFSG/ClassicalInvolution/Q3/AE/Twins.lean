module

public import CFSG.ClassicalInvolution.Q3.AE.Bar

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem zQ_comm_kList : ∀ a ∈ kList, zQ * a = a * zQ := by decide +kernel

theorem zQ_comm_kStarList : ∀ a ∈ kStarList, zQ * a = a * zQ := by decide +kernel

theorem kList_not_comm : ∃ a ∈ kList, ∃ b ∈ kList, a * b ≠ b * a := by decide +kernel

theorem kStarList_not_comm : ∃ a ∈ kStarList, ∃ b ∈ kStarList, a * b ≠ b * a := by
  decide +kernel

theorem zBar_mul_self (α : Finset (Fin n)) (h : α.card = 4) : zBar α h * zBar α h = 1 := by
  rw [zBar, ← map_mul, mul_eq_one_iff_eq_inv.mpr (zOf_inv _).symm, map_one]

theorem zOf_comm_memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ a ∈ memAt α h b, zOf (emb α h) * a = a * zOf (emb α h) := by
  cases b
  · rintro _ ⟨a, ha, rfl⟩
    unfold zOf
    rw [← map_mul, ← map_mul, zQ_comm_kStarList a ha]
  · rintro _ ⟨a, ha, rfl⟩
    unfold zOf
    rw [← map_mul, ← map_mul, zQ_comm_kList a ha]

theorem zBar_comm_memBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ x ∈ memBar α h b, zBar α h * x = x * zBar α h := by
  rintro _ ⟨a, ha, rfl⟩
  rw [zBar, ← map_mul, ← map_mul, zOf_comm_memAt α h b a ha]

theorem exists_not_comm_memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ a ∈ memAt α h b, ∃ a' ∈ memAt α h b, a * a' ≠ a' * a := by
  obtain ⟨a, ha, a', ha', hne⟩ : ∃ a ∈ (bif b then kQ else kQStar : Subgroup (Wr 4)),
      ∃ a' ∈ (bif b then kQ else kQStar : Subgroup (Wr 4)), a * a' ≠ a' * a := by
    cases b
    · exact kStarList_not_comm
    · exact kList_not_comm
  refine ⟨embed (emb α h) a, ?_, embed (emb α h) a', ?_, fun he => hne ?_⟩
  · cases b
    · exact ⟨a, ha, rfl⟩
    · exact ⟨a, ha, rfl⟩
  · cases b
    · exact ⟨a', ha', rfl⟩
    · exact ⟨a', ha', rfl⟩
  · rw [← map_mul, ← map_mul] at he
    exact embed_injective _ he

theorem exists_not_comm_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ x ∈ memBar α h b, ∃ x' ∈ memBar α h b, x * x' ≠ x' * x := by
  obtain ⟨a, ha, a', ha', hne⟩ := exists_not_comm_memAt α h b
  refine ⟨mkQ n a, ⟨a, ha, rfl⟩, mkQ n a', ⟨a', ha', rfl⟩, fun he => hne ?_⟩
  exact comm_of_mkQ_comm_of_supportedOn hn (supportedOn_of_mem_memAt ha)
    (supportedOn_of_mem_memAt ha') he

theorem eq_of_zBar_mul_comm (hn8 : n ≠ 8) {α β : Finset (Fin n)} {h : α.card = 4}
    {h' : β.card = 4}
    (hc : ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (c : Bool), ∀ x ∈ memBar γ hγ c,
      (zBar α h * zBar β h') * x = x * (zBar α h * zBar β h')) : α = β := by
  classical
  by_contra hne
  have h1 : ∀ x ∈ memBar α h true, zBar β h' * x = x * zBar β h' := by
    intro x hx
    have e1 : Commute (zBar α h * zBar β h') x := hc α h true x hx
    have e2 : Commute (zBar α h) x := zBar_comm_memBar α h true x hx
    have := e2.inv_left.mul_left e1
    rwa [inv_mul_cancel_left] at this
  have hd : Disjoint β α := disjoint_of_zBar_comm (Ne.symm hne) h1
  have hcard : (β ∪ α).card = 8 := by rw [Finset.card_union_of_disjoint hd, h, h']
  have hle : (β ∪ α).card ≤ n := by
    have := Finset.card_le_univ (β ∪ α)
    rwa [Fintype.card_fin] at this
  have hlt : (β ∪ α).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_union, not_or] at hm
  obtain ⟨a, ha⟩ : α.Nonempty := Finset.card_pos.mp (by omega)
  have hmα : m ∉ α.erase a := fun hm' => hm.2 (Finset.mem_of_mem_erase hm')
  have hγc : (insert m (α.erase a)).card = 4 := by
    rw [Finset.card_insert_of_notMem hmα, Finset.card_erase_of_mem ha, h]
  have hγα : α ≠ insert m (α.erase a) := fun e => hm.2 (e ▸ Finset.mem_insert_self m _)
  have hγβ : Disjoint β (insert m (α.erase a)) := by
    rw [Finset.disjoint_insert_right]
    exact ⟨hm.1, Finset.disjoint_of_subset_right (Finset.erase_subset a α) hd⟩
  have h2 : ∀ x ∈ memBar (insert m (α.erase a)) hγc true, zBar α h * x = x * zBar α h := by
    intro x hx
    have e1 : Commute (zBar α h * zBar β h') x := hc _ hγc true x hx
    have e2 : Commute (zBar β h') x :=
      comm_memBar_of_disjoint hγβ true true _ (zBar_mem_memBar β h' true) x hx
    have := e1.mul_left e2.inv_left
    rwa [mul_inv_cancel_right] at this
  have hd' := disjoint_of_zBar_comm hγα h2
  obtain ⟨a', ha'⟩ : (α.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha, h]
    omega
  exact Finset.disjoint_left.mp hd' (Finset.mem_of_mem_erase ha') (Finset.mem_insert_of_mem ha')

end CFSG.ClassicalInvolution.Q3.AE
