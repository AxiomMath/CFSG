module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22BlockHom
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Struct

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open MulAction CFSG.Open

section AltStruct

variable {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}

theorem alt2Struct_stab (B₀ : Finset (Fin n)) {m t q : ℕ} (hB : B₀.card = m)
    (hq2 : q * 2 = m.factorial) (hq : 0 < q)
    (Es : List ↥M) (hEs_len : Es.length = 16) (hEs_nd : Es.Nodup)
    (hEs_fix : ∀ e ∈ Es, ∀ x ∈ B₀, e • x = x)
    (hEs_sq : ∀ e ∈ Es, e * e = 1) (hEs_comm : ∀ e ∈ Es, ∀ f ∈ Es, e * f = f * e)
    (hnc : ∃ k ∈ stabilizer ↥M B₀, ∃ e ∈ Es, k * e ≠ e * k)
    (t₀ : Fin t → Fin n) (ht₀ : ∀ i, t₀ i ∈ B₀)
    (hKcard : Nat.card (stabilizer ↥M B₀) = 16 * q)
    (horb : q ≤ Nat.card (orbit ↥(stabilizer ↥M B₀) t₀)) :
    ∃ E₀ : Subgroup ↥M, Alt2Struct (stabilizer ↥M B₀) E₀ m := by
  classical
  set K₀ := stabilizer ↥M B₀ with hK₀
  obtain ⟨φ, hφ⟩ := exists_block_hom (M := M) B₀ hB
  have hEsK : ∀ e ∈ Es, e ∈ K₀ := fun e he => stab_of_fix (hEs_fix e he)
  have hEsker : ∀ e (he : e ∈ Es), (⟨e, hEsK e he⟩ : ↥K₀) ∈ φ.ker := by
    intro e he
    rw [MonoidHom.mem_ker, hφ]
    exact hEs_fix e he
  set E₀ : Subgroup ↥M := φ.ker.map K₀.subtype with hE₀
  have hEsE₀ : ∀ e ∈ Es, e ∈ E₀ := fun e he => ⟨⟨e, hEsK e he⟩, hEsker e he, rfl⟩
  have hcardE₀ : Nat.card E₀ = Nat.card φ.ker :=
    Subgroup.card_map_of_injective K₀.subtype_injective
  have hker_le : Nat.card φ.ker ≤ 16 := by
    have hle : φ.ker ≤ stabilizer ↥K₀ t₀ := by
      intro k hk
      rw [MonoidHom.mem_ker, hφ] at hk
      rw [mem_stabilizer_iff]
      funext i
      exact hk (t₀ i) (ht₀ i)
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_orbit_mul_card_stabilizer (Γ := ↥K₀) t₀
    rw [hKcard] at h2
    have h3 : q * Nat.card (stabilizer ↥K₀ t₀) ≤ q * 16 := by
      calc q * Nat.card (stabilizer ↥K₀ t₀)
          ≤ Nat.card (orbit ↥K₀ t₀) * Nat.card (stabilizer ↥K₀ t₀) :=
            Nat.mul_le_mul_right _ horb
        _ = 16 * q := h2
        _ = q * 16 := mul_comm _ _
    exact h1.trans (Nat.le_of_mul_le_mul_left h3 hq)
  have hsub : {x | x ∈ Es} ⊆ (E₀ : Set ↥M) := fun e he => hEsE₀ e he
  have hEs_card : ({x | x ∈ Es} : Set ↥M).ncard = 16 := by
    rw [← List.coe_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hEs_nd, hEs_len]
  have hE₀_ncard : (E₀ : Set ↥M).ncard = Nat.card E₀ := (Nat.card_coe_set_eq (E₀ : Set ↥M)).symm
  have hker_ge : 16 ≤ Nat.card φ.ker := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hEs_card, hE₀_ncard, hcardE₀] at h1
    exact h1
  have hker16 : Nat.card φ.ker = 16 := le_antisymm hker_le hker_ge
  have hset : (E₀ : Set ↥M) = ↑{x | x ∈ Es} := by
    symm
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [hEs_card, hE₀_ncard, hcardE₀, hker16]
  have hrange : Nat.card φ.range = q := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hker16, hKcard] at h
    omega
  have hindex : φ.range.index = 2 := by
    have h := Subgroup.card_mul_index φ.range
    have hperm : Nat.card (Equiv.Perm (Fin m)) = m.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rw [hperm, hrange, ← hq2] at h
    exact Nat.eq_of_mul_eq_mul_left hq h
  have hrangeAlt : φ.range = alternatingGroup (Fin m) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  have hE₀Es : ∀ x ∈ E₀, x ∈ Es := by
    intro x hx
    have : x ∈ ({x | x ∈ Es} : Set ↥M) := by
      rw [← hset]
      exact hx
    exact this
  refine ⟨E₀, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      exact hEs_comm a (hE₀Es a a.2) b (hE₀Es b b.2)
    · intro x hx
      rw [pow_two]
      exact hEs_sq x (hE₀Es x hx)
  · rw [hcardE₀, hker16]
    norm_num
  · have hmem : ∀ a : alternatingGroup (Fin m), (a : Equiv.Perm (Fin m)) ∈ φ.range := fun a => by
      rw [hrangeAlt]
      exact a.2
    refine ⟨φ.codRestrict (alternatingGroup (Fin m))
      (fun k => by rw [← hrangeAlt]; exact ⟨k, rfl⟩), ?_, ?_⟩
    · intro a
      obtain ⟨k, hk⟩ := hmem a
      exact ⟨k, Subtype.ext hk⟩
    · rw [MonoidHom.ker_codRestrict]
      ext k
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hk
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k', hk', hk'k⟩
        have : k' = k := Subtype.ext hk'k
        rwa [this] at hk'
  · obtain ⟨k, hk, e, he, hne⟩ := hnc
    exact ⟨k, hk, e, hEsE₀ e he, hne⟩

end AltStruct

end CFSG.QuasithinUnique.Vol2Native.L239
