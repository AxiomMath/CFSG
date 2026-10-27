module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sec
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

universe u v w

theorem exists_index_le_of_perm_action {Y : Type w} [Group Y] [Nontrivial Y] :
    ∀ (n : ℕ) {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α = n →
      ∀ {U : Type v} [Group U] (ψ : U →* Equiv.Perm α), Function.Injective ψ →
        ∀ (φ : U →* Y), Function.Surjective φ → ∃ H : Subgroup Y, H ≠ ⊤ ∧ H.index ≤ n := by
  intro n
  induction n with
  | zero =>
    intro α _ _ hcard U _ ψ hψ φ hφ
    exfalso
    have hα : IsEmpty α := Fintype.card_eq_zero_iff.mp hcard
    have hsub : Subsingleton U := by
      refine ⟨fun a b => hψ ?_⟩
      ext x
      exact (IsEmpty.false x).elim
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨u, rfl⟩ := hφ y
    exact hy (by rw [Subsingleton.elim u 1, map_one])
  | succ m ih =>
    intro α _ _ hcard U _ ψ hψ φ hφ
    have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨ω⟩ := hne
    have hUfin : Finite U := Finite.of_injective ψ hψ
    let Uω : Subgroup U := (MulAction.stabilizer (Equiv.Perm α) ω).comap ψ
    have hmem : ∀ u : U, u ∈ Uω ↔ ψ u ω = ω := fun u => by
      simp [Uω, MulAction.mem_stabilizer_iff]
    by_cases hr : Uω.map φ = ⊤
    ·
      let ρ : ↥Uω →* Equiv.Perm {x : α // x ≠ ω} :=
        { toFun := fun u => (ψ u.1).subtypePerm (fun x => by
            show ψ u.1 x ≠ ω ↔ x ≠ ω
            have h1 : ψ u.1 ω = ω := (hmem u.1).mp u.2
            constructor
            · intro hx hxω
              apply hx
              rw [hxω, h1]
            · intro hx hy
              apply hx
              apply (ψ u.1).injective
              rw [hy, h1])
          map_one' := by
            apply Equiv.ext
            intro x
            apply Subtype.ext
            show (ψ ((1 : ↥Uω) : U)) (x : α) = (x : α)
            rw [Subgroup.coe_one, map_one]
            rfl
          map_mul' := fun a b => by
            apply Equiv.ext
            intro x
            apply Subtype.ext
            show (ψ ((a * b : ↥Uω) : U)) (x : α) = (ψ (a : U)) ((ψ (b : U)) (x : α))
            rw [Subgroup.coe_mul, map_mul]
            rfl }
      have hρ : Function.Injective ρ := by
        intro a b hab
        apply Subtype.ext
        apply hψ
        ext x
        by_cases hx : x = ω
        · subst hx
          rw [(hmem a.1).mp a.2, (hmem b.1).mp b.2]
        · have := congrArg (fun f : Equiv.Perm {x : α // x ≠ ω} => (f ⟨x, hx⟩ : α)) hab
          simpa [ρ, Equiv.Perm.subtypePerm_apply] using this
      have hcardβ : Fintype.card {x : α // x ≠ ω} = m := by
        have h1 := Fintype.card_subtype_compl (fun x : α => x = ω)
        have h2 : Fintype.card {x : α // x = ω} = 1 := Fintype.card_subtype_eq ω
        have h3 : Fintype.card {x : α // ¬ x = ω} = Fintype.card {x : α // x ≠ ω} := rfl
        omega
      have hφ' : Function.Surjective ((φ.comp Uω.subtype)) := by
        intro y
        have hy : y ∈ Uω.map φ := by rw [hr]; trivial
        obtain ⟨u, hu, rfl⟩ := hy
        exact ⟨⟨u, hu⟩, rfl⟩
      obtain ⟨H, hH, hidx⟩ := ih hcardβ ρ hρ (φ.comp Uω.subtype) hφ'
      exact ⟨H, hH, by omega⟩
    · refine ⟨Uω.map φ, hr, ?_⟩
      have h1 : (Uω.map φ).index ∣ Uω.index := Subgroup.index_map_dvd Uω hφ
      have h2 : Uω.index ≤ Fintype.card α := by
        let _ : MulAction U α := MulAction.compHom α ψ
        have hstab : MulAction.stabilizer U ω = Uω := by
          ext u
          rw [MulAction.mem_stabilizer_iff, hmem]
          rfl
        rw [← hstab, MulAction.index_stabilizer]
        have := Nat.card_le_card_of_injective (Subtype.val : MulAction.orbit U ω → α) Subtype.val_injective
        rwa [Nat.card_eq_fintype_card (α := α)] at this
      have hpos : 0 < Uω.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have h3 : (Uω.map φ).index ≤ Uω.index := Nat.le_of_dvd hpos h1
      omega

theorem exists_index_le_of_isSection_perm {Y : Type w} [Group Y] [Nontrivial Y] {α : Type u}
    [Fintype α] [DecidableEq α] (h : IsSection Y (Equiv.Perm α)) :
    ∃ H : Subgroup Y, H ≠ ⊤ ∧ H.index ≤ Fintype.card α := by
  obtain ⟨U, φ, hφ⟩ := h
  exact exists_index_le_of_perm_action (Fintype.card α) rfl U.subtype U.subtype_injective φ hφ

theorem not_isSection_alt_of_index {Y : Type w} [Group Y] [Nontrivial Y] {n : ℕ}
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → n < H.index) :
    ¬ IsSection Y (alternatingGroup (Fin n)) := by
  intro h
  obtain ⟨H, hH, hidx⟩ := exists_index_le_of_isSection_perm
    (IsSection.of_le (alternatingGroup (Fin n)) h)
  have := hmin H hH
  rw [Fintype.card_fin] at hidx
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
