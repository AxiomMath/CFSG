module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5Transport

public section

namespace CFSG.ComponentClassification.FooteLit.FCC

open CFSG Subgroup CFSG.ComponentClassification.Foote5

@[expose] def FCConcl (Y : Type) [Group Y] (β : MulAut Y) (M : Subgroup Y) : Prop :=
  (∀ m ∈ M, β m = m) ∧
    Nat.card ↥(MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id Y)) ≤ 2 * Nat.card M ∧
    (∀ N : Subgroup Y, N ≤ M → (∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) → N ≠ ⊥ →
      ∃ a ∈ N, ∃ b ∈ N, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) ∧
    ∀ α : MulAut Y, (∀ m ∈ M, α m = m) → α = 1 ∨ α = β

variable {Y Y' : Type} [Group Y] [Group Y'] (φ : Y ≃* Y')

theorem map_eqLocus (β : MulAut Y) :
    (MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id Y)).map φ.toMonoidHom =
      MonoidHom.eqLocus (MulAut.congr φ β).toMonoidHom (MonoidHom.id Y') := by
  ext y
  rw [mem_map_equiv]
  show β (φ.symm y) = φ.symm y ↔ MulAut.congr φ β y = y
  rw [Aut5.congr_apply_apply]
  constructor
  · intro h
    rw [h, MulEquiv.apply_symm_apply]
  · intro h
    apply φ.injective
    rw [h, MulEquiv.apply_symm_apply]

theorem FCConcl.map {β : MulAut Y} {M : Subgroup Y} (h : FCConcl Y β M) :
    FCConcl Y' (MulAut.congr φ β) (M.map φ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    show MulAut.congr φ β (φ m) = φ m
    rw [Aut5.congr_apply_apply, MulEquiv.symm_apply_apply, h1 m hm]
  · rw [← map_eqLocus φ, card_map_of_injective φ.injective, card_map_of_injective φ.injective]
    exact h2
  · intro N' hN'M hN'n hN'1
    have hNM : N'.comap φ.toMonoidHom ≤ M := fun x hx => by
      have hx' : φ x ∈ M.map φ.toMonoidHom := hN'M hx
      rwa [mem_map_equiv, MulEquiv.symm_apply_apply] at hx'
    have hNn : ∀ m ∈ M, ∀ x ∈ N'.comap φ.toMonoidHom, m * x * m⁻¹ ∈ N'.comap φ.toMonoidHom :=
      fun m hm x hx => by
        show φ (m * x * m⁻¹) ∈ N'
        rw [map_mul, map_mul, map_inv]
        exact hN'n (φ m) ⟨m, hm, rfl⟩ (φ x) hx
    have hN1 : N'.comap φ.toMonoidHom ≠ ⊥ := by
      intro hbot
      apply hN'1
      rw [eq_bot_iff]
      intro y hy
      have hy' : φ.symm y ∈ N'.comap φ.toMonoidHom := by
        show φ (φ.symm y) ∈ N'
        rwa [MulEquiv.apply_symm_apply]
      rw [hbot, mem_bot] at hy'
      rw [mem_bot, ← MulEquiv.apply_symm_apply φ y, hy', map_one]
    obtain ⟨a, ha, b, hb, haa, hbb, ha1, hb1, hab, hc⟩ := h3 _ hNM hNn hN1
    refine ⟨φ a, ha, φ b, hb, by rw [← map_mul, haa, map_one], by rw [← map_mul, hbb, map_one],
      fun h => ha1 (φ.injective (by rw [h, map_one])),
      fun h => hb1 (φ.injective (by rw [h, map_one])), fun h => hab (φ.injective h), ?_⟩
    rw [← map_mul, ← map_mul, hc]
  · intro α' hα'
    have hα : ∀ m ∈ M, (MulAut.congr φ).symm α' m = m := fun m hm => by
      rw [Aut5.congr_symm_apply_apply, hα' (φ m) ⟨m, hm, rfl⟩, MulEquiv.symm_apply_apply]
    rcases h4 _ hα with h | h
    · left
      rw [← (MulAut.congr φ).apply_symm_apply α', h, map_one]
    · right
      rw [← (MulAut.congr φ).apply_symm_apply α', h]

theorem foote5FCC_of {β : MulAut Y} {M : Subgroup Y} (h : FCConcl Y β M) :
    ∃ M : Subgroup Y, (∀ m ∈ M, β m = m) ∧
      Nat.card ↥(MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id Y)) ≤ 2 * Nat.card M ∧
      (∀ N : Subgroup Y, N ≤ M → (∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) → N ≠ ⊥ →
        ∃ V : Subgroup Y, IsKleinFour V ∧ V ≤ N) ∧
      ∀ α : MulAut Y, (∀ m ∈ M, α m = m) → α = 1 ∨ α = β := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨M, h1, h2, fun N hNM hNn hN1 => ?_, h4⟩
  obtain ⟨a, ha, b, hb, haa, hbb, ha1, hb1, hab, hc⟩ := h3 N hNM hNn hN1
  obtain ⟨V, hVN, hV, -, -⟩ := GorensteinWalter.exists_kleinFour_of_commuting_involutions_le N a b
    ⟨ha1, by rw [sq]; exact haa⟩ ⟨hb1, by rw [sq]; exact hbb⟩ hab hc ha hb
  exact ⟨V, hV, hVN⟩

end CFSG.ComponentClassification.FooteLit.FCC
