module

public import CFSG.LargeExtraspecial.S14W4LocAct
public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup CFSG.LargeExtraspecial.S4

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {π : T.M →* (V ≃ₗ[ZMod 2] V)}

theorem not_isReducible_of_irr
    (hirr : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = ⊤) :
    ¬ T.IsReducible := by
  rintro ⟨W, h0, htop, hW⟩
  rcases hirr W (fun r _ v hv => hW r v hv) with h | h
  · exact h0 h
  · exact htop h

theorem comm_of_π_eq_one (A : Act T R π) {c : T.M} (hc : π c = 1) (r : T.M) (hr : (r : X) ∈ R) :
    T.ρ c * T.ρ r = T.ρ r * T.ρ c := by
  refine comm_of_mem_Q (A.ker_R _ (mul_mem (A.conj_mem c r hr) (inv_mem hr)) ?_)
  simp only [map_mul, map_inv, hc, one_mul, inv_one, mul_one, mul_inv_cancel]

theorem exists_odd_pow_ρ_eq_one (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R)
    {c : T.M} (hc : π c = 1) : ∃ m : ℕ, Odd m ∧ T.ρ c ^ m = 1 := by
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨m, hm, ?_⟩
  have h2 : ∃ n : ℕ, (c ^ m) ^ 2 ^ n = 1 :=
    ⟨a, by rw [← pow_mul, mul_comm, ← ham, pow_orderOf_eq_one]⟩
  have hπm : π (c ^ m) = 1 := by rw [map_pow, hc, one_pow]
  rw [← map_pow]
  exact T.ρ_eq_one_of_mem_Q (mem_Q_of_π_eq_one A hcard hL _ h2 hπm)

theorem map_W₁_eq (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R)
    {W₁ W₂ : Submodule (ZMod 2) T.Qt} (h1 : W4Dict.IsInv T R W₁) (h2 : W4Dict.IsInv T R W₂)
    (h12 : W₁ ⊓ W₂ = ⊥) (hc1 : Nat.card W₁ = 2 ^ 4) (hc2 : Nat.card W₂ = 2 ^ 4)
    (hall : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = W₁ ∨ W = W₂ ∨ W = ⊤)
    {c : T.M} (hc : π c = 1) :
    ∀ v ∈ W₁, ((T.ρ c : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W₁ := by
  have hcomm := comm_of_π_eq_one A hc
  set e := ((T.ρ c : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) with he
  have h16 : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → Nat.card W = 2 ^ 4 →
      W = W₁ ∨ W = W₂ := by
    intro W hW hcW
    rcases hall W hW with h | h | h | h
    · rw [h, card_bot_submodule] at hcW
      norm_num at hcW
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, card_top_submodule, hcard] at hcW
      norm_num at hcW
  have hW₁0 : W₁ ≠ W₂ := by
    intro h
    have h3 : W₁ = ⊥ := by rw [← h12, ← h, inf_idem]
    rw [h3, card_bot_submodule] at hc1
    norm_num at hc1
  rcases h16 _ (map_isInv c hcomm W₁ h1) ((card_map_ρ c W₁).trans hc1) with hm1 | hm1
  · exact fun v hv => hm1.le (Submodule.mem_map_of_mem hv)
  · exfalso
    rcases h16 _ (map_isInv c hcomm W₂ h2) ((card_map_ρ c W₂).trans hc2) with hm2 | hm2
    ·
      have hsq : ∀ v ∈ W₁, ((T.ρ c ^ 2 : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W₁ := by
        intro v hv
        have hv2 : e v ∈ W₂ := hm1.le (Submodule.mem_map_of_mem hv)
        have hv3 : e (e v) ∈ W₁ := hm2.le (Submodule.mem_map_of_mem hv2)
        rw [pow_two]
        exact hv3
      obtain ⟨m, hm, hρm⟩ := exists_odd_pow_ρ_eq_one A hcard hL hc
      obtain ⟨j, rfl⟩ := hm
      have hmem : T.ρ c ∈ zpowers (T.ρ c ^ 2) := by
        refine mem_zpowers_iff.mpr ⟨-(j : ℤ), ?_⟩
        rw [← zpow_natCast, ← zpow_mul]
        have h3 : T.ρ c ^ ((2 * j + 1 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, hρm]
        calc T.ρ c ^ (((2 : ℕ) : ℤ) * -(j : ℤ)) =
            T.ρ c ^ (((2 * j + 1 : ℕ) : ℤ)) * T.ρ c ^ (((2 : ℕ) : ℤ) * -(j : ℤ)) := by
              rw [h3, one_mul]
          _ = T.ρ c := by
            rw [← zpow_add]
            push_cast
            ring_nf
            exact zpow_one _
      have hfix := zpowers_mapsTo (T.ρ c ^ 2) W₁ hsq (T.ρ c) hmem
      have hle : W₁.map e.toLinearMap ≤ W₁ := by
        rintro _ ⟨v, hv, rfl⟩
        exact hfix v hv
      have heq : W₁.map e.toLinearMap = W₁ :=
        Submodule.eq_of_le_of_finrank_eq hle (by
          have := card_map_ρ c W₁
          rw [T.card_submodule, T.card_submodule] at this
          exact Nat.pow_right_injective (le_refl 2) this)
      exact hW₁0 (heq.symm.trans hm1)
    · exact hW₁0 (Submodule.map_injective_of_injective e.injective (hm1.trans hm2.symm))

end CFSG.LargeExtraspecial.S14.W4Loc
