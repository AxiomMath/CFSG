module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN2a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndCtx

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

section Cent

variable (h : Hyp6Sec2 G T M L V)

include h in

theorem oTwoUpper_Mz_le_F4 (h6212 : Stmt6_2_12_F4) :
    oTwoUpper (HH T ⊓ M) ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
  (h6212 G T M L V h).1.1

include h in

theorem oTwoUpper_Mz_eq_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h6212 : Stmt6_2_12_F4) :
    oTwoUpper (HH T ⊓ M) = oTwoUpper (M ⊓ Subgroup.centralizer (V : Set G)) := by
  have hle := oTwoUpper_Mz_le_F4 h h6212
  refine le_antisymm ?_ (oTwoUpper_mono (le_inf (M_inf_centralizer_le_HH h hZ) inf_le_left))
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  obtain ⟨a, ha⟩ := exists_pow_mem_oTwoUpper (HH T ⊓ M) hx
  have haC : x ^ 2 ^ a ∈ M ⊓ Subgroup.centralizer (V : Set G) := hle ha
  obtain ⟨b, hb⟩ := exists_pow_mem_oTwoUpper (M ⊓ Subgroup.centralizer (V : Set G)) haC
  exact ⟨a + b, by rw [pow_add, pow_mul]; exact hb⟩

include h in

theorem L_le_normalizer_X_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h6212 : Stmt6_2_12_F4) :
    L ≤ Subgroup.normalizer (oTwoUpper (HH T ⊓ M) : Set G) := by
  rw [oTwoUpper_Mz_eq_F4 h hZ h6212]
  exact (L_le_normalizer_C h).trans (normalizer_le_normalizer_oTwoUpper _)

include h in

theorem V_inf_X_eq_bot_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h6212 : Stmt6_2_12_F4)
    (hnot : ¬ V ≤ oTwoUpper (HH T ⊓ M)) : V ⊓ oTwoUpper (HH T ⊓ M) = ⊥ := by
  have hLX := L_le_normalizer_X_F4 h hZ h6212
  have hLV := h.toHyp611.L_le_normalizer
  have hLW : L ≤ Subgroup.normalizer ((V ⊓ oTwoUpper (HH T ⊓ M) : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.mp (hLV hl) g
    have h2 := Subgroup.mem_normalizer_iff.mp (hLX hl) g
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  rcases h.natural.irreducible _ inf_le_left hLW with h0 | h1
  · exact h0
  · exact absurd (h1 ▸ inf_le_right) hnot

include h in

theorem not_V_le_oTwoUpper_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h6210 : Stmt6_2_10_F4)
    {n : ℕ} (ψ : ↥(HH T) →* Equiv.Perm (Fin n))
    (hswap : ∀ a : ↥(HH T), (a : G) ∈ V → (a : G) ∉ CHU T L V → (ψ a).IsSwap) :
    ¬ V ≤ oTwoUpper (HH T ⊓ M) := by
  obtain ⟨v₀, hv₀V, hv₀C⟩ : ∃ v₀ ∈ V, v₀ ∉ CHU T L V := by
    by_contra hcon
    push Not at hcon
    exact not_V_le_CHU_F4 h h6210 fun v hv => hcon v hv
  intro hVX
  have hsign : ∀ x ∈ oTwoUpper (HH T ⊓ M), ∃ hx : x ∈ HH T,
      Equiv.Perm.sign (ψ ⟨x, hx⟩) = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hxH : x ∈ HH T := (Subgroup.mem_inf.mp hx.1).1
      refine ⟨hxH, ?_⟩
      have h1 : (⟨x, hxH⟩ : ↥(HH T)) ^ orderOf x = 1 := Subtype.ext (by simp)
      have h2 : Equiv.Perm.sign (ψ ⟨x, hxH⟩) ^ orderOf x = 1 := by
        rw [← map_pow, ← map_pow, h1, map_one, map_one]
      rwa [Int.units_pow_eq_pow_mod_two, Nat.odd_iff.mp hx.2, pow_one] at h2
    | one =>
      refine ⟨Subgroup.one_mem _, ?_⟩
      have : (⟨1, Subgroup.one_mem _⟩ : ↥(HH T)) = 1 := rfl
      rw [this, map_one, map_one]
    | mul x y hx hy ihx ihy =>
      obtain ⟨hx', ihx'⟩ := ihx
      obtain ⟨hy', ihy'⟩ := ihy
      refine ⟨Subgroup.mul_mem _ hx' hy', ?_⟩
      have : (⟨x * y, Subgroup.mul_mem _ hx' hy'⟩ : ↥(HH T)) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
      rw [this, map_mul, map_mul, ihx', ihy', one_mul]
    | inv x hx ihx =>
      obtain ⟨hx', ihx'⟩ := ihx
      refine ⟨Subgroup.inv_mem _ hx', ?_⟩
      have : (⟨x⁻¹, Subgroup.inv_mem _ hx'⟩ : ↥(HH T)) = ⟨x, hx'⟩⁻¹ := rfl
      rw [this, map_inv, map_inv, ihx', inv_one]
  obtain ⟨hv₀H, hs⟩ := hsign v₀ (hVX hv₀V)
  have := (hswap ⟨v₀, hv₀H⟩ hv₀V hv₀C).sign_eq
  rw [this] at hs
  exact absurd hs (by decide)

end Cent

end CFSG.Quasithin.H13.GM22
