module

public import CFSG.Quasithin.H13.A6S1356S6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1356Two

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem normalizer_R45_not_le_F4 (h1222 : Stmt12_2_2_F4)
    (hS6 : ¬ autOn T V ≤ autOn L V) {g : G} (hg : conjSub g S.V2 = S.W0) :
    ¬ Subgroup.normalizer (S.R45 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro hN
  obtain ⟨t, htT, hρt⟩ := S.exists_T_45 hS6
  have htR : (t : G) ∈ S.R45 := S.mem_R45_of htT (by rw [hρt]; exact Or.inr rfl)
  have hR2 : IsPGroup 2 S.R45 := S.h13.sylow.1.to_le S.R45_le_T

  have hPC : conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G)) ≤
      Subgroup.centralizer (S.W0 : Set G) := by
    rw [← hg, conjSub_centralizer]
    exact conjSub_mono g inf_le_right
  have hP2 : IsPGroup 2 (conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G))) :=
    F7.isPGroup_conjSub (S.h13.sylow.1.to_le inf_le_left)
  have hRP : Nat.card S.R45 <
      Nat.card (conjSub g (T ⊓ Subgroup.centralizer (S.V2 : Set G))) := by
    rw [A5.card_conjSub']
    exact S.card_R45_lt
  obtain ⟨S', hS', hRS'⟩ := A4.exists_isSylowTwoOf_ge S.R45_le_centralizer_W0 hR2
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS' hPC hP2
  have hPS' := (Subgroup.card_le_of_le hx).trans (A5.card_conjSub' x S').le
  have hlt : S.R45 < S' := lt_of_le_of_ne hRS' fun h => by
    rw [h] at hRP
    omega
  obtain ⟨s, hsS', hsR, hsN⟩ := A5.exists_mem_normalizer_not_mem hS'.2.1 hlt
  have hsC : s ∈ Subgroup.centralizer (S.W0 : Set G) := hS'.1 hsS'
  have hsV : s ∈ Subgroup.normalizer (V : Set G) :=
    S.mem_normalizer_V_of_TI_F4 h1222 (hN hsN) S.W0_le_V S.W0_ne_bot fun w hw => by
      have := Subgroup.mem_centralizer_iff.mp hsC w hw
      rw [← this, mul_inv_cancel_right]
      exact S.W0_le_V hw

  have hfix : ∀ y : P6, InW4 y → InW0 y → act4f (S.frame.ρ ⟨s, hsV⟩) y = y := by
    intro y hy hy0
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨y, hy⟩
    have hvW : (v : G) ∈ S.W0 := S.mem_pre.2 ⟨v.2, by rw [hv]; exact hy0⟩
    have h := (S.conj_eq_iff ⟨s, hsV⟩ v).1 (by
      have := Subgroup.mem_centralizer_iff.mp hsC (v : G) hvW
      calc s * (v : G) * s⁻¹ = (v : G) * s * s⁻¹ := by rw [this]
        _ = v := by group)
    rw [hv] at h
    exact congrArg Subtype.val h

  have h4 : (S.frame.ρ ⟨s, hsV⟩) ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hS'.2.1 ⟨s, hsS'⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨s, hsV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]

  have hcomm : S.frame.ρ ⟨s, hsV⟩ * swap 4 5 = swap 4 5 * S.frame.ρ ⟨s, hsV⟩ := by
    have hsts : s * (t : G) * s⁻¹ ∈ S.R45 := (Subgroup.mem_normalizer_iff.mp hsN t).mp htR
    obtain ⟨-, hN', hρ'⟩ := S.mem_R45.1 hsts
    have e : (⟨s * (t : G) * s⁻¹, hN'⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨s, hsV⟩ * t * ⟨s, hsV⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hρt] at hρ'
    rcases hρ' with h1 | h1
    · exfalso
      apply swap45_ne_one
      calc swap (4 : Fin 6) 5 = (S.frame.ρ ⟨s, hsV⟩)⁻¹ * (S.frame.ρ ⟨s, hsV⟩ * swap 4 5 *
            (S.frame.ρ ⟨s, hsV⟩)⁻¹) * S.frame.ρ ⟨s, hsV⟩ := by group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
    · calc S.frame.ρ ⟨s, hsV⟩ * swap 4 5 = S.frame.ρ ⟨s, hsV⟩ * swap 4 5 *
            (S.frame.ρ ⟨s, hsV⟩)⁻¹ * S.frame.ρ ⟨s, hsV⟩ := by group
        _ = swap 4 5 * S.frame.ρ ⟨s, hsV⟩ := by rw [h1]

  have heq := F1.eq_of_isSylowTwoOf_le S.isSylowTwoOf_CTV inf_le_right
    (hS'.2.1.to_le inf_le_left) (le_inf (S.Q_le_R45.trans hRS') inf_le_right)
  rcases fix_W0_comm45 _ h4 (hfix _ dv_mem_W0.1.1 dv_mem_W0.1.2)
      (hfix _ dv_mem_W0.2.1 dv_mem_W0.2.2) hcomm with h1 | h1
  · have hmem : s ∈ S' ⊓ Subgroup.centralizer (V : Set G) := ⟨hsS', (S.rho_eq_one_iff _).1 h1⟩
    rw [← heq] at hmem
    exact hsR (S.Q_le_R45 hmem)
  · have hst : S.frame.ρ (⟨s, hsV⟩ * t⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, hρt, mul_inv_cancel]
    have hmem : s * (t : G)⁻¹ ∈ S' ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨S'.mul_mem hsS' (S'.inv_mem (hRS' htR)), (S.rho_eq_one_iff _).1 hst⟩
    rw [← heq] at hmem
    have := S.R45.mul_mem (S.Q_le_R45 hmem) htR
    rw [inv_mul_cancel_right] at this
    exact hsR this

end Setting4

@[expose] def Input1356TwoS6Block_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ autOn T V ≤ autOn L V → IsBlock2 (L ⊔ T) L →
      CFSG.Quasithin.IsAltBlockType L 6 → ∀ g : G, conjSub g S.V2 ≠ S.W0

end CFSG.Quasithin.H13.A6
