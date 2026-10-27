module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DObj

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem d_X₁_le_Λ : (sec3DData e t).X₁ ≤ (sec3DData e t).Λ := toG_ch_le (by decide)

theorem d_odd_index_X₁ : Odd ((sec3DData e t).X₁.relIndex (sec3DData e t).Λ) := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) (sec3DData e t).X₁ (sec3DData e t).Λ bot_le
    d_X₁_le_Λ
  rw [relIndex_bot_left, relIndex_bot_left] at h
  have h1 : Nat.card (sec3DData e t).X₁ = 4 := card_sX₁
  have h2 : Nat.card (sec3DData e t).Λ = 60 := by
    rw [show (sec3DData e t).Λ = toG e chLam.grp from rfl, card_toG_ch gensOK_chLam, card_chLam]
  rw [h1, h2] at h
  have : (sec3DData e t).X₁.relIndex (sec3DData e t).Λ = 15 := by omega
  rw [this]
  decide

theorem d_u₁_mem : (sec3DData e t).u₁ ∈ (sec3DData e t).X₁ := gw_mem_ch (by decide)

theorem d_u₂_mem : (sec3DData e t).u₂ ∈ (sec3DData e t).X₁ := gw_mem_ch (by decide)

theorem d_X₁_le_closure :
    (sec3DData e t).X₁ ≤ closure {(sec3DData e t).u₁, (sec3DData e t).u₂} := by
  refine toG_le_of_gens gensOK_chX1 fun w hw => ?_
  have hw' : w = [0] ∨ w = [1] := by simpa [chX1] using hw
  rcases hw' with rfl | rfl
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem d_u₁_sq : (sec3DData e t).u₁ * (sec3DData e t).u₁ = 1 := by
  show gw e [0] * gw e [0] = 1
  rw [← gw_append, gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem d_u₂_sq : (sec3DData e t).u₂ * (sec3DData e t).u₂ = 1 := by
  show gw e [1] * gw e [1] = 1
  rw [← gw_append, gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem d_u₁_comm_u₂ :
    (sec3DData e t).u₁ * (sec3DData e t).u₂ = (sec3DData e t).u₂ * (sec3DData e t).u₁ := by
  show gw e [0] * gw e [1] = gw e [1] * gw e [0]
  rw [← gw_append, ← gw_append]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem d_a₀_mem : (sec3DData e t).a₀ ∈ (sec3DData e t).A₄ := gw_mem_ch (by decide)

theorem d_A₄_le_closure : (sec3DData e t).A₄ ≤
    closure ((fun x => x * (sec3DData e t).a₀ * x⁻¹) '' ((sec3DData e t).X₁ : Set G)) := by
  refine toG_le_of_prodCheck gensOK_chA4 xWit_spec.2.1 (by decide) (by decide) fun p hp b hb => ?_
  have hl : ∀ p ∈ a4aData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chX1.gens) ∧ b.2 = [11] := by
    decide
  obtain ⟨h1, h2⟩ := hl p hp b hb
  rw [gw_cjW (fun k hk => (h1 k hk).1), h2]
  exact subset_closure ⟨gw e b.1, gw_mem_ch h1, rfl⟩

theorem d_norm_a₀ : (sec3DData e t).a₀ * ((sec3DData e t).u₁ * (sec3DData e t).a₀ *
    (sec3DData e t).u₁⁻¹) * ((sec3DData e t).u₂ * (sec3DData e t).a₀ * (sec3DData e t).u₂⁻¹) *
    (((sec3DData e t).u₁ * (sec3DData e t).u₂) * (sec3DData e t).a₀ *
      ((sec3DData e t).u₁ * (sec3DData e t).u₂)⁻¹) = (sec3DData e t).z := by
  show gw e [11] * (gw e [0] * gw e [11] * (gw e [0])⁻¹) *
    (gw e [1] * gw e [11] * (gw e [1])⁻¹) *
    ((gw e [0] * gw e [1]) * gw e [11] * (gw e [0] * gw e [1])⁻¹) = gw e [14]
  rw [← gw_append [0] [1], ← gw_cjW (b := [11]) (by decide), ← gw_cjW (b := [11]) (by decide),
    ← gw_cjW (b := [11]) (by decide), ← gw_append, ← gw_append, ← gw_append]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem d_A₄_cent_X₁ :
    (sec3DData e t).A₄ ⊓ centralizer ((sec3DData e t).X₁ : Set G) ≤ zpowers (sec3DData e t).z := by
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm]
  exact toG_inf_centralizer_le (grp_le_T46 gensOK_chX1) fun g hg _ hc =>
    (a4_spec g hg).1 fun _ hw => hc _ (wP_mem_grp hw)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
