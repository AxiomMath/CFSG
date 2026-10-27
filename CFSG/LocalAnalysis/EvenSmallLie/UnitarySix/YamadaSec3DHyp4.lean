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

theorem d_z_mem_A₄ : (sec3DData e t).z ∈ (sec3DData e t).A₄ := gw_mem_ch (by decide)

theorem d_z_ne_one : (sec3DData e t).z ≠ 1 := by
  intro h
  have h1 : Nat.card (toG e chZ.grp) = 2 := by rw [card_toG_ch gensOK_chZ, card_chZ]
  rw [toG_chZ, show gw e [14] = (sec3DData e t).z from rfl, h, zpowers_one_eq_bot,
    Subgroup.card_bot] at h1
  exact absurd h1 (by decide)

theorem d_z_comm_S : (sec3DData e t).S ≤ centralizer ({(sec3DData e t).z} : Set G) := by
  have h := toG_le_centralizer (e := e) xComm_spec.2.2.2.2.2.2.1
  rw [toG_chZ] at h
  exact h.trans (centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers _)))

theorem d_z_cent_X₁ : (sec3DData e t).z ∈ centralizer ((sec3DData e t).X₁ : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have hxS : x ∈ (sec3DData e t).S := toG_ch_le (by decide) hx
  exact mem_centralizer_singleton_iff.1 (d_z_comm_S hxS)

theorem d_A₁_le : (sec3DData e t).A₁ ≤ (sec3DData e t).X₁ ⊔ (sec3DData e t).A₃ := by
  refine toG_le_of_gens gensOK_chA1 fun w hw => ?_
  have hw' : (∀ k ∈ w, k < 18 ∧ [k] ∈ chX1.gens) ∨ ∀ k ∈ w, k < 18 ∧ [k] ∈ chA3.gens := by
    revert w
    decide
  rcases hw' with h | h
  · exact mem_sup_left (gw_mem_ch h)
  · exact mem_sup_right (gw_mem_ch h)

theorem d_z_mem_A₁ : (sec3DData e t).z ∈ (sec3DData e t).A₁ := gw_mem_ch (by decide)

theorem d_card_A₁ : Nat.card (sec3DData e t).A₁ = 2 ^ 9 := by
  rw [show (sec3DData e t).A₁ = toG e chA1.grp from rfl, card_toG_ch gensOK_chA1, card_chA1]
  norm_num

theorem d_center_A₁ :
    (sec3DData e t).A₁ ⊓ centralizer ((sec3DData e t).A₁ : Set G) ≤ zpowers (sec3DData e t).z := by
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm]
  exact toG_inf_centralizer_le (grp_le_T46 gensOK_chA1) fun g hg _ hc =>
    (a1_spec g hg).1 fun _ hw => hc _ (wP_mem_grp hw)

theorem chA1_comm : ∀ a ∈ chA1.grp, ∀ b ∈ chA1.grp, ⁅a, b⁆ ∈ chZ.grp := by
  intro a ha b hb
  have hz : ∀ y ∈ chZ.grp, ∀ x ∈ chA1.grp, x * y = y * x := fun y hy x hx =>
    mem_centralizer_iff.1 (xComm_spec.2.2.2.2.2.2.2 hx) y hy |>.symm
  induction hb using Subgroup.closure_induction with
  | mem b hb =>
    obtain ⟨w, hw, rfl⟩ := hb
    exact (a1_spec a ha).2.2.1 w hw
  | one => simp [commutatorElement_def]
  | mul b c hb hc ihb ihc =>
    have e1 : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e1, show b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ by rw [hz _ ihc b hb, mul_inv_cancel_right]]
    exact mul_mem ihb ihc
  | inv b hb ihb =>
    have e1 : ⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b := by simp only [commutatorElement_def]; group
    rw [e1, hz _ (inv_mem ihb) b⁻¹ (inv_mem hb), inv_mul_cancel_right]
    exact inv_mem ihb

theorem d_A₁_comm : ∀ a ∈ (sec3DData e t).A₁, ∀ b ∈ (sec3DData e t).A₁,
    a * b * a⁻¹ * b⁻¹ ∈ zpowers (sec3DData e t).z := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := mem_toG.1 ha
  obtain ⟨b', hb', rfl⟩ := mem_toG.1 hb
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm, ← commutatorElement_def]
  exact iotaG_comm_mem (chA1_comm _ ha' _ hb')

theorem d_A₁_sq : ∀ a ∈ (sec3DData e t).A₁, a * a ∈ zpowers (sec3DData e t).z := by
  intro a ha
  obtain ⟨a', ha', rfl⟩ := mem_toG.1 ha
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm, ← map_mul]
  exact iotaG_mem_toG.2 (a1_spec _ ha').2.1

theorem d_K₁_cent_z : (sec3DData e t).K₁ ≤ centralizer ({(sec3DData e t).z} : Set G) := by
  have h := toG_le_centralizer (e := e) xComm_spec.2.2.2.2.2.1
  rw [toG_chZ] at h
  exact h.trans (centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers _)))

theorem d_K₁_perfect : (sec3DData e t).K₁ ≤ ⁅(sec3DData e t).K₁, (sec3DData e t).K₁⁆ := by
  refine toG_le_of_prodCheck gensOK_chK1 xWit_spec.2.2.2.2.1 (by decide) (by decide)
    fun p hp b hb => ?_
  have hl : ∀ p ∈ k1pData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chK1.gens) ∧
      ∀ k ∈ b.2, k < 18 ∧ [k] ∈ chK1.gens := by decide
  obtain ⟨h1, h2⟩ := hl p hp b hb
  rw [gw_cwW (fun k hk => (h1 k hk).1) (fun k hk => (h2 k hk).1)]
  exact commutator_mem_commutator (gw_mem_ch h1) (gw_mem_ch h2)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
