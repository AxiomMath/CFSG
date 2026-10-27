module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp6
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQSetting

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem d_e_mem_Sig : (sec3DData e t).e ∈ (sec3DData e t).Sig := gw_mem_ch (by decide)

theorem d_j₀_comm_e :
    (sec3DData e t).j₀ * (sec3DData e t).e = (sec3DData e t).e * (sec3DData e t).j₀ := by
  show gw e j0W * gw e [4, 17] = gw e [4, 17] * gw e j0W
  rw [← gw_append, ← gw_append]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem d_w₂₃₂_sq : (sec3DData e t).w₂₃₂ * (sec3DData e t).w₂₃₂ = 1 := by
  show gw e [16, 17, 16] * gw e [16, 17, 16] = 1
  rw [← gw_append, gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem d_w₂₃₂_mem_K₁ : (sec3DData e t).w₂₃₂ ∈ (sec3DData e t).K₁ := gw_mem_ch (by decide)

theorem d_w₂₃₂_comm_e :
    (sec3DData e t).w₂₃₂ * (sec3DData e t).e = (sec3DData e t).e * (sec3DData e t).w₂₃₂ := by
  show gw e [16, 17, 16] * gw e [4, 17] = gw e [4, 17] * gw e [16, 17, 16]
  rw [← gw_append, ← gw_append]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem d_w₂₃₂_comm_j₀ :
    (sec3DData e t).w₂₃₂ * (sec3DData e t).j₀ = (sec3DData e t).j₀ * (sec3DData e t).w₂₃₂ := by
  show gw e [16, 17, 16] * gw e j0W = gw e j0W * gw e [16, 17, 16]
  rw [← gw_append, ← gw_append]
  exact gw_eq_xId (by decide) (by decide) (by decide)

theorem d_w₂₃₂_X₈ : ∀ b ∈ (sec3DData e t).X₈,
    (sec3DData e t).w₂₃₂ * b * (sec3DData e t).w₂₃₂⁻¹ ∈ (sec3DData e t).X₁ := by
  have h : (sec3DData e t).X₈ ≤
      (sec3DData e t).X₁.comap (MulAut.conj (sec3DData e t).w₂₃₂).toMonoidHom := by
    refine toG_le_of_gens gensOK_chX8 fun w hw => ?_
    have hw' : w = [12] ∨ w = [13] := by simpa [chX8] using hw
    show (MulAut.conj (gw e [16, 17, 16])) (gw e w) ∈ (sec3DData e t).X₁
    rw [MulAut.conj_apply, ← gw_cjW (by decide)]
    rcases hw' with rfl | rfl
    · rw [gw_eq_xId (b := [0]) (by decide) (by decide) (by decide)]
      exact gw_mem_ch (by decide)
    · rw [gw_eq_xId (b := [1]) (by decide) (by decide) (by decide)]
      exact gw_mem_ch (by decide)
  exact fun b hb => h hb

theorem pg_comm_chZ {y : Equiv.Perm (Fin 693)} (hy : y ∈ chZ.grp) : pg * y = y * pg := by
  have h : wP [16, 17, 16] ∈ centralizer (chZ.grp : Set (Equiv.Perm (Fin 693))) :=
    xComm_spec.2.2.2.2.2.1 (wP_mem_of_letters _ (by decide))
  exact (mem_centralizer_iff.1 h y hy).symm

theorem d_Z₂S_inf_g : (sec3DData e t).Z₂S ⊓ (sec3DData e t).conjG (sec3DData e t).Z₂S ≤
    zpowers (sec3DData e t).z := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx2
  have hZ : (sec3DData e t).Z₂S = toG e chZ2S.grp := d_Z₂S_eq
  rw [hZ] at hy hx1
  obtain ⟨y', hy', rfl⟩ := mem_toG.1 hy
  have hconj : (MulAut.conj (sec3DData e t).w₂₃₂).toMonoidHom (iotaG e y') =
      iotaG e (tw [16, 17, 16] (by decide) * y' * (tw [16, 17, 16] (by decide))⁻¹) := by
    rw [show (sec3DData e t).w₂₃₂ = gw e [16, 17, 16] from rfl, gw_eq [16, 17, 16] (by decide),
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [hconj] at hx1 ⊢
  have h1 := iotaG_mem_toG.1 hx1
  have hyz : (y' : Equiv.Perm (Fin 693)) ∈ chZ.grp :=
    (z2s_spec _ hy').2.2 (by simpa [tw, pg] using h1)
  have heq : tw [16, 17, 16] (by decide) * y' * (tw [16, 17, 16] (by decide))⁻¹ = y' := by
    apply Subtype.ext
    have := pg_comm_chZ hyz
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, tw]
    rw [show wP [16, 17, 16] = pg from rfl, this, mul_inv_cancel_right]
  rw [heq, show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm]
  exact iotaG_mem_toG.2 hyz

theorem d_X₁_le_A₁ : (sec3DData e t).X₁ ≤ (sec3DData e t).A₁ := toG_ch_le (by decide)

theorem d_A₁_le_conj : (sec3DData e t).A₁ ≤ closure {g | ∃ a ∈ (sec3DData e t).A₃,
    ∃ x ∈ (sec3DData e t).X₁, g = a * x * a⁻¹} := by
  refine toG_le_of_prodCheck gensOK_chA1 xWit_spec.2.2.2.2.2.1 (by decide) (by decide)
    fun p hp b hb => ?_
  have hl : ∀ p ∈ a1cData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chA3.gens) ∧
      ∀ k ∈ b.2, k < 18 ∧ [k] ∈ chX1.gens := by decide
  obtain ⟨h1, h2⟩ := hl p hp b hb
  rw [gw_cjW (fun k hk => (h1 k hk).1)]
  exact subset_closure ⟨gw e b.1, gw_mem_ch h1, gw e b.2, gw_mem_ch h2, rfl⟩

theorem d_A₂_closure : ∀ B : Subgroup G, (sec3DData e t).A₄ ≤ B → B ≤ (sec3DData e t).A₂ →
    (sec3DData e t).K₁ ⊓ (sec3DData e t).K₂ ≤ normalizer (B : Set G) →
      B = (sec3DData e t).A₂ := by
  intro B hAB hBA hN
  refine le_antisymm hBA ?_
  refine toG_le_of_prodCheck gensOK_chA2 xWit_spec.2.2.2.2.2.2.1 (by decide) (by decide)
    fun p hp b hb => ?_
  have hl : ∀ p ∈ a2cData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chK1.gens ∧ [k] ∈ chK2.gens) ∧
      ∀ k ∈ b.2, k < 18 ∧ [k] ∈ chA4.gens := by decide
  obtain ⟨h1, h2⟩ := hl p hp b hb
  rw [gw_cjW (fun k hk => (h1 k hk).1)]
  have hn : gw e b.1 ∈ normalizer (B : Set G) :=
    hN ⟨gw_mem_ch fun k hk => ⟨(h1 k hk).1, (h1 k hk).2.1⟩,
      gw_mem_ch fun k hk => ⟨(h1 k hk).1, (h1 k hk).2.2⟩⟩
  exact (mem_normalizer_iff.1 hn _).1 (hAB (gw_mem_ch h2))

theorem d_CA₁A₂ : (sec3DData e t).A₁ ⊓
    centralizer (((sec3DData e t).A₁ ⊓ (sec3DData e t).A₂ : Subgroup G) : Set G) ≤
      (sec3DData e t).A₂ := by
  rw [d_A₁_inf_A₂_eq]
  exact toG_inf_centralizer_le (grp_le_T46 gensOK_chX6Z) fun g hg _ hc =>
    (a1_spec g hg).2.2.2.2 fun _ hw => hc _ (wP_mem_grp hw)

theorem d_A₁A₂_le_comm : (sec3DData e t).A₁ ⊓ (sec3DData e t).A₂ ≤
    ⁅(sec3DData e t).A₁, (sec3DData e t).A₂⁆ := by
  rw [d_A₁_inf_A₂_eq]
  refine toG_le_of_prodCheck gensOK_chX6Z xWit_spec.2.2.2.2.2.2.2.1 (by decide) (by decide)
    fun p hp b hb => ?_
  have hl : ∀ p ∈ a12cData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chA1.gens) ∧
      ∀ k ∈ b.2, k < 18 ∧ [k] ∈ chA2.gens := by decide
  obtain ⟨h1, h2⟩ := hl p hp b hb
  rw [gw_cwW (fun k hk => (h1 k hk).1) (fun k hk => (h2 k hk).1)]
  exact commutator_mem_commutator (gw_mem_ch h1) (gw_mem_ch h2)

theorem d_card_A₁A₂ : Nat.card ((sec3DData e t).A₁ ⊓ (sec3DData e t).A₂ : Subgroup G) = 2 ^ 5 := by
  rw [d_A₁_inf_A₂_eq, card_toG_ch gensOK_chX6Z, card_chX6Z]
  norm_num

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
