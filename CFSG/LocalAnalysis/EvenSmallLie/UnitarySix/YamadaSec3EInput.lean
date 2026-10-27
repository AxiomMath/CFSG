module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3ECheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DOrb

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Sporadic.Schreier

section Perm


theorem rep_nativeWordA {w : List ℤ} (hw : ∀ c ∈ w, 1 ≤ c.natAbs ∧ c.natAbs ≤ 46) :
    Rep 693 (nativeWordA w) (u62W w) := by
  rw [u62W, tab_eq]
  exact rep_nativeWord w hw

theorem uT_le_chS : uT ≤ chS.grp := by
  have h := eNative_check
  unfold eNativeCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  rw [uT_eq]
  refine closure_le_of_mem fun g hg => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  have hall : ∀ w' ∈ tWords, ∀ c ∈ w', 1 ≤ c.natAbs ∧ c.natAbs ≤ 46 := by decide
  have hs := (h.1 _ (List.mem_map.2 ⟨w, hw, rfl⟩)).2
  exact (mem_chS_iff (rep_nativeWordA (hall w hw))).2 hs

theorem uK_le_chK2 : uK ≤ chK2.grp := by
  have h := eNative_check
  unfold eNativeCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  rw [uK_eq]
  refine closure_le_of_mem fun g hg => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  have hall : ∀ w' ∈ kWords, ∀ c ∈ w', 1 ≤ c.natAbs ∧ c.natAbs ≤ 46 := by decide
  have hs := (h.2 _ (List.mem_map.2 ⟨w, hw, rfl⟩)).2
  exact (mem_chK2_iff (rep_nativeWordA (hall w hw))).2 hs

theorem uS_eq_chS : uS = chS.grp := by
  have hle : uS ≤ chS.grp := by
    rw [uS_eq]
    exact sup_le (uA_eq_chA2 ▸ chA2_le_chS) uT_le_chS
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_uS, card_chS])

theorem uK_eq_chK2 : uK = chK2.grp :=
  Subgroup.eq_of_le_of_card_ge uK_le_chK2 (by rw [card_uK, card_chK2])

theorem uP_eq_chK2A2 : uP = chK2.grp ⊔ chA2.grp := by
  rw [uP_eq, uA_eq_chA2, uK_eq_chK2, sup_comm]

theorem qzWords_lt : ∀ w ∈ qzWords, ∀ k ∈ w, k < 18 := by decide +kernel

theorem centralizer_gP14_le {g : Equiv.Perm (Fin 693)} (hT : g ∈ T46)
    (hc : g * gP 14 = gP 14 * g) : g ∈ chK1A1.grp := by
  have h := eTrans_check
  unfold eTransCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨hlen, hall⟩ := h
  set f := g 0 with hf
  obtain ⟨⟨hv, h0⟩, hz⟩ := hall f.val f.2
  have hmem : qzWords[f.val]! ∈ qzWords := by
    rw [getElem!_pos qzWords f.val (by rw [hlen]; exact f.2)]
    exact List.getElem_mem _
  set q := wP qzWords[f.val]! with hqdef
  have hq : Rep 693 (wA qzWords[f.val]!) q := rep_wA tabs_check _ (qzWords_lt _ hmem)
  have hq0 : q 0 = f := Fin.ext (by rw [← h0]; exact (hq 0).symm)
  have hqT : q ∈ T46 := wP_mem_T46 _ (qzWords_lt _ hmem)
  have hh0 : (q⁻¹ * g) 0 = 0 := by
    rw [Equiv.Perm.mul_apply, ← hf, Equiv.Perm.inv_eq_iff_eq, hq0]
  have hhKA : q⁻¹ * g ∈ chK1A1.grp := by
    rw [← stabilizer_zero_eq]
    exact ⟨⟨q⁻¹ * g, mul_mem (inv_mem hqT) hT⟩, MulAction.mem_stabilizer_iff.2 (by
      show (q⁻¹ * g : Equiv.Perm (Fin 693)) 0 = 0
      exact hh0), rfl⟩
  have hKA : chK1A1.grp ≤ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) := by
    rw [chK1A1_eq]
    exact sup_le chK1_le_normalizer_A1 le_normalizer
  have hzA : gP 14 ∈ chA1.grp := by rw [← wP_single]; exact wP_mem_grp (by decide)
  have hzmem : q⁻¹ * gP 14 * q ∈ chA1.grp := by
    have hc' : g * gP 14 * g⁻¹ = gP 14 := by rw [hc, mul_inv_cancel_right]
    have e1 : q⁻¹ * gP 14 * q = (q⁻¹ * g) * gP 14 * (q⁻¹ * g)⁻¹ := by
      calc q⁻¹ * gP 14 * q = q⁻¹ * (g * gP 14 * g⁻¹) * q := by rw [hc']
        _ = (q⁻¹ * g) * gP 14 * (q⁻¹ * g)⁻¹ := by group
    rw [e1]
    exact (mem_normalizer_iff.1 (hKA hhKA) _).1 hzA
  rcases hz with hf0 | hns
  · have hg0 : g 0 = 0 := Fin.ext hf0
    rw [← stabilizer_zero_eq]
    exact ⟨⟨g, hT⟩, MulAction.mem_stabilizer_iff.2 hg0, rfl⟩
  · have hrep := rep_conjInvA hv (rep_gA tabs_check (by norm_num : 14 < 18))
    rw [permOfArr_eq_of_rep hq] at hrep
    rw [(mem_chA1_iff hrep).1 hzmem] at hns
    exact absurd hns (by decide)

end Perm

section GLevel

variable {G : Type} [Group G] {L : Subgroup G}
  {t : G}

theorem eL_iotaG' (e : L ≃* T46) (g : T46) : e ⟨iotaG e g, iotaG_mem g⟩ = g := by
  have : (⟨iotaG e g, iotaG_mem g⟩ : L) = e.symm g := rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem sS_abelian_eq_sA₂ (e : L ≃* T46) (X : Subgroup G) (hXS : X ≤ sS e)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX : Nat.card X = 2 ^ 9) : X = sA₂ e := by
  have hXL : X ≤ L := hXS.trans (toG_le_L _)
  set φ : L →* Equiv.Perm (Fin 693) := T46.subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  set Y := (X.subgroupOf L).map φ with hY
  have hφx : ∀ g : T46, φ ⟨iotaG e g, iotaG_mem g⟩ = g := fun g => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eL_iotaG']
    rfl
  have hYS : Y ≤ uS := by
    rintro _ ⟨⟨x, hxL⟩, hx, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_toG.1 (hXS (mem_subgroupOf.1 hx))
    rw [hφx, uS_eq_chS]
    exact hg
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hcomm _ (mem_subgroupOf.1 hx) _ (mem_subgroupOf.1 hy)))
  have hYcard : Nat.card Y = 512 := by
    rw [hY, card_map_of_injective hφinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv, hX]
    norm_num
  have hYA := (abelian_le_uS hYS hYc).2 hYcard
  have hle : X ≤ sA₂ e := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_toG.1 (hXS hx)
    refine iotaG_mem_toG.2 ?_
    rw [← uA_eq_chA2, ← hYA, ← hφx g]
    exact ⟨_, mem_subgroupOf.2 hx, rfl⟩
  have : Finite (sA₂ e) := finite_of_le_L e (toG_le_L _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hX, show sA₂ e = toG e chA2.grp from rfl, card_toG_ch gensOK_chA2, card_chA2]
  norm_num

theorem normalizer_sA₂_le (e : L ≃* T46) :
    L ⊓ normalizer (sA₂ e : Set G) ≤ sK₂ e ⊔ sA₂ e := by
  intro x hx
  have h1 : x ∈ normalizer (toG e chA2.grp : Set G) ⊓ L := ⟨hx.2, hx.1⟩
  rw [normalizer_toG (grp_le_T46 gensOK_chA2)] at h1
  have h2 : normalizer (chA2.grp : Set (Equiv.Perm (Fin 693))) ⊓ T46 = chK2.grp ⊔ chA2.grp := by
    rw [inf_comm, ← uA_eq_chA2, normalizer_uA, uP_eq_chK2A2, uA_eq_chA2]
  rw [h2, toG_sup (grp_le_T46 gensOK_chK2) (grp_le_T46 gensOK_chA2)] at h1
  exact h1

theorem centralizer_z_le (e : L ≃* T46) :
    L ⊓ centralizer ({(sec3DData e t).z} : Set G) ≤ sK₁ e ⊔ sA₁ e := by
  rintro x ⟨hxL, hxz⟩
  obtain ⟨g, rfl⟩ := exists_iotaG (e := e) hxL
  have hc : (g : Equiv.Perm (Fin 693)) * gP 14 = gP 14 * g := by
    have h1 := mem_centralizer_singleton_iff.1 hxz
    rw [show (sec3DData e t).z = iotaG e (tw [14] (by decide)) from gw_eq [14] (by decide),
      ← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (iotaG_injective h1)
    simpa [tw, wP_single] using h2
  have hg := centralizer_gP14_le g.2 hc
  rw [chK1A1_eq] at hg
  rw [show sK₁ e = toG e chK1.grp from rfl, show sA₁ e = toG e chA1.grp from rfl,
    ← toG_sup (grp_le_T46 gensOK_chK1) (grp_le_T46 gensOK_chA1)]
  exact iotaG_mem_toG.2 hg

end GLevel

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
