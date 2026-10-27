module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp5
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSettingB

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem d_K₂_le_normalizer :
    (sec3DData e t).K₂ ≤ normalizer ((sec3DData e t).A₂ : Set G) :=
  toG_le_normalizer (grp_le_T46 gensOK_chK2) (grp_le_T46 gensOK_chA2) chK2_le_normalizer_A2

theorem d_Λ_le_K₂ : (sec3DData e t).Λ ≤ (sec3DData e t).K₂ := toG_ch_le (by decide)

theorem d_w₂_eq : (sec3DData e t).w₂ = gw e [16] := by
  show phiG e (yamGen (15 + 1)) = phiG e (yamWord [16])
  simp [yamWord]

theorem d_w₂_mem_K₁ : (sec3DData e t).w₂ ∈ (sec3DData e t).K₁ := by
  rw [d_w₂_eq]
  exact gw_mem_ch (by decide)

theorem d_w₂_mem_K₂ : (sec3DData e t).w₂ ∈ (sec3DData e t).K₂ := by
  rw [d_w₂_eq]
  exact gw_mem_ch (by decide)

theorem d_A₁_inf_A₄ :
    (sec3DData e t).A₁ ⊓ (sec3DData e t).A₄ ≤ (sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z := by
  rw [d_Z₂S_eq, show (sec3DData e t).A₁ = toG e chA1.grp from rfl,
    show (sec3DData e t).A₄ = toG e chA4.grp from rfl, ← toG_inf]
  exact toG_mono fun x hx => (a4_spec x (mem_inf.1 hx).2).2.1 (mem_inf.1 hx).1

theorem chA1_inf_chA2 : chA1.grp ⊓ chA2.grp = chX6Z.grp :=
  le_antisymm (fun x hx => a2_spec x (mem_inf.1 hx).2 (mem_inf.1 hx).1)
    (le_inf (grp_le_of_subset (by decide)) (grp_le_of_subset (by decide)))

theorem d_A₁_inf_A₂_eq : (sec3DData e t).A₁ ⊓ (sec3DData e t).A₂ = toG e chX6Z.grp := by
  rw [show (sec3DData e t).A₁ = toG e chA1.grp from rfl,
    show (sec3DData e t).A₂ = toG e chA2.grp from rfl, ← toG_inf, chA1_inf_chA2]

theorem d_A₁_inf_A₂ : (sec3DData e t).A₁ ⊓ (sec3DData e t).A₂ ≤
    ((sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z) ⊔
      (sec3DData e t).conjW ((sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z) := by
  rw [d_A₁_inf_A₂_eq]
  refine toG_le_of_gens gensOK_chX6Z fun w hw => ?_
  have hw' : w = [9] ∨ w = [10] ∨ ∀ k ∈ w, k < 18 ∧ [k] ∈ chZ2S.gens := by
    revert w
    decide
  have hZ : ∀ {k : ℕ}, [k] ∈ chZ2S.gens → k < 18 →
      gw e [k] ∈ (sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z := fun hk hlt => by
    rw [d_Z₂S_eq]
    exact gw_mem_ch fun k' hk' => by rw [List.mem_singleton.1 hk']; exact ⟨hlt, hk⟩
  rcases hw' with rfl | rfl | h
  · refine mem_sup_right ⟨gw e [12], hZ (by decide) (by decide), ?_⟩
    show (MulAut.conj (sec3DData e t).w₂).toMonoidHom (gw e [12]) = gw e [9]
    rw [d_w₂_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← gw_cjW (by decide)]
    exact gw_eq_xId (by decide) (by decide) (by decide)
  · refine mem_sup_right ⟨gw e [13], hZ (by decide) (by decide), ?_⟩
    show (MulAut.conj (sec3DData e t).w₂).toMonoidHom (gw e [13]) = gw e [10]
    rw [d_w₂_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← gw_cjW (by decide)]
    exact gw_eq_xId (by decide) (by decide) (by decide)
  · exact mem_sup_left (by rw [d_Z₂S_eq]; exact gw_mem_ch h)

theorem gP16_comm_chZ {y : Equiv.Perm (Fin 693)} (hy : y ∈ chZ.grp) : gP 16 * y = y * gP 16 := by
  have h : wP [16] ∈ centralizer (chZ.grp : Set (Equiv.Perm (Fin 693))) :=
    xComm_spec.2.2.2.2.2.1 (wP_mem_grp (by decide))
  rw [← wP_single]
  exact (mem_centralizer_iff.1 h y hy).symm

theorem d_Z₂S_inf : ((sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z) ⊓
    (sec3DData e t).conjW ((sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z) ≤
      zpowers (sec3DData e t).z := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx2
  rw [d_Z₂S_eq] at hy hx1
  obtain ⟨y', hy', rfl⟩ := mem_toG.1 hy
  have hconj : (MulAut.conj (sec3DData e t).w₂).toMonoidHom (iotaG e y') =
      iotaG e (tw [16] (by decide) * y' * (tw [16] (by decide))⁻¹) := by
    rw [d_w₂_eq, gw_eq [16] (by decide), MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_mul, map_inv]
  rw [hconj] at hx1 ⊢
  have h1 := iotaG_mem_toG.1 hx1
  have hyz : (y' : Equiv.Perm (Fin 693)) ∈ chZ.grp :=
    (z2s_spec _ hy').2.1 (by simpa [tw, wP_single] using h1)
  have heq : tw [16] (by decide) * y' * (tw [16] (by decide))⁻¹ = y' := by
    apply Subtype.ext
    have := gP16_comm_chZ hyz
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, tw, wP_single]
    rw [this, mul_inv_cancel_right]
  rw [heq, show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm]
  exact iotaG_mem_toG.2 hyz

theorem chS_center : ∀ s ∈ chS.grp, s ∈ T46 → (∀ x ∈ chS.grp, s * x = x * s) → s ∈ chZ.grp := by
  intro s hs hT hc
  have hA : s ∈ chA2.grp := by
    rw [← uA_eq_chA2, ← centralizer_uA]
    refine ⟨hT, mem_centralizer_iff.2 fun a ha => ?_⟩
    rw [uA_eq_chA2] at ha
    exact (hc a (chA2_le_chS ha)).symm
  exact zS_spec s hA fun w hw => hc _ (wP_mem_grp hw)

theorem d_center_S : (sec3DData e t).S ⊓ centralizer ((sec3DData e t).S : Set G) =
    zpowers (sec3DData e t).z := by
  rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm]
  apply le_antisymm
  · exact toG_inf_centralizer_le (grp_le_T46 gensOK_chS) fun g hg hT hc =>
      chS_center g hg hT fun x hx => hc x hx
  · refine le_inf (toG_le_of_gens gensOK_chZ fun w hw => ?_) ?_
    · rw [show w = [14] from List.mem_singleton.1 hw]
      exact (gw_mem_toG (by decide)).2 (by rw [wP_single]; exact gP_mem_chS (by norm_num))
    · exact toG_le_centralizer (le_centralizer_iff.1 xComm_spec.2.2.2.2.2.2.1)

theorem d_CA₁e : ∀ a ∈ (sec3DData e t).A₁, a * (sec3DData e t).e = (sec3DData e t).e * a →
    ∃ x ∈ (sec3DData e t).X₁, ∃ b ∈ (sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z, a = x * b := by
  intro a ha hae
  have hmem : a ∈ toG e chX1Z.grp :=
    toG_inf_centralizer_gw_le (H := chA1.grp) (by decide) (fun g hg _ hc => (a1_spec g hg).2.2.2.1 hc)
      ⟨ha, mem_centralizer_singleton_iff.2 hae⟩
  have hsup : toG e chX1Z.grp = (sec3DData e t).X₁ ⊔ ((sec3DData e t).X₈ ⊔
      zpowers (sec3DData e t).z) := by
    rw [d_Z₂S_eq, show (sec3DData e t).X₁ = toG e chX1.grp from rfl,
      ← toG_sup (grp_le_T46 gensOK_chX1) (grp_le_T46 gensOK_chZ2S), ← grp_append (c := chX1Z)
        (by decide)]
  rw [hsup] at hmem
  have hnorm : (sec3DData e t).X₁ ≤ normalizer (((sec3DData e t).X₈ ⊔
      zpowers (sec3DData e t).z : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have hc := d_comm_X₁_Z₂ x hx b hb
      have e1 : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
      rw [e1]
      exact mul_mem (mem_sup_right hc) hb
    · intro hb
      have hb' : b = x⁻¹ * (x * b * x⁻¹) * x := by group
      have hc := d_comm_X₁_Z₂ x⁻¹ (inv_mem hx) _ hb
      rw [hb']
      have e1 : x⁻¹ * (x * b * x⁻¹) * x = (x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ * (x * b * x⁻¹)⁻¹) *
          (x * b * x⁻¹) := by group
      rw [e1]
      exact mul_mem (mem_sup_right hc) hb
  have hmem' : a ∈ (((sec3DData e t).X₁ ⊔ ((sec3DData e t).X₈ ⊔ zpowers (sec3DData e t).z) :
      Subgroup G) : Set G) := hmem
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hmem'
  obtain ⟨x, hx, b, hb, rfl⟩ := hmem'
  exact ⟨x, hx, b, hb, rfl⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
