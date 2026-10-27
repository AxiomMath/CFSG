module

public import CFSG.Quasithin.EmptyFaithful.SzC4A38Real
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153G24
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzC4A38

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.FLc CFSG.Quasithin CFSG.Quasithin.A38c10
open scoped commutatorElement Pointwise

theorem ms_false_corr2_F4 (hMS : MS93.AS_C_1_34_corr_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hYY : Yp = Y153 Mc M) (hYpL : Yp ≤ L)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    (hodd1 : ∀ y ∈ Yp, Odd (orderOf y) → (∀ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ = z) → y = 1)
    {Vp Y₁ Y₂ : Subgroup G} (hVp2 : IsPGroup 2 ↥Vp) (hVpS : Vp ≤ Sgp153 T V₁)
    (hVL : L ≤ Subgroup.normalizer (Vp : Set G))
    (hVS : Sgp153 T V₁ ≤ Subgroup.normalizer (Vp : Set G))
    (hY₁ : Y₁ ≤ Yp) (hY₂ : Y₂ ≤ Yp) (hY₁c : ∃ a, Nat.card ↥Y₁ = 2 ^ a * 3)
    (hY₂c : ∃ a, Nat.card ↥Y₂ = 2 ^ a * 3)
    (hV : MSG2 L (Sgp153 T V₁) Vp Yp Y₁ Y₂) : False := by
  obtain ⟨α, hαs, hαk, -, ⟨ψ₁, q₁, hm₁⟩, ⟨ψ₃, q₃, hm₃⟩⟩ := hV
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hh.hyp.qtfe.sylow.1.to_le inf_le_left
  obtain ⟨h₁, hq₁⟩ := hyp6_of_msgat hαs hαk hS2 hSL hm₁
  obtain ⟨h₃, hq₃⟩ := hyp6_of_msgat hαs hαk hS2 hSL hm₃
  obtain ⟨hPL₁, hSLP₁, -, hSP₁, hmin₁, hYP₁, hψs₁, hψk₁, -, hq1₁, hqP₁, hqK₁⟩ := hm₁
  obtain ⟨hPL₃, hSLP₃, -, hSP₃, hmin₃, hYP₃, hψs₃, hψk₃, -, hq1₃, hqP₃, hqK₃⟩ := hm₃
  have hc₁ := case4_of_msgat_F4 hMS c hYY hYpL hSL hodd1 hVp2 hVpS hVL hVS hY₁ hY₂ hY₁c hY₂c
    (Pof L α 1) ψ₁ q₁ hPL₁ hSLP₁ hSP₁ hmin₁ hYP₁ hψs₁ hψk₁ hq1₁ hqP₁ hqK₁
  have hc₃ := case4_of_msgat_F4 hMS c hYY hYpL hSL hodd1 hVp2 hVpS hVL hVS hY₁ hY₂ hY₁c hY₂c
    (Pof L α 3) ψ₃ q₃ hPL₃ hSLP₃ hSP₃ hmin₃ hYP₃ hψs₃ hψk₃ hq1₃ hqP₃ hqK₃
  exact chirality4 chiAPI h₁ h₃ hq₁ hq₃ hc₁ hc₃

theorem l4Four_holds_corr2_F4 (h113 : StageLemma14113) (h36 : Input15336One) (h51 : AsB51)
    (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (hMS : MS93.AS_C_1_34_corr_F4) : L4Four_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c17 hq
  obtain ⟨Y₁, Y₂, E⟩ := env4_of_ctx h113 h36 c c17 hq
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLIc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    S153D.pCoreOf_sup_R153_le hF hLIc hLq hRN
  have hVZ : VZ T M ≤ VL153 T V₁ Yp L := S153D.VZ_le_VL153 hh c.ctx hF hLIc hO

  obtain ⟨y₀, hy₀, z, hzZ, hy₀z⟩ := exists_moves_Z h113 hh
  have hzVp : z ∈ VL153 T V₁ Yp L := hVZ (hh.hyp.Z_le_VZ hzZ)
  have hzB : ∀ b ∈ Sgp153 T V₁ ⊓ L, b * z * b⁻¹ = z := by
    intro b hb
    have hbT : b ∈ T := (inf_le_left : Sgp153 T V₁ ≤ T) hb.1
    have := Subgroup.mem_centralizer_iff.mp (hh.hyp.T_le_centralizer_Z hbT) z hzZ
    calc b * z * b⁻¹ = z * b * b⁻¹ := by rw [← this]
      _ = z := by group
  have hzY : ∃ y ∈ Y₁ ⊔ Y₂, y * z * y⁻¹ ≠ z := ⟨y₀, E.Yp_Y hy₀, hy₀z⟩
  obtain ⟨hsplit, -, hkey, htri⟩ := vmain_G2 h51 hI16 hA8 E hzVp hzB hzY
  rcases hh.cases with hY | ⟨hU, hY⟩
  ·
    exfalso
    have hE : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := by
      rcases hF.struct_Yp with h | h
      · exact h
      · exfalso
        have h27 : Nat.card (OTwoQuot Yp) = 3 ^ 3 := h.2.1
        apply not_dvd_27_card_of_quot4 hq
        have h1 : Nat.card (OTwoQuot Yp) ∣ Nat.card Yp := Subgroup.card_quotient_dvd_card _
        have h2 : Nat.card Yp ∣ Nat.card L := Subgroup.card_dvd_of_le E.Yp_L
        rw [h27] at h1
        exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ h1.trans h2
    have hodd1 : ∀ y ∈ Yp, Odd (orderOf y) →
        (∀ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ = z) → y = 1 := fun y hy hodd hz =>
      odd_centralizes_Z_trivial h113 hh hY hE hy hodd hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact hy₀z (by group)
    have hZ := Z_eq_zpowers hh.hyp hzZ hz1
    have hfixZ : ∀ y : G, (y * z * y⁻¹ = z) →
        ∀ z' ∈ quasithinOmegaOneCenter T, y * z' * y⁻¹ = z' := by
      intro y hy z' hz'
      rw [hZ] at hz'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
      calc y * z ^ k * y⁻¹ = (y * z * y⁻¹) ^ k := by rw [conj_zpow]
        _ = z ^ k := by rw [hy]
    rcases htri with h1 | h2 | hms
    · obtain ⟨y, hy, hord⟩ := exists_order_three_of_card E.Y₁_card
      have := hodd1 y (E.Y₁_Yp hy) (by rw [hord]; decide) (hfixZ y (h1 y hy))
      rw [this, orderOf_one] at hord
      omega
    · obtain ⟨y, hy, hord⟩ := exists_order_three_of_card E.Y₂_card
      have := hodd1 y (E.Y₂_Yp hy) (by rw [hord]; decide) (hfixZ y (h2 y hy))
      rw [this, orderOf_one] at hord
      omega
    · have hRS : R153 T V₁ Yp ≤ Sgp153 T V₁ := by
        intro r hr
        have hr' := hF.R_eq ▸ hr
        refine ⟨hr'.1, ?_⟩
        have h1 : r ∈ Subgroup.centralizer (V₁ : Set G) :=
          Subgroup.centralizer_le hh.decomp.le₁ hr'.2
        exact Subgroup.centralizer_le_normalizer (V₁ : Set G) h1
      have hVpR : VL153 T V₁ Yp L ≤ R153 T V₁ Yp :=
        ((Subgroup.closure_le _).2 fun x hx => hx.1.1).trans hO
      have hVp2 : IsPGroup 2 ↥(VL153 T V₁ Yp L) := fun x =>
        ⟨1, Subtype.ext (by simpa using E.Vp_elem.2 x x.2)⟩
      exact ms_false_corr2_F4 hMS c hY E.Yp_L E.S_L hodd1 hVp2 (hVpR.trans hRS) E.L_N E.S_N E.Y₁_Yp
        E.Y₂_Yp E.Y₁_card E.Y₂_card hms
  ·
    refine ⟨⟨hU, hY⟩, ?_⟩
    have hV₁Vp : V₁ ≤ VL153 T V₁ Yp L := hh.decomp.le₁.trans hVZ
    have hYV₁ : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
      rw [hY]
      exact (oTwoUpper_le _).trans inf_le_right
    have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hh.hyp.qtfe.sylow.1.to_le inf_le_left
    have hVc : V₁ ≤ Subgroup.centralizer (L : Set G) :=
      closeV (fun a ha b hb => congrArg Subtype.val (E.Vp_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
        E.Vp_elem.2 E.L_N hS2 hsplit hkey hV₁Vp inf_le_right hYV₁ (sup_le E.Y₁_Yp E.Y₂_Yp) E.Yp_L
    exact Subgroup.le_centralizer_iff.mp hVc

end CFSG.Quasithin.SzC4
