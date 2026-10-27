module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2SetA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem fzc_sy2_rho_QW (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : Nat.card (twoCore t) = 2) :
    ∀ q ∈ fzR t x₁ x₂, rho * q * rho⁻¹ * q⁻¹ ∈ ctxW t x₁ x₂ → q ∈ ctxW t x₁ x₂ := by
  intro q hqR hc
  obtain ⟨f, hfZ, hf⟩ := hq.R_act_t q hqR
  have hfW : f ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right (S4A.pt_four_le_base x₁ x₂ hfZ)
  have htW := fzc_sy2_t_mem h
  have hrt := fzc_sy2_rho_t h
  have hrt' : rho⁻¹ * t * rho = t := by
    calc rho⁻¹ * t * rho = rho⁻¹ * (rho * t * rho⁻¹) * rho := by rw [hrt]
      _ = t := by group
  have h1 : (rho * q * rho⁻¹) * t * (rho * q * rho⁻¹)⁻¹ = t * f := by
    have hq1 : rho * q * rho⁻¹ = (rho * q * rho⁻¹ * q⁻¹) * q := by group
    rw [hq1]
    calc rho * q * rho⁻¹ * q⁻¹ * q * t * (rho * q * rho⁻¹ * q⁻¹ * q)⁻¹
        = (rho * q * rho⁻¹ * q⁻¹) * (q * t * q⁻¹) * (rho * q * rho⁻¹ * q⁻¹)⁻¹ := by group
      _ = (rho * q * rho⁻¹ * q⁻¹) * (t * f) * (rho * q * rho⁻¹ * q⁻¹)⁻¹ := by rw [hf]
      _ = t * f := by
        rw [fzc_sy2_W_comm h _ hc (t * f) (mul_mem htW hfW)]
        group
  have h2 : (rho * q * rho⁻¹) * t * (rho * q * rho⁻¹)⁻¹ = t * (rho * f * rho⁻¹) := by
    calc (rho * q * rho⁻¹) * t * (rho * q * rho⁻¹)⁻¹
        = rho * (q * (rho⁻¹ * t * rho) * q⁻¹) * rho⁻¹ := by group
      _ = rho * (t * f) * rho⁻¹ := by rw [hrt', hf]
      _ = (rho * t * rho⁻¹) * (rho * f * rho⁻¹) := by group
      _ = t * (rho * f * rho⁻¹) := by rw [hrt]
  have hfix : rho * f * rho⁻¹ = f := (mul_left_cancel (h1.symm.trans h2)).symm
  have hfC : f ∈ fzR t x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hq.W_le_R hfW, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc f * rho = rho * f * rho⁻¹ * rho := by rw [hfix]
      _ = rho * f := by group
  rw [hq.cent_R_rho] at hfC
  rcases fzc_sy2_twoCore_cases h hK f hfC with hf1 | hft
  · have hqt : q * t * q⁻¹ = t := by rw [hf, hf1, mul_one]
    have hmem : q ∈ fzR t x₁ x₂ ⊓ invCent t := by
      refine Subgroup.mem_inf.mpr ⟨hqR, ?_⟩
      show q ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc q * t = q * t * q⁻¹ * q := by group
        _ = t * q := by rw [hqt]
    rwa [hq.cent_R_t] at hmem
  · exfalso
    apply fzc_sy2_t_notin_E h
    rw [← hft]
    exact S4A.pt_four_le_base x₁ x₂ hfZ

theorem fzc_sy2_str (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : Nat.card (twoCore t) = 2) :
    FzCSy2Str t rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) (fzQ t x₁ x₂ rho) := by
  have hQR := hq.Q_eq
  have hW32 := fzc_sy2_card_W h hK
  refine
    { ZE := S4A.pt_four_le_base x₁ x₂
      EW := le_sup_right
      WQ := le_sup_left
      card_Z := (WreathRel.fourGrp_eq_omega h.wreath).2.2
      card_E := (h.wreath.baseGrp_eq).2.2
      card_W := hW32
      card_Q := ?_
      W_comm := fzc_sy2_W_comm h
      W_rank := fzc_sy2_W_rank h
      t_mem := fzc_sy2_t_mem h
      t_sq := fzc_sy2_t_sq h
      t_notin_E := fzc_sy2_t_notin_E h
      W_split := fzc_sy2_W_split h hK
      E_sq := fzc_sy2_E_sq h
      Z_sq := fun z hz => (WreathRel.fourGrp_eq_omega h.wreath).2.1.2 z hz
      Z_sqrt := fzc_sy2_Z_sqrt h
      E_invol := fzc_sy2_E_invol h
      Q_comm := ?_
      Q_sq := ?_
      Q_Z := ?_
      Q_t := ?_
      rho_ord := ?_
      rho_t := fzc_sy2_rho_t h
      rho_nrm_E := fzc_sy2_rho_nrm_E h
      rho_nrm_W := fzc_sy2_rho_nrm_W h
      rho_nrm_Q := ?_
      rho_Q := ?_
      rho_QW := ?_ }
  · rw [hQR, hq.card_R, hW32]
  · intro a ha b hb
    rw [hQR] at ha hb
    exact hq.R_comm_le_W (Subgroup.commutator_mem_commutator ha hb)
  · intro q hqQ
    rw [hQR] at hqQ
    rw [pow_two]
    exact hq.R_sq_mem_W q hqQ
  · intro q hqQ z hz
    rw [hQR] at hqQ
    rw [hq.R_cent_fourGrp q hqQ z hz]
    group
  · intro n hn hnW hnt
    rw [hQR] at hn
    apply hnW
    have hmem : n ∈ fzR t x₁ x₂ ⊓ invCent t := by
      refine Subgroup.mem_inf.mpr ⟨hn, ?_⟩
      show n ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [hnt]
    rwa [hq.cent_R_t] at hmem
  · have h1 := pow_orderOf_eq_one rho
    rwa [h.ord_rho] at h1
  · intro q hqQ
    rw [hQR] at hqQ ⊢
    exact hq.rho_norm_R q hqQ
  · intro q hqQ hfix
    rw [hQR] at hqQ
    have hmem : q ∈ fzR t x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hqQ, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc q * rho = rho * q * rho⁻¹ * rho := by rw [hfix]
        _ = rho * q := by group
    rw [hq.cent_R_rho] at hmem
    exact fzc_sy2_twoCore_cases h hK q hmem
  · intro q hqQ hc
    rw [hQR] at hqQ
    exact fzc_sy2_rho_QW h hq hK q hqQ hc

end CFSG.OddStandard.SmallF3.FritzII
