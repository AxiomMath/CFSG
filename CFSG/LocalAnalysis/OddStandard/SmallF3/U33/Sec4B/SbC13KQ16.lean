module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13K0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16g

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}


theorem c13K_om_mem_M (hc : Ctx13M t L S x₁ x₂ lam rho tau om) : om ∈ ctxM t tau x₁ x₂ := by
  have hCO : om ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_eq]
    exact Subgroup.subset_closure (by simp)
  have hOle : ctxO t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
    unfold ctxO CFSG.Open.pCoreOf
    exact Subgroup.map_subtype_le _
  exact hOle (Subgroup.mem_inf.mp hCO).1

theorem c13K_tau_mem_M (hc : Ctx13M t L S x₁ x₂ lam rho tau om) : tau ∈ ctxM t tau x₁ x₂ := by
  exact Subgroup.le_normalizer (Subgroup.subset_closure (by simp))

theorem c13K_QQ_le_M (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) ≤ ctxM t tau x₁ x₂ := by
  refine sup_le hc.normal_Q.1 ((Subgroup.closure_le (K := ctxM t tau x₁ x₂)).mpr ?_)
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact c13K_tau_mem_M hc
  · exact c13K_om_mem_M hc

theorem c13K_tau_mem_QQ (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    tau ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem c13K_om_mem_QQ (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    om ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem c13K_normal_Q_QQ (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G), ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      g * q * g⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  intro g hg q hq
  exact hc.normal_Q.2 g (c13K_QQ_le_M hc hg) q hq

theorem c13K_om_not_mem_Q (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    om ∉ ctxQ t tau x₁ x₂ rho := by
  intro hom
  have hQleY : ctxQ t tau x₁ x₂ rho ≤ ctxYq t tau x₁ x₂ rho := by
    intro a ha
    have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({om} : Set G) :=
      Subgroup.mem_inf.mpr
        ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr (IsZ4Z4E4.comm hc.q_iso ha hom)⟩
    rwa [hc.Q_om.2.2.2.1] at hmem
  have hcard := Subgroup.card_le_of_le hQleY
  rw [IsZ4Z4E4.card hc.q_iso, card_ctxYq hc.q_iso] at hcard
  omega

theorem c13K_omtau_not_mem_Q (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    om * tau ∉ ctxQ t tau x₁ x₂ rho := by
  intro hom
  have hQleY : ctxQ t tau x₁ x₂ rho ≤ ctxYq t tau x₁ x₂ rho := by
    intro a ha
    have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({om * tau} : Set G) :=
      Subgroup.mem_inf.mpr
        ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr (IsZ4Z4E4.comm hc.q_iso ha hom)⟩
    rwa [hc.Q_omtau.2.2.2.1] at hmem
  have hcard := Subgroup.card_le_of_le hQleY
  rw [IsZ4Z4E4.card hc.q_iso, card_ctxYq hc.q_iso] at hcard
  omega

theorem c13K_comm_om_mem_Y (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : om * q * om⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  have hd : q * om * q⁻¹ * om⁻¹ ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ := by
    have h := Subgroup.commutator_mem_commutator (H₁ := ctxQ t tau x₁ x₂ rho)
      (H₂ := zpowers om) hq (Subgroup.mem_zpowers om)
    simpa [commutatorElement_def] using h
  have hcmem : om * q * om⁻¹ * q⁻¹ ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ := by
    have heq : om * q * om⁻¹ * q⁻¹ = (q * om * q⁻¹ * om⁻¹)⁻¹ := by group
    rw [heq]
    exact (⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆).inv_mem hd
  have hc2 : (om * q * om⁻¹ * q⁻¹) ^ 2 = 1 := hc.Q_om.1.2 _ hcmem
  have hcQ : om * q * om⁻¹ * q⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    (ctxQ t tau x₁ x₂ rho).mul_mem (hc.normal_Q.2 om (c13K_om_mem_M hc) q hq)
      ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
  exact (mem_ctxYq_iff hc.q_iso _).mpr ⟨hcQ, hc2⟩

theorem c13K_invol_om (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) (hsq : (om * q) ^ 2 = 1) : q ∈ ctxYq t tau x₁ x₂ rho := by
  have hmem : om * q ∈ InvIn (om • (ctxQ t tau x₁ x₂ rho : Set G)) := by
    refine ⟨?_, hsq, ?_⟩
    · rw [Set.mem_smul_set]
      exact ⟨q, hq, by rw [smul_eq_mul]⟩
    · intro h1
      have homq : om = q⁻¹ := by
        have h : om = om * q * q⁻¹ := by group
        rw [h1, one_mul] at h
        exact h
      exact c13K_om_not_mem_Q hc (homq.symm ▸ (ctxQ t tau x₁ x₂ rho).inv_mem hq)
  have hmemY : om * q ∈ om • (ctxYq t tau x₁ x₂ rho : Set G) := by
    rw [← hc.Q_om.2.2.2.2]
    exact hmem
  obtain ⟨y, hy, hxy⟩ := Set.mem_smul_set.mp hmemY
  rw [smul_eq_mul] at hxy
  exact (mul_left_cancel hxy) ▸ hy

theorem c13K_invol_omtau (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) (hsq : (om * tau * q) ^ 2 = 1) :
    q ∈ ctxYq t tau x₁ x₂ rho := by
  have hmem : om * tau * q ∈ InvIn ((om * tau) • (ctxQ t tau x₁ x₂ rho : Set G)) := by
    refine ⟨?_, hsq, ?_⟩
    · rw [Set.mem_smul_set]
      exact ⟨q, hq, by rw [smul_eq_mul]⟩
    · intro h1
      have homq : om * tau = q⁻¹ := by
        have h : om * tau = om * tau * q * q⁻¹ := by group
        rw [h1, one_mul] at h
        exact h
      exact c13K_omtau_not_mem_Q hc (homq.symm ▸ (ctxQ t tau x₁ x₂ rho).inv_mem hq)
  have hmemY : om * tau * q ∈ (om * tau) • (ctxYq t tau x₁ x₂ rho : Set G) := by
    rw [← hc.Q_omtau.2.2.2.2]
    exact hmem
  obtain ⟨y, hy, hxy⟩ := Set.mem_smul_set.mp hmemY
  rw [smul_eq_mul] at hxy
  exact (mul_left_cancel hxy) ▸ hy

theorem c13K_setting16 (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Setting16
      ((ctxQ t tau x₁ x₂ rho).subgroupOf (ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)))
      ((ctxYq t tau x₁ x₂ rho).subgroupOf (ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)))
      (⟨tau, c13K_tau_mem_QQ hc⟩ : ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)))
      ⟨om, c13K_om_mem_QQ hc⟩ := by
  obtain ⟨_, _, hom2, htau2, _, _, hτω, _⟩ := c13K_rel hc
  refine Setting16.of_subgroupOf (Q := ctxQ t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    (𝒬 := ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) (τ := tau) (ω := om) rfl
    (c13K_tau_mem_QQ hc) (c13K_om_mem_QQ hc) (c13K_normal_Q_QQ hc)
    (fun a ha b hb => IsZ4Z4E4.comm hc.q_iso ha hb) (mem_ctxYq_iff hc.q_iso)
    (IsZ4Z4E4.card hc.q_iso) (card_ctxYq hc.q_iso) (IsZ4Z4E4.exists_sq_ne_one hc.q_iso)
    htau2 hom2 hτω hc.tau_inv_Q hc.om_cent_Y (fun q hq => c13K_comm_om_mem_Y hc hq) ?_ ?_
    (fun q hq h => c13K_invol_om hc hq h) (fun q hq h => c13K_invol_omtau hc hq h)
  · intro a ha hcomm
    have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({om} : Set G) :=
      Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rwa [hc.Q_om.2.2.2.1] at hmem
  · intro a ha hcomm
    have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({om * tau} : Set G) :=
      Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rwa [hc.Q_omtau.2.2.2.1] at hmem

theorem c13K_lemma4_16 (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Lemma4_16Concl t tau x₁ x₂ rho om := by
  let 𝒬 : Subgroup G := ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)
  let Q0 : Subgroup ↥𝒬 := (ctxQ t tau x₁ x₂ rho).subgroupOf 𝒬
  let Y0 : Subgroup ↥𝒬 := (ctxYq t tau x₁ x₂ rho).subgroupOf 𝒬
  let τ0 : ↥𝒬 := ⟨tau, c13K_tau_mem_QQ hc⟩
  let ω0 : ↥𝒬 := ⟨om, c13K_om_mem_QQ hc⟩
  have hs : Setting16 Q0 Y0 τ0 ω0 := c13K_setting16 hc
  have hQle : ctxQ t tau x₁ x₂ rho ≤ 𝒬 := le_sup_left
  have hYle : ctxYq t tau x₁ x₂ rho ≤ 𝒬 := ctxYq_le_ctxQ.trans le_sup_left
  have hQ0map : Q0.map 𝒬.subtype = ctxQ t tau x₁ x₂ rho :=
    Subgroup.map_subgroupOf_eq_of_le hQle
  have hY0map : Y0.map 𝒬.subtype = ctxYq t tau x₁ x₂ rho :=
    Subgroup.map_subgroupOf_eq_of_le hYle
  have hτ : 𝒬.subtype τ0 = tau := rfl
  have hω : 𝒬.subtype ω0 = om := rfl
  have himg : 𝒬.subtype '' ({τ0, ω0} : Set ↥𝒬) = ({tau, om} : Set G) := by
    rw [Set.image_pair, hτ, hω]
  have hQ0τmap : (Q0 ⊔ zpowers τ0).map 𝒬.subtype = ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    rw [Subgroup.map_sup, hQ0map, MonoidHom.map_zpowers, hτ]
  have hE6map : (closure ({τ0, ω0} : Set ↥𝒬) ⊔ Y0).map 𝒬.subtype =
      closure ({tau, om} : Set G) ⊔ ctxYq t tau x₁ x₂ rho := by
    rw [Subgroup.map_sup, MonoidHom.map_closure, himg, hY0map]
  have hτYmap : (zpowers τ0 ⊔ Y0).map 𝒬.subtype = zpowers tau ⊔ ctxYq t tau x₁ x₂ rho := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hτ, hY0map]
  unfold Lemma4_16Concl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact charIn_of_map hYle hY0map hs.char_Y
  · exact charIn_of_map hQle hQ0map hs.char_Q
  · refine charIn_of_map (A₀ := Q0 ⊔ zpowers τ0) ?_ hQ0τmap hs.char_Qtau
    exact sup_le hQle (Subgroup.zpowers_le.mpr (c13K_tau_mem_QQ hc))
  · refine charIn_of_map (A₀ := closure ({τ0, ω0} : Set ↥𝒬) ⊔ Y0) ?_ hE6map hs.char_E6
    refine sup_le ?_ hYle
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact c13K_tau_mem_QQ hc
    · exact c13K_om_mem_QQ hc
  · refine charIn_of_map (A₀ := zpowers τ0 ⊔ Y0) ?_ hτYmap hs.char_tauY
    exact sup_le (Subgroup.zpowers_le.mpr (c13K_tau_mem_QQ hc)) hYle

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
