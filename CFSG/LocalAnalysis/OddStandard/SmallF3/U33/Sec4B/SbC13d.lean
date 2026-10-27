module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

private lemma mem_zpowers_eq_one_or_eq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

private lemma c13_tau_ne_one (hc : Ctx13A t L S x₁ x₂ lam rho tau om) : tau ≠ 1 :=
  fun h => hc.tau_not_mem (by rw [h]; exact Subgroup.one_mem _)

private lemma c13_om_ne_one (hc : Ctx13A t L S x₁ x₂ lam rho tau om) : om ≠ 1 :=
  fun h => hc.om_not_mem (by rw [h]; exact Subgroup.one_mem _)

private lemma c13_comm_om_tau (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    tau * om = om * tau := by
  have htauZ : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
      centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [hc.CO_center]
    exact Subgroup.mem_zpowers tau
  have hcent : tau ∈ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := htauZ.2
  exact (Subgroup.mem_centralizer_iff.mp hcent om hc.om_mem).symm

theorem c13_lam_data (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    lam ∈ ctxM t tau x₁ x₂ ∧ lam * lam = 1 ∧ lam * t = t * lam ∧ lam * tau = tau * lam ∧
      lam * rho * lam⁻¹ = rho⁻¹ ∧ lam ∉ ctxO t tau x₁ x₂ := by
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := (l12_rho_lam_mem_M hc).2
  have hlam2 : lam * lam = 1 := by
    have h := pow_orderOf_eq_one lam
    rw [hc.wreath.ord_lam] at h
    simpa [pow_two] using h
  have hlamL : lam ∈ L := by
    have hW : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    exact (Subgroup.mem_inf.mp (hc.inf_eq ▸ hW)).2
  have hlamt : lam * t = t * lam :=
    S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hlamL)
  exact ⟨hlamM, hlam2, hlamt, hc.tau_lam.symm, hc.lam_rho,
    (ctx8e_of_ctx11 hc).lam_not_mem_O⟩

theorem c13_sigma_data (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    lam * t ∈ ctxM t tau x₁ x₂ ∧ (lam * t) * (lam * t) = 1 ∧ (lam * t) * tau = tau * (lam * t) ∧
      (lam * t) * rho * (lam * t)⁻¹ = rho⁻¹ ∧ lam * t ∉ ctxO t tau x₁ x₂ := by
  obtain ⟨hlamM, hlam2, hlamt, hlamtau, hlamrho, hlamO⟩ := c13_lam_data hc
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htO : t ∈ ctxO t tau x₁ x₂ :=
    hc.R_le_O (hc.X_le_R (Subgroup.subset_closure (by simp)))
  have htM : t ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ htO
  have htrho : t * rho = rho * t :=
    (S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hc.rho_mem)).symm
  have httau : t * tau = tau * t :=
    (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  refine ⟨mul_mem hlamM htM, ?_, ?_, ?_, ?_⟩
  · calc (lam * t) * (lam * t) = lam * (t * lam) * t := by group
      _ = lam * (lam * t) * t := by rw [hlamt]
      _ = (lam * lam) * (t * t) := by group
      _ = 1 := by rw [hlam2, ht2, mul_one]
  · calc (lam * t) * tau = lam * (t * tau) := by group
      _ = lam * (tau * t) := by rw [httau]
      _ = tau * (lam * t) := by rw [← mul_assoc, hlamtau]; group
  · have h1 : (lam * t) * rho * (lam * t)⁻¹ = lam * (t * rho * t⁻¹) * lam⁻¹ := by group
    rw [h1]
    have htconj : t * rho * t⁻¹ = rho := by rw [htrho]; group
    rw [htconj, hlamrho]
  · intro hs
    apply hlamO
    have htinv : t⁻¹ ∈ ctxO t tau x₁ x₂ := (ctxO t tau x₁ x₂).inv_mem htO
    have hmem := (ctxO t tau x₁ x₂).mul_mem hs htinv
    have heq : (lam * t) * t⁻¹ = lam := by group
    rwa [heq] at hmem

theorem c13_tlam_conj (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ∃ h : G, h * t * h⁻¹ = lam * t := by
  obtain ⟨hlamM, hlam2, hlamt, -, -, -⟩ := c13_lam_data hc
  have hlamL : lam ∈ L := by
    have hW : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    exact (Subgroup.mem_inf.mp (hc.inf_eq ▸ hW)).2
  have hlam_ne : lam ≠ 1 := by
    intro h
    have h2 : orderOf lam = orderOf (1 : G) := by rw [h]
    rw [hc.wreath.ord_lam, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨c, hcL, hcz⟩ := hc.invol_L lam hlamL hlam2 hlam_ne
  have hct : c * t * c⁻¹ = t := by
    have hcomm : c * t = t * c := S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hcL)
    rw [hcomm]; group
  have htmem : t * (x₁ * x₂) ^ 2 ∈ conjIn (Subgroup.normalizer (S : Set G)) t := by
    rw [Ctx4.fusion_tz hc.toCtx10.toCtx4]
    exact ⟨(x₁ * x₂) ^ 2, Subgroup.mem_zpowers _, rfl⟩
  obtain ⟨n, _, hn⟩ := htmem
  refine ⟨c * n, ?_⟩
  have hmain : (c * n) * t * (c * n)⁻¹ = t * lam := by
    calc (c * n) * t * (c * n)⁻¹ = c * (n * t * n⁻¹) * c⁻¹ := by group
      _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [hn]
      _ = (c * t * c⁻¹) * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group
      _ = t * lam := by rw [hct, hcz]
  rw [hmain]
  exact hlamt.symm

theorem c13_lam_norm_CO (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ∀ g ∈ ctxCO t tau x₁ x₂ rho, lam * g * lam⁻¹ ∈ ctxCO t tau x₁ x₂ rho := by
  intro g hg
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := (l12_rho_lam_mem_M hc).2
  have hgO : g ∈ ctxO t tau x₁ x₂ := hg.1
  have hgcent : g * rho = rho * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
  refine Subgroup.mem_inf.mpr ⟨(p0_normal_O t tau x₁ x₂).2 lam hlamM g hgO, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : lam * (g * rho) * lam⁻¹ = lam * (rho * g) * lam⁻¹ := by rw [hgcent]
  have h2 : lam * (g * rho) * lam⁻¹ = (lam * g * lam⁻¹) * rho⁻¹ := by
    calc lam * (g * rho) * lam⁻¹ = (lam * g * lam⁻¹) * (lam * rho * lam⁻¹) := by group
      _ = (lam * g * lam⁻¹) * rho⁻¹ := by rw [hc.lam_rho]
  have h3 : lam * (rho * g) * lam⁻¹ = rho⁻¹ * (lam * g * lam⁻¹) := by
    calc lam * (rho * g) * lam⁻¹ = (lam * rho * lam⁻¹) * (lam * g * lam⁻¹) := by group
      _ = rho⁻¹ * (lam * g * lam⁻¹) := by rw [hc.lam_rho]
  have hw : (lam * g * lam⁻¹) * rho⁻¹ = rho⁻¹ * (lam * g * lam⁻¹) := by
    rw [← h2, ← h3, hconj]
  have hw_inv : rho * (lam * g * lam⁻¹)⁻¹ = (lam * g * lam⁻¹)⁻¹ * rho := by
    have := congrArg Inv.inv hw
    simpa [mul_inv_rev] using this
  have h1 : rho = (lam * g * lam⁻¹)⁻¹ * rho * (lam * g * lam⁻¹) := by
    have := congrArg (fun u => u * (lam * g * lam⁻¹)) hw_inv
    simpa [mul_assoc] using this
  calc (lam * g * lam⁻¹) * rho
      = (lam * g * lam⁻¹) * ((lam * g * lam⁻¹)⁻¹ * rho * (lam * g * lam⁻¹)) := by rw [← h1]
    _ = rho * (lam * g * lam⁻¹) := by group

theorem c13_CO_coset (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    ∀ x ∈ ctxCO t tau x₁ x₂ rho,
      x ∈ closure ({t, tau} : Set G) ∨ ∃ s ∈ closure ({t, tau} : Set G), x = s * om := by
  intro x hx
  by_cases hxN : x ∈ closure ({t, tau} : Set G)
  · exact Or.inl hxN
  · right
    have htauCO : tau ∈ ctxCO t tau x₁ x₂ rho :=
      ⟨(c13_mem_O hc).2.1,
        Subgroup.mem_centralizer_singleton_iff.mpr (c13_tau_data hc).2.2⟩
    have htCO : t ∈ ctxCO t tau x₁ x₂ rho :=
      ⟨(c13_mem_O hc).1,
        Subgroup.mem_centralizer_singleton_iff.mpr (c13_t_data hc).2.2⟩
    have hNle : closure ({t, tau} : Set G) ≤ ctxCO t tau x₁ x₂ rho := by
      rw [Subgroup.closure_le]
      rintro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact htCO
      · exact htauCO
    have hcardN : Nat.card ↥(closure ({t, tau} : Set G)) = 4 :=
      (Ctx4.centralizer_t_tau hc.toCtx11.toCtx10.toCtx4).2.2.1
    have hcardCO : Nat.card ↥(ctxCO t tau x₁ x₂ rho) = 8 := by
      obtain ⟨e⟩ := hc.CO_dihedral
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hrel : (closure ({t, tau} : Set G)).relIndex (ctxCO t tau x₁ x₂ rho) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := closure ({t, tau} : Set G))
        (K := ctxCO t tau x₁ x₂ rho)
      rw [inf_eq_left.mpr hNle, hcardN, hcardCO] at h
      omega
    have hidx : ((closure ({t, tau} : Set G)).subgroupOf (ctxCO t tau x₁ x₂ rho)).index = 2 :=
      hrel
    have hmul : (⟨x, hx⟩ : ↥(ctxCO t tau x₁ x₂ rho)) * ⟨om, hc.om_mem⟩ ∈
        (closure ({t, tau} : Set G)).subgroupOf (ctxCO t tau x₁ x₂ rho) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp [hxN, hc.om_not_mem]
    refine ⟨x * om, ?_, ?_⟩
    · simpa using (Subgroup.mem_subgroupOf.mp hmul)
    · rw [mul_assoc, hc.om_sq, mul_one]

theorem c13_lam_om_cases (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    lam * om * lam⁻¹ = om ∨ lam * om * lam⁻¹ = om * tau := by
  set w : G := lam * om * lam⁻¹ with hwdef
  have hwCO : w ∈ ctxCO t tau x₁ x₂ rho := c13_lam_norm_CO hc.toCtx11 om hc.om_mem
  have hw2 : w * w = 1 := by
    rw [hwdef]
    calc (lam * om * lam⁻¹) * (lam * om * lam⁻¹) = lam * (om * om) * lam⁻¹ := by group
      _ = 1 := by rw [hc.om_sq]; group
  have hlam_central : closure ({t, tau} : Set G) ≤ centralizer ({lam} : Set G) := by
    rw [Subgroup.closure_le]
    rintro n (hn : n ∈ ({t, tau} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (c13_lam_data hc.toCtx11).2.2.1.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (c13_lam_data hc.toCtx11).2.2.2.1.symm
  have hwN : w ∉ closure ({t, tau} : Set G) := by
    intro hwin
    apply hc.om_not_mem
    have hcomm_w : w * lam = lam * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (hlam_central hwin)
    have hfix : lam * w * lam⁻¹ = w := by rw [← hcomm_w]; group
    have hconj_eq : lam⁻¹ * w * lam = w := by
      calc lam⁻¹ * w * lam = lam⁻¹ * (lam * w * lam⁻¹) * lam := by rw [hfix]
        _ = w := by group
    have heq : lam⁻¹ * w * lam = om := by rw [hwdef]; group
    rw [← heq, hconj_eq]
    exact hwin
  rcases c13_CO_coset hc w hwCO with hwin | ⟨s, hsN, hws⟩
  · exact absurd hwin hwN
  · have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
    have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
    have httau : t * tau = tau * t :=
      (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
    have hcm : om * t = t * tau * om := by
      have h := congrArg (fun u => u * om) hc.t_om
      simpa [mul_assoc] using h
    have hconj_t : om * t * om = t * tau := by
      have hinv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hc.om_sq
      simpa [hinv] using hc.t_om
    have hconj_tau : om * tau * om = tau := by
      rw [← c13_comm_om_tau hc, mul_assoc, hc.om_sq, mul_one]
    have hom_conj : om * (t * tau) * om = t := by
      have e1 : om * (t * tau) * om = (om * t) * (tau * om) := by group
      have e2 : (om * t) * (tau * om) = (om * t) * (om * tau) := by
        rw [c13_comm_om_tau hc]
      have e3 : (om * t) * (om * tau) = (om * t * om) * tau := by group
      calc om * (t * tau) * om = (om * t) * (tau * om) := e1
        _ = (om * t) * (om * tau) := e2
        _ = (om * t * om) * tau := e3
        _ = (t * tau) * tau := by rw [hconj_t]
        _ = t := by rw [mul_assoc, htau2, mul_one]
    have hsq_t : (t * om) * (t * om) = tau := by
      calc (t * om) * (t * om) = t * (om * t) * om := by group
        _ = t * (t * tau * om) * om := by rw [hcm]
        _ = (t * t) * tau * (om * om) := by group
        _ = tau := by rw [ht2, hc.om_sq, one_mul, mul_one]
    have hsq_ttau : ((t * tau) * om) * ((t * tau) * om) = tau := by
      have e1 : ((t * tau) * om) * ((t * tau) * om) =
          (t * tau) * (om * (t * tau) * om) := by group
      calc ((t * tau) * om) * ((t * tau) * om) = (t * tau) * (om * (t * tau) * om) := e1
        _ = (t * tau) * t := by rw [hom_conj]
        _ = t * (tau * t) := by group
        _ = t * (t * tau) := by rw [← httau]
        _ = (t * t) * tau := by rw [← mul_assoc]
        _ = tau := by rw [ht2, one_mul]
    rcases (mem_closure_pair_of_invol ht2 htau2 httau).mp hsN with hs1 | hs2 | hs3 | hs4
    · left; rw [hws, hs1]; simp
    · exfalso
      have hws' : w = t * om := by rw [hws, hs2]
      have hsq : (t * om) * (t * om) = 1 := by rw [← hws']; exact hw2
      rw [hsq_t] at hsq
      exact c13_tau_ne_one hc hsq
    · right; rw [hws, hs3]; exact c13_comm_om_tau hc
    · exfalso
      have hws' : w = (t * tau) * om := by rw [hws, hs4]
      have hsq : ((t * tau) * om) * ((t * tau) * om) = 1 := by rw [← hws']; exact hw2
      rw [hsq_ttau] at hsq
      exact c13_tau_ne_one hc hsq

theorem c13_CY_sigma_card (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    4 ≤ Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) := by
  have hsig := c13_sigma_data hc.toCtx11
  have hle := card_le_sq_card_centralizer (A := ctxYq t tau x₁ x₂ rho) hc.Y_elem hsig.2.1
    (fun a ha => hc.normal_Y.2 (lam * t) hsig.1 a ha)
  rw [card_ctxYq hc.q_iso] at hle
  by_contra h
  have hC : Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ≤ 3 := by
    omega
  have hsq : Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ^ 2 ≤ 9 := by
    have := Nat.pow_le_pow_left hC 2
    norm_num at this
    exact this
  omega

theorem c13_A2 (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (closure ({tau, om} : Set G)) ∧
      Nat.card ↥(closure ({tau, om} : Set G)) = 4 ∧
      closure ({tau, om} : Set G) ≤ ctxCO t tau x₁ x₂ rho ∧
      ∀ g ∈ closure ({tau, om} : Set G), ∀ a ∈ ctxYq t tau x₁ x₂ rho, g * a = a * g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : tau * om = om * tau := c13_comm_om_tau hc.toCtx13A
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have hom2 : om * om = 1 := hc.om_sq
  have hE : zpowers tau ⊔ zpowers om = closure ({tau, om} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have hElem : CFSG.Open.IsElemAbelian 2 (closure ({tau, om} : Set G)) := by
    rw [← hE]
    refine isElemAbelian_sup (isElemAbelian_zpowers htau2) (isElemAbelian_zpowers hom2) ?_
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Commute.zpow_zpow hcomm m n
  have hcard : Nat.card ↥(closure ({tau, om} : Set G)) = 4 := by
    rw [← hE]
    have htau_ne : tau ≠ 1 := c13_tau_ne_one hc.toCtx13A
    have hom_ne : om ≠ 1 := c13_om_ne_one hc.toCtx13A
    have htau_ne_om : tau ≠ om := by
      intro h
      apply hc.om_not_mem
      rw [← h]
      exact Subgroup.subset_closure (by simp)
    have hinf : zpowers tau ⊓ zpowers om = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      obtain ⟨hxH, hxK⟩ := Subgroup.mem_inf.mp hx
      rcases mem_zpowers_eq_one_or_eq htau2 hxH with h1 | h1
      · exact h1
      · rcases mem_zpowers_eq_one_or_eq hom2 hxK with h2 | h2
        · exact absurd (h1.symm.trans h2) htau_ne
        · exact absurd (h1.symm.trans h2) htau_ne_om
    have hK : ∀ k ∈ zpowers om, ∀ h ∈ zpowers tau, k * h * k⁻¹ ∈ zpowers tau := by
      intro k hk h hh
      have hkh : k * h = h * k := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact Commute.zpow_zpow hcomm.symm m n
      rw [hkh]
      simpa [mul_assoc] using hh
    rw [card_sup_eq_mul hK hinf, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime hc.l44.1 htau_ne,
      orderOf_eq_prime (by rw [pow_two]; exact hom2) hom_ne]
  have hleCO : closure ({tau, om} : Set G) ≤ ctxCO t tau x₁ x₂ rho := by
    have htauCO : tau ∈ ctxCO t tau x₁ x₂ rho :=
      ⟨(c13_mem_O hc.toCtx13A).2.1,
        Subgroup.mem_centralizer_singleton_iff.mpr (c13_tau_data hc.toCtx13A).2.2⟩
    rw [Subgroup.closure_le]
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact htauCO
    · exact hc.om_mem
  refine ⟨hElem, hcard, hleCO, ?_⟩
  have hcent : closure ({tau, om} : Set G) ≤
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr (fun a ha => (hc.tau_cent_Y a ha).symm)
    · exact Subgroup.mem_centralizer_iff.mpr (fun a ha => (hc.om_cent_Y a ha).symm)
  intro g hg a ha
  exact (Subgroup.mem_centralizer_iff.mp (hcent hg) a ha).symm

theorem c13_sigma_om (hc : Ctx13A t L S x₁ x₂ lam rho tau om)
    (h : lam * om * lam⁻¹ = om * tau) : (lam * t) * om = om * (lam * t) := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht_om_t : t * om * t⁻¹ = om * tau := by
    have h' : om * t = t * tau * om := by
      have hc' := congrArg (fun u => u * om) hc.t_om
      simpa [mul_assoc] using hc'
    calc t * om * t⁻¹ = t * (om * t) := by rw [htinv]; group
      _ = t * (t * tau * om) := by rw [h']
      _ = tau * om := by rw [← mul_assoc, ← mul_assoc, ht2, one_mul]
      _ = om * tau := c13_comm_om_tau hc
  have hlam_conj : (lam * t) * om * (lam * t)⁻¹ = om := by
    have h1 : (lam * t) * om * (lam * t)⁻¹ = lam * (t * om * t⁻¹) * lam⁻¹ := by group
    rw [h1, ht_om_t]
    have h2 : lam * (om * tau) * lam⁻¹ = (lam * om * lam⁻¹) * (lam * tau * lam⁻¹) := by
      group
    rw [h2, h]
    have h3 : lam * tau * lam⁻¹ = tau := by
      rw [(c13_lam_data hc.toCtx11).2.2.2.1]; group
    rw [h3, mul_assoc, htau2, mul_one]
  calc (lam * t) * om = ((lam * t) * om * (lam * t)⁻¹) * (lam * t) := by group
    _ = om * (lam * t) := by rw [hlam_conj]

theorem c13_E32 (hc : Ctx13C t L S x₁ x₂ lam rho tau om)
    (h : lam * om * lam⁻¹ = om * tau) :
    ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A ∧ A ≤ centralizer ({lam * t} : Set G) ∧
      32 ≤ Nat.card A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsig := c13_sigma_data hc.toCtx11
  have hA2data := c13_A2 hc
  have hsigmatau : (lam * t) * tau = tau * (lam * t) := hsig.2.2.1
  have hsigmaom : (lam * t) * om = om * (lam * t) := c13_sigma_om hc.toCtx13A h
  let A₁ : Subgroup G := ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)
  let A₂ : Subgroup G := closure ({tau, om} : Set G)
  let A₃ : Subgroup G := zpowers (lam * t)
  have hA1elem : CFSG.Open.IsElemAbelian 2 A₁ := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro x y
      apply Subtype.ext
      exact hc.Y_elem.comm (Subgroup.mem_inf.mp x.2).1 (Subgroup.mem_inf.mp y.2).1
    · intro x hx
      exact ((mem_ctxYq_iff hc.q_iso x).mp (Subgroup.mem_inf.mp hx).1).2
  have hA1ge : 4 ≤ Nat.card A₁ := c13_CY_sigma_card hc.toCtx13B
  have hA2elem : CFSG.Open.IsElemAbelian 2 A₂ := hA2data.1
  have hA2card : Nat.card A₂ = 4 := hA2data.2.1
  have hA2centY : ∀ k ∈ A₂, ∀ a ∈ ctxYq t tau x₁ x₂ rho, k * a = a * k := hA2data.2.2.2
  have hA2leCO : A₂ ≤ ctxCO t tau x₁ x₂ rho := hA2data.2.2.1
  have hA2cent_sigma : A₂ ≤ centralizer ({lam * t} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hsigmatau.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hsigmaom.symm
  have hsig_ne : lam * t ≠ 1 :=
    fun h1 => hsig.2.2.2.2 (by rw [h1]; exact Subgroup.one_mem _)
  have hA3elem : CFSG.Open.IsElemAbelian 2 A₃ := isElemAbelian_zpowers hsig.2.1
  have hA3card : Nat.card A₃ = 2 := by
    rw [show A₃ = zpowers (lam * t) from rfl, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hsig.2.1) hsig_ne
  have hcomm12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    exact (hA2centY b hb a (Subgroup.mem_inf.mp ha).1).symm
  have hK12 : ∀ k ∈ A₂, ∀ a ∈ A₁, k * a * k⁻¹ ∈ A₁ := by
    intro k hk a ha
    rw [← hcomm12 a ha k hk]
    simpa [mul_assoc] using ha
  have hinf12 : A₁ ⊓ A₂ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxA1, hxA2⟩ := Subgroup.mem_inf.mp hx
    have hxQ : x ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ (Subgroup.mem_inf.mp hxA1).1
    have hxcent : x ∈ centralizer ({rho} : Set G) := (Subgroup.mem_inf.mp (hA2leCO hxA2)).2
    exact l12_cent_Q_rho hc.toCtx11 x hxQ
      (Subgroup.mem_centralizer_singleton_iff.mp hxcent)
  have hcard12 : Nat.card ↥(A₁ ⊔ A₂) = Nat.card A₁ * Nat.card A₂ :=
    card_sup_eq_mul hK12 hinf12
  have hA12O : A₁ ⊔ A₂ ≤ ctxO t tau x₁ x₂ := by
    refine sup_le ?_ (hA2leCO.trans inf_le_left)
    exact inf_le_left.trans (ctxYq_le_ctxQ.trans ((l12_Q_le_R hc.toCtx11).trans hc.R_le_O))
  have hsup12cent : A₁ ⊔ A₂ ≤ centralizer ({lam * t} : Set G) :=
    sup_le inf_le_right hA2cent_sigma
  have hA3cent : A₃ ≤ centralizer ({lam * t} : Set G) := by
    rw [show A₃ = zpowers (lam * t) from rfl]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcen_eq : centralizer ({lam * t} : Set G) =
      centralizer ((A₃ : Subgroup G) : Set G) := by
    show centralizer ({lam * t} : Set G) =
      centralizer ((zpowers (lam * t) : Subgroup G) : Set G)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcomm123 : ∀ a ∈ A₁ ⊔ A₂, ∀ b ∈ A₃, a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ centralizer ((A₃ : Subgroup G) : Set G) := hcen_eq ▸ hsup12cent ha
    exact (Subgroup.mem_centralizer_iff.mp ha' b hb).symm
  have hK123 : ∀ k ∈ A₃, ∀ a ∈ A₁ ⊔ A₂, k * a * k⁻¹ ∈ A₁ ⊔ A₂ := by
    intro k hk a ha
    rw [← hcomm123 a ha k hk]
    simpa [mul_assoc] using ha
  have hinf123 : (A₁ ⊔ A₂) ⊓ A₃ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hx12, hx3⟩ := Subgroup.mem_inf.mp hx
    have hxO : x ∈ ctxO t tau x₁ x₂ := hA12O hx12
    rcases mem_zpowers_eq_one_or_eq hsig.2.1 hx3 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxO) hsig.2.2.2.2
  have hcard123 : Nat.card ↥(A₁ ⊔ A₂ ⊔ A₃) = Nat.card ↥(A₁ ⊔ A₂) * Nat.card A₃ :=
    card_sup_eq_mul hK123 hinf123
  refine ⟨A₁ ⊔ A₂ ⊔ A₃, ?_, ?_, ?_⟩
  · exact isElemAbelian_sup (isElemAbelian_sup hA1elem hA2elem hcomm12) hA3elem hcomm123
  · exact sup_le hsup12cent hA3cent
  · calc 32 = 4 * 4 * 2 := by norm_num
      _ ≤ Nat.card A₁ * Nat.card A₂ * Nat.card A₃ :=
          Nat.mul_le_mul (Nat.mul_le_mul hA1ge hA2card.ge) hA3card.ge
      _ = Nat.card ↥(A₁ ⊔ A₂) * Nat.card A₃ := by rw [hcard12]
      _ = Nat.card ↥(A₁ ⊔ A₂ ⊔ A₃) := hcard123.symm

theorem c13_lam_om (hc : Ctx13C t L S x₁ x₂ lam rho tau om) : lam * om * lam⁻¹ = om := by
  rcases c13_lam_om_cases hc.toCtx13A with h | h
  · exact h
  · obtain ⟨A, hAe, hAc, hA32⟩ := c13_E32 hc h
    obtain ⟨g, hg⟩ := c13_tlam_conj hc.toCtx11
    have hAc' : A ≤ centralizer ({g * t * g⁻¹} : Set G) := by
      rw [hg]
      exact hAc
    have hle := c17_card_elemAbelian_conj_le hc.toCtx11.toCtx10 g hAc' hAe
    omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
