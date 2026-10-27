module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeX

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] {E : Subgroup G} {t z : G}

abbrev CocodeXOf (hm : M24Out G E t) (hz : IsZ E t z) : Prop :=
  @CocodeX ↥E (commGroupOfM24Out hm) (finite_E_of_m24Out hm) (S44.XE E) ⟨t, hm.t_mem⟩ ⟨z, hz.1⟩

namespace CocodeToData

variable (hm : M24Out G E t) (hz : IsZ E t z)

theorem card_Ctz (h : CocodeXOf hm hz) :
    Nat.card ↥(CNz E z ⊓ centralizer ({t} : Set G)) = 2 ^ 19 * 3 * 5 := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  rw [CNz_inf_centralizer_eq_preS hm hm.t_mem hz.1, card_preS hm (inf_le_left.trans inf_le_left),
    h.card_Ctz]
  norm_num

theorem card_NV (h : CocodeXOf hm hz) : Nat.card ↥(Nrm E ⊓ Jg t z) = 2 ^ 20 * 3 * 5 := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  rw [Nrm_inf_Jg_eq_preS hm hm.t_mem hz.1, card_preS hm inf_le_left, h.card_NV]
  norm_num

theorem swap (h : CocodeXOf hm hz) : ∃ y ∈ Nrm E ⊓ Jg t z, y * t * y⁻¹ = t * z := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  obtain ⟨g, hg, hgt⟩ := h.swap
  obtain ⟨y, hy, rfl⟩ := exists_mem_preS_actN inf_le_left hg
  refine ⟨y, ?_, ?_⟩
  · rw [Nrm_inf_Jg_eq_preS hm hm.t_mem hz.1]
    exact hy
  · exact congrArg Subtype.val hgt

theorem card_P (h : CocodeXOf hm hz) : Nat.card ↥(Pg E z) = 2 ^ 17 := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  rw [card_Pg hm hz.1, h.card_P]
  norm_num

theorem O2_NV (h : CocodeXOf hm hz) : TwoFi22.O2In (Nrm E ⊓ Jg t z) = Pg E z := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  rw [O2In_Nrm_inf_Jg_eq_preS hm hm.t_mem hz.1, Pg_eq_preS hm hz.1, h.O2_NV]

theorem card_O23 (h : CocodeXOf hm hz) :
    Nat.card ↥(TwoFi22.O23In (CNz E z)) = 3 * 2 ^ 17 := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  rw [card_O23In_CNz hm hz.1, h.card_O23]
  norm_num

theorem exists_perfect (h : CocodeXOf hm hz) :
    ∃ Y : Subgroup G, Y ≤ CNz E z ∧ ⁅Y, Y⁆ = Y ∧ Nat.card ↥Y = 2 ^ 20 * 3 ^ 3 * 5 := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  obtain ⟨Y, hYle, hY1, hY2, hYc⟩ := h.exists_perfect
  have hYX : Y ≤ S44.XE E := hYle.trans inf_le_left
  refine ⟨preS Y, ?_, commutator_preS_eq_of hm hYX hY1 hY2, ?_⟩
  · rw [CNz_eq_preS hm hz.1]
    exact preS_mono hYle
  · rw [card_preS hm hYX, hYc]
    norm_num

theorem P_comm (h : CocodeXOf hm hz) : ∀ a ∈ Pg E z, ∀ b ∈ Pg E z, a * b * a⁻¹ * b⁻¹ ∈ E := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro a ha b hb
  rw [Pg_eq_preS hm hz.1] at ha hb
  obtain ⟨haN, haT⟩ := mem_preS.1 ha
  obtain ⟨hbN, hbT⟩ := mem_preS.1 hb
  exact (commutator_mem_E_iff hm.centralizer_eq haN hbN).2 (h.P_comm _ haT _ hbT)

theorem P_sq (h : CocodeXOf hm hz) : ∀ a ∈ Pg E z, a ^ 2 ∈ E := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro a ha
  rw [Pg_eq_preS hm hz.1] at ha
  obtain ⟨haN, haT⟩ := mem_preS.1 ha
  exact (pow_mem_E_iff hm.centralizer_eq haN 2).2 (h.P_sq _ haT)

theorem r_fpf (h : CocodeXOf hm hz) :
    ∀ r ∈ TwoFi22.O23In (CNz E z), orderOf r = 3 → ∀ p ∈ Pg E z,
      r * p * r⁻¹ * p⁻¹ ∈ E → p ∈ E := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro r hr hr3 p hp hcomm
  rw [O23In_CNz_eq_preS hm hz.1] at hr
  rw [Pg_eq_preS hm hz.1] at hp
  obtain ⟨hrN, hrT⟩ := mem_preS.1 hr
  obtain ⟨hpN, hpT⟩ := mem_preS.1 hp
  have h1 := (commutator_mem_E_iff hm.centralizer_eq hrN hpN).1 hcomm
  have h2 : S44.actN E ⟨r, hrN⟩ * S44.actN E ⟨p, hpN⟩ * (S44.actN E ⟨r, hrN⟩)⁻¹ *
      (S44.actN E ⟨p, hpN⟩)⁻¹ = 1 := by
    rw [h1]
    group
  have h3 := h.r_fpf _ hrT (orderOf_actN_eq_three hm hrN hr3) _ hpT h2
  exact (mem_E_iff_actN_eq_one hm.centralizer_eq hpN).2 h3

theorem r_E (h : CocodeXOf hm hz) :
    ∀ r ∈ TwoFi22.O23In (CNz E z), orderOf r = 3 → ∀ U : Subgroup G, U ≤ E →
      InvUnder (CNz E z) U → Nat.card ↥U = 2 ^ 7 → ∀ e ∈ E, r * e * r⁻¹ * e⁻¹ ∈ U := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro r hr hr3 U hUE hUinv hUc e he
  rw [O23In_CNz_eq_preS hm hz.1] at hr
  obtain ⟨hrN, hrT⟩ := mem_preS.1 hr
  rw [CNz_eq_preS hm hz.1] at hUinv
  have hinv := (invUnder_preS_iff inf_le_left hUE).1 hUinv
  have hcard : Nat.card ↥(U.subgroupOf E) = 2 ^ 7 := by
    rw [← card_eq_card_subgroupOf hUE]
    exact hUc
  exact h.r_E _ hrT (orderOf_actN_eq_three hm hrN hr3) (U.subgroupOf E) hinv hcard ⟨e, he⟩

theorem exists_A (h : CocodeXOf hm hz) :
    ∃ A : Subgroup G, A ≤ Nrm E ⊓ Jg t z ∧ E ≤ A ∧
      (∀ a ∈ A, ∀ r ∈ TwoFi22.O23In (CNz E z), orderOf r = 3 → a * r * a⁻¹ * r⁻¹ ∈ Pg E z) ∧
      HomVanish E z A := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  obtain ⟨Ab, hAb, hAr, hAU⟩ := h.exists_A
  refine ⟨preS Ab, ?_, E_le_preS hm.centralizer_eq Ab, ?_, ?_⟩
  · rw [Nrm_inf_Jg_eq_preS hm hm.t_mem hz.1]
    exact preS_mono hAb
  · intro a ha r hr hr3
    rw [O23In_CNz_eq_preS hm hz.1] at hr
    obtain ⟨haN, haT⟩ := mem_preS.1 ha
    obtain ⟨hrN, hrT⟩ := mem_preS.1 hr
    rw [Pg_eq_preS hm hz.1, commutator_mem_preS_iff haN hrN]
    exact hAr _ haT _ hrT (orderOf_actN_eq_three hm hrN hr3)
  · exact homVanish_preS_of_le_stabSub hm hz hAb hAU

theorem lattice (h : CocodeXOf hm hz) :
    ∀ U : Subgroup G, U ≤ E → InvUnder (CNz E z) U →
      U = ⊥ ∨ U = zpowers z ∨ Nat.card ↥U = 2 ^ 7 ∨ U = E := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro U hUE hUinv
  rw [CNz_eq_preS hm hz.1] at hUinv
  have hinv := (invUnder_preS_iff inf_le_left hUE).1 hUinv
  rcases h.lattice _ hinv with h1 | h1 | h1 | h1
  · exact Or.inl ((eq_bot_iff_subgroupOf_eq_bot hUE).2 h1)
  · exact Or.inr (Or.inl ((eq_zpowers_iff_subgroupOf_eq_zpowers hUE hz.1).2 h1))
  · exact Or.inr (Or.inr (Or.inl (by rw [card_eq_card_subgroupOf hUE]; exact h1)))
  · exact Or.inr (Or.inr (Or.inr ((eq_self_iff_subgroupOf_eq_top hUE).2 h1)))

theorem P_irred (h : CocodeXOf hm hz) :
    ∀ S : Subgroup G, E ≤ S → S ≤ Pg E z → InvUnder (CNz E z) S → S = E ∨ S = Pg E z := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro S hES hSP hSinv
  have hPX : TwoFi22.O2In (S44.XE E ⊓ centSub (zpowers (⟨z, hz.1⟩ : ↥E))) ≤ S44.XE E :=
    (O2In_le _).trans inf_le_left
  rw [Pg_eq_preS hm hz.1] at hSP ⊢
  obtain ⟨T, hTX, rfl⟩ := exists_T hm.centralizer_eq hES (hSP.trans (preS_le_Nrm _))
  have hTP := (preS_le_preS_iff hTX).1 hSP
  rw [CNz_eq_preS hm hz.1] at hSinv
  have hinv := (invUnder_preS_preS_iff inf_le_left hTX).1 hSinv
  rcases h.P_irred T hTP hinv with h1 | h1
  · rw [h1]
    exact Or.inl (preS_bot hm.centralizer_eq)
  · rw [h1]
    exact Or.inr rfl

theorem comm_ne (h : CocodeXOf hm hz) : ⁅E, Pg E z⁆ ≠ zpowers z := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  rw [Pg_eq_preS hm hz.1]
  intro hEq
  exact h.comm_ne
    ((commutator_E_preS_eq_zpowers_iff hm ((O2In_le _).trans inf_le_left) hz.1).1 hEq)

theorem exists_sextet (h : CocodeXOf hm hz) :
    ∀ U : Subgroup G, U ≤ E → InvUnder (CNz E z) U → Nat.card ↥U = 2 ^ 7 →
      ∃ z' ∈ U, z' ≠ z ∧ z' ∈ normClass E z := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro U hUE hUinv hUc
  rw [CNz_eq_preS hm hz.1] at hUinv
  have hinv := (invUnder_preS_iff inf_le_left hUE).1 hUinv
  have hcard : Nat.card ↥(U.subgroupOf E) = 2 ^ 7 := by
    rw [← card_eq_card_subgroupOf hUE]
    exact hUc
  obtain ⟨w, hwU, hwne, hworb⟩ := h.exists_sextet _ hinv hcard
  exact ⟨w, hwU, fun heq => hwne (Subtype.ext heq),
    (mem_normClass_iff_mem_orbit ⟨z, hz.1⟩ w).2 hworb⟩

theorem normal_card (h : CocodeXOf hm hz) :
    ∀ M : Subgroup G, M ≤ CNz E z → Pg E z ≤ M → InvUnder (CNz E z) M →
      Nat.card ↥M = Nat.card ↥(Pg E z) ∨ Nat.card ↥M = 3 * Nat.card ↥(Pg E z) ∨
      Nat.card ↥M = 1080 * Nat.card ↥(Pg E z) ∨ Nat.card ↥M = 2160 * Nat.card ↥(Pg E z) := by
  letI := commGroupOfM24Out hm
  haveI := finite_E_of_m24Out hm
  intro M hMC hPM hMinv
  have hPX : TwoFi22.O2In (S44.XE E ⊓ centSub (zpowers (⟨z, hz.1⟩ : ↥E))) ≤ S44.XE E :=
    (O2In_le _).trans inf_le_left
  have hEP : E ≤ Pg E z := by
    rw [Pg_eq_preS hm hz.1]
    exact E_le_preS hm.centralizer_eq _
  have hMN : M ≤ normalizer (E : Set G) := hMC.trans (CNz_le_Nrm E z)
  obtain ⟨T, hTX, rfl⟩ := exists_T hm.centralizer_eq (hEP.trans hPM) hMN
  rw [CNz_eq_preS hm hz.1] at hMC hMinv
  rw [Pg_eq_preS hm hz.1] at hPM ⊢
  have hTz := (preS_le_preS_iff hTX).1 hMC
  have hPT := (preS_le_preS_iff hPX).1 hPM
  have hinv := (invUnder_preS_preS_iff inf_le_left hTX).1 hMinv
  have h1 := h.normal_card T hTz hPT hinv
  rw [card_preS hm hTX, card_preS hm hPX, h.card_P]
  omega

end CocodeToData

theorem CocodeX.toCocodeData (hm : M24Out G E t) (hz : IsZ E t z)
    (h : @CocodeX ↥E (commGroupOfM24Out hm) (finite_E_of_m24Out hm) (S44.XE E)
      ⟨t, hm.t_mem⟩ ⟨z, hz.1⟩) : CocodeData E t z where
  card_Ctz := CocodeToData.card_Ctz hm hz h
  card_NV := CocodeToData.card_NV hm hz h
  swap := CocodeToData.swap hm hz h
  card_P := CocodeToData.card_P hm hz h
  O2_NV := CocodeToData.O2_NV hm hz h
  P_comm := CocodeToData.P_comm hm hz h
  P_sq := CocodeToData.P_sq hm hz h
  lattice := CocodeToData.lattice hm hz h
  P_irred := CocodeToData.P_irred hm hz h
  comm_ne := CocodeToData.comm_ne hm hz h
  card_O23 := CocodeToData.card_O23 hm hz h
  r_fpf := CocodeToData.r_fpf hm hz h
  r_E := CocodeToData.r_E hm hz h
  exists_A := CocodeToData.exists_A hm hz h
  exists_sextet := CocodeToData.exists_sextet hm hz h
  exists_perfect := CocodeToData.exists_perfect hm hz h
  normal_card := CocodeToData.normal_card hm hz h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
