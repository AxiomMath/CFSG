module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WLab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WMu
public import CFSG.ClassicalInvolution.Q3.Q3AMTriB01

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement




namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5 CFSG.ClassicalInvolution.Asc77.Thompson

section Epi

theorem three_dvd_of_epi {Mm Q : Type*} [Group Mm] [Finite Mm] [Group Q] [Finite Q]
    (Φ : Mm →* Equiv.Perm (Fin 4)) (hΦ : Function.Surjective Φ) (Nm : Subgroup Mm) [Nm.Normal]
    (hNodd : Odd (Nat.card Nm)) (π : Mm →* Q) (hπ : ∀ x, π x = 1 → x ∈ Nm) :
    3 ∣ Nat.card Q := by
  by_contra h3
  obtain ⟨c, hc3, hc1⟩ := exists_three_cycle
  obtain ⟨y, hy⟩ := hΦ c
  set k := orderOf (π y) with hk
  have hkQ : k ∣ Nat.card Q := orderOf_dvd_natCard _
  have hk3 : ¬ 3 ∣ k := fun h => h3 (h.trans hkQ)
  have hcop : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk3
  set n : Mm := y ^ k with hn
  have hnN : n ∈ Nm := hπ _ (by rw [hn, map_pow, hk, pow_orderOf_eq_one])
  have hΦn : Φ n = c ^ k := by rw [hn, map_pow, hy]
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hc'3 : (c ^ k) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  have hc'1 : c ^ k ≠ 1 := by
    intro h
    have h3k : 3 ∣ k := hord ▸ orderOf_dvd_of_pow_eq_one h
    exact hk3 h3k
  obtain ⟨g, hg2, hg1⟩ := S4_commutator _ hc'3 hc'1
  obtain ⟨m, hm⟩ := hΦ g
  set kk : Mm := n * (m * n⁻¹ * m⁻¹) with hkk
  have hkN : kk ∈ Nm := Nm.mul_mem hnN (by
    have := (inferInstance : Nm.Normal).conj_mem n⁻¹ (Nm.inv_mem hnN) m
    simpa [mul_assoc] using this)
  have hΦk : Φ kk = c ^ k * (g * (c ^ k)⁻¹ * g⁻¹) := by
    rw [hkk]
    simp only [map_mul, map_inv]
    rw [hΦn, hm]
  have hord2 : orderOf (Φ kk) = 2 := by
    rw [hΦk]
    exact orderOf_eq_prime hg2 hg1
  have h2k : 2 ∣ orderOf kk := hord2 ▸ orderOf_map_dvd Φ kk
  have h2N : 2 ∣ Nat.card Nm := h2k.trans (Subgroup.orderOf_dvd_natCard Nm hkN)
  have := Nat.odd_iff.mp hNodd
  omega

end Epi

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {Wg : Subgroup G}

@[expose] noncomputable def projLayer (Ω : Set (Subgroup G)) (c : G) :
    ↥(coreLayer Ω c) →* (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))).comp
    (Subgroup.equivMapOfInjective (coreHull Ω c) (Subgroup.centralizer ({c} : Set G)).subtype
      (Subgroup.centralizer ({c} : Set G)).subtype_injective).symm.toMonoidHom

theorem projLayer_apply {τ : G} (hC : τ ∈ Subgroup.centralizer ({c} : Set G))
    (hH : (⟨τ, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c)
    (hL : τ ∈ coreLayer Ω c) :
    projLayer Ω c ⟨τ, hL⟩ = QuotientGroup.mk (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)) := by
  have h : (Subgroup.equivMapOfInjective (coreHull Ω c) (Subgroup.centralizer ({c} : Set G)).subtype
      (Subgroup.centralizer ({c} : Set G)).subtype_injective).symm ⟨τ, hL⟩ =
        (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  show QuotientGroup.mk' _ ((Subgroup.equivMapOfInjective _ _ _).symm ⟨τ, hL⟩) = _
  rw [h]
  rfl

theorem MGrp_le_coreLayer (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hDc : ∀ R ∈ DSet Ω Wg, R ≤ Subgroup.centralizer ({c} : Set G)) :
    MGrp Ω Wg ≤ coreLayer Ω c := by
  refine le_trans ?_ (rLayer_le_coreLayer hΩ h2 hc2)
  exact iSup₂_le fun R hR => le_iSup₂_of_le R hR.1
    (le_iSup (fun _ : R ≤ Subgroup.centralizer ({c} : Set G) => R) (hDc R hR))

theorem three_dvd_of_mu_layer (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hDc : ∀ R ∈ DSet Ω Wg, R ≤ Subgroup.centralizer ({c} : Set G))
    (e : ↥(muGroup Ω Wg) ≃* Equiv.Perm (Fin 4)) :
    3 ∣ Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) := by
  have hLc := MGrp_le_coreLayer hΩ h2 hc2 hDc
  let Nm : Subgroup ↥(MGrp Ω Wg) := (oddCoreOf (coreLayer Ω c)).subgroupOf (MGrp Ω Wg)
  have hNn : Nm.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Q3AM.conj_mem_oddCoreOf_of_mem_tri (hLc g.2) hn⟩
  have hNodd : Odd (Nat.card Nm) := by
    have hcard : Nat.card Nm = Nat.card ↥(oddCoreOf (coreLayer Ω c) ⊓ MGrp Ω Wg) := by
      show Nat.card ((oddCoreOf (coreLayer Ω c)).subgroupOf (MGrp Ω Wg)) = _
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hcard]
    exact (oddCoreOf_odd_natCard (coreLayer Ω c)).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  refine three_dvd_of_epi (PhiM e) (PhiM_surjective e) Nm hNodd
    ((projLayer Ω c).comp (Subgroup.inclusion hLc)) ?_
  intro x hx
  obtain ⟨hC, hH⟩ := mem_C_H_of_mem_coreLayer (hLc x.2)
  have h1 : projLayer Ω c ⟨(x : G), hLc x.2⟩ = 1 := hx
  rw [projLayer_apply hC hH] at h1
  have hN := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_subgroupOf.mpr (mem_oddCoreOf_coreLayer hΩ hc2 hN)

end Layer

section P23

theorem p23_three_dvd_e {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {K' Wg : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' Wg u e g) :
    3 ∣ Nat.card (SecQ R e) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hNe := normalizer_le_centralizer_e hc.data
  obtain ⟨eμ⟩ := hc.std.hS4
  exact three_dvd_of_mu_layer hΩ h2 hc2 (fun R' hR' => hR'.2.trans hNe) eμ

end P23

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
