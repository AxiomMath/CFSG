module

public import CFSG.GF2Type.Smith1979.CaseIIDLayer
public import CFSG.GF2Type.Smith1979.CaseI25Index

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

variable (D : Data S g t)
include D

theorem orbit_Rbar_eq : (MulAction.orbit (Rbar S g t) (S.cl (g * S.z * g⁻¹)) : Set S.Qt) =
    {v | v ∈ Vt S g t ∧ v ≠ 0} := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨apply_mem_Vt_of_mem_Rbar D.H.conj_mem x.2 (cl_a_mem_Vt D.ht), ?_⟩
    intro h
    exact cl_conj_z_ne_zero S D.H.conj_mem D.H.conj_ne ((LinearEquiv.map_eq_zero_iff _).mp h)
  · rintro ⟨hv, hv0⟩
    obtain ⟨x, hx, hvx⟩ := D.hL.mem_orbit ⟨v, hv⟩ (fun h => hv0 (congrArg Subtype.val h))
    exact ⟨⟨x, hx⟩, hvx.symm⟩

theorem card_orbit_Rbar :
    Nat.card (MulAction.orbit (Rbar S g t) (S.cl (g * S.z * g⁻¹))) = 7 := by
  have h1 : Nat.card (Vt S g t) = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vt S g t), D.h3, Nat.card_zmod]
    norm_num
  have h2 : ((Vt S g t : Set S.Qt)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h1
  have h3 : ({v | v ∈ Vt S g t ∧ v ≠ 0} : Set S.Qt) = (Vt S g t : Set S.Qt) \ {0} := by
    ext v
    simp
  rw [Nat.card_coe_set_eq, D.orbit_Rbar_eq, h3,
    Set.ncard_sdiff_singleton_of_mem (Submodule.zero_mem _), h2]

theorem card_Rbar_inf_NLbar (hCE : S4.CentralExtInput.{0}) :
    Nat.card (Rbar S g t ⊓ NLbar S g : Subgroup S.O) = 384 := by
  set a : S.Qt := S.cl (g * S.z * g⁻¹)
  have hsmul : ∀ (x : Rbar S g t) (v : S.Qt),
      x • v = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := fun _ _ => rfl
  have hstab : (MulAction.stabilizer (Rbar S g t) a).map (Rbar S g t).subtype =
      Rbar S g t ⊓ NLbar S g := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf, Case25.mem_NLbar_iff D.H]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Rbar_le_Mbar y.2, by rw [MulAction.mem_stabilizer_iff, hsmul] at hy; exact hy⟩
    · rintro ⟨hxR, -, hfix⟩
      exact ⟨⟨x, hxR⟩, by rw [MulAction.mem_stabilizer_iff, hsmul]; exact hfix, rfl⟩
  have hcard_stab : Nat.card (MulAction.stabilizer (Rbar S g t) a) =
      Nat.card (Rbar S g t ⊓ NLbar S g : Subgroup S.O) := by
    rw [← hstab, Subgroup.card_map_of_injective (Rbar S g t).subtype_injective]
  have hOS := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Rbar S g t) a)
  rw [Nat.card_prod, hcard_stab, D.card_orbit_Rbar, (Rbar_structure_II D hCE).2.1] at hOS
  omega

theorem ncard_Delta_le : (Delta S g t).ncard ≤ 16 := by
  obtain ⟨Kb, hKL, hKchar, -, htK, hLK⟩ :=
    exists_Kbar_of_rank_six D.H D.C D.hw D.ht D.finrank_commSpace
  have hKcard : Nat.card Kb ≤ 16 := by
    have hdvd : Nat.card Kb ∣ Nat.card (S.Lbar g) := Subgroup.card_dvd_of_le hKL
    have hne : Nat.card Kb ≠ Nat.card (S.Lbar g) := fun h => htK (by
      have := Subgroup.eq_of_le_of_card_ge hKL h.ge
      rw [this]
      exact D.ht)
    rw [D.C.card_Lbar, D.hw] at hdvd hne
    norm_num at hdvd hne
    have hc : Nat.card Kb ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card Kb = c at hdvd hne hc ⊢
    interval_cases c <;> omega
  have hmap : ∀ x ∈ Delta S g t, t * x ∈ Kb := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    have hxL : n * t * n⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hn.2 t).mp D.ht
    have h6 : finrank (ZMod 2) (commSpace ((n * t * n⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 6 := by
      have e : ((n * t * n⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
          (n : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) *
            (n : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := rfl
      rw [e, finrank_commSpace_conj]
      exact D.finrank_commSpace
    have hnK : n * t * n⁻¹ ∉ Kb := fun h => (hKchar _ hxL).mp h h6
    exact (hLK _ hxL).resolve_left hnK
  have hinj : Set.InjOn (fun x : S.O => t * x) (Delta S g t) := fun x _ y _ h =>
    mul_left_cancel h
  have h1 := Set.ncard_le_ncard_of_injOn (fun x : S.O => t * x) hmap hinj
    (Set.toFinite (Kb : Set S.O))
  have h2 : (Kb : Set S.O).ncard = Nat.card Kb := (Nat.card_coe_set_eq (Kb : Set S.O)).symm
  omega

theorem card_NLbar_eq (hCE : S4.CentralExtInput.{0}) :
    Nat.card (NLbar S g) = (Delta S g t).ncard * 384 := by
  have h1 := Subgroup.relIndex_mul_card (H := centralizer ({t} : Set S.O)) (K := NLbar S g)
  have h2 : centralizer ({t} : Set S.O) ⊓ NLbar S g = Rbar S g t ⊓ NLbar S g := by
    ext x
    constructor
    · rintro ⟨hxc, hxN⟩
      have hxR : x ∈ centralizer ({t} : Set S.O) ⊓ S.Mbar := ⟨hxc, hxN.1⟩
      rw [(Rbar_structure_II D hCE).1] at hxR
      exact ⟨hxR, hxN⟩
    · rintro ⟨hxR, hxN⟩
      exact ⟨Rbar_le_centralizer D.H.conj_mem hxR, hxN⟩
  rw [h2, D.card_Rbar_inf_NLbar hCE] at h1
  rw [← h1, CaseIClosure.ncard_Delta_eq_index]
  rfl

theorem not_two_pow_twelve_dvd_card_NLbar (hCE : S4.CentralExtInput.{0}) :
    ¬ 2 ^ 12 ∣ Nat.card (NLbar S g) := by
  intro h
  have hpos : 0 < Nat.card (NLbar S g) := Nat.card_pos
  rw [D.card_NLbar_eq hCE] at h hpos
  have hΔ := D.ncard_Delta_le
  norm_num at h
  omega

theorem not_two_pow_twelve_dvd_card_Mbar (hCE : S4.CentralExtInput.{0}) :
    ¬ 2 ^ 12 ∣ Nat.card S.Mbar := by
  intro h
  have h1 := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h
  rw [Case25.factorization_two_Mbar_eq D.H D.C] at h1
  exact D.not_two_pow_twelve_dvd_card_NLbar hCE
    ((Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr h1)

end Data

theorem not_two_pow_eleven_dvd_card_X (D : Data S g t) (hCE : S4.CentralExtInput.{0}) :
    ¬ 2 ^ 11 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := by
  intro h
  haveI : (timmesfeldLayer S.Mbar).Normal := Layer.normal S.Mbar
  have hE : 2 ^ 11 ∣ Nat.card (timmesfeldLayer S.Mbar) :=
    h.trans ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (timmesfeldLayer S.Mbar))⟩
  have htt : CaseI25Transfer.tM D.ht * CaseI25Transfer.tM D.ht = 1 :=
    Subtype.ext (mul_self_of_mem_Lbar S D.H.conj_mem D.ht)
  have h2 : 2 ∣ (timmesfeldLayer S.Mbar).index :=
    Case25.two_dvd_index_of_not_mem _ htt D.tM_not_mem_layer
  have h12 : 2 ^ 12 ∣ Nat.card S.Mbar := by
    rw [← Subgroup.card_mul_index (timmesfeldLayer S.Mbar)]
    have := mul_dvd_mul hE h2
    rwa [← pow_succ] at this
  exact D.not_two_pow_twelve_dvd_card_Mbar hCE h12

end CFSG.GF2Type.Smith1979.Case2
