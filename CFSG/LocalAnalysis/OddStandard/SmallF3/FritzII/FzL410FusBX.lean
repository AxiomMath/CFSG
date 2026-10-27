module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE4T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Set

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}

theorem fz410x_fz410_fusb_card_le_64
    (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P) {K : Subgroup G}
    (hpK : IsPGroup 2 K) (hKH : K ≤ invCent t)
    (hKcentZ : K ≤ Subgroup.centralizer (Z : Set G)) : Nat.card K ≤ 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S_H : Sylow 2 ↥(invCent t) :=
    (D.ctx.isPGroup.comap_subtype).toSylow (by
      simpa [Subgroup.relIndex] using D.ctx.relIndex_odd)
  have hSH : (S_H : Subgroup ↥(invCent t)) = S.subgroupOf (invCent t) := rfl
  have hK_le_conj : ∃ h : G, h ∈ invCent t ∧ K ≤ MulAut.conj h • S := by
    obtain ⟨Q, hQ⟩ := (hpK.comap_subtype (K := invCent t)).exists_le_sylow
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥(invCent t)) Q S_H
    have hQmap : MulAut.conj h • (Q : Subgroup ↥(invCent t)) = (S_H : Subgroup ↥(invCent t)) := by
      rw [← Sylow.coe_subgroup_smul, hh]
    refine ⟨(h : G)⁻¹, (invCent t).inv_mem h.2, ?_⟩
    intro k hk
    have hkQ : (⟨k, hKH hk⟩ : ↥(invCent t)) ∈ Q :=
      hQ (Subgroup.mem_subgroupOf.mpr hk)
    have hkSH : MulAut.conj h • (⟨k, hKH hk⟩ : ↥(invCent t)) ∈
        (S_H : Subgroup ↥(invCent t)) := by
      rw [← hQmap]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj h) _ hkQ
    rw [hSH] at hkSH
    have hkS : ((MulAut.conj h • (⟨k, hKH hk⟩ : ↥(invCent t)) : ↥(invCent t)) : G) ∈ S :=
      Subgroup.mem_subgroupOf.mp hkSH
    have hkS' : (h : G) * k * (h : G)⁻¹ ∈ S := hkS
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨(h : G) * k * (h : G)⁻¹, hkS', ?_⟩
    show (MulAut.conj (h : G)⁻¹) • ((h : G) * k * (h : G)⁻¹) = k
    simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv]
    group
  have hK_le_128 : Nat.card K ≤ 128 := by
    obtain ⟨h, -, hle⟩ := hK_le_conj
    calc Nat.card K ≤ Nat.card (MulAut.conj h • S : Subgroup G) := Subgroup.card_le_of_le hle
      _ = Nat.card S :=
        (Nat.card_congr (Subgroup.equivSMul (MulAut.conj h) S).toEquiv).symm
      _ = 128 := by rw [D.ctx.card_S, D.card_two]; norm_num
  have hZS_card : Nat.card (S ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) ≤ 4 := by
    have hle : S ⊓ Subgroup.centralizer (S : Set G) ≤ twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2) :=
      D.ctx.center_le
    have hsup : Nat.card (twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2) : Subgroup G) ≤ 4 := by
      have hK : twoCore t = zpowers t := by
        have hle : zpowers t ≤ twoCore t := Subgroup.zpowers_le_of_mem D.ctx.hyp.mem_twoCore
        have hcard : Nat.card (twoCore t) ≤ Nat.card (zpowers t) := by
          rw [D.card_two, Nat.card_zpowers, D.ctx.hyp.ord_t]
        exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
      have hle2 : twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2) ≤
          closure ({t, (x₁ * x₂) ^ 2} : Set G) := by
        refine sup_le ?_ ?_
        · rw [hK]
          exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
        · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      have hmemZ : (x₁ * x₂) ^ 2 ∈ Z := by
        rw [D.hZ]
        exact Subgroup.subset_closure (by simp)
      have hz2 : ((x₁ * x₂) ^ 2) * ((x₁ * x₂) ^ 2) = 1 := by
        have h := D.str.Z_sq _ hmemZ
        rwa [pow_two] at h
      have ht2 : t * t = 1 := by
        have h := D.str.t_sq
        rwa [pow_two] at h
      have hcomm : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t :=
        D.str.W_comm t D.str.t_mem _ (D.str.EW (D.str.ZE hmemZ))
      have hcl : Nat.card (closure ({t, (x₁ * x₂) ^ 2} : Set G)) ≤ 4 :=
        S4A.card_closure_pair_le_four hcomm ht2 hz2
      exact (Subgroup.card_le_of_le hle2).trans hcl
    exact (Subgroup.card_le_of_le hle).trans hsup
  have hK_ne_128 : Nat.card K ≠ 128 := by
    intro hK128
    obtain ⟨h, hhH, hle⟩ := hK_le_conj
    have hSc_card : Nat.card (MulAut.conj h • S : Subgroup G) = 128 := by
      rw [(Nat.card_congr (Subgroup.equivSMul (MulAut.conj h) S).toEquiv).symm, D.ctx.card_S,
        D.card_two]
      norm_num
    have hKeq : K = MulAut.conj h • S :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hK128, hSc_card])
    have hSccent : MulAut.conj h • S ≤ Subgroup.centralizer (Z : Set G) := by
      rw [← hKeq]; exact hKcentZ
    set Z' : Subgroup G := MulAut.conj h⁻¹ • Z with hZ'def
    have hZ'card : Nat.card Z' = 4 := by
      rw [hZ'def]
      exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj h⁻¹) Z).toEquiv).symm.trans
        D.str.card_Z
    have hZ'leH : Z' ≤ invCent t := by
      intro z' hz'
      rw [hZ'def, Subgroup.mem_smul_pointwise_iff_exists] at hz'
      obtain ⟨z, hz, hz'eq⟩ := hz'
      rw [← hz'eq]
      change ∀ g ∈ ({t} : Set G), g * (MulAut.conj h⁻¹ • z) = (MulAut.conj h⁻¹ • z) * g
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv]
      have hzH : z * t = t * z :=
        D.str.W_comm z (D.str.EW (D.str.ZE hz)) t D.str.t_mem
      have hhH' : t * h = h * t := by
        rw [invCent] at hhH
        exact hhH t (Set.mem_singleton t)
      have hth : t * h⁻¹ = h⁻¹ * t := by
        calc t * h⁻¹ = h⁻¹ * (h * t) * h⁻¹ := by group
          _ = h⁻¹ * (t * h) * h⁻¹ := by rw [hhH']
          _ = h⁻¹ * t := by group
      calc t * (h⁻¹ * z * h) = (t * h⁻¹) * z * h := by group
        _ = (h⁻¹ * t) * z * h := by rw [hth]
        _ = h⁻¹ * (t * z) * h := by group
        _ = h⁻¹ * (z * t) * h := by rw [← hzH]
        _ = h⁻¹ * z * (t * h) := by group
        _ = h⁻¹ * z * (h * t) := by rw [hhH']
        _ = (h⁻¹ * z * h) * t := by group
    have hZ'centS : Z' ≤ Subgroup.centralizer (S : Set G) := by
      intro z' hz'
      rw [hZ'def, Subgroup.mem_smul_pointwise_iff_exists] at hz'
      obtain ⟨z, hz, hz'eq⟩ := hz'
      rw [← hz'eq]
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv]
      have hsZ : (MulAut.conj h) • s ∈ MulAut.conj h • S :=
        Subgroup.smul_mem_pointwise_smul s (MulAut.conj h) S hs
      have hsc := hSccent hsZ
      rw [Subgroup.mem_centralizer_iff] at hsc
      have hcom : (h * s * h⁻¹) * z = z * (h * s * h⁻¹) := (hsc z hz).symm
      calc s * (h⁻¹ * z * h) = h⁻¹ * ((h * s * h⁻¹) * z) * h := by group
        _ = h⁻¹ * (z * (h * s * h⁻¹)) * h := by rw [hcom]
        _ = (h⁻¹ * z * h) * s := by group
    have hZ'p : IsPGroup 2 Z' := by
      rw [hZ'def]
      have hZT : Z ≤ T :=
        D.str.ZE.trans (D.str.EW.trans (D.str.WQ.trans (D.str.QR.trans D.str.RT)))
      exact (D.str.pgroup_T.to_le hZT).of_equiv (Subgroup.equivSMul (MulAut.conj h⁻¹) Z)
    have hZ'leS : Z' ≤ S := by
      have hsup : IsPGroup 2 (S ⊔ Z' : Subgroup G) := by
        rw [sup_comm]
        exact IsPGroup.to_sup_of_normal_right' hZ'p D.ctx.isPGroup
          (hZ'centS.trans (Subgroup.centralizer_le_normalizer (S : Set G)))
      have hmax := S_H.is_maximal' (Q := (S ⊔ Z').subgroupOf (invCent t)) (hsup.comap_subtype)
        (Subgroup.subgroupOf_mono (invCent t) le_sup_left)
      have h1 : (S ⊔ Z').subgroupOf (invCent t) = S.subgroupOf (invCent t) := by
        rw [hmax, hSH]
      have h2 := congrArg (Subgroup.map (invCent t).subtype) h1
      rw [Subgroup.map_subgroupOf_eq_of_le (sup_le D.ctx.le_invCent hZ'leH),
        Subgroup.map_subgroupOf_eq_of_le D.ctx.le_invCent] at h2
      exact le_sup_right.trans_eq h2
    have hZ'leZS : Z' ≤ S ⊓ Subgroup.centralizer (S : Set G) := le_inf hZ'leS hZ'centS
    have hZeq : Z' = S ⊓ Subgroup.centralizer (S : Set G) :=
      Subgroup.eq_of_le_of_card_ge hZ'leZS (by rw [hZ'card]; exact hZS_card)
    have htZS : t ∈ S ⊓ Subgroup.centralizer (S : Set G) :=
      D.ctx.center_ge (Subgroup.subset_closure (by simp))
    have htZ' : t ∈ Z' := by rw [hZeq]; exact htZS
    have htZ : t ∈ Z := by
      rw [hZ'def, Subgroup.mem_smul_pointwise_iff_exists] at htZ'
      obtain ⟨z, hz, hz_eq⟩ := htZ'
      have hz_eq' : h⁻¹ * z * h = t := by
        simpa only [MulAut.smul_def, MulAut.conj_apply, inv_inv] using hz_eq
      have hhH' : t * h = h * t := by
        rw [invCent] at hhH
        exact hhH t (Set.mem_singleton t)
      have hzt : z = t := by
        calc z = h * (h⁻¹ * z * h) * h⁻¹ := by group
          _ = h * t * h⁻¹ := by rw [hz_eq']
          _ = t := by rw [← hhH']; group
      rwa [hzt] at hz
    exact D.str.t_notin_E (D.str.ZE htZ)
  obtain ⟨n, hn⟩ := hpK.exists_card_eq
  have hn_le : n ≤ 7 := by
    by_contra h
    have h8 : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at hK_le_128
    norm_num at h8
    omega
  have hn_ne : n ≠ 7 := by
    intro h
    exact hK_ne_128 (by rw [hn, h]; norm_num)
  have hn6 : n ≤ 6 := by omega
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
    _ = 64 := by norm_num

end CFSG.OddStandard.SmallF3.FritzII
