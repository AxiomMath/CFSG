module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSigma
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Center

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

@[expose] def realSub {K W : Subgroup G} (hWN : W ≤ normalizer (K : Set G))
    (q : Jhat K →* Equiv.Perm (Fin 42)) : Subgroup ↥R where
  carrier := {r | ∃ s, ∃ hs : s ∈ W, ∀ e,
    q (betaHat K (hWN hs) e) = (r : Equiv.Perm (Fin 42)) * q e * (r : Equiv.Perm (Fin 42))⁻¹}
  mul_mem' := by
    rintro a b ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
    refine ⟨s₂ * s₁, W.mul_mem hs₂ hs₁, fun e => ?_⟩
    rw [show betaHat K (hWN (W.mul_mem hs₂ hs₁)) e =
      betaHat K (mul_mem (hWN hs₂) (hWN hs₁)) e from rfl, betaHat_mul K (hWN hs₂) (hWN hs₁) e,
      h₁, h₂]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  one_mem' := ⟨1, W.one_mem, fun e => by rw [betaHat_eq_self K _ rfl]; simp⟩
  inv_mem' := by
    rintro a ⟨s, hs, h⟩
    refine ⟨s⁻¹, W.inv_mem hs, fun e => ?_⟩
    have h1 := h (betaHat K (hWN (W.inv_mem hs)) e)
    rw [show betaHat K (hWN hs) (betaHat K (hWN (W.inv_mem hs)) e) =
      betaHat K (mul_mem (hWN (W.inv_mem hs)) (hWN hs)) e from
        (betaHat_mul K (hWN (W.inv_mem hs)) (hWN hs) e).symm,
      betaHat_eq_self K _ (inv_mul_cancel s)] at h1
    simp only [Subgroup.coe_inv, inv_inv]
    rw [h1]
    group

theorem isPGroup_realSub {K W : Subgroup G}
    (hWN : W ≤ normalizer (K : Set G)) (hW2 : IsPGroup 2 W) {q : Jhat K →* Equiv.Perm (Fin 42)}
    (hqsurj : ∀ t ∈ S, ∃ e, q e = t) : IsPGroup 2 (realSub hWN q) := by
  rintro ⟨⟨r, hrR⟩, s, hs, h⟩
  obtain ⟨k, hk⟩ := hW2 ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    rwa [SubmonoidClass.coe_pow] at this
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have hp := betaHat_pow (hWN hs) h (2 ^ k)
  have hc : r ^ (2 ^ k) ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun t ht => ?_, R.pow_mem hrR _⟩
    obtain ⟨e, rfl⟩ := hqsurj t ht
    have h1 := hp e
    rw [betaHat_eq_self K _ hk' e] at h1
    calc q e * r ^ (2 ^ k) = r ^ (2 ^ k) * q e * (r ^ (2 ^ k))⁻¹ * r ^ (2 ^ k) := by
          rw [← h1]
      _ = r ^ (2 ^ k) * q e := by group
  rw [centralizer_S_inf_R] at hc
  simpa using (mem_bot.mp hc)

theorem exists_frame_Sigma0
    [Finite G]
    {K W : Subgroup G} (hK : ⁅K, K⁆ = K) (hL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hW : IsSylowTwoIn W (normalizer (K : Set G))) :
    ∃ (q : Jhat K →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat K), IsQSetting q l ∧
      (∀ e, q e ∈ T0 ↔ ∃ p ∈ W ⊓ K, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e) ∧
      ∀ s (hs : s ∈ W), ∃ ρ ∈ Sigma0, ∀ e, q (betaHat K (hW.1 hs) e) = ρ * q e * ρ⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q₀, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  have hR2 := isPGroup_realSub hW.1 (GrS4.isPGroup_of_isSylowTwoIn hW) hqsurj
  obtain ⟨Q, hQ⟩ := hR2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥R)
    (isPGroup_Sigma0.toSylow not_two_dvd_index_Sigma0) Q
  have hconj : ∀ r : ↥R, r ∈ realSub hW.1 q₀ →
      (c : Equiv.Perm (Fin 42))⁻¹ * r * c ∈ Sigma0 := by
    intro r hr
    have h1 : r ∈ (Q : Subgroup ↥R) := hQ hr
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨x, hx, hxr⟩ := h1
    have hx' : (x : Equiv.Perm (Fin 42)) ∈ Sigma0 := mem_subgroupOf.mp hx
    have hval : (c : Equiv.Perm (Fin 42)) * x * (c : Equiv.Perm (Fin 42))⁻¹ = r := by
      have := congrArg Subtype.val hxr
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [← hval]
    rwa [show (c : Equiv.Perm (Fin 42))⁻¹ * ((c : Equiv.Perm (Fin 42)) * x *
      (c : Equiv.Perm (Fin 42))⁻¹) * c = x by group]
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem c.2)
  set q := (MulAut.conj (c : Equiv.Perm (Fin 42))⁻¹).toMonoidHom.comp q₀ with hqd
  have hqe : ∀ e, q e = (c : Equiv.Perm (Fin 42))⁻¹ * q₀ e * c := fun e => by simp [hqd]
  have hker'' : q.ker = center (Jhat K) := by rw [hker', hqker]
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hK) q hS' hsurj' (hker'' ▸ le_refl _)
  have hQs : IsQSetting q l := ⟨hS', hsurj', hker'', by rw [hker']; exact h3, hl, hls⟩
  have hreal : ∀ s (hs : s ∈ W), ∃ ρ ∈ Sigma0,
      ∀ e, q (betaHat K (hW.1 hs) e) = ρ * q e * ρ⁻¹ := by
    intro s hs
    obtain ⟨r, hrR, hr⟩ := exists_realization q₀ hqS hqsurj (betaHat K (hW.1 hs)) (fun e => by
      rw [hqker]
      exact mulEquiv_mem_center_iff _ e)
    refine ⟨(c : Equiv.Perm (Fin 42))⁻¹ * r * c, hconj ⟨r, hrR⟩ ⟨s, hs, hr⟩, fun e => ?_⟩
    rw [hqe, hqe, hr]
    group
  have hP : IsSylowTwoIn (W ⊓ K) K := GrS4.isSylowTwoIn_inf hW
  have hTP : ∀ p (hp : p ∈ K), p ∈ W ⊓ K → q (jq K ⟨p, hp⟩) ∈ T0 := by
    intro p hp hpP
    obtain ⟨ρ, hρS0, hρ⟩ := hreal p hpP.1
    have h1 : ∀ e, q (betaHat K (hW.1 hpP.1) e) =
        (q (jq K ⟨p, hp⟩))⁻¹ * q e * (q (jq K ⟨p, hp⟩))⁻¹⁻¹ := fun e => by
      rw [betaHat_of_mem hp, map_mul, map_mul, map_inv, inv_inv]
    have hu := realization_unique hsurj' (S_le_R (S.inv_mem (hS' _))) (Sigma0_le_R hρS0) h1 hρ
    have hmem := mem_T0_of_mem_Sigma0 (hu ▸ hρS0) (S.inv_mem (hS' _))
    simpa using T0.inv_mem hmem
  refine ⟨q, l, hQs, fun e => ⟨fun he => ?_, ?_⟩, hreal⟩
  · obtain ⟨T, hT⟩ := hP.2
    set φ : ↥K →* ↥S := (q.comp (jq K)).codRestrict S (fun j => hS' _) with hφ
    have hφs : Function.Surjective φ := by
      intro t
      obtain ⟨e', he'⟩ := hsurj' t t.2
      obtain ⟨j, rfl⟩ := jq_surjective K e'
      exact ⟨j, Subtype.ext he'⟩
    have hle : ((T.mapSurjective hφs : Sylow 2 ↥S) : Subgroup ↥S) ≤ T0.subgroupOf S := by
      rw [Sylow.coe_mapSurjective, hT]
      rintro _ ⟨j, hj, rfl⟩
      exact mem_subgroupOf.mpr (hTP j j.2 (mem_subgroupOf.mp hj))
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [← coe_sylowT0, Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity])
    have hmem : (⟨q e, hS' e⟩ : ↥S) ∈ ((T.mapSurjective hφs : Sylow 2 ↥S) : Subgroup ↥S) := by
      rw [heq]
      exact mem_subgroupOf.mpr he
    rw [Sylow.coe_mapSurjective, hT] at hmem
    obtain ⟨j, hj, hje⟩ := hmem
    have hqq : q (jq K j) = q e := congrArg Subtype.val hje
    have hz : (jq K j)⁻¹ * e ∈ center (Jhat K) := by
      rw [← hker'', MonoidHom.mem_ker, map_mul, map_inv, hqq, inv_mul_cancel]
    obtain ⟨p', hp'P, hp'K, hp'e⟩ := exists_mem_of_mem_center hP hz
    refine ⟨j * p', (W ⊓ K).mul_mem (mem_subgroupOf.mp hj) hp'P, K.mul_mem j.2 hp'K, ?_⟩
    have e1 : (⟨(j : G) * p', K.mul_mem j.2 hp'K⟩ : K) = j * ⟨p', hp'K⟩ := rfl
    rw [e1, map_mul, hp'e]
    group
  · rintro ⟨p, hpP, hpK, rfl⟩
    exact hTP p hpK hpP

theorem sylowCentralLift :
    ∀ (G : Type) [Group G] [Finite G] (K S : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn S (normalizer (K : Set G)) →
      (∀ z ∈ S ⊓ zStarIn K, z * z = 1) →
      ∃ y ∈ S ⊓ K, y ∉ zStarIn K ∧ y * y = 1 ∧ ∀ s ∈ S, s * y = y * s := by
  intro G _ _ K W hK hL hW hZ
  obtain ⟨q, l, hQ, hT, hreal⟩ := exists_frame_Sigma0 hK hL hW
  have hP : IsSylowTwoIn (W ⊓ K) K := GrS4.isSylowTwoIn_inf hW
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hk2 := ker_mul_self_of_elem hP hQ.ker fun z hz => hZ z ⟨hz.1.1, hz.2⟩
  have hq₀ : q (l (cv liftW0)) = wordPerm (tg 4) := hQ.q_liftW0
  have hZ0 : q (l (cv liftW0)) ∈ Z0 := by rw [hq₀]; exact mem_Z0.2 ⟨4, by simp, rfl⟩
  obtain ⟨y, hyP, hyK, hy⟩ := (hT (l (cv liftW0))).1 (hq₀ ▸ tg_mem_T0 4 (by norm_num))
  have hfix : ∀ s (hs : s ∈ W), betaHat K (hW.1 hs) (l (cv liftW0)) = l (cv liftW0) := by
    intro s hs
    obtain ⟨ρ, hρS0, hρ⟩ := hreal s hs
    obtain ⟨t, ht, ν, hν, rfl⟩ := hρS0
    obtain ⟨et, het⟩ := hQ.qsurj t (T0_le_S ht)
    have hcomm : et * l (cv liftW0) = l (cv liftW0) * et :=
      hQ.comm_of_Z0_ker2 hk2 (by rw [het]; exact ht) hZ0
    rcases hν with rfl | hν
    · obtain ⟨e₁, he₁, hβ⟩ := eq_conj_of_realization hK hQ.qsurj hQ.ker (T0_le_S ht)
        (fun e => by rw [hρ, mul_one])
      rw [hβ, hQ.comm_of_Z0_ker2 hk2 (by rw [he₁]; exact ht) hZ0, mul_inv_cancel_right]
    · set β' : Jhat K ≃* Jhat K := (betaHat K (hW.1 hs)).trans (MulAut.conj et⁻¹) with hβ'
      have hβ'e : ∀ e, β' e = et⁻¹ * betaHat K (hW.1 hs) e * et := fun e => by
        simp [hβ']
      have hq' : ∀ e, q (β' e) = ν * q e * ν⁻¹ := fun e => by
        rw [hβ'e, map_mul, map_mul, map_inv, het, hρ]
        group
      have h1 := hQ.beta_liftW0 hν hq'
      rw [hβ'e] at h1
      calc betaHat K (hW.1 hs) (l (cv liftW0)) =
            et * (et⁻¹ * betaHat K (hW.1 hs) (l (cv liftW0)) * et) * et⁻¹ := by group
        _ = et * l (cv liftW0) * et⁻¹ := by rw [h1]
        _ = l (cv liftW0) := by rw [hcomm, mul_inv_cancel_right]
  refine ⟨y, hyP, fun hyZ => ?_, ?_, fun s hs => ?_⟩
  · have hc := (mem_zStarIn_iff hyK).1 hyZ
    rw [← hQ.ker, MonoidHom.mem_ker, hy, hq₀, ← wordPerm_tg_zero] at hc
    exact absurd (tg_injective (by norm_num) (by norm_num) hc) (by norm_num)
  · refine eq_one_of_jq_eq_one hP.1 hP2 ((W ⊓ K).mul_mem hyP hyP) ?_
    show jq K (⟨y, hyK⟩ * ⟨y, hyK⟩) = 1
    rw [map_mul, hy]
    exact hQ.liftW0_mul_self
  · have hsP : s⁻¹ * y * s ∈ W ⊓ K :=
      ⟨W.mul_mem (W.mul_mem (W.inv_mem hs) hyP.1) hs,
        conj_mem_of_mem_normalizer (hW.1 hs) hyK⟩
    have h1 : s⁻¹ * y * s = y := by
      apply eq_of_jq_eq hP.1 hP2 hsP hyP
      have h2 := hfix s hs
      rw [← hy, betaHat_jq] at h2
      exact h2
    calc s * y = s * (s⁻¹ * y * s) := by rw [h1]
      _ = y * s := by group

end CFSG.ComponentClassification.GrSLit.L34Facts
