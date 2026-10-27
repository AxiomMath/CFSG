module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFieldStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

private theorem z443_sq : ∀ d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ×
    Multiplicative (ZMod 3), d * d = 1 →
      (d.1.toAdd.val = 0 ∨ d.1.toAdd.val = 2) ∧ (d.2.1.toAdd.val = 0 ∨ d.2.1.toAdd.val = 2) ∧
        d.2.2.toAdd.val = 0 := by
  decide

theorem mul_self_Z0
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ Z0) : t * t = 1 :=
  U1_mul_self (Z0_le_U1 ht)

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem IsQSetting.comm_of_Z0_ker2
    (h : IsQSetting q l)
    (h2 : ∀ z ∈ q.ker, z * z = 1) {e c : E} (he : q e ∈ T0) (hc : q c ∈ Z0) :
    e * c = c * e := by
  obtain ⟨e', rfl⟩ := h.lsurj e
  obtain ⟨c', rfl⟩ := h.lsurj c
  rw [h.q_l] at he hc
  obtain ⟨w, hw⟩ : ∃ w, w = e'⁻¹ * c'⁻¹ * e' * c' := ⟨_, rfl⟩
  have hwk : w ∈ sigma.ker := by
    have hcomm : sigma e' * sigma c' = sigma c' * sigma e' := (mem_centralizer_iff.mp hc.1) _ he
    rw [MonoidHom.mem_ker, hw, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_assoc _ (sigma e') (sigma c'), hcomm]
    group
  have hwi : c' * w⁻¹ = w⁻¹ * c' := mem_center_iff.mp (inv_mem (ker_sigma_le_center hwk)) c'
  have hc2 : c' * c' ∈ sigma.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact mul_self_Z0 hc
  have hc2c := mem_center_iff.mp (ker_sigma_le_center hc2)
  have hconj : e'⁻¹ * c' * e' = c' * w⁻¹ := by rw [hw]; group
  have hw2 : w * w = 1 := by
    have h1 : e'⁻¹ * (c' * c') * e' = c' * c' := by
      rw [mul_assoc, ← hc2c e', ← mul_assoc, inv_mul_cancel, one_mul]
    have h2' : e'⁻¹ * (c' * c') * e' = c' * c' * (w⁻¹ * w⁻¹) := by
      calc e'⁻¹ * (c' * c') * e' = (e'⁻¹ * c' * e') * (e'⁻¹ * c' * e') := by group
        _ = c' * w⁻¹ * (c' * w⁻¹) := by rw [hconj]
        _ = c' * (w⁻¹ * c') * w⁻¹ := by group
        _ = c' * (c' * w⁻¹) * w⁻¹ := by rw [← hwi]
        _ = c' * c' * (w⁻¹ * w⁻¹) := by group
    rw [h1] at h2'
    have h3 : w⁻¹ * w⁻¹ = 1 := mul_eq_left.mp h2'.symm
    calc w * w = (w⁻¹ * w⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = 1 := by rw [h3, inv_one]
  rw [← range_zHom] at hwk
  obtain ⟨d, hd⟩ := hwk
  have hdd : d * d = 1 := zHom_injective (by rw [map_mul, hd, hw2, map_one])
  obtain ⟨h1, h2'', -⟩ := z443_sq d hdd
  have hz1 : l z₁ * l z₁ = 1 := h2 _ (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₁))
  have hz2 : l z₂ * l z₂ = 1 := h2 _ (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₂))
  have hlw : l w = 1 := by
    rw [← hd, zHom_apply, map_mul, map_mul, map_pow, map_pow, map_pow, h.lz₃, one_pow, mul_one]
    rcases h1 with h1 | h1 <;> rcases h2'' with h2'' | h2'' <;>
      simp [h1, h2'', pow_two, hz1, hz2]
  rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv] at hlw
  calc l e' * l c' = l c' * l e' * ((l e')⁻¹ * (l c')⁻¹ * l e' * l c') := by group
    _ = l c' * l e' := by rw [hlw, mul_one]

theorem fieldSylowFusion :
    ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G) (s : G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) →
      (s ∈ normalizer (J : Set G) ∧ s * s = 1 ∧ s ∉ withKernel J ∧
        Nat.card {j : J // (j : G)⁻¹ * s⁻¹ * j * s ∈ zStarIn J} = 168 * Nat.card (zStarIn J)) →
      IsSylowTwoIn P J → s ∈ normalizer (P : Set G) → Nat.card ↥(P ⊓ zStarIn J) = 2 →
      ∀ p ∈ P, p * s * (p * s) = 1 →
        ∃ q ∈ P, ∃ y ∈ P, (∀ r ∈ P, r * y = y * r) ∧ y * s = s * y ∧
          q * (p * s) * q⁻¹ = y * s := by
  intro G _ _ J P s hJ hL ⟨hsN, hs2, hsK, hcount⟩ hP hsP h2 p hp hps
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨φ, l, hQ, hβ, hT⟩ := exists_field_standard hJ hL hsN hs2 hsK hcount hP hsP
  obtain ⟨ζ, -⟩ := exists_zeta hP hQ.ker
  have hk : Nat.card φ.ker = 2 := (Nat.card_congr ζ.toEquiv).symm.trans h2
  have hk2 : ∀ z ∈ φ.ker, z * z = 1 := fun z hz => by
    have h1 : (⟨z, hz⟩ : φ.ker) ^ Nat.card φ.ker = 1 := pow_card_eq_one'
    rw [hk, pow_two] at h1
    exact congrArg Subtype.val h1
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hr2 : r₂⁻¹ = r₂ := inv_eq_of_mul_eq_one_right r₂_mul_self
  have hpJ : p ∈ J := hP.1 hp
  obtain ⟨t, ht⟩ : ∃ t, φ (jq J ⟨p, hpJ⟩) = t := ⟨_, rfl⟩
  have htT : t ∈ T0 := ht ▸ (hT _).2 ⟨p, hp, hpJ, rfl⟩
  have hinv : r₂ * t * r₂ * t = 1 := by
    have hconj : s⁻¹ * p * s = p⁻¹ := by
      rw [hsi]
      calc s * p * s = p⁻¹ * (p * s * (p * s)) := by group
        _ = p⁻¹ := by rw [hps, mul_one]
    have h1 := hβ (jq J ⟨p, hpJ⟩)
    rw [betaHat_jq] at h1
    have h1' : conjJ J hsN ⟨p, hpJ⟩ = (⟨p, hpJ⟩ : J)⁻¹ := Subtype.ext hconj
    rw [h1', map_inv, map_inv, hr2, ht] at h1
    rw [← h1, inv_mul_cancel]
  obtain ⟨u, huT, d, hdZ, htd⟩ := field_free htT hinv
  obtain ⟨eu, heu⟩ := hQ.qsurj u (T0_le_S huT)
  obtain ⟨q₀, hq₀P, hq₀J, hq₀e⟩ := (hT eu).1 (heu ▸ huT)
  have hu : φ (jq J ⟨q₀, hq₀J⟩) = u := by rw [hq₀e, heu]
  have hsq₀P : s⁻¹ * q₀ * s ∈ P := conj_mem_of_mem_normalizer hsP hq₀P
  have hsq₀J : s⁻¹ * q₀ * s ∈ J := hP.1 hsq₀P
  obtain ⟨v, hv⟩ : ∃ v, φ (jq J ⟨s⁻¹ * q₀ * s, hsq₀J⟩) = v := ⟨_, rfl⟩
  have hvT : v ∈ T0 := hv ▸ (hT _).2 ⟨_, hsq₀P, hsq₀J, rfl⟩
  have hvr : v = r₂ * u * r₂ := by
    have h1 := hβ (jq J ⟨q₀, hq₀J⟩)
    rw [betaHat_jq, hu, hr2] at h1
    rw [← hv]
    exact h1
  obtain ⟨y, hy⟩ : ∃ y, y = q₀⁻¹ * p * (s⁻¹ * q₀ * s) := ⟨_, rfl⟩
  have hyP : y ∈ P := hy ▸ P.mul_mem (P.mul_mem (P.inv_mem hq₀P) hp) hsq₀P
  have hyJ : y ∈ J := hP.1 hyP
  have hyd : φ (jq J ⟨y, hyJ⟩) = d := by
    have e1 : (⟨y, hyJ⟩ : J) = (⟨q₀, hq₀J⟩ : J)⁻¹ * ⟨p, hpJ⟩ * ⟨s⁻¹ * q₀ * s, hsq₀J⟩ :=
      Subtype.ext hy
    have hvi : r₂ * u⁻¹ * r₂ = v⁻¹ := by
      rw [hvr, mul_inv_rev, mul_inv_rev, hr2, mul_assoc]
    have hdv : v * d = d * v := (mem_centralizer_iff.mp hdZ.1) v hvT
    rw [e1, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hu, ht, hv]
    calc u⁻¹ * t * v = u⁻¹ * (u * r₂ * u⁻¹ * r₂ * d) * v := by rw [htd]
      _ = r₂ * u⁻¹ * r₂ * d * v := by group
      _ = v⁻¹ * (d * v) := by rw [hvi, mul_assoc]
      _ = d := by rw [← hdv, inv_mul_cancel_left]
  have hyc : ∀ r ∈ P, r * y = y * r := by
    intro r hr
    have hrJ := hP.1 hr
    have h1 := hQ.comm_of_Z0_ker2 hk2 ((hT (jq J ⟨r, hrJ⟩)).2 ⟨r, hr, hrJ, rfl⟩)
      (c := jq J ⟨y, hyJ⟩) (by rw [hyd]; exact hdZ)
    apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hr hyP) (P.mul_mem hyP hr)
    have e1 : (⟨r * y, hP.1 (P.mul_mem hr hyP)⟩ : J) = ⟨r, hrJ⟩ * ⟨y, hyJ⟩ := rfl
    have e2 : (⟨y * r, hP.1 (P.mul_mem hyP hr)⟩ : J) = ⟨y, hyJ⟩ * ⟨r, hrJ⟩ := rfl
    rw [e1, e2, map_mul, map_mul]
    exact h1
  have hyy : y * y = 1 := by
    have hU : jq J ⟨y, hyJ⟩ ∈ U1.comap φ := by
      rw [mem_comap, hyd]
      exact Z0_le_U1 hdZ
    have h1 := (hQ.isElemTwo_U1_comap hk2).2 _ hU
    apply eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hyP hyP)
    have e1 : (⟨y * y, hP.1 (P.mul_mem hyP hyP)⟩ : J) = ⟨y, hyJ⟩ * ⟨y, hyJ⟩ := rfl
    rw [e1, map_mul]
    exact h1
  have hys : q₀⁻¹ * (p * s) * q₀ = y * s := by
    have h1 : y * s = q₀⁻¹ * p * s⁻¹ * q₀ * (s * s) := by rw [hy]; group
    rw [h1, hs2, mul_one, hsi]
    group
  have hys2 : y * s * (y * s) = 1 := by
    rw [← hys]
    calc q₀⁻¹ * (p * s) * q₀ * (q₀⁻¹ * (p * s) * q₀) = q₀⁻¹ * (p * s * (p * s)) * q₀ := by
          group
      _ = 1 := by rw [hps, mul_one, inv_mul_cancel]
  have hsy : y * s = s * y := by
    have h1 : y * s = (y * s)⁻¹ := (inv_eq_of_mul_eq_one_right hys2).symm
    rw [h1, mul_inv_rev, hsi, inv_eq_of_mul_eq_one_right hyy]
  exact ⟨q₀⁻¹, P.inv_mem hq₀P, y, hyP, hyc, hsy, by rw [inv_inv]; exact hys⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
