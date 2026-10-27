module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A511Qf
public import CFSG.Quasithin.H13.L32A511Qh
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A511Core
public import CFSG.Quasithin.H13.L32A513a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A512b

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.Q511
open scoped Pointwise commutatorElement

theorem lemma14_5_11Core_holds_F4 : Lemma14_5_11Core_F4 := by
  intro G _ _ T L V V₂ Y C hXS3 hinf hQ hsolv _ hX1 p hp hp5 P _ hPH hPn hPp
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXT : xL L V₂ ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hXH : xL L V₂ ≤ hY T L V₂ Y := le_sup_left.trans hXT
  have hTH : T ≤ hY T L V₂ Y := le_sup_right
  have hWe : IsElemAbelian 2 (vH T L V V₂ Y) := (C.vH_le_center_F4 hQ).2
  have hHN : hY T L V₂ Y ≤ Subgroup.normalizer (vH T L V V₂ Y : Set G) :=
    (C.isTwoReducedIn_vH_F4 hQ).2.1
  have hHC : hY T L V₂ Y ≤
      Subgroup.normalizer (Subgroup.centralizer (vH T L V V₂ Y : Set G) : Set G) :=
    Ctx.le_normalizer_centralizer_vH le_rfl
  have hCT4 : (Subgroup.centralizer (vH T L V V₂ Y : Set G)).relIndex T ≤ 4 :=
    C.relIndex_centralizer_vH_le_F4 hXS3 hinf hQ hsolv
  have hTCQ : T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) ≤ pCoreOf 2 (xL L V₂ ⊔ T) :=
    fun t ht => C.inf_xT_le'_F4 hXS3 ⟨Subgroup.mem_sup_right ht.1, ht.2⟩
  have hQT : pCoreOf 2 (xL L V₂ ⊔ T) ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (C.isSylowTwoOf_T_F4 (K := xL L V₂ ⊔ T) le_sup_right)
  have hTQ2 : (pCoreOf 2 (xL L V₂ ⊔ T)).relIndex T = 2 := C.relIndex_pCoreOf_xT_F4 hXS3
  obtain ⟨A, hAT, hAe, hmax, hAQ⟩ := C.exists_offender_F4 hX1
  have hcard := C.card_le_mul_F4 hQ hAT hAe hmax
  have hPp' : ∀ g ∈ P, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (vH T L V V₂ Y : Set G) :=
    fun g hg => (hPp g hg).imp fun _ hk => hk.2
  have hQgrp : IsPGroup 2 ↥(pCoreOf 2 (xL L V₂ ⊔ T)) := pCoreOf_isPGroup 2 _
  have hXTQ : xL L V₂ ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (xL L V₂ ⊔ T) : Set G) :=
    fun x hx => normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer hx)
  have hQker : ∀ k : ↥(xL L V₂ ⊔ T), k ∈ Open.pCore 2 ↥(xL L V₂ ⊔ T) →
      (k : G) ∈ pCoreOf 2 (xL L V₂ ⊔ T) := fun k hk => ⟨k, hk, rfl⟩
  clear hPp
  generalize vH T L V V₂ Y = W at *
  generalize hY T L V₂ Y = H at *
  generalize pCoreOf 2 (xL L V₂ ⊔ T) = Q at *
  set CW := Subgroup.centralizer (W : Set G) with hCW
  have : IsMulCommutative ↥W := hWe.1
  have hne0 : ∀ A B : Subgroup G, A.relIndex B ≠ 0 := fun A B =>
    (Subgroup.index_ne_zero_of_finite : (A.subgroupOf B).index ≠ 0)
  have hQ2 : (T ⊓ CW).relIndex Q ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ CW) Q T hTCQ hQT
    have h2 : (T ⊓ CW).relIndex T = CW.relIndex T := by
      rw [inf_comm]; exact Subgroup.inf_relIndex_right _ _
    rw [hTQ2, h2] at h1
    omega
  have hmul : ∀ a ∈ Q, ∀ b ∈ Q, a ∉ CW → b ∉ CW → a * b ∈ CW := by
    intro a ha b hb haC hbC
    have h2 : (T ⊓ CW).relIndex Q = 2 := by
      have h1 : (T ⊓ CW).relIndex Q ≠ 1 := fun h =>
        haC (Subgroup.relIndex_eq_one.mp h ha).2
      have := hne0 (T ⊓ CW) Q
      omega
    have h3 : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥Q) ∈ (T ⊓ CW).subgroupOf Q := by
      rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      exact iff_of_false (fun h => haC h.2) (fun h => hbC h.2)
    exact (Subgroup.mem_subgroupOf.mp h3).2
  have hconj : ∀ q ∈ Q, q ∉ CW → ∀ x ∈ xL L V₂ ⊔ T, x * q * x⁻¹ * q⁻¹ ∈ CW := by
    intro q hqQ hqC x hx
    have h1 : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hXTQ hx) q).mp hqQ
    have h2 : x * q * x⁻¹ ∉ CW := fun h =>
      hqC ((Subgroup.mem_normalizer_iff.mp (hHC (hXT hx)) q).mpr h)
    exact hmul _ h1 _ (Q.inv_mem hqQ) h2 (fun h => hqC (by simpa using CW.inv_mem h))
  obtain ⟨s, hsA, hsQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have hAH : A ≤ H := hAT.trans hTH
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have h24 : (A ⊓ CW).relIndex A = 2 ∨ (A ⊓ CW).relIndex A = 4 := by
    obtain ⟨n, hn⟩ := hAp.index ((A ⊓ CW).subgroupOf A)
    have hn' : (A ⊓ CW).relIndex A = 2 ^ n := hn
    have hA4 : (A ⊓ CW).relIndex A ≤ 4 := by
      have e : (A ⊓ CW).relIndex A = CW.relIndex A := by
        rw [inf_comm]; exact Subgroup.inf_relIndex_right _ _
      rw [e]
      exact (Subgroup.relIndex_le_of_le_right hAT (hne0 CW T)).trans hCT4
    have hA1 : (A ⊓ CW).relIndex A ≠ 1 := fun h =>
      hAQ fun a ha => hTCQ ⟨hAT ha, (Subgroup.relIndex_eq_one.mp h ha).2⟩
    rw [hn'] at hA4 hA1 ⊢
    have hn3 : n ≤ 2 := by
      by_contra h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 3 ≤ n by omega)
      norm_num at this
      omega
    interval_cases n
    · exact absurd rfl hA1
    · left; rfl
    · right; rfl
  obtain ⟨c, hcA, hcQ, hb⟩ : ∃ c ∈ A, (c = 1 ∨ (c ∈ Q ∧ c ∉ CW)) ∧
      (Nat.card W ≤ 4 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ∨
        (c ∉ CW ∧ Nat.card W ≤ 8 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)))) := by
    rcases h24 with h2 | h4
    · refine ⟨1, A.one_mem, Or.inl rfl, Or.inl ?_⟩
      rw [h2] at hcard
      omega
    · have hAQ2 : (A ⊓ Q).relIndex A ≤ 2 := by
        have e : (A ⊓ Q).relIndex A = Q.relIndex A := by
          rw [inf_comm]; exact Subgroup.inf_relIndex_right _ _
        rw [e, ← hTQ2]
        exact Subgroup.relIndex_le_of_le_right hAT (hne0 Q T)
      have hle : A ⊓ CW ≤ A ⊓ Q := fun a ha => ⟨ha.1, hTCQ ⟨hAT ha.1, ha.2⟩⟩
      have h5 := Subgroup.relIndex_mul_relIndex (A ⊓ CW) (A ⊓ Q) A hle inf_le_left
      rw [h4] at h5
      have h6 : ¬ A ⊓ Q ≤ A ⊓ CW := by
        intro h
        rw [Subgroup.relIndex_eq_one.mpr h, one_mul] at h5
        omega
      obtain ⟨c, hcAQ, hcC⟩ := IsConcreteLE.not_le_iff_exists.mp h6
      have hcC' : c ∉ CW := fun h => hcC ⟨hcAQ.1, h⟩
      refine ⟨c, hcAQ.1, Or.inr ⟨hcAQ.2, hcC'⟩, Or.inr ⟨hcC', ?_⟩⟩
      rw [h4] at hcard
      omega
  intro g hg x hx
  refine commute_of_action hWe.2 hHN hPH hPn hp5 hPp' (hAH hsA) (hAH hcA) hsA hcA (hAe.2 s hsA)
    (hAe.2 c hcA) (hAc c hcA s hsA) hb
    (S₀ := {x | x ∈ L ⊓ Subgroup.normalizer (V₂ : Set G) ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1}) ?_ g hg
    x hx
  rintro x ⟨hxL, m, hm, hxm⟩
  have hxX : x ∈ xL L V₂ := Subgroup.subset_closure ⟨hxL, m, hm, hxm⟩
  have hxXT : x ∈ xL L V₂ ⊔ T := Subgroup.mem_sup_left hxX
  have hx3 : x ^ 3 = 1 :=
    cube_of_odd hXS3 hxXT (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm))
  refine ⟨hXH hxX, hx3, fun hqC => ?_, ?_⟩
  ·
    have hxQ : x ∉ Q := by
      intro hxQ
      obtain ⟨k, hk⟩ := hQgrp ⟨x, hxQ⟩
      have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
        ((Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).coprime_dvd_left
          (orderOf_dvd_of_pow_eq_one hx3)) (orderOf_dvd_of_pow_eq_one hk')
      apply hqC
      rw [orderOf_eq_one_iff.mp h1, mul_one, mul_one, mul_inv_cancel]
      exact CW.one_mem
    have hsXT : s ∈ xL L V₂ ⊔ T := Subgroup.mem_sup_right (hAT hsA)
    have hq : s * x * s⁻¹ * x ∈ Q := by
      obtain ⟨φ, -, hφk⟩ := hXS3
      have hφ : ∀ k : ↥(xL L V₂ ⊔ T), φ k = 1 → (k : G) ∈ Q := by
        intro k hk
        rw [← MonoidHom.mem_ker, hφk] at hk
        exact hQker k hk
      have h1 : φ ⟨s, hsXT⟩ ^ 2 = 1 := by
        rw [← map_pow]
        have : (⟨s, hsXT⟩ : ↥(xL L V₂ ⊔ T)) ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 s hsA)
        rw [this, map_one]
      have h2 : φ ⟨s, hsXT⟩ ≠ 1 := fun h => hsQ (hφ _ h)
      have h3 : φ ⟨x, hxXT⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨x, hxXT⟩ : ↥(xL L V₂ ⊔ T)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
        rw [this, map_one]
      have := hφ ((⟨s, hsXT⟩ : ↥(xL L V₂ ⊔ T)) * ⟨x, hxXT⟩ * (⟨s, hsXT⟩ : ↥(xL L V₂ ⊔ T))⁻¹ *
        ⟨x, hxXT⟩) (by
          rw [map_mul, map_mul, map_mul, map_inv]
          exact s3_conj_inv _ _ h1 h2 h3)
      simpa using this
    exact ⟨hmul _ hq _ hq hqC hqC, hconj _ hq hqC x hxXT⟩
  ·
    rcases hcQ with rfl | ⟨hcQ', hcC⟩
    · rw [one_mul, inv_one, mul_one, mul_inv_cancel]
      exact CW.one_mem
    · have h1 := CW.inv_mem (hconj c hcQ' hcC x hxXT)
      have e : (x * c * x⁻¹ * c⁻¹)⁻¹ = c * x * c⁻¹ * x⁻¹ := by group
      rwa [e] at h1

end CFSG.Quasithin.H13.L32A.T53

end
