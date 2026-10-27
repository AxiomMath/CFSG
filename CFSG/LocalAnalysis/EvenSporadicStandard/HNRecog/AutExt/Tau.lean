module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.F5Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem tau_of_index_two {K N : Subgroup G} {t : G} (hNK : N ≤ K) (htN : t ∈ N)
    (hcent : ∀ g ∈ K, g * t = t * g) (ht2 : t * t = 1)
    (hidx : ∀ x ∈ K, ∀ y ∈ K, x ∉ N → y ∉ N → x * y ∈ N) :
    ∃ τ : G → G, IsIsoOn K K τ ∧ (∀ g ∈ N, τ g = g) ∧ ∀ g ∈ K, g ∉ N → τ g = g * t := by
  classical
  let τ : G → G := fun g => if g ∈ N then g else g * t
  have hτN : ∀ g ∈ N, τ g = g := by
    intro g hg
    dsimp only [τ]
    rw [if_pos hg]
  have hτK : ∀ g ∈ K, g ∉ N → τ g = g * t := by
    intro g _ hgn
    dsimp only [τ]
    rw [if_neg hgn]
  have htK : t ∈ K := hNK htN
  refine ⟨τ, ⟨?_, ?_, ?_, ?_⟩, hτN, hτK⟩
  ·
    intro x hx y hy
    by_cases hxN : x ∈ N
    · by_cases hyN : y ∈ N
      · rw [hτN x hxN, hτN y hyN, hτN (x * y) (N.mul_mem hxN hyN)]
      · have hxyN : x * y ∉ N := fun hc => hyN (by
          have hm : x⁻¹ * (x * y) ∈ N := N.mul_mem (N.inv_mem hxN) hc
          rwa [inv_mul_cancel_left] at hm)
        rw [hτN x hxN, hτK y hy hyN, hτK (x * y) (K.mul_mem hx hy) hxyN,
          mul_assoc x y t]
    · by_cases hyN : y ∈ N
      · have hxyN : x * y ∉ N := fun hc => hxN (by
          have hm : (x * y) * y⁻¹ ∈ N := N.mul_mem hc (N.inv_mem hyN)
          rwa [mul_inv_cancel_right] at hm)
        rw [hτK x hx hxN, hτN y hyN, hτK (x * y) (K.mul_mem hx hy) hxyN,
          mul_assoc x y t, mul_assoc x t y, ← hcent y hy]
      · have hxyN : x * y ∈ N := hidx x hx y hy hxN hyN
        rw [hτK x hx hxN, hτK y hy hyN, hτN (x * y) hxyN,
          mul_assoc, ← mul_assoc t y t, ← hcent y hy, mul_assoc y t t, ht2, mul_one]
  ·
    intro x hx
    by_cases hxN : x ∈ N
    · rw [hτN x hxN]; exact hx
    · rw [hτK x hx hxN]; exact K.mul_mem hx htK
  ·
    intro x hx y hy h
    by_cases hxN : x ∈ N
    · by_cases hyN : y ∈ N
      · rwa [hτN x hxN, hτN y hyN] at h
      · rw [hτN x hxN, hτK y hy hyN] at h
        have hyx : y = x * t := by rw [h, mul_assoc, ht2, mul_one]
        exact absurd (by rw [hyx]; exact N.mul_mem hxN htN) hyN
    · by_cases hyN : y ∈ N
      · rw [hτK x hx hxN, hτN y hyN] at h
        have hxy : x = y * t := by rw [← h, mul_assoc, ht2, mul_one]
        exact absurd (by rw [hxy]; exact N.mul_mem hyN htN) hxN
      · rw [hτK x hx hxN, hτK y hy hyN] at h
        exact mul_right_cancel h
  ·
    intro y hy
    by_cases hyN : y ∈ N
    · exact ⟨y, hy, hτN y hyN⟩
    · refine ⟨y * t, K.mul_mem hy htK, ?_⟩
      have hytN : y * t ∉ N := fun hc => hyN (by
        have hm : y = (y * t) * t := by rw [mul_assoc, ht2, mul_one]
        rw [hm]; exact N.mul_mem hc htN)
      rw [hτK (y * t) (K.mul_mem hy htK) hytN, mul_assoc, ht2, mul_one]

theorem derived_Gx_a (h : F5Std a z) :
    a ∈ derivedOf (Gx a) ∧ ∀ x ∈ Gx a, ∀ y ∈ Gx a, x ∉ derivedOf (Gx a) →
      y ∉ derivedOf (Gx a) → x * y ∈ derivedOf (Gx a) := by
  classical
  obtain ⟨E, hE⟩ := h.typ.cent_a
  have hcomm : _root_.commutator ↥(Gx a) = E :=
    TwoHSData.commutator_eq_of_isF5Centralizer hE
  have ha_center : GxSelf a ∈ Subgroup.center ↥(Gx a) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_Gx.mp g.2).symm
  refine ⟨?_, ?_⟩
  · rw [mem_derivedOf_iff]
    refine ⟨self_mem_Gx a, ?_⟩
    rw [hcomm]
    exact hE.centralizer_le (by
      rw [Subgroup.mem_centralizer_iff]
      intro e _
      exact Subgroup.mem_center_iff.mp ha_center e)
  · intro x hx y hy hxN hyN
    have hxE : (⟨x, hx⟩ : ↥(Gx a)) ∉ E := fun hc =>
      hxN (by rw [mem_derivedOf_iff]; exact ⟨hx, by rwa [hcomm]⟩)
    have hyE : (⟨y, hy⟩ : ↥(Gx a)) ∉ E := fun hc =>
      hyN (by rw [mem_derivedOf_iff]; exact ⟨hy, by rwa [hcomm]⟩)
    have hmul : (⟨x, hx⟩ : ↥(Gx a)) * ⟨y, hy⟩ ∈ E := by
      rw [Subgroup.mul_mem_iff_of_index_two hE.index_eq_two]
      exact ⟨fun hc => (hxE hc).elim, fun hc => (hyE hc).elim⟩
    rw [mem_derivedOf_iff]
    exact ⟨(Gx a).mul_mem hx hy, by rwa [hcomm]⟩

theorem derived_Gx_z (h : F5Std a z) :
    z ∈ derivedOf (Gx z) ∧ ∀ x ∈ Gx z, ∀ y ∈ Gx z, x ∉ derivedOf (Gx z) →
      y ∉ derivedOf (Gx z) → x * y ∈ derivedOf (Gx z) := by
  classical
  haveI : Finite G := h.finite
  obtain ⟨Q, hQn, hAH⟩ := h.loc.gz9.self.aschbacher
  haveI : Q.Normal := hQn
  have hz_center : GxSelf z ∈ Subgroup.center ↥(Gx z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_Gx.mp g.2).symm
  have hzQ : GxSelf z ∈ Q :=
    hAH.centralizer_le (by
      rw [Subgroup.mem_centralizer_iff]
      intro e _
      exact Subgroup.mem_center_iff.mp hz_center e)
  have hle : Q ≤ _root_.commutator ↥(Gx z) := hAH.le_commutator
  have hidx : (_root_.commutator ↥(Gx z)).index = 2 := hAH.index_commutator
  refine ⟨?_, ?_⟩
  · rw [mem_derivedOf_iff]
    exact ⟨self_mem_Gx z, hle hzQ⟩
  · intro x hx y hy hxN hyN
    have hxE : (⟨x, hx⟩ : ↥(Gx z)) ∉ _root_.commutator ↥(Gx z) := fun hc =>
      hxN (by rw [mem_derivedOf_iff]; exact ⟨hx, hc⟩)
    have hyE : (⟨y, hy⟩ : ↥(Gx z)) ∉ _root_.commutator ↥(Gx z) := fun hc =>
      hyN (by rw [mem_derivedOf_iff]; exact ⟨hy, hc⟩)
    have hmul : (⟨x, hx⟩ : ↥(Gx z)) * ⟨y, hy⟩ ∈ _root_.commutator ↥(Gx z) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact ⟨fun hc => (hxE hc).elim, fun hc => (hyE hc).elim⟩
    rw [mem_derivedOf_iff]
    exact ⟨(Gx z).mul_mem hx hy, hmul⟩

theorem exists_tau (h : F5Std a z) {t : G} (ht : IsConj a t ∨ IsConj z t) :
    ∃ τ : G → G, IsIsoOn (Gx t) (Gx t) τ ∧ (∀ g ∈ derivedOf (Gx t), τ g = g) ∧
      ∀ g ∈ Gx t, g ∉ derivedOf (Gx t) → τ g = g * t := by
  have ht2 : t * t = 1 := by
    have h2 : t ^ 2 = 1 := by simpa [h.orderOf_eq_two ht] using pow_orderOf_eq_one t
    rwa [← pow_two]
  have hcent : ∀ g ∈ Gx t, g * t = t * g := fun g hg => (mem_Gx.mp hg).symm
  rcases ht with ht | ht
  · obtain ⟨htN, hidx⟩ := derived_Gx_a (h.of_isConj ht (IsConj.refl z))
    exact tau_of_index_two (derivedOf_le _) htN hcent ht2 hidx
  · obtain ⟨htN, hidx⟩ := derived_Gx_z (h.of_isConj (IsConj.refl a) ht)
    exact tau_of_index_two (derivedOf_le _) htN hcent ht2 hidx

end CFSG.EvenSporadicStandard.HNRecog.Section4
