module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G} {q : ℕ}

open Classical in
@[expose] noncomputable def deltaCoord (L T : Subgroup G) (t : G) (Q : Subgroup G) : G :=
  if h : ∃ a, a ∈ gmsA L T ∧ a * t ∈ Q then h.choose else 1

omit [Finite G] in
theorem eq_deltaCoord (h313 : Lemma313 L T q) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) {t a : G}
    (ha : a ∈ gmsA L T) (hat : a * t ∈ Q) : a = deltaCoord L T t Q := by
  have hex : ∃ a, a ∈ gmsA L T ∧ a * t ∈ Q := ⟨a, ha, hat⟩
  rw [deltaCoord, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hc, hct⟩ := hex.choose_spec
  have h1 : a * hex.choose⁻¹ ∈ Q ⊓ gmsA L T := by
    refine mem_inf.mpr ⟨?_, mul_mem ha (inv_mem hc)⟩
    have := mul_mem hat (inv_mem hct)
    simpa [mul_assoc] using this
  rw [h313.inf_gmsA_eq_bot hQ, mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem deltaCoord_spec
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation)
    {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) :
    deltaCoord L T t Q ∈ gmsA L T ∧ deltaCoord L T t Q * t ∈ Q := by
  obtain ⟨a, ha, hat⟩ := h313.exists_mul_mem hX h hF hQ (mem_sup_right ht)
  rw [← eq_deltaCoord h313 hQ ha hat]
  exact ⟨ha, hat⟩

omit [Finite G] in
theorem deltaCoord_T₀ (h313 : Lemma313 L T q) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) :
    deltaCoord L T t (T ⊓ centralizer (L : Set G)) = 1 :=
  (eq_deltaCoord h313 mem_delta_T₀ (one_mem _) (by simpa using ht)).symm

omit [Finite G] in
theorem deltaCoord_one (h313 : Lemma313 L T q) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) :
    deltaCoord L T 1 Q = 1 :=
  (eq_deltaCoord h313 hQ (one_mem _) (by simp)).symm

theorem deltaCoord_conj
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation)
    {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G))
    {n : G} (hn : n ∈ gmsN₁ L T) :
    deltaCoord L T t (rightConjugate Q n⁻¹) =
      n * deltaCoord L T t Q * n⁻¹ * (n * t * n⁻¹ * t⁻¹) := by
  obtain ⟨hnV, hnA, hnc⟩ := mem_gmsN₁.mp hn
  obtain ⟨ha, hat⟩ := deltaCoord_spec h313 hX h hF hQ ht
  have hQ' := rightConjugate_mem_delta hQ (inv_mem hnV)
  refine (eq_deltaCoord h313 hQ' (mul_mem ((mem_normalizer_iff.mp hnA _).mp ha)
    (hnc t (mem_sup_right ht))) ?_).symm
  rw [mem_rightConjugate_iff]
  have : n⁻¹ * (n * deltaCoord L T t Q * n⁻¹ * (n * t * n⁻¹ * t⁻¹) * t) * n⁻¹⁻¹ =
      deltaCoord L T t Q * t := by group
  rw [this]
  exact hat

theorem deltaCoord_bijective
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {t₁ : G}
    (ht₁ : t₁ ∈ T ⊓ centralizer (L : Set G)) (ht₁1 : t₁ ≠ 1) :
    Function.Bijective (fun Q : gmsDelta L T =>
      (⟨deltaCoord L T t₁ Q, (deltaCoord_spec h313 hX h hF Q.2 ht₁).1⟩ : gmsA L T)) := by
  refine Function.Injective.bijective_of_nat_card_le (fun Q Q' hQQ' => ?_) ?_
  · have hc : deltaCoord L T t₁ Q = deltaCoord L T t₁ Q' := congrArg Subtype.val hQQ'
    obtain ⟨hcA, hcQ⟩ := deltaCoord_spec h313 hX h hF Q.2 ht₁
    obtain ⟨-, hcQ'⟩ := deltaCoord_spec h313 hX h hF Q'.2 ht₁
    rw [← hc] at hcQ'
    by_contra hne
    have hne' : (Q : Subgroup G) ≠ Q' := fun h1 => hne (Subtype.ext h1)
    have h1 : deltaCoord L T t₁ Q * t₁ ∈ (Q : Subgroup G) ⊓ Q' := mem_inf.mpr ⟨hcQ, hcQ'⟩
    rw [h313.inf_eq_bot _ Q.2 _ Q'.2 hne', mem_bot] at h1
    have h2 : t₁ ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := by
      refine mem_inf.mpr ⟨ht₁, ?_⟩
      have : t₁ = (deltaCoord L T t₁ Q)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact inv_mem hcA
    rw [h313.inf_gmsA_eq_bot mem_delta_T₀, mem_bot] at h2
    exact ht₁1 h2
  · rw [h313.card_eq, (hX.sylow h).1]

namespace IsTorus

variable {y : G}

theorem deltaCoord_pow
    (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T)
    (hF : Foundation) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) (k : ℕ) :
    deltaCoord L T t (rightConjugate Q (y ^ k)) = (y ^ k)⁻¹ * deltaCoord L T t Q * y ^ k := by
  obtain ⟨ha, hat⟩ := deltaCoord_spec h313 hX h hF hQ ht
  have hQ' := rightConjugate_mem_delta hQ (pow_mem hy.mem_normalizer k)
  have hyA : (y ^ k)⁻¹ ∈ normalizer (gmsA L T : Set G) := inv_mem (pow_mem hy.mem_normalizer_gmsA k)
  have hc : (y ^ k)⁻¹ * deltaCoord L T t Q * y ^ k ∈ gmsA L T := by
    simpa using (mem_normalizer_iff.mp hyA _).mp ha
  refine (eq_deltaCoord h313 hQ' hc ?_).symm
  rw [mem_rightConjugate_iff]
  have hyt : y ^ k * t = t * y ^ k := Commute.pow_left (hy.commute ht) k
  have : y ^ k * ((y ^ k)⁻¹ * deltaCoord L T t Q * y ^ k * t) * (y ^ k)⁻¹ =
      deltaCoord L T t Q * t := by
    calc y ^ k * ((y ^ k)⁻¹ * deltaCoord L T t Q * y ^ k * t) * (y ^ k)⁻¹
        = deltaCoord L T t Q * (y ^ k * t) * (y ^ k)⁻¹ := by group
      _ = deltaCoord L T t Q * t := by rw [hyt]; group
  rw [this]
  exact hat

theorem exists_pow_deltaCoord
    (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T)
    (hF : Foundation) {t₁ t : G} (ht₁ : t₁ ∈ T ⊓ centralizer (L : Set G)) (ht₁1 : t₁ ≠ 1)
    (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1) :
    ∃ m : ℕ, ∀ Q ∈ gmsDelta L T,
      deltaCoord L T t Q = (y ^ m)⁻¹ * deltaCoord L T t₁ Q * y ^ m := by
  obtain ⟨Q₁, hQ₁⟩ := exists_ne_deltaT₀ h313 hX
  have hQ₁T : (Q₁ : Subgroup G) ≠ T ⊓ centralizer (L : Set G) := fun h1 => hQ₁ (Subtype.ext h1)
  have hne1 : ∀ s ∈ T ⊓ centralizer (L : Set G), s ≠ 1 → deltaCoord L T s Q₁ ≠ 1 := by
    intro s hs hs1 h1
    have h2 := (deltaCoord_spec h313 hX h hF Q₁.2 hs).2
    rw [h1, one_mul] at h2
    have h3 : s ∈ (Q₁ : Subgroup G) ⊓ (T ⊓ centralizer (L : Set G)) := mem_inf.mpr ⟨h2, hs⟩
    rw [h313.inf_eq_bot _ Q₁.2 _ mem_delta_T₀ hQ₁T, mem_bot] at h3
    exact hs1 h3
  obtain ⟨m, hm⟩ := hy.trans _ (deltaCoord_spec h313 hX h hF Q₁.2 ht₁).1 _
    (deltaCoord_spec h313 hX h hF Q₁.2 ht).1 (hne1 t₁ ht₁ ht₁1) (hne1 t ht ht1)
  refine ⟨m, fun Q hQ => ?_⟩
  by_cases hQT : Q = T ⊓ centralizer (L : Set G)
  · rw [hQT, deltaCoord_T₀ h313 ht, deltaCoord_T₀ h313 ht₁]
    group
  obtain ⟨k, rfl⟩ := hy.exists_pow_eq h313 hX h Q₁.2 hQ₁T hQ hQT
  rw [hy.deltaCoord_pow h313 hX h hF Q₁.2 ht, hy.deltaCoord_pow h313 hX h hF Q₁.2 ht₁, ← hm]
  have hkm : y ^ k * y ^ m = y ^ m * y ^ k := by rw [← pow_add, ← pow_add, add_comm]
  calc (y ^ k)⁻¹ * ((y ^ m)⁻¹ * deltaCoord L T t₁ Q₁ * y ^ m) * y ^ k
      = (y ^ m * y ^ k)⁻¹ * deltaCoord L T t₁ Q₁ * (y ^ m * y ^ k) := by group
    _ = (y ^ k * y ^ m)⁻¹ * deltaCoord L T t₁ Q₁ * (y ^ k * y ^ m) := by rw [hkm]
    _ = (y ^ m)⁻¹ * ((y ^ k)⁻¹ * deltaCoord L T t₁ Q₁ * y ^ k) * y ^ m := by group

theorem conj_comm_of_mem_gmsN₁
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation)
    {t₁ t : G} (ht₁ : t₁ ∈ T ⊓ centralizer (L : Set G)) (ht₁1 : t₁ ≠ 1)
    (ht : t ∈ T ⊓ centralizer (L : Set G)) {m : ℕ}
    (hm : ∀ Q ∈ gmsDelta L T, deltaCoord L T t Q = (y ^ m)⁻¹ * deltaCoord L T t₁ Q * y ^ m)
    {n : G} (hn : n ∈ gmsN₁ L T) {a : G} (ha : a ∈ gmsA L T) :
    n * ((y ^ m)⁻¹ * a * y ^ m) * n⁻¹ = (y ^ m)⁻¹ * (n * a * n⁻¹) * y ^ m := by
  obtain ⟨Q, hQ⟩ := (deltaCoord_bijective h313 hX h hF ht₁ ht₁1).2 ⟨a, ha⟩
  have hQa : deltaCoord L T t₁ Q = a := congrArg Subtype.val hQ
  have hnV := (GMS78.mem_gmsN₁.mp hn).1
  have hQ' := rightConjugate_mem_delta Q.2 (inv_mem hnV)
  have hT' := rightConjugate_mem_delta mem_delta_T₀ (inv_mem hnV)
  have hη : n * t * n⁻¹ * t⁻¹ = (y ^ m)⁻¹ * (n * t₁ * n⁻¹ * t₁⁻¹) * y ^ m := by
    have h1 := deltaCoord_conj h313 hX h hF mem_delta_T₀ ht hn
    have h2 := deltaCoord_conj h313 hX h hF mem_delta_T₀ ht₁ hn
    rw [deltaCoord_T₀ h313 ht] at h1
    rw [deltaCoord_T₀ h313 ht₁] at h2
    have h3 := hm _ hT'
    rw [h1, h2] at h3
    simpa using h3
  have h1 := deltaCoord_conj h313 hX h hF Q.2 ht hn
  have h2 := deltaCoord_conj h313 hX h hF Q.2 ht₁ hn
  have h3 := hm _ hQ'
  rw [h1, h2, hm _ Q.2, hQa, hη] at h3
  have h4 : n * ((y ^ m)⁻¹ * a * y ^ m) * n⁻¹ * ((y ^ m)⁻¹ * (n * t₁ * n⁻¹ * t₁⁻¹) * y ^ m) =
      (y ^ m)⁻¹ * (n * a * n⁻¹) * y ^ m * ((y ^ m)⁻¹ * (n * t₁ * n⁻¹ * t₁⁻¹) * y ^ m) := by
    rw [h3]
    group
  exact mul_right_cancel h4

end IsTorus

end Sec3

end CFSG.ComponentClassification.GMS78
