module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov9
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Syl

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

section TwSq

variable {L : Type} [Group L] {t : L} (F : TwFacts L t)
include F

theorem TwFacts.t_ne_one : t ≠ 1 := fun h => F.not_sq 1 (by rw [h, mul_one])

theorem TwFacts.φ_t : F.φ t = 1 := (F.ker_iff t).2 (Or.inr rfl)

theorem TwFacts.mul_self_of_φ {y : L} (h : F.φ y * F.φ y = 1) : y * y = 1 := by
  have h1 : F.φ (y * y) = 1 := by rw [map_mul]; exact h
  rcases (F.ker_iff _).1 h1 with h2 | h2
  · exact h2
  · exact absurd h2 (F.not_sq y)

theorem TwFacts.t_sq : t * t = 1 := F.mul_self_of_φ (by rw [F.φ_t, mul_one])

theorem TwFacts.t_central (x : L) : t * x = x * t := by
  have h1 : F.φ (x * t * x⁻¹) = 1 := by
    rw [map_mul, map_mul, F.φ_t, mul_one, map_inv, mul_inv_cancel]
  rcases (F.ker_iff _).1 h1 with h | h
  · exact absurd (by simpa using h : t = 1) F.t_ne_one
  · calc t * x = (x * t * x⁻¹) * x := by rw [h]
      _ = x * t := by group

theorem TwFacts.φ_w₂ : F.φ (F.w₂ * F.w₂) = F.z := by
  have h : F.φ (F.w₂ * F.w₂ * t) = F.φ (F.w₂ * F.w₂) := by rw [map_mul, F.φ_t, mul_one]
  rw [← h, ← F.w_rel, F.φ_sq]

theorem TwFacts.sq₁ : (F.w₁ * F.w₁) * (F.w₁ * F.w₁) = 1 :=
  F.mul_self_of_φ (by rw [F.φ_sq, F.z_sq])

theorem TwFacts.w₂_eq : F.w₂ * F.w₂ = F.w₁ * F.w₁ * t := by
  calc F.w₂ * F.w₂ = F.w₂ * F.w₂ * (t * t) := by rw [F.t_sq, mul_one]
    _ = (F.w₂ * F.w₂ * t) * t := (mul_assoc _ _ _).symm
    _ = F.w₁ * F.w₁ * t := by rw [← F.w_rel]

theorem TwFacts.z₁_central {x : L} (hx : F.φ x ∈ F.S0) :
    (F.w₁ * F.w₁) * x = x * (F.w₁ * F.w₁) := by
  have hcent : Subgroup.closure {p : L | F.φ p ∈ F.S0 ∧ p * p = 1} ≤
      Subgroup.centralizer ({F.w₁ * F.w₁} : Set L) := by
    rw [Subgroup.closure_le]
    rintro p ⟨hpS, hpp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hcomm : F.φ p * F.z = F.z * F.φ p := (F.z_central _ hpS).symm
    have h2 : (F.w₁ * F.w₁ * p) * (F.w₁ * F.w₁ * p) = 1 := by
      refine F.mul_self_of_φ ?_
      rw [map_mul, F.φ_sq]
      calc F.z * F.φ p * (F.z * F.φ p) = F.z * (F.φ p * F.z) * F.φ p := by group
        _ = F.z * (F.z * F.φ p) * F.φ p := by rw [hcomm]
        _ = (F.z * F.z) * (F.φ p * F.φ p) := by group
        _ = 1 := by rw [F.z_sq, ← map_mul, hpp, map_one, one_mul]
    have hA : (F.w₁ * F.w₁)⁻¹ = F.w₁ * F.w₁ := inv_eq_of_mul_eq_one_right F.sq₁
    have hp : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
    have h3 : F.w₁ * F.w₁ * p = (F.w₁ * F.w₁ * p)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
    rw [mul_inv_rev, hA, hp] at h3
    exact h3.symm
  have hx' : x ∈ Subgroup.closure {p : L | F.φ p ∈ F.S0 ∧ p * p = 1} := by
    rw [F.gen]
    exact hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hcent hx')).symm

theorem TwFacts.sqData : SqData t (F.S0.comap F.φ) (F.w₁ * F.w₁) (F.w₂ * F.w₂) where
  t_mem := by
    show F.φ t ∈ F.S0
    rw [F.φ_t]
    exact F.S0.one_mem
  z_mem := by
    show F.φ (F.w₁ * F.w₁) ∈ F.S0
    rw [F.φ_sq]
    exact F.z_mem
  z'_mem := by
    show F.φ (F.w₂ * F.w₂) ∈ F.S0
    rw [F.φ_w₂]
    exact F.z_mem
  ne := by
    intro h
    have h2 := h.trans F.w₂_eq
    exact F.t_ne_one (by simpa using h2)
  mul := by
    rw [F.w₂_eq]
    calc F.w₁ * F.w₁ * (F.w₁ * F.w₁ * t) = (F.w₁ * F.w₁ * (F.w₁ * F.w₁)) * t := by
          simp only [mul_assoc]
      _ = t := by rw [F.sq₁, one_mul]
  z_ne := fun h => F.z_ne (by rw [← F.φ_sq, h, map_one])
  z'_ne := fun h => F.z_ne (by rw [← F.φ_w₂, h, map_one])
  z_central := fun x hx => F.z₁_central hx
  z'_central := by
    intro x hx
    rw [F.w₂_eq]
    calc F.w₁ * F.w₁ * t * x = F.w₁ * F.w₁ * (t * x) := by rw [mul_assoc]
      _ = F.w₁ * F.w₁ * (x * t) := by rw [F.t_central x]
      _ = (F.w₁ * F.w₁ * x) * t := (mul_assoc _ _ _).symm
      _ = (x * (F.w₁ * F.w₁)) * t := by rw [F.z₁_central hx]
      _ = x * (F.w₁ * F.w₁ * t) := by rw [mul_assoc]
  z_sq := ⟨F.w₁, F.w₁_mem, rfl⟩
  z'_sq := ⟨F.w₂, F.w₂_mem, rfl⟩
  uniq := by
    rintro u huT hucent hu1 ⟨x, hxT, hxu⟩
    have hφu : ∀ h ∈ F.S0, F.φ u * h = h * F.φ u := by
      intro h hh
      obtain ⟨q, rfl⟩ := F.surj h hh
      rw [← map_mul, ← map_mul, hucent q hh]
    rcases F.center _ huT hφu with h1 | h1
    · rcases (F.ker_iff u).1 h1 with h2 | h2
      · exact absurd h2 hu1
      · exact absurd (hxu.trans h2) (F.not_sq x)
    · have h2 : F.φ ((F.w₁ * F.w₁)⁻¹ * u) = 1 := by
        rw [map_mul, map_inv, F.φ_sq, h1, inv_mul_cancel]
      rcases (F.ker_iff _).1 h2 with h3 | h3
      · exact Or.inl (inv_mul_eq_one.1 h3).symm
      · refine Or.inr ?_
        rw [F.w₂_eq]
        calc u = (F.w₁ * F.w₁) * ((F.w₁ * F.w₁)⁻¹ * u) := by group
          _ = F.w₁ * F.w₁ * t := by rw [h3]

theorem TwFacts.mem_of_isPGroup {Q₀ : Subgroup L} (hQp : IsPGroup 2 Q₀)
    (hP₀Q : F.S0.comap F.φ ≤ Q₀) {l : L} (hl : l ∈ Q₀) : F.φ l ∈ F.S0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQm : IsPGroup 2 (Q₀.map F.φ) := hQp.map F.φ
  have hdvd : Nat.card (Q₀.map F.φ) ∣ 443520 := by
    rw [← F.card_range]
    exact Subgroup.card_dvd_of_le (Subgroup.map_le_range F.φ Q₀)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQm
  have hk7 : k ≤ 7 := by
    by_contra hk8
    push Not at hk8
    have h1 : 2 ^ 8 ∣ 2 ^ k := pow_dvd_pow 2 hk8
    rw [← hk] at h1
    have h2 := dvd_trans h1 hdvd
    norm_num at h2
  have hle : F.S0 ≤ Q₀.map F.φ := fun g hg => by
    obtain ⟨x, hx⟩ := F.surj g hg
    exact ⟨x, hP₀Q (show F.φ x ∈ F.S0 from hx ▸ hg), hx⟩
  have heq : F.S0 = Q₀.map F.φ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hk, F.card_S0]
    calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
      _ = 128 := by norm_num
  have h1 : F.φ l ∈ Q₀.map F.φ := ⟨l, hl, rfl⟩
  rw [← heq] at h1
  exact h1

theorem TwFacts.isPGroup_comap (hcov : IsM22Cover L t) : IsPGroup 2 (F.S0.comap F.φ) := by
  have hS0p : IsPGroup 2 F.S0 := IsPGroup.of_card (n := 7) (by rw [F.card_S0]; norm_num)
  have hker2 : IsPGroup 2 F.φ.ker := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨x, hx⟩
    rcases (F.ker_iff x).1 hx with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [Subgroup.orderOf_mk, pow_one]; exact hcov.orderOf_t⟩
  exact hS0p.comap_of_ker_isPGroup F.φ hker2

end TwSq

section CExt

variable {G : Type*} [Group G]

@[expose] def cExt (P : Subgroup G) (c : G) (hc2 : c * c = 1) (hcP : ∀ x ∈ P, c * x = x * c) :
    Subgroup G where
  carrier := {x | x ∈ P ∨ ∃ y ∈ P, x = y * c}
  mul_mem' := by
    rintro a b (ha | ⟨a', ha', rfl⟩) (hb | ⟨b', hb', rfl⟩)
    · exact Or.inl (P.mul_mem ha hb)
    · exact Or.inr ⟨a * b', P.mul_mem ha hb', by rw [mul_assoc]⟩
    · refine Or.inr ⟨a' * b, P.mul_mem ha' hb, ?_⟩
      calc a' * c * b = a' * (c * b) := by rw [mul_assoc]
        _ = a' * (b * c) := by rw [hcP b hb]
        _ = a' * b * c := by rw [mul_assoc]
    · refine Or.inl ?_
      have : a' * c * (b' * c) = a' * b' := by
        calc a' * c * (b' * c) = a' * (c * b') * c := by simp only [mul_assoc]
          _ = a' * (b' * c) * c := by rw [hcP b' hb']
          _ = a' * b' * (c * c) := by simp only [mul_assoc]
          _ = a' * b' := by rw [hc2, mul_one]
      rw [this]
      exact P.mul_mem ha' hb'
  one_mem' := Or.inl P.one_mem
  inv_mem' := by
    rintro a (ha | ⟨a', ha', rfl⟩)
    · exact Or.inl (P.inv_mem ha)
    · refine Or.inr ⟨a'⁻¹, P.inv_mem ha', ?_⟩
      have hc : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
      rw [mul_inv_rev, hc]
      exact hcP _ (P.inv_mem ha')

variable {P : Subgroup G} {c : G} {hc2 : c * c = 1} {hcP : ∀ x ∈ P, c * x = x * c}

theorem le_cExt : P ≤ cExt P c hc2 hcP := fun _ hx => Or.inl hx

theorem c_mem_cExt : c ∈ cExt P c hc2 hcP := Or.inr ⟨1, P.one_mem, (one_mul c).symm⟩

theorem c_central_cExt : ∀ x ∈ cExt P c hc2 hcP, c * x = x * c := by
  rintro x (hx | ⟨y, hy, rfl⟩)
  · exact hcP x hx
  · calc c * (y * c) = (c * y) * c := by rw [mul_assoc]
      _ = (y * c) * c := by rw [hcP y hy]

theorem isPGroup_cExt (hP : IsPGroup 2 P) : IsPGroup 2 (cExt P c hc2 hcP) := by
  rintro ⟨x, hx | ⟨y, hy, rfl⟩⟩
  · obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  · obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k + 1, Subtype.ext ?_⟩
    show (y * c) ^ 2 ^ (k + 1) = 1
    have hcomm : Commute y c := (hcP y hy).symm
    have e1 : y ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk', one_pow]
    have e2 : c ^ 2 ^ (k + 1) = 1 := by
      have : c ^ 2 = 1 := by rw [sq]; exact hc2
      rw [pow_succ, pow_mul', this, one_pow]
    rw [hcomm.mul_pow, e1, e2, one_mul]

theorem central_mul {T : Subgroup G} {a b : G} (ha : ∀ x ∈ T, a * x = x * a)
    (hb : ∀ x ∈ T, b * x = x * b) : ∀ x ∈ T, (a * b) * x = x * (a * b) := by
  intro x hx
  calc a * b * x = a * (b * x) := by rw [mul_assoc]
    _ = a * (x * b) := by rw [hb x hx]
    _ = (a * x) * b := by rw [mul_assoc]
    _ = (x * a) * b := by rw [ha x hx]
    _ = x * (a * b) := by rw [mul_assoc]

theorem SqData.cExt {t z z' : G} (h : SqData t P z z') :
    SqData t (cExt P c hc2 hcP) z z' where
  t_mem := le_cExt h.t_mem
  z_mem := le_cExt h.z_mem
  z'_mem := le_cExt h.z'_mem
  ne := h.ne
  mul := h.mul
  z_ne := h.z_ne
  z'_ne := h.z'_ne
  z_central := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact h.z_central x hx
    · calc z * (y * c) = (z * y) * c := by rw [mul_assoc]
        _ = (y * z) * c := by rw [h.z_central y hy]
        _ = y * (z * c) := by rw [mul_assoc]
        _ = y * (c * z) := by rw [(hcP z h.z_mem).symm]
        _ = y * c * z := by rw [mul_assoc]
  z'_central := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact h.z'_central x hx
    · calc z' * (y * c) = (z' * y) * c := by rw [mul_assoc]
        _ = (y * z') * c := by rw [h.z'_central y hy]
        _ = y * (z' * c) := by rw [mul_assoc]
        _ = y * (c * z') := by rw [(hcP z' h.z'_mem).symm]
        _ = y * c * z' := by rw [mul_assoc]
  z_sq := by
    obtain ⟨x, hx, hxz⟩ := h.z_sq
    exact ⟨x, le_cExt hx, hxz⟩
  z'_sq := by
    obtain ⟨x, hx, hxz⟩ := h.z'_sq
    exact ⟨x, le_cExt hx, hxz⟩
  uniq := by
    rintro u hu hcentral hu1 ⟨x, hx, hxu⟩
    have hsq : ∃ y ∈ P, y * y = u := by
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact ⟨x, hx, hxu⟩
      · refine ⟨y, hy, ?_⟩
        rw [← hxu]
        calc y * y = y * y * (c * c) := by rw [hc2, mul_one]
          _ = y * (y * c) * c := by simp only [mul_assoc]
          _ = y * (c * y) * c := by rw [← hcP y hy]
          _ = y * c * (y * c) := by simp only [mul_assoc]
    obtain ⟨y, hy, hyu⟩ := hsq
    exact h.uniq u (hyu ▸ P.mul_mem hy hy) (fun w hw => hcentral w (le_cExt hw)) hu1
      ⟨y, hy, hyu⟩

end CExt

end CFSG.EvenSporadicStandard.M22Std
