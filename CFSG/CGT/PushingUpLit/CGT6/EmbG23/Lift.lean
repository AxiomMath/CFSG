module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbG23

open scoped commutatorElement

theorem commutator_mul_central {L : Type*} [Group L] {a b z w : L}
    (hz : z ∈ Subgroup.center L) (hw : w ∈ Subgroup.center L) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have cc : ∀ {c : L}, c ∈ Subgroup.center L → ∀ x, c * x * c⁻¹ = x := by
    intro c hc x
    have := Subgroup.mem_center_iff.1 hc x
    rw [← this]
    simp
  simp only [commutatorElement_def, mul_inv_rev]
  have h1 := cc hz (b * w)
  have h2 := cc hw a⁻¹
  calc a * z * (b * w) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹)
      = a * (z * (b * w) * z⁻¹) * a⁻¹ * (w⁻¹ * b⁻¹) := by simp only [mul_assoc]
    _ = a * (b * w) * a⁻¹ * (w⁻¹ * b⁻¹) := by rw [h1]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by simp only [mul_assoc]
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

theorem eq_one_of_pow_eight {L : Type*} [Group L] {z : L} (hz : Odd (orderOf z))
    (h8 : z ^ 8 = 1) : z = 1 := by
  have hdvd : orderOf z ∣ 2 ^ 3 := by simpa using orderOf_dvd_of_pow_eq_one h8
  obtain ⟨i, -, hzi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    have h2 : Even (2 ^ i) := Nat.even_pow.2 ⟨even_two, hne⟩
    rw [← hzi] at h2
    exact (Nat.not_even_iff_odd.2 hz) h2
  rw [hi0, pow_zero] at hzi
  exact orderOf_eq_one_iff.1 hzi

theorem lift_generation {L : Type*} [Group L] [Group.IsPerfect L]
    (hodd : ∀ z ∈ Subgroup.center L, Odd (orderOf z))
    {Y S : Subgroup L} (hS8 : Nat.card S = 8) {g : L}
    (hgS : QuotientGroup.mk' (Subgroup.center L) g ∈ Subgroup.normalizer
      ((S.map (QuotientGroup.mk' (Subgroup.center L)) :
        Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L)))
    (hgen : Y.map (QuotientGroup.mk' (Subgroup.center L)) ⊔
      (Y.map (QuotientGroup.mk' (Subgroup.center L))).map
        (MulAut.conj (QuotientGroup.mk' (Subgroup.center L) g)).toMonoidHom = ⊤) :
    g ∈ Subgroup.normalizer (S : Set L) ∧ Y ⊔ Y.map (MulAut.conj g).toMonoidHom = ⊤ := by
  set Z : Subgroup L := Subgroup.center L with hZ
  set mk : L →* L ⧸ Z := QuotientGroup.mk' Z with hmk
  have hfinS : Finite ↥S := Nat.finite_of_card_ne_zero (by rw [hS8]; norm_num)
  have hS8' : ∀ x ∈ S, x ^ 8 = 1 := by
    intro x hx
    have h := pow_card_eq_one' (G := ↥S) (x := ⟨x, hx⟩)
    rw [hS8] at h
    simpa using congrArg Subtype.val h
  have hle : ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro x hx
    have hmem : mk (g * x * g⁻¹) ∈ S.map mk := by
      have h1 : mk x ∈ S.map mk := ⟨x, hx, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hgS (mk x)).1 h1
      simpa [map_mul] using h2
    obtain ⟨s, hs, hse⟩ := hmem
    set z : L := s⁻¹ * (g * x * g⁻¹) with hzdef
    have hzmem : z ∈ Z := QuotientGroup.eq.1 hse
    have hw : g * x * g⁻¹ = s * z := by rw [hzdef]; group
    have h8 : (g * x * g⁻¹) ^ 8 = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, hS8' x hx, map_one]
    have hs8 : s ^ 8 = 1 := hS8' s hs
    have hcomm : Commute s z := Subgroup.mem_center_iff.1 hzmem s
    have hz8 : z ^ 8 = 1 := by
      rw [hw, hcomm.mul_pow, hs8, one_mul] at h8
      exact h8
    have hz1 : z = 1 := eq_one_of_pow_eight (hodd z hzmem) hz8
    rw [hw, hz1, mul_one]
    exact hs
  have hnorm : g ∈ Subgroup.normalizer (S : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hle h, fun hh => ?_⟩
    have hmapeq : S.map (MulAut.conj g).toMonoidHom = S := by
      refine Subgroup.eq_of_le_of_card_ge (H := S.map (MulAut.conj g).toMonoidHom) ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hle x hx
      · exact (Nat.card_congr (S.equivMapOfInjective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toEquiv).le
    have hh' : g * h * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := by
      rw [hmapeq]
      exact hh
    obtain ⟨h', hh'', he⟩ := hh'
    have : h' = h := (MulAut.conj g).injective (by simpa [MulAut.conj_apply] using he)
    rw [← this]
    exact hh''
  refine ⟨hnorm, ?_⟩
  set D : Subgroup L := Y ⊔ Y.map (MulAut.conj g).toMonoidHom with hD
  have hcomp : mk.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (mk g)).toMonoidHom.comp mk := by
    ext y
    simp [MulAut.conj_apply]
  have hmapD : D.map mk =
      Y.map mk ⊔ (Y.map mk).map (MulAut.conj (mk g)).toMonoidHom := by
    rw [hD, Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map, hcomp]
  have hdec : ∀ x : L, ∃ d ∈ D, ∃ z ∈ Z, x = d * z := by
    intro x
    have hx : mk x ∈ D.map mk := by
      rw [hmapD, hgen]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hdx⟩ := hx
    exact ⟨d, hd, d⁻¹ * x, QuotientGroup.eq.1 hdx, by group⟩
  have hcommle : commutator L ≤ D := by
    rw [commutator_def, Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨g₁, -, g₂, -, rfl⟩
    obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hdec g₁
    obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hdec g₂
    show ⁅d₁ * z₁, d₂ * z₂⁆ ∈ D
    rw [commutator_mul_central hz₁ hz₂, commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ hd₂) (D.inv_mem hd₁)) (D.inv_mem hd₂)
  rw [eq_top_iff]
  intro x _
  apply hcommle
  rw [Group.IsPerfect.commutator_eq_top]
  exact Subgroup.mem_top x

end CFSG.CGT.PushingUpLit.CGT6.EmbG23
