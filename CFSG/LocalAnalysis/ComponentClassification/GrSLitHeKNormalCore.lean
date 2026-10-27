module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKNormalComp

public section

namespace CFSG.ComponentClassification.GrSLit.HeKN

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type} [Group X]

theorem false_of_normalized {K K' Z : Subgroup X} {a w : X} (hZK : Z ≤ K)
    (hK'K : ∀ k ∈ K, ∀ y ∈ K', k * y = y * k) (haK : ∀ k ∈ K, a * k = k * a)
    (hI : ∀ v : X, v * v = 1 → a * v = v * a → (∀ k ∈ K, v * k = k * v) →
      ∃ z ∈ Z, v = z ∨ v = z * a)
    (hw : w ∈ K') (hww : w * w = 1) (haw : w * a = a * w)
    (hnz : ¬ ∀ k ∈ K', w * k = k * w)
    (hnc : ¬ ∀ k ∈ K', (w⁻¹ * a) * k = k * (w⁻¹ * a)) : False := by
  obtain ⟨z, hz, hv⟩ := hI w hww haw.symm fun k hk => (hK'K k hk w hw).symm
  have hzK : z ∈ K := hZK hz
  rcases hv with hv | hv
  · apply hnz
    intro k hk
    rw [hv]
    exact hK'K z hzK k hk
  · apply hnc
    intro k hk
    have haz : a * z⁻¹ = z⁻¹ * a := (Commute.inv_right (haK z hzK : Commute a z)).eq
    have h1 : w⁻¹ * a = z⁻¹ := by
      rw [hv]
      calc (z * a)⁻¹ * a = a⁻¹ * (z⁻¹ * a) := by group
        _ = a⁻¹ * (a * z⁻¹) := by rw [haz]
        _ = z⁻¹ := by group
    rw [h1]
    exact hK'K z⁻¹ (inv_mem hzK) k hk

theorem false_of_swapped {K K' Z : Subgroup X} {a w : X} (haa : a * a = 1) (hZK : Z ≤ K)
    (hK'K : ∀ k ∈ K, ∀ y ∈ K', k * y = y * k)
    (hK''K : ∀ k ∈ K, ∀ y ∈ K'.map (MulAut.conj a).toMonoidHom, k * y = y * k)
    (hK'K'' : ∀ x ∈ K', ∀ y ∈ K'.map (MulAut.conj a).toMonoidHom, x * y = y * x)
    (hne : ¬ K'.map (MulAut.conj a).toMonoidHom ≤ K')
    (hI : ∀ v : X, v * v = 1 → a * v = v * a → (∀ k ∈ K, v * k = k * v) →
      ∃ z ∈ Z, v = z ∨ v = z * a)
    (hw : w ∈ K') (hww : w * w = 1) (hnz : ¬ ∀ k ∈ K', w * k = k * w) : False := by
  obtain ⟨w', hw'def, hw'm⟩ : ∃ w', w' = a * w * a⁻¹ ∧ w' ∈ K'.map (MulAut.conj a).toMonoidHom :=
    ⟨a * w * a⁻¹, rfl, w, hw, by simp [MulAut.conj_apply]⟩
  have hw'w' : w' * w' = 1 := by
    rw [hw'def]
    calc a * w * a⁻¹ * (a * w * a⁻¹) = a * (w * w) * a⁻¹ := by group
      _ = 1 := by rw [hww]; group
  have haw' : a * w' * a⁻¹ = w := by
    rw [hw'def]
    calc a * (a * w * a⁻¹) * a⁻¹ = (a * a) * w * (a * a)⁻¹ := by group
      _ = w := by rw [haa]; group
  have hww' : w * w' = w' * w := hK'K'' w hw w' hw'm
  have hvv : (w * w') * (w * w') = 1 := by
    calc w * w' * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [← hww']
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [hww, hw'w']; group
  have hav : a * (w * w') = (w * w') * a := by
    calc a * (w * w') = (a * w * a⁻¹) * (a * w' * a⁻¹) * a := by group
      _ = w' * w * a := by rw [← hw'def, haw']
      _ = w * w' * a := by rw [hww']
  have hvK : ∀ k ∈ K, (w * w') * k = k * (w * w') := by
    intro k hk
    have h1 := hK'K k hk w hw
    have h2 := hK''K k hk w' hw'm
    calc w * w' * k = w * (w' * k) := by group
      _ = w * (k * w') := by rw [← h2]
      _ = (w * k) * w' := by group
      _ = (k * w) * w' := by rw [← h1]
      _ = k * (w * w') := by group
  obtain ⟨z, hz, hv⟩ := hI _ hvv hav hvK
  have hzK : z ∈ K := hZK hz
  have hzc : ∀ x ∈ K', z * x = x * z := fun x hx => hK'K z hzK x hx
  rcases hv with hv | hv
  ·
    apply hnz
    intro k hk
    have hweq : w = z * w'⁻¹ := eq_mul_inv_of_mul_eq hv
    have hk' : k * w'⁻¹ = w'⁻¹ * k := by
      have h1 : Commute k w' := hK'K'' k hk w' hw'm
      exact h1.inv_right.eq
    calc w * k = (z * w'⁻¹) * k := by rw [← hweq]
      _ = z * (w'⁻¹ * k) := by group
      _ = z * (k * w'⁻¹) := by rw [hk']
      _ = (z * k) * w'⁻¹ := by group
      _ = (k * z) * w'⁻¹ := by rw [hzc k hk]
      _ = k * (z * w'⁻¹) := by group
      _ = k * w := by rw [← hweq]
  ·
    apply hne
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have ha : a = z⁻¹ * (w * w') := by rw [hv]; group
    have hw'x : w' * x * w'⁻¹ = x := by
      have h1 : Commute x w' := hK'K'' x hx w' hw'm
      calc w' * x * w'⁻¹ = x * w' * w'⁻¹ := by rw [← h1.eq]
        _ = x := by group
    have hconj : a * x * a⁻¹ = z⁻¹ * (w * x * w⁻¹) * z := by
      rw [ha]
      calc z⁻¹ * (w * w') * x * (z⁻¹ * (w * w'))⁻¹
          = z⁻¹ * w * (w' * x * w'⁻¹) * w⁻¹ * z := by group
        _ = z⁻¹ * (w * x * w⁻¹) * z := by rw [hw'x]; group
    have hy : w * x * w⁻¹ ∈ K' := mul_mem (mul_mem hw hx) (inv_mem hw)
    have hzy : z * (w * x * w⁻¹) = (w * x * w⁻¹) * z := hzc _ hy
    have : z⁻¹ * (w * x * w⁻¹) * z = w * x * w⁻¹ := by
      rw [mul_assoc, ← hzy]
      group
    rw [hconj, this]
    exact hy

theorem le_normalizer_of_normal {D K : Subgroup X} (hKD : K ≤ D) (hn : (K.subgroupOf D).Normal) :
    D ≤ normalizer (K : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := hn.conj_mem ⟨h, hKD hh⟩ (mem_subgroupOf.mpr hh) ⟨g, hg⟩
    exact mem_subgroupOf.mp this
  · intro hh
    have := hn.conj_mem ⟨g * h * g⁻¹, hKD hh⟩ (mem_subgroupOf.mpr hh) (⟨g, hg⟩ : ↥D)⁻¹
    have h2 := mem_subgroupOf.mp this
    simp only [coe_mul, coe_inv, inv_inv] at h2
    rwa [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at h2

theorem map_conj_one (K : Subgroup X) : K.map (MulAut.conj (1 : X)).toMonoidHom = K := by
  ext x
  simp

theorem normal_of_key [Finite X] {D K Z : Subgroup X} {a : X} (P : Subgroup X → Prop)
    (hKD : K ≤ D) (haD : a ∈ D) (haa : a * a = 1) (haK : ∀ k ∈ K, a * k = k * a) (hZK : Z ≤ K)
    (hK : IsComponent (K.subgroupOf D))
    (hI : ∀ v : X, v * v = 1 → a * v = v * a → (∀ k ∈ K, v * k = k * v) →
      ∃ z ∈ Z, v = z ∨ v = z * a)
    (hP : ∀ g ∈ D, P (K.map (MulAut.conj g).toMonoidHom))
    (hKA : ∀ K' : Subgroup X, P K' → ∀ τ ∈ normalizer (K' : Set X), τ * τ = 1 →
      ∃ w ∈ K', w * w = 1 ∧ w * τ = τ * w ∧ ¬ (∀ k ∈ K', w * k = k * w) ∧
        ¬ (∀ k ∈ K', (w⁻¹ * τ) * k = k * (w⁻¹ * τ))) :
    (K.subgroupOf D).Normal := by
  have hconj : ∀ g ∈ D, K.map (MulAut.conj g).toMonoidHom = K := by
    intro g hg
    by_contra hne
    have hK'D := map_conj_le hKD hg
    have hK'c := isComponent_map_conj hK ⟨g, hg⟩
    have hK'K : ∀ k ∈ K, ∀ y ∈ K.map (MulAut.conj g).toMonoidHom, k * y = y * k :=
      commute_of_components hKD hK'D hK hK'c (fun h => hne h.symm)
    have hK''eq := map_conj_map_conj K a g
    have hK''D := map_conj_le hK'D haD
    have hK''c : IsComponent
        (((K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom).subgroupOf D) := by
      rw [hK''eq]
      exact isComponent_map_conj hK ⟨a * g, mul_mem haD hg⟩
    by_cases hnorm : (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        K.map (MulAut.conj g).toMonoidHom
    ·
      have haN : a ∈ normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) :=
        mem_normalizer_iff_map_conj_eq.mpr hnorm
      obtain ⟨w, hw, hww, haw, hnz, hnc⟩ := hKA _ (hP g hg) a haN haa
      exact false_of_normalized hZK hK'K haK hI hw hww haw hnz hnc
    ·
      have hK''K : (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom ≠ K := by
        intro h
        apply hne
        have h1 := map_conj_map_conj (K.map (MulAut.conj g).toMonoidHom) a a
        rw [haa, map_conj_one, h, map_conj_eq_of_commute haK] at h1
        exact h1.symm
      have hK'K'' : ∀ x ∈ K.map (MulAut.conj g).toMonoidHom,
          ∀ y ∈ (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom,
          x * y = y * x :=
        commute_of_components hK'D hK''D hK'c hK''c (Ne.symm hnorm)
      have hKK'' : ∀ k ∈ K,
          ∀ y ∈ (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom,
          k * y = y * k :=
        commute_of_components hKD hK''D hK hK''c (Ne.symm hK''K)
      have hnle : ¬ (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom ≤
          K.map (MulAut.conj g).toMonoidHom := by
        intro hle
        apply hnorm
        exact eq_of_le_of_card_ge hle (le_of_eq (card_map_conj _ a).symm)
      obtain ⟨w, hw, hww, -, hnz, -⟩ := hKA _ (hP g hg) 1 (one_mem _) (mul_one 1)
      exact false_of_swapped haa hZK hK'K hKK'' hK'K'' hnle hI hw hww hnz
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have h1 : (g : X) * n * (g : X)⁻¹ ∈ K.map (MulAut.conj (g : X)).toMonoidHom :=
    ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rw [hconj g g.2] at h1
  simpa using h1

theorem eq_of_key [Finite X] {D K K₁ Z : Subgroup X} {a : X} (P : Subgroup X → Prop)
    (hKD : K ≤ D) (hK₁D : K₁ ≤ D) (haD : a ∈ D) (haa : a * a = 1) (haK : ∀ k ∈ K, a * k = k * a)
    (hZK : Z ≤ K) (hKq : IsQuasisimple ↥K) (hK₁q : IsQuasisimple ↥K₁)
    (hKn : (K.subgroupOf D).Normal) (hK₁n : (K₁.subgroupOf D).Normal)
    (hI : ∀ v : X, v * v = 1 → a * v = v * a → (∀ k ∈ K, v * k = k * v) →
      ∃ z ∈ Z, v = z ∨ v = z * a)
    (hP₁ : P K₁)
    (hKA : ∀ K' : Subgroup X, P K' → ∀ τ ∈ normalizer (K' : Set X), τ * τ = 1 →
      ∃ w ∈ K', w * w = 1 ∧ w * τ = τ * w ∧ ¬ (∀ k ∈ K', w * k = k * w) ∧
        ¬ (∀ k ∈ K', (w⁻¹ * τ) * k = k * (w⁻¹ * τ))) :
    K₁ = K := by
  have hKc : IsComponent (K.subgroupOf D) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKD).symm hKq, hKn.isSubnormal⟩
  have hK₁c : IsComponent (K₁.subgroupOf D) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hK₁D).symm hK₁q,
      hK₁n.isSubnormal⟩
  by_contra hne
  have hcomm : ∀ k ∈ K, ∀ y ∈ K₁, k * y = y * k :=
    commute_of_components hKD hK₁D hKc hK₁c (Ne.symm hne)
  have haN : a ∈ normalizer (K₁ : Set X) := le_normalizer_of_normal hK₁D hK₁n haD
  obtain ⟨w, hw, hww, haw, hnz, hnc⟩ := hKA K₁ hP₁ a haN haa
  exact false_of_normalized hZK hcomm haK hI hw hww haw hnz hnc

end CFSG.ComponentClassification.GrSLit.HeKN
