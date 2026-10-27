module

public import CFSG.GH74.GLS.Stage4.T2P53c
public import CFSG.GH74.GLS.Stage4.T2P53b
public import CFSG.GH74.GLS.Stage4.T2Y

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Norm

variable {G : Type} [Group G] [Finite G] {z u : G}

theorem t2U_norm {t : G} (hz : t * z * t⁻¹ ∈ t2U z u) (hu : t * u * t⁻¹ ∈ t2U z u) :
    t ∈ normalizer (t2U z u : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact hz
    · exact hu
  | one => simp
  | mul a b _ _ ha hb =>
    have : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

omit [Finite G] in
theorem t2U_conj_inv (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {t : G}
    (ht : t ∈ normalizer (t2U z u : Set G)) :
    ∀ v, (v = 1 ∨ v = z ∨ v = u ∨ v = z * u) →
      (t⁻¹ * v * t = 1 ∨ t⁻¹ * v * t = z ∨ t⁻¹ * v * t = u ∨ t⁻¹ * v * t = z * u) := by
  intro v hv
  have hvU : v ∈ t2U z u := (t2U_mem hz2 hu2 hzu).2 hv
  have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ht) v).1 hvU
  have h2 : t⁻¹ * v * t ∈ t2U z u := by simpa using h1
  exact (t2U_mem hz2 hu2 hzu).1 h2

end Norm

section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem t2P53_odd_sq {f : G} (hodd : Odd (orderOf f)) (h : f * f = 1) : f = 1 := by
  have hdvd : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact orderOf_eq_one_iff.1 h1
  · exact absurd hodd (by rw [h2]; decide)

omit [Finite G] in
theorem t2P53_kw₂ {H : Subgroup G} {w₀ w₂ k : G} (hw₂H : ∀ h ∈ H, w₂ * h * w₂⁻¹ ∈ H)
    (hw₀w₂ : w₀ * w₂ = w₂ * w₀) (hk : t2InQ H w₀ k) : ∃ hh ∈ H, k * w₂ * k⁻¹ = hh * w₂ := by
  have key : ∀ h ∈ H, ∃ hh ∈ H, h * w₂ * h⁻¹ = hh * w₂ := by
    intro h hh
    refine ⟨h * (w₂ * h⁻¹ * w₂⁻¹), H.mul_mem hh (hw₂H _ (H.inv_mem hh)), by group⟩
  rcases hk with hk | ⟨h, hh, rfl⟩
  · exact key k hk
  · obtain ⟨hh', hhH, e⟩ := key h hh
    refine ⟨hh', hhH, ?_⟩
    calc h * w₀ * w₂ * (h * w₀)⁻¹ = h * (w₀ * w₂ * w₀⁻¹) * h⁻¹ := by group
      _ = h * w₂ * h⁻¹ := by rw [hw₀w₂]; group
      _ = hh' * w₂ := e

theorem t2P53_core {H F : Subgroup G} {z u w₁ w₂ v w₀ : G} (hw₀def : w₀ = w₁ * w₂)
    (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hw₁z : w₁ * z = z * w₁) (hw₁u : w₁ * u * w₁⁻¹ = u * z) (hw₁sq : w₁ * w₁ = z)
    (hw₂z : w₂ * z = z * w₂) (hw₂u : w₂ * u * w₂⁻¹ = u * z) (hw₁w₂ : w₁ * w₂ = w₂ * w₁)
    (hvv : v * v = u) (hvz : v * z * v⁻¹ = z * u)
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hzH : z ∈ H) (huH : u ∈ H)
    (hw₁H : ∀ h ∈ H, w₁ * h * w₁⁻¹ ∈ H) (hw₂H : ∀ h ∈ H, w₂ * h * w₂⁻¹ ∈ H)
    (hw₀2 : w₀ * w₀ = 1) (hw₀H : w₀ ∉ H)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹)
    (hΩ : ∀ x ∈ H, x * x = 1 → x = 1 ∨ x = z ∨ x = u ∨ x = z * u)
    (hFodd : ∀ f ∈ F, Odd (orderOf f)) (hFw₁ : ∀ f ∈ F, f * w₁ = w₁ * f)
    (hFw₂ : ∀ f ∈ F, f * w₂ = w₂ * f) (hFu : ∀ f ∈ F, f * u = u * f)
    (hFz : ∀ f ∈ F, f * z = z * f) (hFH : ∀ f ∈ F, ∀ h ∈ H, f * h * f⁻¹ ∈ H)
    (hdec : ∀ y : G, y * z = z * y → y * u = u * y →
      ∃ k f : G, f ∈ F ∧ (k ∈ H ∨ ∃ h ∈ H, k = h * w₀) ∧ y = k * f) :
    ∃ a : G, a⁻¹ * z * a = u ∧ a⁻¹ * u * a = z * u ∧ a ∈ normalizer (H : Set G) ∧ a ^ 3 ∈ H ∧
      (∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h) ∧ (∃ h ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * h) ∧
      a ∈ Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) ∧
      (∀ f ∈ F, f ∈ normalizer ((Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a})) : Set G)) := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hw₀ : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
  have hw₁z' : w₁ * z * w₁⁻¹ = z := by
    calc w₁ * z * w₁⁻¹ = z * w₁ * w₁⁻¹ := by rw [hw₁z]
      _ = z := by group
  have hw₂z' : w₂ * z * w₂⁻¹ = z := by
    calc w₂ * z * w₂⁻¹ = z * w₂ * w₂⁻¹ := by rw [hw₂z]
      _ = z := by group
  have hw₀z : w₀ * z = z * w₀ := by
    calc w₀ * z = w₁ * (w₂ * z) := by rw [hw₀def]; group
      _ = w₁ * (z * w₂) := by rw [hw₂z]
      _ = (w₁ * z) * w₂ := by group
      _ = (z * w₁) * w₂ := by rw [hw₁z]
      _ = z * w₀ := by rw [hw₀def]; group
  have hw₀u : w₀ * u = u * w₀ := by
    have h1 : w₀ * u * w₀⁻¹ = u := by
      calc w₀ * u * w₀⁻¹ = w₁ * (w₂ * u * w₂⁻¹) * w₁⁻¹ := by rw [hw₀def]; group
        _ = w₁ * (u * z) * w₁⁻¹ := by rw [hw₂u]
        _ = (w₁ * u * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
        _ = (u * z) * z := by rw [hw₁u, hw₁z']
        _ = u * (z * z) := by group
        _ = u := by rw [hz2, mul_one]
    calc w₀ * u = (w₀ * u * w₀⁻¹) * w₀ := by group
      _ = u * w₀ := by rw [h1]
  have hFw₀ : ∀ f ∈ F, f * w₀ = w₀ * f := by
    intro f hf
    calc f * w₀ = (f * w₁) * w₂ := by rw [hw₀def]; group
      _ = (w₁ * f) * w₂ := by rw [hFw₁ f hf]
      _ = w₁ * (f * w₂) := by group
      _ = w₁ * (w₂ * f) := by rw [hFw₂ f hf]
      _ = w₀ * f := by rw [hw₀def]; group
  have hw₁w₀ : w₁ * w₀ = w₀ * w₁ := by
    calc w₁ * w₀ = w₁ * (w₁ * w₂) := by rw [hw₀def]
      _ = w₁ * (w₂ * w₁) := by rw [hw₁w₂]
      _ = w₀ * w₁ := by rw [hw₀def]; group
  have hw₂w₀ : w₀ * w₂ = w₂ * w₀ := by
    calc w₀ * w₂ = (w₁ * w₂) * w₂ := by rw [hw₀def]
      _ = (w₂ * w₁) * w₂ := by rw [hw₁w₂]
      _ = w₂ * w₀ := by rw [hw₀def]; group
  have hw₂ : w₂ = w₁⁻¹ * w₀ := by rw [hw₀def]; group
  have hvu : v * u * v⁻¹ = u := by
    calc v * u * v⁻¹ = v * (v * v) * v⁻¹ := by rw [hvv]
      _ = v * v := by group
      _ = u := hvv
  obtain ⟨c1, c2, c3, c4⟩ := t2P53_cycle hz2 hu2 hzu hw₁z hw₁u hw₁sq hvz hvv
  obtain ⟨d1, d2⟩ := t2P53_a_cycle hz2 hu2 hzu hw₁z hw₁u hw₁sq hvz hvv
  have hwa := t2P53_wa hz2 hu2 hzu hw₁z hw₁u hw₁sq hvz hvv
  have hwb3 := t2P53_wb3 hz2 hu2 hzu hw₁z hw₁u hw₁sq hvz hvv
  obtain ⟨hxz, hxu⟩ := t2P53_b3_comm hz2 hu2 hzu hw₁z hw₁u hw₁sq hvz hvv
  set b := w₁ * v with hb
  set a := b * b with ha
  have hzU : z ∈ t2U z u := Subgroup.subset_closure (by simp)
  have huU : u ∈ t2U z u := Subgroup.subset_closure (by simp)
  have hw₁N : w₁ ∈ normalizer (t2U z u : Set G) :=
    t2U_norm (by rw [hw₁z']; exact hzU) (by rw [hw₁u]; exact Subgroup.mul_mem _ huU hzU)
  have hvN : v ∈ normalizer (t2U z u : Set G) :=
    t2U_norm (by rw [hvz]; exact Subgroup.mul_mem _ hzU huU) (by rw [hvu]; exact huU)
  have hbN : b ∈ normalizer (t2U z u : Set G) := Subgroup.mul_mem _ hw₁N hvN
  have haN : a ∈ normalizer (t2U z u : Set G) := Subgroup.mul_mem _ hbN hbN
  have haN' : a⁻¹ ∈ normalizer (t2U z u : Set G) := Subgroup.inv_mem _ haN
  have hInv : ∀ y : G, y * z = z * y → y * u = u * y → y * y = 1 →
      ¬ (y = 1 ∨ y = z ∨ y = u ∨ y = z * u) → ∃ h ∈ H, y = h * w₀ :=
    fun y h1 h2 h3 h4 => t2Y_inv hdec hFodd hFw₀ hFH hw₀2 hinv hΩ h1 h2 h3 h4
  have hTH : ∀ t : G, t ∈ normalizer (t2U z u : Set G) → ∀ h ∈ H, t * h * t⁻¹ ∈ H :=
    fun t ht => t2Y_normH hInv hHc hzH huH hw₀2 hw₀H hw₀z hw₀u hinv (t2U_conj_inv hz2 hu2 hzu ht)
  have haH : ∀ h ∈ H, a * h * a⁻¹ ∈ H := hTH a haN
  have haH' : ∀ h ∈ H, a⁻¹ * h * a ∈ H := fun h hh => by simpa using hTH a⁻¹ haN' h hh
  have hw₁H' : ∀ h ∈ H, w₁⁻¹ * h * w₁ ∈ H := by
    have hn : w₁ ∈ normalizer (H : Set G) := Subgroup.mem_normalizer_fintype hw₁H
    intro h hh
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) h).1 hh
  have hw₀a : ∃ h ∈ H, w₀ * a * w₀⁻¹ = a * h := by
    obtain ⟨h', hh', e⟩ := t2Y_key hInv hHc hzH huH hw₀2 hw₀H hw₀z hw₀u hinv
      (t2U_conj_inv hz2 hu2 hzu haN') 1 H.one_mem
    refine ⟨h', hh', ?_⟩
    have e' : a⁻¹ * w₀ * a = h' * w₀ := by simpa using e
    calc w₀ * a * w₀⁻¹ = a * (a⁻¹ * w₀ * a) * w₀⁻¹ := by group
      _ = a * (h' * w₀) * w₀⁻¹ := by rw [e']
      _ = a * h' := by group
  have hau : a * u * a⁻¹ = z := by
    calc a * u * a⁻¹ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [d1]
      _ = z := by group
  have hazu : a * (z * u) * a⁻¹ = u := by
    calc a * (z * u) * a⁻¹ = a * (a⁻¹ * u * a) * a⁻¹ := by rw [d2]
      _ = u := by group
  have haz : a * z * a⁻¹ = z * u := by
    have h1 : (a * z * a⁻¹) * z = u := by
      calc (a * z * a⁻¹) * z = (a * z * a⁻¹) * (a * u * a⁻¹) := by rw [hau]
        _ = a * (z * u) * a⁻¹ := by group
        _ = u := hazu
    calc a * z * a⁻¹ = ((a * z * a⁻¹) * z) * z⁻¹ := by group
      _ = u * z := by rw [h1, hz]
      _ = z * u := hzu.symm
  have ha3 : a ^ 3 ∈ H := by
    set x := b * b * b with hx
    obtain ⟨k, f, hf, hk, hxkf⟩ := hdec x hxz hxu
    have hkQ : t2InQ H w₀ k := hk
    have hf2 : f * f ∈ F := F.mul_mem hf hf
    have hk' : t2InQ H w₀ (w₁ * k * w₁⁻¹) := t2InQ_conj hw₁H hw₁w₀ hkQ
    have hfw : w₁ * f * w₁⁻¹ = f := by
      calc w₁ * f * w₁⁻¹ = f * w₁ * w₁⁻¹ := by rw [← hFw₁ f hf]
        _ = f := by group
    have h1 : (w₁ * k * w₁⁻¹) * f = f⁻¹ * k⁻¹ := by
      have e1 : w₁ * x * w₁⁻¹ = x⁻¹ := hwb3
      rw [hxkf] at e1
      calc (w₁ * k * w₁⁻¹) * f = (w₁ * k * w₁⁻¹) * (w₁ * f * w₁⁻¹) := by rw [hfw]
        _ = w₁ * (k * f) * w₁⁻¹ := by group
        _ = (k * f)⁻¹ := e1
        _ = f⁻¹ * k⁻¹ := by group
    have h2 : f * f * (f⁻¹ * (w₁ * k * w₁⁻¹) * f) = k⁻¹ := by
      calc f * f * (f⁻¹ * (w₁ * k * w₁⁻¹) * f) = f * ((w₁ * k * w₁⁻¹) * f) := by group
        _ = f * (f⁻¹ * k⁻¹) := by rw [h1]
        _ = k⁻¹ := by group
    have hfinv : f⁻¹ ∈ F := F.inv_mem hf
    have hm : t2InQ H w₀ (f⁻¹ * (w₁ * k * w₁⁻¹) * f) := by
      have := t2InQ_conj (H := H) (w₀ := w₀) (c := f⁻¹)
        (fun h hh => by simpa using hFH f⁻¹ hfinv h hh) (hFw₀ f⁻¹ hfinv) hk'
      simpa using this
    have hff : f * f = k⁻¹ * (f⁻¹ * (w₁ * k * w₁⁻¹) * f)⁻¹ := by
      have := h2
      calc f * f = (f * f * (f⁻¹ * (w₁ * k * w₁⁻¹) * f)) * (f⁻¹ * (w₁ * k * w₁⁻¹) * f)⁻¹ := by group
        _ = k⁻¹ * (f⁻¹ * (w₁ * k * w₁⁻¹) * f)⁻¹ := by rw [h2]
    have hffQ : t2InQ H w₀ (f * f) := by
      rw [hff]
      exact t2InQ_mul hw₀2 hinv (t2InQ_inv hw₀2 hinv hkQ) (t2InQ_inv hw₀2 hinv hm)
    have hff1 : f * f = 1 := t2Y_F_inter hFodd hFw₀ hw₀2 hinv hf2 hffQ
    have hf1 : f = 1 := t2P53_odd_sq (hFodd f hf) hff1
    subst hf1
    rw [mul_one] at hxkf
    have ha3x : a ^ 3 = x * x := by
      rw [ha, hx]; simp [pow_succ, mul_assoc]
    rw [ha3x, hxkf]
    rcases hkQ with hkH | ⟨h, hh, rfl⟩
    · exact H.mul_mem hkH hkH
    · have h3 := hinv h hh
      rw [hw₀] at h3
      have : h * w₀ * (h * w₀) = 1 := by
        calc h * w₀ * (h * w₀) = h * (w₀ * h * w₀) := by group
          _ = h * h⁻¹ := by rw [h3]
          _ = 1 := by group
      rw [this]
      exact H.one_mem
  have ha3' : a * a * a ∈ H := by
    have : a * a * a = a ^ 3 := by simp [pow_succ, mul_assoc]
    rw [this]; exact ha3
  have hw₁a : ∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h :=
    ⟨u * z, H.mul_mem huH hzH, by rw [ha]; exact hwa⟩
  have hw₂a : ∃ h ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * h := by
    obtain ⟨h₁, hh₁, e₁⟩ := hw₀a
    have hw₁a' : w₁⁻¹ * a * w₁ = a⁻¹ * z := by
      have e0 : w₁ * a * w₁⁻¹ = a⁻¹ * (u * z) := by rw [ha]; exact hwa
      have hw₁inv : w₁⁻¹ = w₁ * z := by
        have : w₁ * z * w₁ = 1 := by
          calc w₁ * z * w₁ = (w₁ * w₁) * (w₁ * w₁) := by rw [← hw₁sq]; group
            _ = z * z := by rw [hw₁sq]
            _ = 1 := hz2
        exact (eq_inv_of_mul_eq_one_left this).symm
      calc w₁⁻¹ * a * w₁ = (w₁⁻¹ * w₁⁻¹) * (w₁ * a * w₁⁻¹) * (w₁ * w₁) := by group
        _ = (w₁⁻¹ * w₁⁻¹) * (a⁻¹ * (u * z)) * z := by rw [e0, hw₁sq]
        _ = ((w₁ * w₁)⁻¹) * (a⁻¹ * (u * z)) * z := by group
        _ = z⁻¹ * (a⁻¹ * (u * z)) * z := by rw [hw₁sq]
        _ = z * a⁻¹ * u * (z * z) := by rw [hz]; group
        _ = z * a⁻¹ * u := by rw [hz2, mul_one]
        _ = (a⁻¹ * (a * z * a⁻¹)) * u := by group
        _ = a⁻¹ * (z * u) * u := by rw [haz]
        _ = a⁻¹ * z * (u * u) := by group
        _ = a⁻¹ * z := by rw [hu2, mul_one]
    refine ⟨z * (w₁⁻¹ * h₁ * w₁), H.mul_mem hzH (hw₁H' h₁ hh₁), ?_⟩
    calc w₂ * a * w₂⁻¹ = w₁⁻¹ * (w₀ * a * w₀⁻¹) * w₁ := by rw [hw₂]; group
      _ = w₁⁻¹ * (a * h₁) * w₁ := by rw [e₁]
      _ = (w₁⁻¹ * a * w₁) * (w₁⁻¹ * h₁ * w₁) := by group
      _ = a⁻¹ * z * (w₁⁻¹ * h₁ * w₁) := by rw [hw₁a']
      _ = a⁻¹ * (z * (w₁⁻¹ * h₁ * w₁)) := by group
  have haN₂ : a ∈ Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) :=
    t2P53_a_mem hw₀def haH ha3' hw₁a hw₀a hw₀2 hinv
  have hHsub : (H : Set G) ⊆ (Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) : Set G) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hFN : ∀ f ∈ F, f ∈ normalizer
      ((Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a})) : Set G) := by
    intro f hf
    have hy1 : (a * f * a⁻¹) * z = z * (a * f * a⁻¹) := by
      calc (a * f * a⁻¹) * z = a * f * (a⁻¹ * z * a) * a⁻¹ := by group
        _ = a * f * u * a⁻¹ := by rw [d1]
        _ = a * (f * u) * a⁻¹ := by group
        _ = a * (u * f) * a⁻¹ := by rw [hFu f hf]
        _ = (a * u * a⁻¹) * (a * f * a⁻¹) := by group
        _ = z * (a * f * a⁻¹) := by rw [hau]
    have hy2 : (a * f * a⁻¹) * u = u * (a * f * a⁻¹) := by
      calc (a * f * a⁻¹) * u = a * f * (a⁻¹ * u * a) * a⁻¹ := by group
        _ = a * f * (z * u) * a⁻¹ := by rw [d2]
        _ = a * (f * (z * u)) * a⁻¹ := by group
        _ = a * ((z * u) * f) * a⁻¹ := by
            congr 2
            calc f * (z * u) = (f * z) * u := by group
              _ = (z * f) * u := by rw [hFz f hf]
              _ = z * (f * u) := by group
              _ = z * (u * f) := by rw [hFu f hf]
              _ = (z * u) * f := by group
        _ = (a * (z * u) * a⁻¹) * (a * f * a⁻¹) := by group
        _ = u * (a * f * a⁻¹) := by rw [hazu]
    obtain ⟨k, f'', hf'', hk, hyk⟩ := hdec _ hy1 hy2
    have hkQ : t2InQ H w₀ k := hk
    obtain ⟨hh, hhH, ehh⟩ := t2P53_kw₂ hw₂H hw₂w₀ hkQ
    have hy2w : (a * f * a⁻¹) * w₂ * (a * f * a⁻¹)⁻¹ = hh * w₂ := by
      rw [hyk]
      calc k * f'' * w₂ * (k * f'')⁻¹ = k * (f'' * w₂ * f''⁻¹) * k⁻¹ := by group
        _ = k * w₂ * k⁻¹ := by
            congr 2
            calc f'' * w₂ * f''⁻¹ = w₂ * f'' * f''⁻¹ := by rw [hFw₂ f'' hf'']
              _ = w₂ := by group
        _ = hh * w₂ := ehh
    have hfr₂ : f * (a⁻¹ * w₂ * a) * f⁻¹ = (a⁻¹ * hh * a) * (a⁻¹ * w₂ * a) := by
      calc f * (a⁻¹ * w₂ * a) * f⁻¹
          = a⁻¹ * ((a * f * a⁻¹) * w₂ * (a * f * a⁻¹)⁻¹) * a := by group
        _ = a⁻¹ * (hh * w₂) * a := by rw [hy2w]
        _ = (a⁻¹ * hh * a) * (a⁻¹ * w₂ * a) := by group
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy | hy
      · exact hHsub (hFH f hf y hy)
      · rw [hy, show f * w₁ * f⁻¹ = w₁ by rw [hFw₁ f hf]; group]
        exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
      · rw [hy, hfr₂]
        exact Subgroup.mul_mem _ (hHsub (haH' hh hhH))
          (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
    | one => simp
    | mul c d _ _ hc hd =>
      have : f * (c * d) * f⁻¹ = (f * c * f⁻¹) * (f * d * f⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hc hd
    | inv c _ hc =>
      have : f * c⁻¹ * f⁻¹ = (f * c * f⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hc
  refine ⟨a, d1, d2, Subgroup.mem_normalizer_fintype haH, ha3, hw₁a, hw₂a, haN₂, hFN⟩

end Core

end CFSG.GH74.GLS.Stage4.Rest
