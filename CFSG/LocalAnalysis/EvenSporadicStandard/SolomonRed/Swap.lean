module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup CFSG CFSG.LocalCores

variable {K : Type*} [Group K] [Finite K] {z : K} {B S₁ S₂ : Subgroup K}

omit [Finite K] in
theorem mem_normalizer_iff_map {S : Subgroup K} {y : K} :
    y ∈ normalizer (S : Set K) ↔ S.map (MulAut.conj y).toMonoidHom = S :=
  Subgroup.mem_normalizer_iff_map_conj_eq

section Cen

variable {S : Subgroup K} {x y : K}

omit [Finite K] in
theorem cen_conj (hx : x ∈ normalizer (S : Set K)) (hy : ∀ s ∈ S, s * y = y * s) :
    ∀ s ∈ S, s * (x * y * x⁻¹) = (x * y * x⁻¹) * s := by
  intro s hs
  have h1 : x⁻¹ * s * x ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) s).1 hs
    simpa using this
  have h2 := hy _ h1
  calc s * (x * y * x⁻¹) = x * ((x⁻¹ * s * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * s * x)) * x⁻¹ := by rw [h2]
    _ = (x * y * x⁻¹) * s := by group

omit [Finite K] in
theorem cen_inv (hy : ∀ s ∈ S, s * y = y * s) : ∀ s ∈ S, s * y⁻¹ = y⁻¹ * s := by
  intro s hs
  have := hy s hs
  calc s * y⁻¹ = y⁻¹ * (y * s) * y⁻¹ := by group
    _ = y⁻¹ * (s * y) * y⁻¹ := by rw [this]
    _ = y⁻¹ * s := by group

omit [Finite K] in
theorem cen_mul {u v : K} (hu : ∀ s ∈ S, s * u = u * s) (hv : ∀ s ∈ S, s * v = v * s) :
    ∀ s ∈ S, s * (u * v) = (u * v) * s := by
  intro s hs
  calc s * (u * v) = (s * u) * v := by group
    _ = (u * s) * v := by rw [hu s hs]
    _ = u * (s * v) := by group
    _ = u * (v * s) := by rw [hv s hs]
    _ = (u * v) * s := by group

end Cen

namespace SwapData

variable (hs : SwapData K z B S₁ S₂) (h : Setting K z B)

omit [Finite K] in
include hs in
theorem comp₂ : IsComponent S₂ := by
  rw [hs.conj_eq]; exact isComponent_conj hs.comp z

include hs in
theorem commute : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a :=
  component_commute hs.comp hs.comp₂ hs.ne

include hs h in
theorem disjoint : S₁ ⊓ S₂ = ⊥ :=
  component_inf_eq_bot h.fitting_eq_bot hs.comp hs.comp₂ hs.ne

omit [Finite K] in
include hs h in
theorem map_S₂ : S₂.map (MulAut.conj z).toMonoidHom = S₁ := by
  rw [hs.conj_eq]; exact map_conj_conj h.z_sq S₁

omit [Finite K] in
include hs in
theorem conj_mem_S₂ {s : K} (hsS : s ∈ S₁) : z * s * z⁻¹ ∈ S₂ := by
  rw [hs.conj_eq]; exact ⟨s, hsS, rfl⟩

omit [Finite K] in
include hs h in
theorem conj_mem_S₁ {s : K} (hsS : s ∈ S₂) : z * s * z⁻¹ ∈ S₁ := by
  have := hs.map_S₂ h
  rw [← this]
  exact ⟨s, hsS, rfl⟩

omit [Finite K] in
include hs in
theorem normalizer_le :
    ∀ y ∈ normalizer (S₁ : Set K), y ∈ normalizer (S₂ : Set K) := by
  intro y hy
  rw [mem_normalizer_iff_map] at hy ⊢
  have hc := isComponent_conj hs.comp₂ y
  rcases hs.comp_cases _ hc with h1 | h1
  · exfalso
    apply hs.ne
    have h2 : S₂.map (MulAut.conj y).toMonoidHom = S₁.map (MulAut.conj y).toMonoidHom := by
      rw [h1, hy]
    exact (Subgroup.map_injective (MulAut.conj y).injective h2).symm
  · exact h1

omit [Finite K] in
include hs h in
theorem cover (k : K) : k ∈ normalizer (S₁ : Set K) ∨ z * k ∈ normalizer (S₁ : Set K) := by
  have hc := isComponent_conj hs.comp k
  rcases hs.comp_cases _ hc with h1 | h1
  · left
    rw [mem_normalizer_iff_map]
    exact h1
  · right
    rw [mem_normalizer_iff_map]
    have e : S₁.map (MulAut.conj (z * k)).toMonoidHom =
        (S₁.map (MulAut.conj k).toMonoidHom).map (MulAut.conj z).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e, h1]
    exact hs.map_S₂ h

omit [Finite K] in
include hs in
theorem z_not_mem_normalizer : z ∉ normalizer (S₁ : Set K) := by
  intro hz
  rw [mem_normalizer_iff_map] at hz
  apply hs.ne
  rw [hs.conj_eq, hz]

omit [Finite K] in
include hs h in
theorem mem_S₁_iff_conj {x : K} : x ∈ S₁ ↔ z * x * z⁻¹ ∈ S₂ := by
  refine ⟨hs.conj_mem_S₂, fun hx => ?_⟩
  have := hs.conj_mem_S₁ h hx
  rwa [conj_conj_of_mul_self_eq_one h.z_sq] at this

omit [Finite K] in
include hs h in
theorem mem_S₂_iff_conj {x : K} : x ∈ S₂ ↔ z * x * z⁻¹ ∈ S₁ := by
  refine ⟨hs.conj_mem_S₁ h, fun hx => ?_⟩
  have := hs.conj_mem_S₂ hx
  rwa [conj_conj_of_mul_self_eq_one h.z_sq] at this

omit [Finite K] in
include hs h in
theorem conj_mem_normalizer {y : K} (hy : y ∈ normalizer (S₁ : Set K)) :
    z * y * z⁻¹ ∈ normalizer (S₁ : Set K) := by
  have hy₂ : y ∈ normalizer (S₂ : Set K) := hs.normalizer_le y hy
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have e : (z * y * z⁻¹) * x * (z * y * z⁻¹)⁻¹ = z * (y * (z * x * z⁻¹) * y⁻¹) * z⁻¹ := by
    simp only [mul_inv_rev, inv_inv]
    rw [hzi]
    group
  rw [e, ← hs.mem_S₂_iff_conj h, hs.mem_S₁_iff_conj h]
  exact Subgroup.mem_normalizer_iff.1 hy₂ _

include hs in
theorem mem_centralizer_layer {x : K} (hx₁ : ∀ s ∈ S₁, s * x = x * s)
    (hx₂ : ∀ t ∈ S₂, t * x = x * t) : x ∈ centralizer (layer K : Set K) := by
  rw [mem_centralizer_iff]
  intro y hy
  rw [hs.layer_eq] at hy
  have hle : S₂ ≤ centralizer (S₁ : Set K) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hs.commute a ha b hb
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hy
  calc a * b * x = a * (b * x) := by group
    _ = a * (x * b) := by rw [hx₂ b hb]
    _ = (a * x) * b := by group
    _ = (x * a) * b := by rw [hx₁ a ha]
    _ = x * (a * b) := by group

include hs h in
theorem eq_of_centralizes
    (hC : ∀ d ∈ centralizer ({z} : Set K), d ∈ normalizer (S₁ : Set K) → d ∈ layer K)
    {c : K} (hc : c ∈ normalizer (S₁ : Set K)) (hcS : ∀ t ∈ S₂, t * c = c * t) : c ∈ S₁ := by
  have hz := h.z_sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hcentE : centralizer (layer K : Set K) = ⊥ := centralizer_layer_eq_bot h.fitting_eq_bot
  have hcom := hs.commute
  obtain ⟨c', hc'def⟩ : ∃ c' : K, c' = z * c * z⁻¹ := ⟨_, rfl⟩
  have hc'S₁ : ∀ s ∈ S₁, s * c' = c' * s := by
    intro s hs1
    have ht : z⁻¹ * s * z ∈ S₂ := by
      have := hs.conj_mem_S₂ hs1
      rw [hzi] at this ⊢
      exact this
    have h1 := hcS _ ht
    rw [hc'def]
    calc s * (z * c * z⁻¹) = z * ((z⁻¹ * s * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * s * z)) * z⁻¹ := by rw [h1]
      _ = (z * c * z⁻¹) * s := by group
  have hc'N : c' ∈ normalizer (S₁ : Set K) :=
    (Subgroup.centralizer_le_normalizer (S₁ : Set K)) (mem_centralizer_iff.2 hc'S₁)
  have hc'N₂ : c' ∈ normalizer (S₂ : Set K) := hs.normalizer_le c' hc'N
  have hcc' : c * c' = c' * c := by
    have h1 : ∀ s ∈ S₁, s * (c * c' * c⁻¹ * c'⁻¹) = (c * c' * c⁻¹ * c'⁻¹) * s :=
      cen_mul (cen_conj hc hc'S₁) (cen_inv hc'S₁)
    have h2 : ∀ t ∈ S₂, t * (c * c' * c⁻¹ * c'⁻¹) = (c * c' * c⁻¹ * c'⁻¹) * t := by
      have e : c * c' * c⁻¹ * c'⁻¹ = c * (c' * c⁻¹ * c'⁻¹) := by group
      rw [e]
      exact cen_mul hcS (cen_conj hc'N₂ (cen_inv hcS))
    have h3 := hs.mem_centralizer_layer h1 h2
    rw [hcentE, mem_bot] at h3
    calc c * c' = (c * c' * c⁻¹ * c'⁻¹) * (c' * c) := by group
      _ = c' * c := by rw [h3, one_mul]
  have hd : c * c' ∈ centralizer ({z} : Set K) := by
    rw [mem_centralizer_singleton_iff]
    have hzc' : z * c' * z⁻¹ = c := by rw [hc'def]; exact conj_conj_of_mul_self_eq_one hz c
    have : z * (c * c') * z⁻¹ = c * c' := by
      calc z * (c * c') * z⁻¹ = (z * c * z⁻¹) * (z * c' * z⁻¹) := by group
        _ = c' * c := by rw [hzc', ← hc'def]
        _ = c * c' := hcc'.symm
    exact (conj_eq_self_iff.1 this).symm
  have hdE : c * c' ∈ layer K := hC _ hd (mul_mem hc hc'N)
  obtain ⟨s, hsS, hds⟩ := hs.diag _ ⟨hdE, hd⟩
  have hX : z * s * z⁻¹ ∈ S₂ := hs.conj_mem_S₂ hsS
  have hcs : c = s * ((z * s * z⁻¹) * c'⁻¹) := by
    calc c = (c * c') * c'⁻¹ := by group
      _ = (s * (z * s * z⁻¹)) * c'⁻¹ := by rw [hds]
      _ = s * ((z * s * z⁻¹) * c'⁻¹) := by group
  have hy1 : ∀ a ∈ S₁, a * ((z * s * z⁻¹) * c'⁻¹) = ((z * s * z⁻¹) * c'⁻¹) * a :=
    cen_mul (fun a ha => hcom a ha _ hX) (cen_inv hc'S₁)
  have hy2 : ∀ t ∈ S₂, t * ((z * s * z⁻¹) * c'⁻¹) = ((z * s * z⁻¹) * c'⁻¹) * t := by
    have e : (z * s * z⁻¹) * c'⁻¹ = s⁻¹ * c := by
      rw [hcs]; group
    rw [e]
    refine cen_mul (fun t ht => ?_) hcS
    have := hcom s⁻¹ (inv_mem hsS) t ht
    exact this.symm
  have hy := hs.mem_centralizer_layer hy1 hy2
  rw [hcentE, mem_bot] at hy
  rw [hcs, hy, mul_one]
  exact hsS

include hs h in
theorem eq_of_centralizes'
    (hC : ∀ d ∈ centralizer ({z} : Set K), d ∈ normalizer (S₁ : Set K) → d ∈ layer K)
    {c : K} (hc : c ∈ normalizer (S₁ : Set K)) (hcS : ∀ s ∈ S₁, s * c = c * s) : c ∈ S₂ := by
  have hz := h.z_sq
  have hc'' := hs.conj_mem_normalizer h hc
  have hS₂ : ∀ t ∈ S₂, t * (z * c * z⁻¹) = (z * c * z⁻¹) * t := by
    intro t ht
    have hs1 : z * t * z⁻¹ ∈ S₁ := hs.conj_mem_S₁ h ht
    have h1 := hcS _ hs1
    have ht' : z * (z * t * z⁻¹) * z⁻¹ = t := conj_conj_of_mul_self_eq_one hz t
    calc t * (z * c * z⁻¹) = (z * (z * t * z⁻¹) * z⁻¹) * (z * c * z⁻¹) := by rw [ht']
      _ = z * ((z * t * z⁻¹) * c) * z⁻¹ := by group
      _ = z * (c * (z * t * z⁻¹)) * z⁻¹ := by rw [h1]
      _ = (z * c * z⁻¹) * (z * (z * t * z⁻¹) * z⁻¹) := by group
      _ = (z * c * z⁻¹) * t := by rw [ht']
  have := hs.eq_of_centralizes h hC hc'' hS₂
  have h2 := hs.conj_mem_S₂ this
  rwa [conj_conj_of_mul_self_eq_one hz] at h2

omit [Finite K] in
include hs in
theorem le_layer : S₁ ≤ layer K := by
  rw [hs.layer_eq]; exact le_sup_left

include hs in
theorem inner_of_mem_layer {x : K} (hx : x ∈ layer K) :
    ∃ a ∈ S₁, ∀ s ∈ S₁, x * s * x⁻¹ = a * s * a⁻¹ := by
  rw [hs.layer_eq] at hx
  have hle : S₂ ≤ centralizer (S₁ : Set K) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hs.commute a ha b hb
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hx
  refine ⟨a, ha, fun s hs1 => ?_⟩
  have h1 := hs.commute s hs1 b hb
  calc a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
    _ = a * s * a⁻¹ := by rw [← h1]; group

include hs h in
theorem mem_layer_of_compare
    (hC : ∀ d ∈ centralizer ({z} : Set K), d ∈ normalizer (S₁ : Set K) → d ∈ layer K)
    {y : K} (hy : y ∈ normalizer (S₁ : Set K))
    (hcmp : ∃ c ∈ S₁, ∀ s ∈ S₁,
      y * s * y⁻¹ = c * ((z * y * z⁻¹) * s * (z * y * z⁻¹)⁻¹) * c⁻¹) : y ∈ layer K := by
  have hz := h.z_sq
  have hdisj := hs.disjoint h
  obtain ⟨c, hcS, hcs⟩ := hcmp
  obtain ⟨y', hy'def⟩ : ∃ y' : K, y' = z * y * z⁻¹ := ⟨_, rfl⟩
  rw [← hy'def] at hcs
  have hy'N : y' ∈ normalizer (S₁ : Set K) := by rw [hy'def]; exact hs.conj_mem_normalizer h hy
  have hcN : c ∈ normalizer (S₁ : Set K) := Subgroup.le_normalizer hcS
  obtain ⟨v, hvdef⟩ : ∃ v : K, v = c⁻¹ * y := ⟨_, rfl⟩
  have hvN : v ∈ normalizer (S₁ : Set K) := by rw [hvdef]; exact mul_mem (inv_mem hcN) hy
  have hv_act : ∀ s ∈ S₁, v * s * v⁻¹ = y' * s * y'⁻¹ := by
    intro s hs1
    rw [hvdef]
    have h1 := hcs s hs1
    calc c⁻¹ * y * s * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * s * y⁻¹) * c := by group
      _ = c⁻¹ * (c * (y' * s * y'⁻¹) * c⁻¹) * c := by rw [h1]
      _ = y' * s * y'⁻¹ := by group
  obtain ⟨b, hbdef⟩ : ∃ b : K, b = v⁻¹ * y' := ⟨_, rfl⟩
  have hbS₁ : ∀ s ∈ S₁, s * b = b * s := by
    intro s hs1
    have h1 : b * s * b⁻¹ = s := by
      rw [hbdef]
      calc v⁻¹ * y' * s * (v⁻¹ * y')⁻¹ = v⁻¹ * (y' * s * y'⁻¹) * v := by group
        _ = v⁻¹ * (v * s * v⁻¹) * v := by rw [hv_act s hs1]
        _ = s := by group
    calc s * b = (b * s * b⁻¹) * b := by rw [h1]
      _ = b * s := by group
  have hbN : b ∈ normalizer (S₁ : Set K) := by rw [hbdef]; exact mul_mem (inv_mem hvN) hy'N
  have hbS₂ : b ∈ S₂ := hs.eq_of_centralizes' h hC hbN hbS₁
  have ha₂ : y⁻¹ * c⁻¹ * y ∈ S₁ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) c⁻¹).1 (inv_mem hcS)
    simpa using this
  have hveq : v = y * (y⁻¹ * c⁻¹ * y) := by rw [hvdef]; group
  have hy'v : y' = v * b := by rw [hbdef]; group
  have ha₂' : z * (y⁻¹ * c⁻¹ * y) * z⁻¹ ∈ S₂ := hs.conj_mem_S₂ ha₂
  have hzv : z * v * z⁻¹ = v * (b * (z * (y⁻¹ * c⁻¹ * y) * z⁻¹)) := by
    calc z * v * z⁻¹ = (z * y * z⁻¹) * (z * (y⁻¹ * c⁻¹ * y) * z⁻¹) := by rw [hveq]; group
      _ = y' * (z * (y⁻¹ * c⁻¹ * y) * z⁻¹) := by rw [hy'def]
      _ = v * (b * (z * (y⁻¹ * c⁻¹ * y) * z⁻¹)) := by rw [hy'v]; group
  obtain ⟨b₂, hb₂def⟩ : ∃ b₂ : K, b₂ = b * (z * (y⁻¹ * c⁻¹ * y) * z⁻¹) := ⟨_, rfl⟩
  rw [← hb₂def] at hzv
  have hb₂S₂ : b₂ ∈ S₂ := by rw [hb₂def]; exact S₂.mul_mem hbS₂ ha₂'
  have hb₂1 : b₂ = 1 := by
    have h1 : v = v * (b₂ * (z * b₂ * z⁻¹)) := by
      calc v = z * (z * v * z⁻¹) * z⁻¹ := (conj_conj_of_mul_self_eq_one hz v).symm
        _ = z * (v * b₂) * z⁻¹ := by rw [hzv]
        _ = (z * v * z⁻¹) * (z * b₂ * z⁻¹) := by group
        _ = (v * b₂) * (z * b₂ * z⁻¹) := by rw [hzv]
        _ = v * (b₂ * (z * b₂ * z⁻¹)) := by group
    have h2 : b₂ * (z * b₂ * z⁻¹) = 1 := by
      have h3 : v * (b₂ * (z * b₂ * z⁻¹)) = v * 1 := by rw [mul_one]; exact h1.symm
      exact mul_left_cancel h3
    have h4 : b₂ = (z * b₂ * z⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h2
    have h5 : b₂ ∈ S₁ ⊓ S₂ := ⟨by rw [h4]; exact S₁.inv_mem (hs.conj_mem_S₁ h hb₂S₂), hb₂S₂⟩
    rw [hdisj, mem_bot] at h5
    exact h5
  have hvfix : z * v * z⁻¹ = v := by rw [hzv, hb₂1, mul_one]
  have hvD : v ∈ centralizer ({z} : Set K) :=
    mem_centralizer_singleton_iff.2 (conj_eq_self_iff.1 hvfix).symm
  have hvE : v ∈ layer K := hC v hvD hvN
  have hyv : y = v * (y⁻¹ * c⁻¹ * y)⁻¹ := by rw [hveq]; group
  rw [hyv]
  exact mul_mem hvE (inv_mem (hs.le_layer ha₂))

include hs h in
theorem normalizer_le_layer
    (hC : ∀ d ∈ centralizer ({z} : Set K), d ∈ normalizer (S₁ : Set K) → d ∈ layer K)
    (hOC1 : ∀ y₁ ∈ normalizer (S₁ : Set K), ∀ y₂ ∈ normalizer (S₁ : Set K), ∃ c ∈ S₁,
      ∀ s ∈ S₁, (y₁ * y₂) * s * (y₁ * y₂)⁻¹ = c * ((y₂ * y₁) * s * (y₂ * y₁)⁻¹) * c⁻¹)
    (hOC2 : ∀ y ∈ normalizer (S₁ : Set K), ∃ a ∈ S₁,
      ∀ s ∈ S₁, (y * y) * s * (y * y)⁻¹ = a * s * a⁻¹) :
    ∀ y ∈ normalizer (S₁ : Set K), y ∈ layer K := by
  intro y hy
  have hz := h.z_sq
  obtain ⟨y', hy'def⟩ : ∃ y' : K, y' = z * y * z⁻¹ := ⟨_, rfl⟩
  have hy'N : y' ∈ normalizer (S₁ : Set K) := by rw [hy'def]; exact hs.conj_mem_normalizer h hy
  have hzy' : z * y' * z⁻¹ = y := by rw [hy'def]; exact conj_conj_of_mul_self_eq_one hz y
  have hwN : y * y' ∈ normalizer (S₁ : Set K) := mul_mem hy hy'N
  have hzw : z * (y * y') * z⁻¹ = y' * y := by
    calc z * (y * y') * z⁻¹ = (z * y * z⁻¹) * (z * y' * z⁻¹) := by group
      _ = y' * y := by rw [← hy'def, hzy']
  have hw : y * y' ∈ layer K := by
    refine hs.mem_layer_of_compare h hC hwN ?_
    obtain ⟨c, hcS, hc⟩ := hOC1 y hy y' hy'N
    refine ⟨c, hcS, fun s hs1 => ?_⟩
    rw [hzw]
    exact hc s hs1
  obtain ⟨a₀, ha₀, hw₀⟩ := hs.inner_of_mem_layer hw
  obtain ⟨a₁, ha₁, h₁⟩ := hOC2 y hy
  have hu : y⁻¹ * a₀ * y ∈ S₁ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) a₀).1 ha₀
    simpa using this
  refine hs.mem_layer_of_compare h hC hy ⟨a₁ * (y⁻¹ * a₀ * y)⁻¹, S₁.mul_mem ha₁ (S₁.inv_mem hu),
    fun s hs1 => ?_⟩
  rw [← hy'def]
  have hys : y⁻¹ * s * y ∈ S₁ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) s).1 hs1
    simpa using this
  have hii : y * s * y⁻¹ = a₁ * (y⁻¹ * s * y) * a₁⁻¹ := by
    have := h₁ _ hys
    calc y * s * y⁻¹ = (y * y) * (y⁻¹ * s * y) * (y * y)⁻¹ := by group
      _ = a₁ * (y⁻¹ * s * y) * a₁⁻¹ := this
  have hi : y' * s * y'⁻¹ = (y⁻¹ * a₀ * y) * (y⁻¹ * s * y) * (y⁻¹ * a₀ * y)⁻¹ := by
    have := hw₀ s hs1
    calc y' * s * y'⁻¹ = y⁻¹ * ((y * y') * s * (y * y')⁻¹) * y := by group
      _ = y⁻¹ * (a₀ * s * a₀⁻¹) * y := by rw [this]
      _ = (y⁻¹ * a₀ * y) * (y⁻¹ * s * y) * (y⁻¹ * a₀ * y)⁻¹ := by group
  calc y * s * y⁻¹ = a₁ * (y⁻¹ * s * y) * a₁⁻¹ := hii
    _ = a₁ * ((y⁻¹ * a₀ * y)⁻¹ * (y' * s * y'⁻¹) * (y⁻¹ * a₀ * y)) * a₁⁻¹ := by
        rw [hi]; group
    _ = (a₁ * (y⁻¹ * a₀ * y)⁻¹) * (y' * s * y'⁻¹) * (a₁ * (y⁻¹ * a₀ * y)⁻¹)⁻¹ := by group

omit [Finite K] in
include hs h in
theorem index_layer (hK0 : ∀ y ∈ normalizer (S₁ : Set K), y ∈ layer K) :
    (layer K).index = 2 := by
  have hz := h.z_sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hEc : (layer K).Characteristic := layer_characteristic
  have hEn : (layer K).Normal := inferInstance
  have hzE : z ∉ layer K := hs.z_not_mem
  rw [Subgroup.index_eq_two_iff]
  refine ⟨z, fun b => ?_⟩
  rcases hs.cover h b with hbN | hzbN
  · have hbE : b ∈ layer K := hK0 b hbN
    refine Or.inr ⟨hbE, fun hbz => hzE ?_⟩
    have := mul_mem (inv_mem hbE) hbz
    simpa using this
  · have hzbE : z * b ∈ layer K := hK0 _ hzbN
    refine Or.inl ⟨?_, fun hbE => hzE ?_⟩
    · have := hEn.conj_mem _ hzbE z
      have e : z * (z * b) * z⁻¹ = b * z := by
        calc z * (z * b) * z⁻¹ = (z * z) * b * z⁻¹ := by group
          _ = b * z := by rw [hz, one_mul, hzi]
      rwa [e] at this
    · have := mul_mem hzbE (inv_mem hbE)
      simpa using this

end SwapData

end CFSG.EvenSporadicStandard.SolomonRed
