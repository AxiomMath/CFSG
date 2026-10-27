module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Pieces
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.AltOn

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped Pointwise

namespace MS2

variable {N : ℕ} {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}

@[expose] def IsKleinElt (Δ₀ : Finset (Fin N)) (q : Perm (Fin N)) : Prop :=
  (∀ x, x ∉ Δ₀ → q x = x) ∧ q * q = 1 ∧ (q = 1 ∨ ∀ x ∈ Δ₀, q x ≠ x)

@[expose] def a0 (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)) :
    Subgroup (Perm (Fin N)) :=
  P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)}

theorem perm_apply_inv_self (σ : Perm (Fin N)) (x : Fin N) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

theorem apply_apply_of_mul_self {p : Perm (Fin N)} (hp : p * p = 1) (x : Fin N) :
    p (p x) = x := by
  simpa [Perm.mul_apply] using congrArg (fun f : Perm (Fin N) => f x) hp

theorem involution_pres {p : Perm (Fin N)} (hp0 : ∀ x, x ∉ Δ₀ → p x = x) (hp2 : p * p = 1) :
    ∀ x, x ∈ Δ₀ ↔ p x ∈ Δ₀ := by
  have key : ∀ x, x ∈ Δ₀ → p x ∈ Δ₀ := fun x hx => by
    by_contra hpx
    have h1 : p (p x) = p x := hp0 _ hpx
    rw [apply_apply_of_mul_self hp2] at h1
    exact hpx (h1 ▸ hx)
  intro x
  refine ⟨key x, fun hx => ?_⟩
  have := key _ hx
  rwa [apply_apply_of_mul_self hp2] at this

theorem P_comm (h : E0Data Δ₀ P ω) {p q : Perm (Fin N)} (hp : p ∈ P) (hq : q ∈ P) :
    p * q = q * p := by
  have h1 : p * q * (p * q) = 1 := h.P_sq _ (P.mul_mem hp hq)
  have e1 : p * q = (p * q)⁻¹ := mul_eq_one_iff_eq_inv.1 h1
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right (h.P_sq p hp),
    inv_eq_of_mul_eq_one_right (h.P_sq q hq)] at e1

theorem P_apply_ne (h : E0Data Δ₀ P ω) {p : Perm (Fin N)} (hp : p ∈ P) (hp1 : p ≠ 1)
    {x : Fin N} (hx : x ∈ Δ₀) : p x ≠ x := by
  intro hpx
  refine hp1 (Perm.ext fun y => ?_)
  by_cases hy : y ∈ Δ₀
  · obtain ⟨q, hq, hqy⟩ := h.P_trans x hx y hy
    have hcomm : p (q x) = q (p x) := by
      simpa [Perm.mul_apply] using congrArg (fun f : Perm (Fin N) => f x) (P_comm h hp hq)
    rw [← hqy, hcomm, hpx]
    rfl
  · exact h.P_fix p hp y hy

theorem eq_of_agree (h : E0Data Δ₀ P ω) {p q : Perm (Fin N)}
    (hp0 : ∀ x, x ∉ Δ₀ → p x = x) (hq0 : ∀ x, x ∉ Δ₀ → q x = x)
    (hp2 : p * p = 1) (hq2 : q * q = 1)
    (hpf : ∀ x ∈ Δ₀, p x ≠ x) (hqf : ∀ x ∈ Δ₀, q x ≠ x) {i : Fin N} (hi : i ∈ Δ₀)
    (hpq : p i = q i) : p = q := by
  refine Perm.ext fun x => ?_
  by_cases hx : x ∈ Δ₀
  swap
  · rw [hp0 x hx, hq0 x hx]
  have hpres := involution_pres hp0 hp2
  have hqres := involution_pres hq0 hq2
  have hj : p i ∈ Δ₀ := (hpres i).1 hi
  have hji : p i ≠ i := hpf i hi
  have hpj : p (p i) = i := apply_apply_of_mul_self hp2 i
  have hqj : q (p i) = i := by rw [hpq]; exact apply_apply_of_mul_self hq2 i
  by_cases hxi : x = i
  · rw [hxi, hpq]
  by_cases hxj : x = p i
  · rw [hxj, hpj, hqj]
  have hcard : (Δ₀ \ {i, p i, x}).card = 1 := by
    have hsub : ({i, p i, x} : Finset (Fin N)) ⊆ Δ₀ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    have h3 : ({i, p i, x} : Finset (Fin N)).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨i, p i, x, hji.symm, fun h' => hxi h'.symm, fun h' => hxj h'.symm, rfl⟩
    rw [Finset.card_sdiff_of_subset hsub, h3, h.card_Δ₀]
  have hmem : ∀ r : Perm (Fin N), (∀ x, x ∉ Δ₀ → r x = x) → r * r = 1 → (∀ x ∈ Δ₀, r x ≠ x) →
      r i = p i → r (p i) = i → r x ∈ Δ₀ \ {i, p i, x} := by
    intro r hr0 hr2 hrf hri hrj
    have hres := involution_pres hr0 hr2
    rw [Finset.mem_sdiff]
    refine ⟨(hres x).1 hx, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hxj (r.injective (h'.trans hrj.symm)),
      fun h' => hxi (r.injective (h'.trans hri.symm)), hrf x hx⟩
  have h1 := hmem p hp0 hp2 hpf rfl hpj
  have h2 := hmem q hq0 hq2 hqf hpq.symm hqj
  exact Finset.card_le_one.1 hcard.le _ h1 _ h2

theorem mem_P_iff (h : E0Data Δ₀ P ω) {q : Perm (Fin N)} : q ∈ P ↔ IsKleinElt Δ₀ q := by
  constructor
  · intro hq
    refine ⟨h.P_fix q hq, h.P_sq q hq, ?_⟩
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · exact Or.inr fun x hx => P_apply_ne h hq hq1 hx
  · rintro ⟨hq0, hq2, hq1 | hqf⟩
    · rw [hq1]
      exact P.one_mem
    · obtain ⟨i, hi⟩ : Δ₀.Nonempty := by
        rw [← Finset.card_pos, h.card_Δ₀]
        norm_num
      have hqi : q i ∈ Δ₀ := (involution_pres hq0 hq2 i).1 hi
      obtain ⟨p, hp, hpi⟩ := h.P_trans i hi (q i) hqi
      have hp1 : p ≠ 1 := fun hp1 => hqf i hi (by rw [← hpi, hp1]; rfl)
      have := eq_of_agree h (h.P_fix p hp) hq0 (h.P_sq p hp) hq2
        (fun x hx => P_apply_ne h hp hp1 hx) hqf hi hpi
      rwa [this] at hp

theorem IsKleinElt.conj {p γ : Perm (Fin N)} (hp : IsKleinElt Δ₀ p)
    (hγ : ∀ x, x ∈ Δ₀ ↔ γ x ∈ Δ₀) : IsKleinElt Δ₀ (γ * p * γ⁻¹) := by
  obtain ⟨h0, h2, h1⟩ := hp
  have hγ' : ∀ x, x ∈ Δ₀ ↔ γ⁻¹ x ∈ Δ₀ := fun x => by
    have := hγ (γ⁻¹ x)
    rw [perm_apply_inv_self] at this
    exact this.symm
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · have : γ⁻¹ x ∉ Δ₀ := fun h' => hx ((hγ' x).2 h')
    show γ (p (γ⁻¹ x)) = x
    rw [h0 _ this]
    exact perm_apply_inv_self γ x
  · calc γ * p * γ⁻¹ * (γ * p * γ⁻¹) = γ * (p * p) * γ⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · rcases h1 with h1 | h1
    · left
      rw [h1]
      group
    · right
      intro x hx hfix
      refine h1 (γ⁻¹ x) ((hγ' x).1 hx) ?_
      have h3 : γ (p (γ⁻¹ x)) = x := hfix
      exact γ.injective (h3.trans (perm_apply_inv_self γ x).symm)

theorem P_le_a0 : P ≤ a0 Δ₀ P ω := le_sup_left

theorem swap_mem_a0 {x : Fin N} (hx : x ∉ Δ₀) : swap x (ω x) ∈ a0 Δ₀ P ω :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨x, hx, rfl⟩)

@[expose] def orbSub (h : E0Data Δ₀ P ω) : Subgroup (Perm (Fin N)) where
  carrier := {s | (∀ x, x ∈ Δ₀ ↔ s x ∈ Δ₀) ∧ ∀ x, x ∉ Δ₀ → s x = x ∨ s x = ω x}
  mul_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    refine ⟨fun x => (ht1 x).trans (hs1 (t x)), fun x hx => ?_⟩
    rcases ht2 x hx with h1 | h1
    · rcases hs2 x hx with h2 | h2
      · left
        simp [Perm.mul_apply, h1, h2]
      · right
        simp [Perm.mul_apply, h1, h2]
    · have hωx : ω x ∉ Δ₀ := h.ω_not_mem hx
      rcases hs2 (ω x) hωx with h2 | h2
      · right
        simp [Perm.mul_apply, h1, h2]
      · left
        simp [Perm.mul_apply, h1, h2, h.ω_invol]
  one_mem' := ⟨fun x => Iff.rfl, fun x _ => Or.inl rfl⟩
  inv_mem' := by
    rintro s ⟨hs1, hs2⟩
    have hs1' : ∀ x, x ∈ Δ₀ ↔ s⁻¹ x ∈ Δ₀ := fun x => by
      have := hs1 (s⁻¹ x)
      rw [perm_apply_inv_self] at this
      exact this.symm
    refine ⟨hs1', fun x hx => ?_⟩
    have hz : s⁻¹ x ∉ Δ₀ := fun h' => hx ((hs1' x).2 h')
    have hsz : s (s⁻¹ x) = x := perm_apply_inv_self s x
    rcases hs2 _ hz with h2 | h2
    · left
      rw [h2] at hsz
      exact hsz
    · right
      rw [h2] at hsz
      calc s⁻¹ x = ω (ω (s⁻¹ x)) := (h.ω_invol _).symm
        _ = ω x := by rw [hsz]

theorem a0_le_orbSub (h : E0Data Δ₀ P ω) : a0 Δ₀ P ω ≤ orbSub h := by
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · intro p hp
    have hp' := (mem_P_iff h).1 hp
    exact ⟨involution_pres hp'.1 hp'.2.1, fun x hx => Or.inl (hp'.1 x hx)⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : ω y ∉ Δ₀ := h.ω_not_mem hy
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · by_cases hxy : x = y
      · subst hxy
        simp [hy, hy']
      by_cases hxy' : x = ω y
      · subst hxy'
        simp [hy, hy']
      rw [swap_apply_of_ne_of_ne hxy hxy']
    · by_cases hxy : x = y
      · subst hxy
        right
        simp
      by_cases hxy' : x = ω y
      · subst hxy'
        right
        simp [h.ω_invol]
      left
      exact swap_apply_of_ne_of_ne hxy hxy'

theorem preserves_of_normalizes (h : E0Data Δ₀ P ω) {γ : Perm (Fin N)}
    (hγ : ∀ s ∈ a0 Δ₀ P ω, γ * s * γ⁻¹ ∈ a0 Δ₀ P ω) {d : Fin N} (hd : d ∈ Δ₀) : γ d ∈ Δ₀ := by
  by_contra hy
  have hsub : Δ₀.image γ ⊆ {γ d, ω (γ d)} := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨p, hp, hpe⟩ := h.P_trans d hd e he
    have hs := (a0_le_orbSub h) (hγ p (P_le_a0 hp))
    have hsy : (γ * p * γ⁻¹) (γ d) = γ e := by simp [Perm.mul_apply, hpe]
    rcases hs.2 (γ d) hy with h1 | h1
    · simp [← hsy, h1]
    · simp [← hsy, h1]
  have hcard : (Δ₀.image γ).card = 4 := by
    rw [Finset.card_image_of_injective _ γ.injective, h.card_Δ₀]
  have h1 := Finset.card_le_card hsub
  have h2 : ({γ d, ω (γ d)} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
  omega

theorem mem_omegaOne_iff {a x : Fin N} : x ∈ omegaOne Δ₀ ω a ↔ x = a ∨ x = ω a ∨ x ∈ Δ₀ := by
  simp [omegaOne]

theorem not_mem_of_not_mem_omegaOne {a x : Fin N} (hx : x ∉ omegaOne Δ₀ ω a) : x ∉ Δ₀ :=
  fun h => hx (mem_omegaOne_iff.2 (Or.inr (Or.inr h)))

theorem ω_not_mem_omegaOne (h : E0Data Δ₀ P ω) {a x : Fin N}
    (hx : x ∉ omegaOne Δ₀ ω a) : ω x ∉ omegaOne Δ₀ ω a := by
  rw [mem_omegaOne_iff] at hx ⊢
  push Not at hx ⊢
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun h4 => h2 ?_, fun h4 => h1 ?_, fun h4 => h3 ?_⟩
  · rw [← h4, h.ω_invol]
  · simpa [h.ω_invol] using congrArg ω h4
  · have h5 := h.ω_fix _ h4
    rw [h.ω_invol] at h5
    rw [h5]
    exact h4

theorem apply_mem_omegaOne {a : Fin N} {γ : Perm (Fin N)}
    (hγ : ∀ x, x ∉ omegaOne Δ₀ ω a → γ x = x) {x : Fin N} (hx : x ∈ omegaOne Δ₀ ω a) :
    γ x ∈ omegaOne Δ₀ ω a := by
  by_contra hγx
  have h1 : γ x = x := γ.injective (hγ _ hγx)
  exact hγx (by rw [h1]; exact hx)

theorem apply_pair (h : E0Data Δ₀ P ω) {a : Fin N} {γ : Perm (Fin N)}
    (hγ1 : ∀ x, x ∈ Δ₀ ↔ γ x ∈ Δ₀) (hγ2 : ∀ x, x ∉ omegaOne Δ₀ ω a → γ x = x) {y : Fin N}
    (hy : y ∉ Δ₀) (hy' : y = a ∨ y = ω a) : γ y = a ∨ γ y = ω a := by
  have hyΩ : y ∈ omegaOne Δ₀ ω a := by
    rcases hy' with rfl | rfl
    · exact mem_omegaOne_iff.2 (Or.inl rfl)
    · exact mem_omegaOne_iff.2 (Or.inr (Or.inl rfl))
  have h1 := mem_omegaOne_iff.1 (apply_mem_omegaOne hγ2 hyΩ)
  have h2 : γ y ∉ Δ₀ := fun h' => hy ((hγ1 y).2 h')
  tauto

theorem normalizes_a0 (h : E0Data Δ₀ P ω) {a : Fin N} (ha : a ∉ Δ₀) {γ : Perm (Fin N)}
    (hγ1 : ∀ x, x ∈ Δ₀ ↔ γ x ∈ Δ₀) (hγ2 : ∀ x, x ∉ omegaOne Δ₀ ω a → γ x = x) :
    ∀ s ∈ a0 Δ₀ P ω, γ * s * γ⁻¹ ∈ a0 Δ₀ P ω := by
  have hba : ω a ≠ a := h.ω_ne_self ha
  have hb : ω a ∉ Δ₀ := h.ω_not_mem ha
  have hpair : swap (γ a) (γ (ω a)) = swap a (ω a) := by
    have hmem := fun y (hy : y ∉ Δ₀) (hy' : y = a ∨ y = ω a) => apply_pair h hγ1 hγ2 hy hy'
    rcases hmem a ha (Or.inl rfl) with h1 | h1
    · have h2 : γ (ω a) = ω a := by
        rcases hmem (ω a) hb (Or.inr rfl) with h3 | h3
        · exact absurd (γ.injective (h3.trans h1.symm)) hba
        · exact h3
      rw [h1, h2]
    · have h2 : γ (ω a) = a := by
        rcases hmem (ω a) hb (Or.inr rfl) with h3 | h3
        · exact h3
        · exact absurd (γ.injective (h3.trans h1.symm)) hba
      rw [h1, h2, swap_comm]
  have key : a0 Δ₀ P ω ≤ Subgroup.comap (MulAut.conj γ).toMonoidHom (a0 Δ₀ P ω) := by
    refine sup_le (fun p hp => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact P_le_a0 ((mem_P_iff h).2 (((mem_P_iff h).1 hp).conj hγ1))
    · rintro _ ⟨x, hx, rfl⟩
      show γ * swap x (ω x) * γ⁻¹ ∈ a0 Δ₀ P ω
      rw [← swap_apply_apply]
      by_cases hxΩ : x ∈ omegaOne Δ₀ ω a
      · rcases mem_omegaOne_iff.1 hxΩ with rfl | hxa | hxΔ
        · rw [hpair]
          exact swap_mem_a0 hx
        · subst hxa
          rw [h.ω_invol, swap_comm, hpair]
          exact swap_mem_a0 ha
        · exact absurd hxΔ hx
      · have h1 : γ x = x := hγ2 x hxΩ
        have h2 : γ (ω x) = ω x := hγ2 _ (ω_not_mem_omegaOne h hxΩ)
        rw [h1, h2]
        exact swap_mem_a0 hx
  intro s hs
  exact key hs

theorem key4 : ∀ β : Perm (Fin 4), ¬ (β * β = 1 ∧ (β = 1 ∨ ∀ x, β x ≠ x)) →
    ∃ γ : Perm (Fin 4), Perm.sign γ = 1 ∧ (β * (γ * β * γ⁻¹)) ^ 3 = 1 ∧
      β * (γ * β * γ⁻¹) ≠ 1 := by
  decide +kernel

theorem key_general {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 4)
    (β : Perm α) (hnot : ¬ (β * β = 1 ∧ (β = 1 ∨ ∀ x, β x ≠ x))) :
    ∃ γ : Perm α, Perm.sign γ = 1 ∧ (β * (γ * β * γ⁻¹)) ^ 3 = 1 ∧
      β * (γ * β * γ⁻¹) ≠ 1 := by
  let e : α ≃ Fin 4 := Fintype.equivFinOfCardEq hα
  let φ : Perm α ≃* Perm (Fin 4) := e.permCongrHom
  have hφ : ∀ (f : Perm α) (x : α), φ f (e x) = e (f x) := fun f x => by
    simp [φ, Equiv.permCongrHom_coe, Equiv.permCongr_apply]
  have h1 : ¬ (φ β * φ β = 1 ∧ (φ β = 1 ∨ ∀ x, φ β x ≠ x)) := by
    rintro ⟨h2, h3⟩
    refine hnot ⟨φ.injective ?_, ?_⟩
    · rw [map_mul, map_one]
      exact h2
    · rcases h3 with h3 | h3
      · exact Or.inl (φ.injective (by rw [map_one]; exact h3))
      · refine Or.inr fun x hx => h3 (e x) ?_
        rw [hφ, hx]
  obtain ⟨g, hs, h3, hne⟩ := key4 (φ β) h1
  obtain ⟨γ, rfl⟩ : ∃ γ, φ γ = g := ⟨φ.symm g, φ.apply_symm_apply g⟩
  refine ⟨γ, ?_, ?_, ?_⟩
  · have : Perm.sign (φ γ) = Perm.sign γ := Perm.sign_permCongr e γ
    rw [← this]
    exact hs
  · apply φ.injective
    rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_one]
    exact h3
  · intro h'
    apply hne
    have := congrArg φ h'
    rw [map_mul, map_mul, map_mul, map_inv, map_one] at this
    exact this

theorem key_support (hΔ : Δ₀.card = 4) {β : Perm (Fin N)} (hβ : ∀ x, x ∉ Δ₀ → β x = x)
    (hnot : ¬ IsKleinElt Δ₀ β) :
    ∃ γ : Perm (Fin N), (∀ x, x ∉ Δ₀ → γ x = x) ∧ Perm.sign γ = 1 ∧
      (β * (γ * β * γ⁻¹)) ^ 3 = 1 ∧ β * (γ * β * γ⁻¹) ≠ 1 := by
  obtain ⟨b, rfl⟩ : β ∈ (Perm.ofSubtype : Perm ↥Δ₀ →* Perm (Fin N)).range := by
    rw [range_ofSubtype_eq_fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact hβ y hy
  have hcard : Fintype.card ↥Δ₀ = 4 := by rw [Fintype.card_coe, hΔ]
  have hb : ¬ (b * b = 1 ∧ (b = 1 ∨ ∀ x, b x ≠ x)) := by
    rintro ⟨h2, h3⟩
    refine hnot ⟨hβ, ?_, ?_⟩
    · rw [← map_mul, h2, map_one]
    · rcases h3 with h3 | h3
      · left
        rw [h3, map_one]
      · right
        intro x hx hxx
        rw [Perm.ofSubtype_apply_of_mem b hx] at hxx
        exact h3 ⟨x, hx⟩ (Subtype.ext hxx)
  obtain ⟨g, hs, h3, hne⟩ := key_general hcard b hb
  refine ⟨Perm.ofSubtype g, fun x hx => Perm.ofSubtype_apply_of_not_mem g hx, ?_, ?_, ?_⟩
  · rw [Perm.sign_ofSubtype]
    exact hs
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h3, map_one]
  · intro h'
    apply hne
    apply Perm.ofSubtype_injective
    rw [map_mul, map_mul, map_mul, map_inv, map_one]
    exact h'

theorem eq_one_of_pow_three_of_pow_two_pow {M : Type*} [Group M] {ε : M} {k : ℕ}
    (h3 : ε ^ 3 = 1) (h2 : ε ^ 2 ^ k = 1) : ε = 1 := by
  have h1 : orderOf ε ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h4 : orderOf ε ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have := Nat.dvd_gcd h1 h4
  rw [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem mem_a0_of_two_power (h : E0Data Δ₀ P ω) {a : Fin N} (ha : a ∉ Δ₀) {α : Perm (Fin N)}
    (hα1 : ∀ x, x ∈ Δ₀ ↔ α x ∈ Δ₀) (hα2 : ∀ x, x ∉ omegaOne Δ₀ ω a → α x = x)
    (h3 : ∀ γ : Perm (Fin N), (∀ x, x ∉ Δ₀ → γ x = x) → Perm.sign γ = 1 →
      (α * (γ * α * γ⁻¹)) ^ 3 = 1 → α * (γ * α * γ⁻¹) = 1) :
    α ∈ a0 Δ₀ P ω := by
  have hba : ω a ≠ a := h.ω_ne_self ha
  have hb : ω a ∉ Δ₀ := h.ω_not_mem ha
  obtain ⟨α₂, hα₂, hα₁'⟩ : ∃ α₂ : Perm (Fin N), (α₂ = 1 ∨ α₂ = swap a (ω a)) ∧
      ∀ x, x ∉ Δ₀ → (α * α₂) x = x := by
    by_cases hαa : α a = a
    · refine ⟨1, Or.inl rfl, fun x hx => ?_⟩
      by_cases hxΩ : x ∈ omegaOne Δ₀ ω a
      · rcases mem_omegaOne_iff.1 hxΩ with rfl | rfl | hxΔ
        · simpa using hαa
        · rcases apply_pair h hα1 hα2 hb (Or.inr rfl) with h' | h'
          · exact absurd (α.injective (h'.trans hαa.symm)) hba
          · simpa using h'
        · exact absurd hxΔ hx
      · simpa using hα2 x hxΩ
    · refine ⟨swap a (ω a), Or.inr rfl, fun x hx => ?_⟩
      have hαa' : α a = ω a := (apply_pair h hα1 hα2 ha (Or.inl rfl)).resolve_left hαa
      have hαb : α (ω a) = a :=
        (apply_pair h hα1 hα2 hb (Or.inr rfl)).resolve_right
          fun h' => hba (α.injective (h'.trans hαa'.symm))
      by_cases hxΩ : x ∈ omegaOne Δ₀ ω a
      · rcases mem_omegaOne_iff.1 hxΩ with rfl | rfl | hxΔ
        · simpa using hαb
        · simpa using hαa'
        · exact absurd hxΔ hx
      · have h1 : x ≠ a := fun h' => hxΩ (mem_omegaOne_iff.2 (Or.inl h'))
        have h2 : x ≠ ω a := fun h' => hxΩ (mem_omegaOne_iff.2 (Or.inr (Or.inl h')))
        simpa [swap_apply_of_ne_of_ne h1 h2] using hα2 x hxΩ
  have hα₂sq : α₂ * α₂ = 1 := by
    rcases hα₂ with rfl | rfl
    · exact mul_one 1
    · exact swap_mul_self _ _
  obtain ⟨α₁, hα₁eq⟩ : ∃ α₁, α₁ = α * α₂ := ⟨_, rfl⟩
  have hα₁ : ∀ x, x ∉ Δ₀ → α₁ x = x := fun x hx => hα₁eq ▸ hα₁' x hx
  have hαeq : α = α₁ * α₂ := by rw [hα₁eq, mul_assoc, hα₂sq, mul_one]
  have hα₁P : α₁ ∈ P := by
    by_contra hnotP
    obtain ⟨γ, hγ0, hγs, hγ3, hγne⟩ :=
      key_support h.card_Δ₀ hα₁ (fun hK => hnotP ((mem_P_iff h).2 hK))
    have hcomm : ∀ f : Perm (Fin N), (∀ x, x ∉ Δ₀ → f x = x) → Commute α₂ f := by
      intro f hf
      rcases hα₂ with rfl | rfl
      · exact Commute.one_left f
      · refine Perm.Disjoint.commute fun x => ?_
        by_cases hx : x ∈ Δ₀
        · left
          exact swap_apply_of_ne_of_ne (fun h' => ha (h' ▸ hx)) (fun h' => hb (h' ▸ hx))
        · right
          exact hf x hx
    have hc1 : Commute α₂ α₁ := hcomm α₁ hα₁
    have hc2 : Commute α₂ γ := hcomm γ hγ0
    have hc3 : Commute α₂ (γ * α₁ * γ⁻¹) := (hc2.mul_right hc1).mul_right hc2.inv_right
    have e1 : γ * (α₁ * α₂) * γ⁻¹ = (γ * α₁ * γ⁻¹) * α₂ := by
      have := hc2.symm.mul_inv_cancel
      calc γ * (α₁ * α₂) * γ⁻¹ = (γ * α₁ * γ⁻¹) * (γ * α₂ * γ⁻¹) := by group
        _ = (γ * α₁ * γ⁻¹) * α₂ := by rw [this]
    have key : α * (γ * α * γ⁻¹) = α₁ * (γ * α₁ * γ⁻¹) := by
      rw [hαeq, e1]
      calc α₁ * α₂ * ((γ * α₁ * γ⁻¹) * α₂) = α₁ * (α₂ * (γ * α₁ * γ⁻¹)) * α₂ := by group
        _ = α₁ * ((γ * α₁ * γ⁻¹) * α₂) * α₂ := by rw [hc3.eq]
        _ = α₁ * (γ * α₁ * γ⁻¹) * (α₂ * α₂) := by group
        _ = α₁ * (γ * α₁ * γ⁻¹) := by rw [hα₂sq, mul_one]
    have := h3 γ hγ0 hγs (by rw [key]; exact hγ3)
    rw [key] at this
    exact hγne this
  rw [hαeq]
  refine (a0 Δ₀ P ω).mul_mem (P_le_a0 hα₁P) ?_
  rcases hα₂ with rfl | rfl
  · exact one_mem _
  · exact swap_mem_a0 ha

theorem pres_inv {σ : Perm (Fin N)} (h : ∀ x, x ∈ Δ₀ ↔ σ x ∈ Δ₀) :
    ∀ x, x ∈ Δ₀ ↔ σ⁻¹ x ∈ Δ₀ := fun x => by
  have := h (σ⁻¹ x)
  rw [perm_apply_inv_self] at this
  exact this.symm

theorem pres_mul {σ τ : Perm (Fin N)} (hσ : ∀ x, x ∈ Δ₀ ↔ σ x ∈ Δ₀)
    (hτ : ∀ x, x ∈ Δ₀ ↔ τ x ∈ Δ₀) : ∀ x, x ∈ Δ₀ ↔ (σ * τ) x ∈ Δ₀ :=
  fun x => (hτ x).trans (hσ (τ x))

theorem pres_of_supported {γ : Perm (Fin N)} (h : ∀ x, x ∉ Δ₀ → γ x = x) :
    ∀ x, x ∈ Δ₀ ↔ γ x ∈ Δ₀ := by
  intro x
  constructor
  · intro hx
    by_contra hγx
    have h2 : γ x = x := γ.injective (h _ hγx)
    exact hγx (by rw [h2]; exact hx)
  · intro hγx
    by_contra hx
    rw [h x hx] at hγx
    exact hx hγx

theorem smul_finset_eq_self_iff (σ : Perm (Fin N)) (D : Finset (Fin N)) :
    σ • D = D ↔ ∀ x, x ∈ D ↔ σ x ∈ D := by
  constructor
  · intro h x
    have h1 := Finset.smul_mem_smul_finset_iff (s := D) σ (b := x)
    rw [h] at h1
    exact h1.symm
  · intro h
    ext y
    rw [← Finset.inv_smul_mem_iff]
    have := h (σ⁻¹ y)
    rw [perm_apply_inv_self] at this
    exact this

theorem index_eq_ncard {K : Type*} [Group K] (φ : K →* Perm (Fin N)) (D₀ : Finset (Fin N))
    (Hs : Subgroup K) (hHs : ∀ k, k ∈ Hs ↔ ∀ x, x ∈ D₀ ↔ φ k x ∈ D₀) :
    Hs.index = {D : Finset (Fin N) | ∃ k, φ k • D₀ = D}.ncard := by
  letI : MulAction K (Finset (Fin N)) := MulAction.compHom (Finset (Fin N)) φ
  have h1 : Hs = MulAction.stabilizer K D₀ := by
    ext k
    rw [hHs, MulAction.mem_stabilizer_iff]
    exact (smul_finset_eq_self_iff _ _).symm
  rw [h1, MulAction.index_stabilizer]
  congr 1

theorem exists_altOn_smul_eq {Ω₁ D₁ D₂ : Finset (Fin N)} (hΩ : Ω₁.card = 6)
    (h₁ : D₁ ⊆ Ω₁) (h₂ : D₂ ⊆ Ω₁) (c₁ : D₁.card = 4) (c₂ : D₂.card = 4) :
    ∃ α ∈ altOn Ω₁, α • D₁ = D₂ := by
  have hX : Nat.card ↥Ω₁ = 6 := by simp [hΩ]
  have hpt : MulAction.IsMultiplyPretransitive (alternatingGroup ↥Ω₁) ↥Ω₁ 4 := by
    have := alternatingGroup.isMultiplyPretransitive ↥Ω₁
    rwa [hX] at this
  let e₁ : Fin 4 ↪ ↥Ω₁ :=
    ⟨fun i => ⟨D₁.orderEmbOfFin c₁ i, h₁ (D₁.orderEmbOfFin_mem c₁ i)⟩,
      fun i j hij => by
        have h' := Subtype.mk.inj hij
        exact (D₁.orderEmbOfFin c₁).toEmbedding.injective h'⟩
  let e₂ : Fin 4 ↪ ↥Ω₁ :=
    ⟨fun i => ⟨D₂.orderEmbOfFin c₂ i, h₂ (D₂.orderEmbOfFin_mem c₂ i)⟩,
      fun i j hij => by
        have h' := Subtype.mk.inj hij
        exact (D₂.orderEmbOfFin c₂).toEmbedding.injective h'⟩
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.1 hpt) e₁ e₂
  refine ⟨((altOnEquiv Ω₁).symm g : altOn Ω₁), ((altOnEquiv Ω₁).symm g).2, ?_⟩
  have hsub : ((altOnEquiv Ω₁).symm g : Perm (Fin N)) • D₁ ⊆ D₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
    have hx' : x ∈ Set.range (D₁.orderEmbOfFin c₁) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨i, rfl⟩ := hx'
    have h3 : (g • e₁) i = e₂ i := by rw [hg]
    have h3' : (g : Perm ↥Ω₁) (e₁ i) = e₂ i := h3
    have h4 : ((altOnEquiv Ω₁).symm g : Perm (Fin N)) (D₁.orderEmbOfFin c₁ i) =
        D₂.orderEmbOfFin c₂ i := by
      rw [coe_altOnEquiv_symm_apply,
        Perm.ofSubtype_apply_of_mem _ (h₁ (D₁.orderEmbOfFin_mem c₁ i))]
      exact congrArg Subtype.val h3'
    show ((altOnEquiv Ω₁).symm g : Perm (Fin N)) (D₁.orderEmbOfFin c₁ i) ∈ D₂
    rw [h4]
    exact D₂.orderEmbOfFin_mem c₂ i
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset, c₁, c₂])

structure MS2Ctx {G : Type} [Group G] {N : ℕ} (B S L₁ : Subgroup G) (t : G → Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)) (a : Fin N) :
    Prop where
  data : E0Data Δ₀ P ω
  ha : a ∉ Δ₀
  S_le : S ≤ B
  L₁_le : L₁ ≤ B
  S_pgroup : IsPGroup 2 S
  t_one : t 1 = 1
  t_mul : ∀ g ∈ B, ∀ h ∈ B, t (g * h) = t g * t h
  t_S : ∀ s ∈ S, t s ∈ a0 Δ₀ P ω
  S_of_t : ∀ g ∈ B, t g ∈ a0 Δ₀ P ω → g ∈ S
  S_surj : ∀ α ∈ a0 Δ₀ P ω, ∃ s ∈ S, t s = α
  t_L₁ : ∀ l ∈ L₁, t l ∈ altOn (omegaOne Δ₀ ω a)
  L₁_surj : ∀ α ∈ altOn (omegaOne Δ₀ ω a), ∃ l ∈ L₁, t l = α

namespace MS2Ctx

variable {G : Type} [Group G] {B S L₁ : Subgroup G} {t : G → Perm (Fin N)} {a : Fin N}
  (hC : MS2Ctx B S L₁ t Δ₀ P ω a)

include hC

theorem t_inv {g : G} (hg : g ∈ B) : t g⁻¹ = (t g)⁻¹ := by
  have h1 := hC.t_mul g hg g⁻¹ (B.inv_mem hg)
  rw [mul_inv_cancel, hC.t_one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem t_pow {g : G} (hg : g ∈ B) (n : ℕ) : t (g ^ n) = t g ^ n := by
  induction n with
  | zero => simp [hC.t_one]
  | succ n ih => rw [pow_succ, hC.t_mul _ (B.pow_mem hg n) _ hg, ih, pow_succ]

theorem t_conj {g s : G} (hg : g ∈ B) (hs : s ∈ B) :
    t (g * s * g⁻¹) = t g * t s * (t g)⁻¹ := by
  rw [hC.t_mul _ (B.mul_mem hg hs) _ (B.inv_mem hg), hC.t_mul _ hg _ hs, hC.t_inv hg]

theorem pres_of_normalizer {g : G} (hg : g ∈ B) (hN : g ∈ Subgroup.normalizer (S : Set G)) :
    ∀ x, x ∈ Δ₀ ↔ t g x ∈ Δ₀ := by
  have key : ∀ g ∈ B, g ∈ Subgroup.normalizer (S : Set G) → ∀ d ∈ Δ₀, t g d ∈ Δ₀ := by
    intro g hg hN d hd
    refine preserves_of_normalizes hC.data (fun s hs => ?_) hd
    obtain ⟨s', hs', rfl⟩ := hC.S_surj s hs
    have h1 : g * s' * g⁻¹ ∈ S := ((Subgroup.mem_set_normalizer_iff.1 hN) s').1 hs'
    have h2 := hC.t_S _ h1
    rwa [hC.t_conj hg (hC.S_le hs')] at h2
  intro x
  refine ⟨key g hg hN x, fun hx => ?_⟩
  have h2 := key g⁻¹ (B.inv_mem hg) (Subgroup.inv_mem _ hN) (t g x) hx
  rwa [hC.t_inv hg, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply] at h2

theorem conj_mem_of_pres {l : G} (hl : l ∈ L₁) (hp : ∀ x, x ∈ Δ₀ ↔ t l x ∈ Δ₀) {s : G}
    (hs : s ∈ S) : l * s * l⁻¹ ∈ S := by
  have hlB := hC.L₁_le hl
  have hsB := hC.S_le hs
  refine hC.S_of_t _ (B.mul_mem (B.mul_mem hlB hsB) (B.inv_mem hlB)) ?_
  rw [hC.t_conj hlB hsB]
  exact normalizes_a0 hC.data hC.ha hp
    (fun x hx => altOn_apply_of_not_mem (hC.t_L₁ l hl) hx) _ (hC.t_S s hs)

theorem mem_normalizer_of_pres {l : G} (hl : l ∈ L₁) (hp : ∀ x, x ∈ Δ₀ ↔ t l x ∈ Δ₀) :
    l ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro s
  refine ⟨fun hs => hC.conj_mem_of_pres hl hp hs, fun hs => ?_⟩
  have hp' : ∀ x, x ∈ Δ₀ ↔ t l⁻¹ x ∈ Δ₀ := by
    rw [hC.t_inv (hC.L₁_le hl)]
    exact pres_inv hp
  have := hC.conj_mem_of_pres (L₁.inv_mem hl) hp' hs
  simpa [mul_assoc] using this

theorem not_le_normalizer : ¬ L₁ ≤ Subgroup.normalizer (S : Set G) := by
  intro hle
  obtain ⟨d, hd⟩ : Δ₀.Nonempty := by
    rw [← Finset.card_pos, hC.data.card_Δ₀]
    norm_num
  have ha := hC.ha
  have hb : ω a ∉ Δ₀ := hC.data.ω_not_mem ha
  have hba : ω a ≠ a := hC.data.ω_ne_self ha
  have hda : d ≠ a := fun h' => ha (h' ▸ hd)
  have hdb : d ≠ ω a := fun h' => hb (h' ▸ hd)
  have hγ : swap d a * swap a (ω a) ∈ altOn (omegaOne Δ₀ ω a) :=
    swap_mul_swap_mem_altOn (mem_omegaOne_iff.2 (Or.inr (Or.inr hd)))
      (mem_omegaOne_iff.2 (Or.inl rfl)) (mem_omegaOne_iff.2 (Or.inr (Or.inl rfl)))
      hda hba.symm hdb
  obtain ⟨l, hl, hlt⟩ := hC.L₁_surj _ hγ
  have h1 := (hC.pres_of_normalizer (hC.L₁_le hl) (hle hl) d).1 hd
  rw [hlt, Perm.mul_apply, swap_apply_of_ne_of_ne hda hdb, swap_apply_left] at h1
  exact ha h1

theorem exists_mul (hN : S ≤ Subgroup.normalizer (L₁ : Set G)) {m : G} (hm : m ∈ L₁ ⊔ S) :
    ∃ l ∈ L₁, ∃ s ∈ S, m = l * s := by
  have h1 := Subgroup.coe_mul_of_right_le_normalizer_left L₁ S hN
  have hm' : m ∈ (L₁ : Set G) * (S : Set G) := by
    rw [← h1]
    exact hm
  obtain ⟨l, hl, s, hs, rfl⟩ := Set.mem_mul.1 hm'
  exact ⟨l, hl, s, hs, rfl⟩

theorem normalizer_iff_pres (hN : S ≤ Subgroup.normalizer (L₁ : Set G)) {m : G}
    (hm : m ∈ L₁ ⊔ S) :
    m ∈ Subgroup.normalizer (S : Set G) ↔ ∀ x, x ∈ Δ₀ ↔ t m x ∈ Δ₀ := by
  have hM : L₁ ⊔ S ≤ B := sup_le hC.L₁_le hC.S_le
  constructor
  · intro hmN
    exact hC.pres_of_normalizer (hM hm) hmN
  · intro hp
    obtain ⟨l, hl, s, hs, rfl⟩ := hC.exists_mul hN hm
    have hlB := hC.L₁_le hl
    have hsB := hC.S_le hs
    have hts : ∀ x, x ∈ Δ₀ ↔ t s x ∈ Δ₀ := (a0_le_orbSub hC.data (hC.t_S s hs)).1
    have htl : ∀ x, x ∈ Δ₀ ↔ t l x ∈ Δ₀ := by
      have e : t l = t (l * s) * (t s)⁻¹ := by
        rw [hC.t_mul l hlB s hsB]
        simp
      rw [e]
      exact pres_mul hp (pres_inv hts)
    exact Subgroup.mul_mem _ (hC.mem_normalizer_of_pres hl htl) (Subgroup.le_normalizer hs)

theorem relIndex_normalizer (hN : S ≤ Subgroup.normalizer (L₁ : Set G)) :
    (Subgroup.normalizer (S : Set G)).relIndex (L₁ ⊔ S) = 15 := by
  have hM : L₁ ⊔ S ≤ B := sup_le hC.L₁_le hC.S_le
  let φ : ↥(L₁ ⊔ S) →* Perm (Fin N) :=
    MonoidHom.mk' (fun m => t m) (fun m n => hC.t_mul m (hM m.2) n (hM n.2))
  have hHs : ∀ k : ↥(L₁ ⊔ S), k ∈ (Subgroup.normalizer (S : Set G)).subgroupOf (L₁ ⊔ S) ↔
      ∀ x, x ∈ Δ₀ ↔ φ k x ∈ Δ₀ := fun k => by
    rw [Subgroup.mem_subgroupOf]
    exact hC.normalizer_iff_pres hN k.2
  rw [Subgroup.relIndex, index_eq_ncard φ Δ₀ _ hHs]
  have hΔΩ : Δ₀ ⊆ omegaOne Δ₀ ω a := fun x hx => mem_omegaOne_iff.2 (Or.inr (Or.inr hx))
  have horb : {D : Finset (Fin N) | ∃ k : ↥(L₁ ⊔ S), φ k • Δ₀ = D} =
      ↑(Finset.powersetCard 4 (omegaOne Δ₀ ω a)) := by
    ext D
    rw [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨m, hm⟩, rfl⟩
      obtain ⟨l, hl, s, hs, rfl⟩ := hC.exists_mul hN hm
      have hlB := hC.L₁_le hl
      have hsB := hC.S_le hs
      refine ⟨fun y hy => ?_, by rw [Finset.card_smul_finset, hC.data.card_Δ₀]⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
      have h1 : t s x ∈ Δ₀ := ((a0_le_orbSub hC.data (hC.t_S s hs)).1 x).1 hx
      show t (l * s) x ∈ omegaOne Δ₀ ω a
      rw [hC.t_mul l hlB s hsB, Perm.mul_apply]
      exact altOn_apply_mem (hC.t_L₁ l hl) (hΔΩ h1)
    · rintro ⟨hsub, hcard⟩
      obtain ⟨α, hα, hαD⟩ := exists_altOn_smul_eq (hC.data.card_omegaOne hC.ha) hΔΩ hsub
        hC.data.card_Δ₀ hcard
      obtain ⟨l, hl, hlt⟩ := hC.L₁_surj α hα
      refine ⟨⟨l, Subgroup.mem_sup_left hl⟩, ?_⟩
      show t l • Δ₀ = D
      rw [hlt]
      exact hαD
  rw [horb, Set.ncard_coe_finset, Finset.card_powersetCard, hC.data.card_omegaOne hC.ha]
  rfl

theorem S_le_pCoreOf :
    S ≤ pCoreOf 2 ((L₁ ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) := by
  have hSH : S ≤ (L₁ ⊔ S) ⊓ Subgroup.normalizer (S : Set G) :=
    le_inf le_sup_right Subgroup.le_normalizer
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 S _ hSH ?_ hC.S_pgroup
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSH]
  exact inf_le_right

theorem pCoreOf_le_S (hN : S ≤ Subgroup.normalizer (L₁ : Set G)) :
    pCoreOf 2 ((L₁ ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) ≤ S := by
  set H' := (L₁ ⊔ S) ⊓ Subgroup.normalizer (S : Set G) with hH'
  have hSO := hC.S_le_pCoreOf
  intro x hx
  have hxH : x ∈ H' := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H' hx
  obtain ⟨l, hl, s, hs, rfl⟩ := hC.exists_mul hN hxH.1
  have hlO : l ∈ pCoreOf 2 H' := by
    have := (pCoreOf 2 H').mul_mem hx ((pCoreOf 2 H').inv_mem (hSO hs))
    simpa using this
  have hlH : l ∈ H' := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H' hlO
  have hlB := hC.L₁_le hl
  have hpres := hC.pres_of_normalizer hlB hlH.2
  have hlS : l ∈ S := by
    refine hC.S_of_t l hlB (mem_a0_of_two_power hC.data hC.ha hpres
      (fun y hy => altOn_apply_of_not_mem (hC.t_L₁ l hl) hy) ?_)
    intro γ hγ0 hγs hγ3
    have hγalt : γ ∈ altOn (omegaOne Δ₀ ω a) :=
      mem_altOn_iff.2 ⟨mem_alternatingGroup.2 hγs,
        fun y hy => hγ0 y (not_mem_of_not_mem_omegaOne hy)⟩
    obtain ⟨h₀, hh₀, hth₀⟩ := hC.L₁_surj γ hγalt
    have hh₀B := hC.L₁_le hh₀
    have hh₀N := hC.mem_normalizer_of_pres hh₀ (by rw [hth₀]; exact pres_of_supported hγ0)
    have hh₀H : h₀ ∈ H' := ⟨Subgroup.mem_sup_left hh₀, hh₀N⟩
    have hconj : h₀ * l * h₀⁻¹ ∈ pCoreOf 2 H' :=
      ((Subgroup.mem_normalizer_iff.1
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H' hh₀H)) l).1
          hlO
    have hδ : l * (h₀ * l * h₀⁻¹) ∈ pCoreOf 2 H' := (pCoreOf 2 H').mul_mem hlO hconj
    obtain ⟨k, hk⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H' ⟨_, hδ⟩
    have hk' : (l * (h₀ * l * h₀⁻¹)) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hδB : l * (h₀ * l * h₀⁻¹) ∈ B :=
      B.mul_mem hlB (B.mul_mem (B.mul_mem hh₀B hlB) (B.inv_mem hh₀B))
    have ht : t (l * (h₀ * l * h₀⁻¹)) = t l * (γ * t l * γ⁻¹) := by
      rw [hC.t_mul l hlB _ (B.mul_mem (B.mul_mem hh₀B hlB) (B.inv_mem hh₀B)),
        hC.t_conj hh₀B hlB, hth₀]
    have h5 := congrArg t hk'
    rw [hC.t_pow hδB, ht, hC.t_one] at h5
    exact eq_one_of_pow_three_of_pow_two_pow hγ3 h5
  exact Subgroup.mul_mem S hlS hs

theorem exists_H' (hN : S ≤ Subgroup.normalizer (L₁ : Set G)) :
    ∃ H' : Subgroup G, H' < L₁ ⊔ S ∧ ¬ 2 ∣ H'.relIndex (L₁ ⊔ S) ∧ S = pCoreOf 2 H' := by
  refine ⟨(L₁ ⊔ S) ⊓ Subgroup.normalizer (S : Set G), ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun heq => hC.not_le_normalizer ?_
    calc L₁ ≤ L₁ ⊔ S := le_sup_left
      _ = (L₁ ⊔ S) ⊓ Subgroup.normalizer (S : Set G) := heq.symm
      _ ≤ Subgroup.normalizer (S : Set G) := inf_le_right
  · rw [Subgroup.inf_relIndex_left, hC.relIndex_normalizer hN]
    omega
  · exact le_antisymm hC.S_le_pCoreOf (hC.pCoreOf_le_S hN)

end MS2Ctx

section Theta

variable {G : Type} [Group G] {B : Subgroup G} (θ : ↥B →* Perm (Fin N))

open scoped Classical in
@[expose] noncomputable def thetaFun (B : Subgroup G) (θ : ↥B →* Perm (Fin N)) (g : G) :
    Perm (Fin N) :=
  if hg : g ∈ B then θ ⟨g, hg⟩ else 1

theorem thetaFun_apply {g : G} (hg : g ∈ B) : thetaFun B θ g = θ ⟨g, hg⟩ := dif_pos hg

theorem thetaFun_one : thetaFun B θ 1 = 1 := by
  rw [thetaFun_apply θ B.one_mem]
  exact map_one θ

theorem thetaFun_mul {g h : G} (hg : g ∈ B) (hh : h ∈ B) :
    thetaFun B θ (g * h) = thetaFun B θ g * thetaFun B θ h := by
  rw [thetaFun_apply θ hg, thetaFun_apply θ hh, thetaFun_apply θ (B.mul_mem hg hh)]
  exact map_mul θ ⟨g, hg⟩ ⟨h, hh⟩

theorem thetaFun_mem {K : Subgroup G} {Y : Subgroup (Perm (Fin N))}
    (hY : (K.subgroupOf B).map θ = Y) {g : G} (hgB : g ∈ B) (hg : g ∈ K) :
    thetaFun B θ g ∈ Y := by
  rw [thetaFun_apply θ hgB, ← hY]
  exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 hg)

theorem exists_thetaFun_eq {K : Subgroup G} {Y : Subgroup (Perm (Fin N))}
    (hY : (K.subgroupOf B).map θ = Y) {α : Perm (Fin N)} (hα : α ∈ Y) :
    ∃ g ∈ K, thetaFun B θ g = α := by
  rw [← hY] at hα
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hα
  exact ⟨x, Subgroup.mem_subgroupOf.1 hx, thetaFun_apply θ x.2⟩

theorem mem_of_thetaFun_mem {S : Subgroup G} {Y : Subgroup (Perm (Fin N))}
    (hY : (S.subgroupOf B).map θ = Y) (hker : ∀ m : ↥B, θ m = 1 → (m : G) ∈ S) {g : G}
    (hgB : g ∈ B) (hg : thetaFun B θ g ∈ Y) : g ∈ S := by
  rw [thetaFun_apply θ hgB, ← hY] at hg
  obtain ⟨s', hs', hθ⟩ := Subgroup.mem_map.1 hg
  have h1 := hker (⟨g, hgB⟩ * s'⁻¹) (by rw [map_mul, map_inv, hθ, mul_inv_cancel])
  have h2 : (s' : G) ∈ S := Subgroup.mem_subgroupOf.1 hs'
  have h3 : g = g * (s' : G)⁻¹ * s' := by group
  rw [h3]
  exact S.mul_mem (by simpa using h1) h2

end Theta

theorem MS2Ctx.of_E0NS {G : Type} [Group G] [Finite G] {X S L : Subgroup G} {N : ℕ}
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))}
    {ω : Perm (Fin N)} (hE : E0NS X S L N θ Δ₀ P ω) {a : Fin N} (ha : a ∉ Δ₀)
    {L₁ : Subgroup G} (hL₁ : L₁ = subL S L θ (omegaOne Δ₀ ω a))
    (hθ₁ : (L₁.subgroupOf (L ⊔ S)).map θ = altOn (omegaOne Δ₀ ω a)) :
    MS2Ctx (L ⊔ S) S L₁ (thetaFun (L ⊔ S) θ) Δ₀ P ω a := by
  have hL₁le : L₁ ≤ L ⊔ S := hL₁ ▸ (subL_le S L θ _).trans le_sup_left
  have hSθ : (S.subgroupOf (L ⊔ S)).map θ = a0 Δ₀ P ω := hE.image_S
  refine ⟨hE.toE0Data, ha, le_sup_right, hL₁le, hE.asc.twoRadical.isPGroup, thetaFun_one θ,
    fun g hg h hh => thetaFun_mul θ hg hh, fun s hs => ?_, fun g hg hgt => ?_, fun α hα => ?_,
    fun l hl => ?_, fun α hα => ?_⟩
  · exact thetaFun_mem θ hSθ ((le_sup_right : S ≤ L ⊔ S) hs) hs
  · exact mem_of_thetaFun_mem θ hSθ hE.ker_le hg hgt
  · obtain ⟨g, hg, hgt⟩ := exists_thetaFun_eq θ hSθ hα
    exact ⟨g, hg, hgt⟩
  · exact thetaFun_mem θ hθ₁ (hL₁le hl) hl
  · obtain ⟨g, hg, hgt⟩ := exists_thetaFun_eq θ hθ₁ hα
    exact ⟨g, hg, hgt⟩

end MS2

theorem notNormSubLStmt_holds : NotNormSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁
  exact (MS2.MS2Ctx.of_E0NS hE ha hL₁ hθ₁).not_le_normalizer

theorem mS2SubLStmt_holds : MS2SubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁ hN
  exact (MS2.MS2Ctx.of_E0NS hE ha hL₁ hθ₁).exists_H' hN

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
