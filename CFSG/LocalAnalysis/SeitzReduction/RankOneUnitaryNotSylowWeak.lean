module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylowSplit

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

@[expose] def U3StrongClosureInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂) →
    ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), g⁻¹ * t * g ∈ T ⊔ R₂ →
      g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t

@[expose] def U3StrongClosureNcycInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂) →
    ∀ v ∈ T, v ^ 2 = 1 → v ∉ szT₁ L T ⊔ zpowers t →
    ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), g⁻¹ * t * g ∈ T ⊔ R₂ →
      g⁻¹ * t * g ∈ szR (szT₁ L T) R₂ t

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_commutatorAut_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {v : G} (hvT : v ∈ T)
    (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t) :
    ∃ W : Subgroup G, W ≤ szT₁ L T ∧ szA₁ (szT₁ L T) ≤ W ∧ Nat.card W = (2 ^ f) ^ 2 ∧
      ∀ y ∈ szT₁ L T, y⁻¹ * (v * y * v⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ W := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  have hout := (h.outer_facts_of_card_sylow hS2 hvT hv2 hvS).1
  set σ := L.normalizerMonoidHom ⟨v, h.le_normalizer hvT⟩ with hσdef
  have hσ : ∀ y : L, ((σ y : L) : G) = v * y * v⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hσ, hσ]
    calc v * (v * (y : G) * v⁻¹) * v⁻¹ = (v * v) * y * (v * v)⁻¹ := by group
      _ = y := by rw [hvv]; group
  have hσout : ¬ ∃ g : L, ∀ y : L, σ y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hout ⟨g, g.2, fun y hy => ?_⟩
    have := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hσ] at this
    simpa using this
  have hσQ : ∀ y ∈ (Q : Subgroup L), σ y ∈ (Q : Subgroup L) := by
    intro y hy
    rw [hmemQ, hσ]
    exact (mem_normalizer_iff.mp (hTN₁ hvT) y).mp ((hmemQ y).mp hy)
  obtain ⟨hWQ, hZW, hWcard, -, -, -, -, -, hiff⟩ := hB.lemma_3_4_d5_unitary Q σ hσσ hσout hσQ
  refine ⟨(commutatorAut (Q : Subgroup L) σ).map L.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (hmemQ w).mp (hWQ hw)
  · intro a ha
    have haL : a ∈ L := szT₁_le_right L T (szA₁_le _ ha)
    exact ⟨⟨a, haL⟩, hZW ((hmemZ ⟨a, haL⟩).mpr ha), rfl⟩
  · rw [card_map_of_injective L.subtype_injective, hWcard]
  · intro y hy hyv
    have hyL : y ∈ L := szT₁_le_right L T hy
    refine ⟨⟨y, hyL⟩, (hiff ⟨y, hyL⟩ ((hmemQ _).mpr hy)).mp ((hmemZ _).mpr ?_), rfl⟩
    simpa [hσ] using hyv

section Certificates

theorem mem_szA₁_of_conj_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) {r : G} (hr : r ∈ R₂) :
    v * r * v⁻¹ * r⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, -, -, -, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hsR : v * r * v⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (hNR₂ (hTA hvT)) r).mp hr
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hvA₁ := (h.outer_facts_of_card_sylow hS2 hvT hv2 hvS).2.1
  have hvt' : v⁻¹ * t * v = t := by rw [mul_assoc, ← hvt, inv_mul_cancel_left]
  have h1 : r * t * r⁻¹ = (v * r * v⁻¹) * t * (v * r * v⁻¹)⁻¹ := by
    have hρ := hR.rho_mem r hr
    have e : (v * r * v⁻¹) * t * (v * r * v⁻¹)⁻¹ * t = r * t * r⁻¹ * t := by
      calc (v * r * v⁻¹) * t * (v * r * v⁻¹)⁻¹ * t =
          v * (r * (v⁻¹ * t * v) * r⁻¹ * (v⁻¹ * t * v)) * v⁻¹ := by group
        _ = v * (r * t * r⁻¹ * t) * v⁻¹ := by rw [hvt']
        _ = r * t * r⁻¹ * t := by rw [hvA₁ _ hρ, mul_inv_cancel_right]
    exact (mul_right_cancel e).symm
  have hA : r⁻¹ * (v * r * v⁻¹) ∈ szA₁ (szT₁ L T) := by
    refine hR.rho_ker _ (mul_mem (inv_mem hr) hsR) ?_
    calc r⁻¹ * (v * r * v⁻¹) * t =
        r⁻¹ * ((v * r * v⁻¹) * t * (v * r * v⁻¹)⁻¹) * (v * r * v⁻¹) := by group
      _ = r⁻¹ * (r * t * r⁻¹) * (v * r * v⁻¹) := by rw [h1]
      _ = t * (r⁻¹ * (v * r * v⁻¹)) := by group
  rw [show v * r * v⁻¹ * r⁻¹ = (v * r * v⁻¹) * r⁻¹ from rfl, hR.comm _ hsR _ (inv_mem hr)]
  exact hA

theorem weakClosed_of_outer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) :
    ∀ k ∈ normalizer (szA₁ (szT₁ L T) : Set G),
      (∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ T ⊔ R₂) →
        ∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ szR (szT₁ L T) R₂ t := by
  classical
  intro k hk hkS
  by_contra hcon
  push Not at hcon
  obtain ⟨r₀, hr₀, hx⟩ := hcon
  obtain ⟨hR₁, hS₁N, -, hR₁S₁, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hvA₁ := (h.outer_facts_of_card_sylow hS2 hvT hv2 hvS).2.1
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  set R₁ := szR (szT₁ L T) R₂ t with hR₁def
  have hR₁A : ∀ e ∈ R₁, ∀ a ∈ szA₁ (szT₁ L T), a * e = e * a := by
    intro e he a ha
    have he' : e ∈ u3R₁ L T t := by rw [← hR₁]; exact he
    exact mem_centralizer_iff.mp he'.2.1 a ha
  have hcommR₁ : ∀ e ∈ R₁, ∀ e' ∈ R₁, e * e' * e⁻¹ * e'⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro e he e' he'
    have h1 : e ∈ u3R₁ L T t := by rw [← hR₁]; exact he
    have h2 : e' ∈ u3R₁ L T t := by rw [← hR₁]; exact he'
    exact h.comm_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 h1 h2
  have hsqR₁ : ∀ e ∈ R₁, e ^ 2 ∈ szA₁ (szT₁ L T) := by
    intro e he
    have h1 : e ∈ u3R₁ L T t := by rw [← hR₁]; exact he
    exact h.sq_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 h1
  set F := R₁.map (MulAut.conj k⁻¹).toMonoidHom with hFdef
  have hmemF : ∀ y, y ∈ F ↔ k * y * k⁻¹ ∈ R₁ := fun y => mem_map_conj_inv_iff'
  have hFS : ∀ y ∈ F, y ∈ T ⊔ R₂ := by
    intro y hy
    have := hkS _ ((hmemF y).mp hy)
    rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group] at this
  have hkA : ∀ a ∈ szA₁ (szT₁ L T), k⁻¹ * a * k ∈ szA₁ (szT₁ L T) := fun a ha =>
    (mem_normalizer_iff''.mp hk a).mp ha
  have hsqF : ∀ y ∈ F, y ^ 2 ∈ szA₁ (szT₁ L T) := by
    intro y hy
    have := hkA _ (hsqR₁ _ ((hmemF y).mp hy))
    rwa [show k⁻¹ * (k * y * k⁻¹) ^ 2 * k = y ^ 2 by rw [sq, sq]; group] at this
  have hcommF : ∀ y ∈ F, ∀ y' ∈ F, y * y' * y⁻¹ * y'⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro y hy y' hy'
    have := hkA _ (hcommR₁ _ ((hmemF y).mp hy) _ ((hmemF y').mp hy'))
    rwa [show k⁻¹ * (k * y * k⁻¹ * (k * y' * k⁻¹) * (k * y * k⁻¹)⁻¹ * (k * y' * k⁻¹)⁻¹) * k =
      y * y' * y⁻¹ * y'⁻¹ by group] at this
  have hT₁tR₁ : szT₁ L T ⊔ zpowers t ≤ R₁ :=
    sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))
  have hvF : ∀ y ∈ F, y ∉ R₁ → v⁻¹ * y ∈ R₁ := by
    intro y hy hyR
    obtain ⟨s, hs, r, hr, hsr, hs2⟩ := h.exists_sq_mem_szT₁_of_card_sylow hS2 hR (hFS y hy)
      (mem_sup_left (szA₁_le _ (hsqF y hy)))
    have hsS : s ∉ szT₁ L T ⊔ zpowers t := fun hsS => hyR (hsr ▸ mul_mem (hT₁tR₁ hsS) hr)
    have hsv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hs hvT (mem_sup_left hs2)
      (by rw [hv2]; exact one_mem _) hsS hvS
    have hvN : v⁻¹ ∈ normalizer (R₁ : Set G) := inv_mem (hS₁N (mem_sup_left hvT))
    rw [← hsr, show v⁻¹ * (s * r) = v⁻¹ * (s * v⁻¹) * v⁻¹⁻¹ * r by group]
    exact mul_mem ((mem_normalizer_iff.mp hvN _).mp (hT₁tR₁ hsv)) hr
  set x := k⁻¹ * r₀ * k with hxdef
  have hxF : x ∈ F := by
    rw [hmemF x, hxdef, show k * (k⁻¹ * r₀ * k) * k⁻¹ = r₀ by group]
    exact hr₀
  have hr₁ := hvF x hxF hx
  obtain ⟨W, hWT₁, hAW, hWcard, hWmem⟩ := h.exists_commutatorAut_of_card_sylow hS2 hvT hv2 hvS
  have hFR : F ⊓ R₁ ≤ (W ⊔ R₂) ⊔ zpowers t := by
    intro e he
    obtain ⟨heF, heR⟩ := mem_inf.mp he
    set r₁ := v⁻¹ * x with hr₁def
    have hc := hcommR₁ r₁ hr₁ e⁻¹ (inv_mem heR)
    set c := r₁ * e⁻¹ * r₁⁻¹ * e⁻¹⁻¹ with hcdef
    have hvc : v * c = c * v := (hvA₁ c hc)
    have hec : e * c = c * e := (hR₁A e heR c hc).symm
    have hev : e * v * e⁻¹ * v⁻¹ ∈ szA₁ (szT₁ L T) := by
      have h1 := hcommF e heF x hxF
      have e1 : e * x * e⁻¹ * x⁻¹ = c * (e * v * e⁻¹ * v⁻¹) := by
        have hx' : x = v * r₁ := by rw [hr₁def]; group
        calc e * x * e⁻¹ * x⁻¹ = e * v * (r₁ * e⁻¹ * r₁⁻¹ * e⁻¹⁻¹) * e⁻¹ * v⁻¹ := by
              rw [hx']; group
          _ = e * (v * c) * e⁻¹ * v⁻¹ := by rw [hcdef]; group
          _ = e * (c * v) * e⁻¹ * v⁻¹ := by rw [hvc]
          _ = (e * c) * v * e⁻¹ * v⁻¹ := by group
          _ = (c * e) * v * e⁻¹ * v⁻¹ := by rw [hec]
          _ = c * (e * v * e⁻¹ * v⁻¹) := by group
      rw [e1] at h1
      have := mul_mem (inv_mem hc) h1
      rwa [inv_mul_cancel_left] at this
    obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_of_mem_szR hR heR
    obtain ⟨y, hy, r, hr, hyr⟩ := hR.mem_sup_iff.mp hw
    have hzv : z * v = v * z := (commute_of_mem_zpowers hz hvt).symm
    have ha := h.mem_szA₁_of_conj_of_card_sylow hS2 hR hvT hv2 hvS (inv_mem hr)
    set a := v * r⁻¹ * v⁻¹ * r⁻¹⁻¹ with hadef
    have har : r * a = a * r := (hR.comm _ hr _ (hR.le ha))
    have hay : y * a = a * y := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy
    have hyv : y * v * y⁻¹ * v⁻¹ ∈ szA₁ (szT₁ L T) := by
      have e2 : e * v * e⁻¹ * v⁻¹ = a * (y * v * y⁻¹ * v⁻¹) := by
        rw [← hwz, ← hyr]
        calc y * r * z * v * (y * r * z)⁻¹ * v⁻¹ = y * r * (z * v) * z⁻¹ * r⁻¹ * y⁻¹ * v⁻¹ := by
              group
          _ = y * r * (v * z) * z⁻¹ * r⁻¹ * y⁻¹ * v⁻¹ := by rw [hzv]
          _ = y * (r * (v * r⁻¹ * v⁻¹ * r⁻¹⁻¹) * r⁻¹) * v * y⁻¹ * v⁻¹ := by group
          _ = y * (r * a * r⁻¹) * v * y⁻¹ * v⁻¹ := by rw [hadef]
          _ = y * (a * r * r⁻¹) * v * y⁻¹ * v⁻¹ := by rw [har]
          _ = (y * a) * v * y⁻¹ * v⁻¹ := by group
          _ = (a * y) * v * y⁻¹ * v⁻¹ := by rw [hay]
          _ = a * (y * v * y⁻¹ * v⁻¹) := by group
      rw [e2] at hev
      have := mul_mem (inv_mem ha) hev
      rwa [inv_mul_cancel_left] at this
    have hyW : y ∈ W := by
      refine hWmem y hy ?_
      set b := y * v * y⁻¹ * v⁻¹ with hbdef
      have hby : y * b = b * y := mem_centralizer_iff.mp (mem_szA₁.mp hyv).2 y hy
      have hb'y : b⁻¹ * y = y * b⁻¹ := by
        calc b⁻¹ * y = b⁻¹ * (y * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * y) * b⁻¹ := by rw [hby]
          _ = y * b⁻¹ := by group
      have e3 : y⁻¹ * (v * y * v⁻¹) = y⁻¹ * b⁻¹ * y := by rw [hbdef]; group
      rw [e3, mul_assoc, hb'y, inv_mul_cancel_left]
      exact inv_mem hyv
    rw [← hwz, ← hyr]
    exact mul_mem (mem_sup_left (mul_mem (mem_sup_left hyW) (mem_sup_right hr))) (mem_sup_right hz)
  have hcardF : Nat.card F = 2 * (2 ^ f) ^ 4 := by
    rw [hFdef, card_map_of_injective (MulAut.conj k⁻¹).injective, hR₁,
      h.card_u3R₁_of_card_sylow hS2]
  have hxR₁ : ∀ y : F, (y : G) ∉ R₁ → x⁻¹ * (y : G) ∈ F ⊓ R₁ := by
    intro y hy
    refine mem_inf.mpr ⟨mul_mem (inv_mem hxF) y.2, ?_⟩
    rw [show x⁻¹ * (y : G) = (v⁻¹ * x)⁻¹ * (v⁻¹ * y) by group]
    exact mul_mem (inv_mem hr₁) (hvF y y.2 hy)
  have hle1 : Nat.card F ≤ Nat.card (F ⊓ R₁ : Subgroup G) * 2 := by
    let φ : F → (F ⊓ R₁ : Subgroup G) × Bool := fun y =>
      if hy : (y : G) ∈ R₁ then (⟨y, mem_inf.mpr ⟨y.2, hy⟩⟩, false)
      else (⟨x⁻¹ * y, hxR₁ y hy⟩, true)
    have hinj : Function.Injective φ := by
      intro y y' hyy'
      by_cases hy : (y : G) ∈ R₁ <;> by_cases hy' : (y' : G) ∈ R₁
      · have := congrArg (fun p => ((p.1 : (F ⊓ R₁ : Subgroup G)) : G)) hyy'
        simp only [φ, hy, hy', dite_true] at this
        exact Subtype.ext this
      · have := congrArg Prod.snd hyy'
        simp [φ, hy, hy'] at this
      · have := congrArg Prod.snd hyy'
        simp [φ, hy, hy'] at this
      · have := congrArg (fun p => ((p.1 : (F ⊓ R₁ : Subgroup G)) : G)) hyy'
        simp only [φ, hy, hy', dite_false] at this
        exact Subtype.ext (mul_left_cancel this)
    have := Nat.card_le_card_of_injective φ hinj
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  have hle2 : Nat.card (F ⊓ R₁ : Subgroup G) ≤ 2 * (2 ^ f) ^ 3 := by
    have h1 : Nat.card (F ⊓ R₁ : Subgroup G) ≤ Nat.card ((W ⊔ R₂) ⊔ zpowers t : Subgroup G) :=
      card_le_of_le hFR
    have htW : t ∈ normalizer (W : Set G) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => hR.t_comm w (hWT₁ hw))
    have htN : zpowers t ≤ normalizer ((W ⊔ R₂ : Subgroup G) : Set G) :=
      zpowers_le.mpr (mem_normalizer_sup_of_mem_inf htW hR.t_mem_normalizer)
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer htN
    rw [sup_comm] at hprod
    have hzt : Nat.card (zpowers t) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hR.t_sq
    have h2 : Nat.card ((W ⊔ R₂) ⊔ zpowers t : Subgroup G) ≤
        2 * Nat.card (W ⊔ R₂ : Subgroup G) := by
      have hpos : 0 < Nat.card (zpowers t ⊓ (W ⊔ R₂) : Subgroup G) := Nat.card_pos
      calc Nat.card ((W ⊔ R₂) ⊔ zpowers t : Subgroup G) ≤
          Nat.card ((W ⊔ R₂) ⊔ zpowers t : Subgroup G) *
            Nat.card (zpowers t ⊓ (W ⊔ R₂) : Subgroup G) := Nat.le_mul_of_pos_right _ hpos
        _ = Nat.card (zpowers t) * Nat.card (W ⊔ R₂ : Subgroup G) := hprod
        _ ≤ 2 * Nat.card (W ⊔ R₂ : Subgroup G) := Nat.mul_le_mul_right _ hzt
    have hprod2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (hWT₁.trans hR.T₁_le_normalizer)
    rw [hWcard, hR.card] at hprod2
    have hWR : 2 ^ f ≤ Nat.card (W ⊓ R₂ : Subgroup G) := hA₁card ▸ card_le_of_le (le_inf hAW hR.le)
    have hq : 0 < 2 ^ f := by positivity
    have h3 : Nat.card (W ⊔ R₂ : Subgroup G) ≤ (2 ^ f) ^ 3 := by
      have h4 : Nat.card (W ⊔ R₂ : Subgroup G) * 2 ^ f ≤ (2 ^ f) ^ 3 * 2 ^ f := by
        calc Nat.card (W ⊔ R₂ : Subgroup G) * 2 ^ f ≤
            Nat.card (W ⊔ R₂ : Subgroup G) * Nat.card (W ⊓ R₂ : Subgroup G) :=
              Nat.mul_le_mul_left _ hWR
          _ = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := hprod2
          _ = (2 ^ f) ^ 3 * 2 ^ f := by ring
      exact Nat.le_of_mul_le_mul_right h4 hq
    omega
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have h5 : 2 * (2 ^ f) ^ 4 ≤ 2 * (2 ^ f) ^ 3 * 2 :=
    hcardF ▸ hle1.trans (Nat.mul_le_mul_right 2 hle2)
  have h6 : 2 * (2 ^ f) ^ 4 = 2 * (2 ^ f) ^ 3 * 2 ^ f := by ring
  rw [h6] at h5
  have h7 : 0 < 2 * (2 ^ f) ^ 3 := by positivity
  have := Nat.le_of_mul_le_mul_left h5 h7
  omega

omit [Finite G] in
theorem _root_.CFSG.SeitzReduction.RankOne.u3StrongClosureInput_of_ncyc
    (hnc : U3StrongClosureNcycInput) : U3StrongClosureInput := by
  intro G _ _ L f t T R₂ h hS2 hR hS g hg hx
  by_cases hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T
  · refine h.mem_szR_of_sq_mem_of_card_sylow hS2 hR hcyc hx ?_
    rw [show (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g by rw [sq, sq]; group, h.sq_eq_one, mul_one,
      inv_mul_cancel]
    exact one_mem _
  · obtain ⟨v, hvT, hv2, hvS⟩ := u3SplitInput G L f t T h hS2 hcyc
    exact hnc G L f t T R₂ h hS2 hR hS v hvT hv2 hvS g hg hx

omit [Finite G] in
theorem _root_.CFSG.SeitzReduction.RankOne.u3ClosureInput_of_strong
    (hsc : U3StrongClosureInput) : U3ClosureInput := by
  intro G _ _ L f t T R₂ h hS2 hR hS
  refine ⟨?_, hsc G L f t T R₂ h hS2 hR hS⟩
  by_cases hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T
  · intro k hk hkS r hr
    obtain ⟨hR₁, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
    refine h.mem_szR_of_sq_mem_of_card_sylow hS2 hR hcyc (hkS r hr) ?_
    have hr2 : r ^ 2 ∈ szA₁ (szT₁ L T) := by
      rw [hR₁] at hr
      exact h.sq_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 hr
    rw [show (k⁻¹ * r * k) ^ 2 = k⁻¹ * r ^ 2 * k by rw [sq, sq]; group]
    exact mem_sup_left (szA₁_le _ ((mem_normalizer_iff''.mp hk _).mp hr2))
  · obtain ⟨v, hvT, hv2, hvS⟩ := u3SplitInput G L f t T h hS2 hcyc
    exact h.weakClosed_of_outer_of_card_sylow hS2 hR hvT hv2 hvS

theorem not_isSylow_S₁_of_strong_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f)
    (hsc : U3StrongClosureInput) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ :=
  h.not_isSylow_S₁_of_closure_of_card_sylow hS2 hR hstar (u3ClosureInput_of_strong hsc)

end Certificates

section Certificates43

theorem not_isSylow_S₁_of_strong (h : U3Start G L f t T) (hstar : StarPrimeStatement f)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) (hsc : U3StrongClosureInput) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ :=
  h.not_isSylow_S₁_of_strong_of_card_sylow h.card_sylow hR hstar hsc

theorem not_isSylow_S₁_of_ncyc (h : U3Start G L f t T) (hstar : StarPrimeStatement f)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) (hnc : U3StrongClosureNcycInput) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ :=
  h.not_isSylow_S₁_of_strong hstar hR (u3StrongClosureInput_of_ncyc hnc)

end Certificates43

end U3Start

end CFSG.SeitzReduction.RankOne
