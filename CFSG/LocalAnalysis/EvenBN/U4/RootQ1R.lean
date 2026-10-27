module

public import CFSG.LocalAnalysis.EvenBN.U4.RootQ1S
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.CentralSquares

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf
  mem_of_mem_commutator_sup_of_fixed card_sup_mul_card_inf_eq)
open scoped commutatorElement

@[expose] noncomputable def miyamotoRG {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  ⁅miyamotoIG h L η, miyamotoS h L η t Q⁆ ⊔ (miyamotoF1G h L η t ⊔ miyamotoPG h L η)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

noncomputable def crossedQ1 (hS : Setting h L η t Q T) (g : G) : K :=
  hS.coordP1 (t * (g⁻¹ * t * g))

theorem crossed_mem_P1 (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :
    t * (g⁻¹ * t * g) ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η :=
  hS.orbit_shape.1 g hg

theorem coordP1_F1_mul (hS : Setting h L η t Q T) {f₀ x : G} (hf₀ : f₀ ∈ miyamotoF1G h L η t)
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) : hS.coordP1 (f₀ * x) = hS.coordP1 x := by
  rw [hS.coordP1_mul (mem_sup_left hf₀) hx, hS.coordP1_of_mem_F1 hf₀, zero_add]

theorem coordP1_mul_F1 (hS : Setting h L η t Q T) {f₀ x : G} (hf₀ : f₀ ∈ miyamotoF1G h L η t)
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) : hS.coordP1 (x * f₀) = hS.coordP1 x := by
  rw [hS.coordP1_mul hx (mem_sup_left hf₀), hS.coordP1_of_mem_F1 hf₀, add_zero]

theorem crossedQ1_mul (hS : Setting h L η t Q T) {s s' : G} (hs : s ∈ miyamotoS h L η t Q)
    (hs' : s' ∈ miyamotoS h L η t Q) :
    hS.crossedQ1 (s * s') = hS.crossedQ1 s + hS.crossedQ1 s' := by
  have hcs := hS.crossed_mem_P1 (hS.miyamotoS_le_normalizer_Q1 hs)
  have hcs' := hS.crossed_mem_P1 (hS.miyamotoS_le_normalizer_Q1 hs')
  have hf := hS.commutator_miyamotoS_P1_mem_F1 (inv_mem hs') hcs
  set c := t * (s⁻¹ * t * s) with hc
  set c' := t * (s'⁻¹ * t * s') with hc'
  have e : t * ((s * s')⁻¹ * t * (s * s')) = c' * ((s'⁻¹ * c * s'⁻¹⁻¹ * c⁻¹) * c) := by
    calc t * ((s * s')⁻¹ * t * (s * s')) = t * s'⁻¹ * (t * t) * s⁻¹ * t * s * s' := by
          rw [hS.t_mul_t]; group
      _ = c' * ((s'⁻¹ * c * s'⁻¹⁻¹ * c⁻¹) * c) := by rw [hc, hc']; group
  simp only [crossedQ1]
  rw [e, hS.coordP1_mul hcs' (mul_mem (mem_sup_left hf) hcs), hS.coordP1_F1_mul hf hcs,
    add_comm]

theorem crossedQ1_one (hS : Setting h L η t Q T) : hS.crossedQ1 1 = 0 := by
  simp only [crossedQ1, inv_one, one_mul, mul_one, hS.t_mul_t]
  exact hS.coordP1_of_mem_F1 (one_mem _)

theorem crossedQ1_inv (hS : Setting h L η t Q T) {s : G} (hs : s ∈ miyamotoS h L η t Q) :
    hS.crossedQ1 s⁻¹ = -hS.crossedQ1 s := by
  have := hS.crossedQ1_mul hs (inv_mem hs)
  rw [mul_inv_cancel, hS.crossedQ1_one] at this
  linear_combination -this

theorem crossedQ1_eq_zero_iff (hS : Setting h L η t Q T) {s : G}
    (hs : s ∈ miyamotoS h L η t Q) : hS.crossedQ1 s = 0 ↔ s ∈ miyamotoF1G h L η t ⊔ Q := by
  have hcs := hS.crossed_mem_P1 (hS.miyamotoS_le_normalizer_Q1 hs)
  have e : (s * t)⁻¹ * (t * s) = t * (s⁻¹ * t * s) := by
    rw [mul_inv_rev, hS.t_inv]; group
  rw [crossedQ1, hS.coordP1_eq_zero_iff hcs]
  constructor
  · intro h1
    exact hS.mem_Q1_of_mem_miyamotoS hs (e ▸ h1)
  · intro hsQ
    have := (hS.Q1_mod_F1).2 t⁻¹ (inv_mem (mem_sup_right hS.t_mem_Q)) s⁻¹ (inv_mem hsQ)
    rw [commutatorElement_def, inv_inv, inv_inv, hS.t_inv] at this
    rwa [show t * (s⁻¹ * t * s) = t * s⁻¹ * t * s by group]

theorem exists_crossedQ1_eq (hS : Setting h L η t Q T) (κ : K) :
    ∃ s ∈ miyamotoS h L η t Q, hS.crossedQ1 s = κ := by
  have hx := hS.rootElt_mem_P1 κ
  obtain ⟨s, hs, hf⟩ := hS.exists_mem_miyamotoS_conj hx
  refine ⟨s, hs, ?_⟩
  have e : t * (s⁻¹ * t * s) = hS.rootElt κ * ((s⁻¹ * t * s)⁻¹ * (t * hS.rootElt κ))⁻¹ := by
    calc t * (s⁻¹ * t * s) = t⁻¹ * (s⁻¹ * t * s) := by rw [hS.t_inv]
      _ = hS.rootElt κ * ((s⁻¹ * t * s)⁻¹ * (t * hS.rootElt κ))⁻¹ := by group
  rw [crossedQ1, e, hS.coordP1_mul_F1 (inv_mem hf) hx, hS.coordP1_rootElt]

theorem coordP1_torus_conj (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) {x : G} (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    hS.coordP1 ((hS.torusElt p hp)⁻¹ * x * hS.torusElt p hp) =
      miyamotoWeightA p * hS.coordP1 x := by
  set i := hS.torusElt p hp with hi
  have hiN := hS.IG_le_normalizer_F1 (hS.torusElt_mem_IG p hp)
  have hspec := hS.coordP1_spec hx
  set f₀ := x * (hS.rootElt (hS.coordP1 x))⁻¹ with hf₀
  refine hS.coordP1_eq ?_
  have h1 : i⁻¹ * f₀ * i ∈ miyamotoF1G h L η t := by
    have := (mem_normalizer_iff.1 (inv_mem hiN) f₀).1 hspec
    rwa [inv_inv] at this
  have e : i⁻¹ * x * i * (hS.rootElt (miyamotoWeightA p * hS.coordP1 x))⁻¹ = i⁻¹ * f₀ * i := by
    rw [← hS.torusElt_conj_rootElt p hp, ← hi, hf₀]
    group
  rw [e]
  exact h1

theorem crossedQ1_torus_conj (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) {s : G}
    (hs : s ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :
    hS.crossedQ1 ((hS.torusElt p hp)⁻¹ * s * hS.torusElt p hp) =
      miyamotoWeightA p * hS.crossedQ1 s := by
  set i := hS.torusElt p hp with hi
  have hit : i * t = t * i := mem_centralizer_singleton_iff.1 (hS.IG_le_C (hS.torusElt_mem_IG p hp))
  have e : t * ((i⁻¹ * s * i)⁻¹ * t * (i⁻¹ * s * i)) = i⁻¹ * (t * (s⁻¹ * t * s)) * i := by
    have hit' : i⁻¹ * t = t * i⁻¹ := by
      calc i⁻¹ * t = i⁻¹ * (t * i) * i⁻¹ := by group
        _ = i⁻¹ * (i * t) * i⁻¹ := by rw [hit]
        _ = t * i⁻¹ := by group
    calc t * ((i⁻¹ * s * i)⁻¹ * t * (i⁻¹ * s * i)) = (t * i⁻¹) * s⁻¹ * (i * t) * i⁻¹ * s * i := by
          group
      _ = i⁻¹ * (t * (s⁻¹ * t * s)) * i := by rw [← hit', hit]; group
  simp only [crossedQ1]
  rw [e]
  exact hS.coordP1_torus_conj p hp (hS.crossed_mem_P1 hs)

theorem mem_P1_sup_zpowers_of_mem_Q1 (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ Q) :
    x ∈ (miyamotoF1G h L η t ⊔ miyamotoPG h L η) ⊔ zpowers t := by
  rcases hS.mem_P1_or_of_mem_Q1 hx with h1 | h1
  · exact mem_sup_left h1
  · have e : x = t * (t * x) := by rw [← mul_assoc, hS.t_mul_t, one_mul]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)

theorem miyamotoS_mod_P1 (hS : Setting h L η t Q T) :
    (∀ s ∈ miyamotoS h L η t Q, s * s ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) ∧
      ∀ s ∈ miyamotoS h L η t Q, ∀ s' ∈ miyamotoS h L η t Q,
        s * s' * s⁻¹ * s'⁻¹ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
  have : CharP K 2 := h.charP
  have := h.finite
  have hP1Q1 := hS.P1_le_Q1
  have hQ1S := hS.Q1_le_miyamotoS
  have hSN : miyamotoS h L η t Q ≤
      normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
    hS.miyamotoS_le_normalizer_Q1.trans hS.normalizer_Q1_le_normalizer_P1
  have htN : t ∈ normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
    hSN (hQ1S (mem_sup_right hS.t_mem_Q))
  have hγ0 := fun {s : G} (hs : s ∈ miyamotoS h L η t Q) => hS.crossedQ1_eq_zero_iff hs
  have hZ2 : ∀ a ∈ miyamotoF1G h L η t ⊔ Q, ∀ b ∈ miyamotoF1G h L η t ⊔ Q,
      a ∉ miyamotoF1G h L η t ⊔ miyamotoPG h L η → b ∉ miyamotoF1G h L η t ⊔ miyamotoPG h L η →
        a * b ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
    intro a ha b hb haP hbP
    have ha' := (hS.mem_P1_or_of_mem_Q1 ha).resolve_left haP
    have hb' := (hS.mem_P1_or_of_mem_Q1 hb).resolve_left hbP
    have e : a * b = (t * (t * a) * t⁻¹) * (t * b) := by
      calc a * b = (t * t) * a * (t⁻¹ * t) * b := by rw [hS.t_mul_t, inv_mul_cancel]; group
        _ = (t * (t * a) * t⁻¹) * (t * b) := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 htN _).1 ha') hb'
  have hZc : ∀ s ∈ miyamotoS h L η t Q, ∀ a ∈ miyamotoF1G h L η t ⊔ Q,
      s * a * s⁻¹ * a⁻¹ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
    intro s hs a ha
    rcases hS.mem_P1_or_of_mem_Q1 ha with haP | htaP
    · exact mem_sup_left (hS.commutator_miyamotoS_P1_mem_F1 hs haP)
    ·
      set p := t * a with hp
      have hap : a = t * p := by rw [hp, ← mul_assoc, hS.t_mul_t, one_mul]
      have h1 : t * (s * t * s⁻¹) ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
        have := hS.crossed_mem_P1 (hS.miyamotoS_le_normalizer_Q1 (inv_mem hs))
        rwa [inv_inv] at this
      have h2 : s * p * s⁻¹ * p⁻¹ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η :=
        mem_sup_left (hS.commutator_miyamotoS_P1_mem_F1 hs htaP)
      have e : s * a * s⁻¹ * a⁻¹ = t * ((t * (s * t * s⁻¹)) * (s * p * s⁻¹ * p⁻¹)) * t⁻¹ := by
        calc s * a * s⁻¹ * a⁻¹ = (t * t) * s * t * p * s⁻¹ * (p⁻¹ * t⁻¹) := by
              rw [hS.t_mul_t, hap]; group
          _ = t * ((t * (s * t * s⁻¹)) * (s * p * s⁻¹ * p⁻¹)) * t⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 htN _).1 (mul_mem h1 h2)
  refine sq_mem_and_commutator_mem_of_transitive hP1Q1 hQ1S hSN hZ2 hZc
    (fun s hs => (hγ0 (mul_mem hs hs)).1 ?_) (fun s hs s' hs' => (hγ0 ?_).1 ?_)
    (fun s hs hsZ s' hs' hs'Z => ?_) ?_
  · rw [hS.crossedQ1_mul hs hs, CharTwo.add_self_eq_zero]
  · exact mul_mem (mul_mem (mul_mem hs hs') (inv_mem hs)) (inv_mem hs')
  · rw [hS.crossedQ1_mul (mul_mem (mul_mem hs hs') (inv_mem hs)) (inv_mem hs'),
      hS.crossedQ1_mul (mul_mem hs hs') (inv_mem hs), hS.crossedQ1_mul hs hs',
      hS.crossedQ1_inv hs, hS.crossedQ1_inv hs']
    ring
  ·
    have hγs : hS.crossedQ1 s ≠ 0 := fun e => hsZ ((hγ0 hs).1 e)
    have hγs' : hS.crossedQ1 s' ≠ 0 := fun e => hs'Z ((hγ0 hs').1 e)
    obtain ⟨p, hp, hpB, hpA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h
      (Units.mk0 (hS.crossedQ1 s' / hS.crossedQ1 s) (div_ne_zero hγs' hγs))
    set i := hS.torusElt p hp with hi
    have hiI := hS.torusElt_mem_IG p hp
    have hiQ := hS.IG_le_normalizer_Q1 hiI
    have hsH := hS.miyamotoS_le_normalizer_Q1 hs
    have hisS : i⁻¹ * s * i ∈ miyamotoS h L η t Q := by
      have := (mem_normalizer_iff.1 (hS.normalizer_Q1_le_normalizer_miyamotoS (inv_mem hiQ)) s).1
        hs
      rwa [inv_inv] at this
    refine ⟨i⁻¹, fun a ha => ?_, by rwa [inv_inv], ?_⟩
    ·
      rw [inv_inv]
      have hiP : i⁻¹ ∈ normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) :
          Set G) := hS.normalizer_Q1_le_normalizer_P1 (inv_mem hiQ)
      have hit : i * t = t * i := mem_centralizer_singleton_iff.1 (hS.IG_le_C hiI)
      rcases hS.mem_P1_or_of_mem_Q1 ha with haP | htaP
      · have := (mem_normalizer_iff.1 hiP a).1 haP
        rw [inv_inv] at this
        exact mul_mem this (inv_mem haP)
      · have e : i⁻¹ * a * i * a⁻¹ = t * (i⁻¹ * (t * a) * i * (t * a)⁻¹) * t⁻¹ := by
          have hit' : i⁻¹ * t = t * i⁻¹ := by
            calc i⁻¹ * t = i⁻¹ * (t * i) * i⁻¹ := by group
              _ = i⁻¹ * (i * t) * i⁻¹ := by rw [hit]
              _ = t * i⁻¹ := by group
          calc i⁻¹ * a * i * a⁻¹ = (t * t) * i⁻¹ * a * i * a⁻¹ * (t * t)⁻¹ := by
                rw [hS.t_mul_t]; group
            _ = t * (t * i⁻¹) * a * i * a⁻¹ * (t * t)⁻¹ := by group
            _ = t * (i⁻¹ * t) * a * i * a⁻¹ * (t * t)⁻¹ := by rw [← hit']
            _ = t * (i⁻¹ * (t * a) * i * (t * a)⁻¹) * t⁻¹ := by group
        rw [e]
        refine (mem_normalizer_iff.1 htN _).1 (mul_mem ?_ (inv_mem htaP))
        have := (mem_normalizer_iff.1 hiP (t * a)).1 htaP
        rwa [inv_inv] at this
    · rw [inv_inv]
      refine (hγ0 (mul_mem hisS (inv_mem hs'))).1 ?_
      rw [hS.crossedQ1_mul hisS (inv_mem hs'), hS.crossedQ1_inv hs', hi,
        hS.crossedQ1_torus_conj p hp hsH, hpA, Units.val_mk0, div_mul_cancel₀ _ hγs, add_neg_cancel]
  ·
    have hK : 4 < Nat.card K := by
      rw [h.card_eq_sq]
      have := hS.four_le
      nlinarith
    obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
        by_cases hx : x = 0
        · exact Or.inl hx
        · exact Or.inr (hcon x hx)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ] at this
      have h2 := Set.ncard_insert_le (0 : K) {1}
      rw [Set.ncard_singleton] at h2
      omega
    obtain ⟨b, hb0, hb1, hba, hba1⟩ : ∃ b : K, b ≠ 0 ∧ b ≠ 1 ∧ b ≠ a ∧ b ≠ 1 + a := by
      by_contra hcon
      push Not at hcon
      have hsub : (Set.univ : Set K) ⊆ {0, 1, a, 1 + a} := fun x _ => by
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        by_cases hx1 : x = 1
        · exact Or.inr (Or.inl hx1)
        by_cases hxa : x = a
        · exact Or.inr (Or.inr (Or.inl hxa))
        exact Or.inr (Or.inr (Or.inr (hcon x hx0 hx1 hxa)))
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ] at this
      have h4 : ({0, 1, a, 1 + a} : Set K).ncard ≤ 4 := by
        calc ({0, 1, a, 1 + a} : Set K).ncard ≤ ({1, a, 1 + a} : Set K).ncard + 1 :=
              Set.ncard_insert_le _ _
          _ ≤ (({a, 1 + a} : Set K).ncard + 1) + 1 := by
              have := Set.ncard_insert_le (1 : K) {a, 1 + a}
              omega
          _ ≤ ((({1 + a} : Set K).ncard + 1) + 1) + 1 := by
              have := Set.ncard_insert_le a {1 + a}
              omega
          _ = 4 := by rw [Set.ncard_singleton]
      omega
    obtain ⟨x, hx, hxγ⟩ := hS.exists_crossedQ1_eq (1 : K)
    obtain ⟨y, hy, hyγ⟩ := hS.exists_crossedQ1_eq a
    obtain ⟨w, hw, hwγ⟩ := hS.exists_crossedQ1_eq b
    have hne : ∀ {u : G} (hu : u ∈ miyamotoS h L η t Q), hS.crossedQ1 u ≠ 0 →
        u ∉ miyamotoF1G h L η t ⊔ Q := fun hu hne hQ => hne ((hγ0 hu).2 hQ)
    have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    refine ⟨x, hx, y, hy, w, hw, hne hx (by rw [hxγ]; exact one_ne_zero),
      hne hy (by rw [hyγ]; exact ha0), hne (mul_mem hx hy) ?_, hne (mul_mem hx hw) ?_,
      hne (mul_mem hy hw) ?_, hne (mul_mem hx (mul_mem hy hw)) ?_,
      hne hw (by rw [hwγ]; exact hb0)⟩
    · rw [hS.crossedQ1_mul hx hy, hxγ, hyγ]
      intro e
      apply ha1
      linear_combination e - h2
    · rw [hS.crossedQ1_mul hx hw, hxγ, hwγ]
      intro e
      apply hb1
      linear_combination e - h2
    · rw [hS.crossedQ1_mul hy hw, hyγ, hwγ]
      intro e
      apply hba
      linear_combination e - a * h2
    · rw [hS.crossedQ1_mul hx (mul_mem hy hw), hS.crossedQ1_mul hy hw, hxγ, hyγ, hwγ]
      intro e
      apply hba1
      linear_combination e - (1 + a) * h2

theorem odd_card_IG (_hS : Setting h L η t Q T) : Odd (Nat.card (miyamotoIG h L η)) := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η (miyamotoI_le_gramSU h)]
  exact odd_card_miyamotoI h

theorem IG_le_normalizer_miyamotoS (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoS h L η t Q : Set G) :=
  hS.IG_le_normalizer_Q1.trans hS.normalizer_Q1_le_normalizer_miyamotoS

theorem miyamotoS_le_normalizer_P1 (hS : Setting h L η t Q T) :
    miyamotoS h L η t Q ≤
      normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
  hS.miyamotoS_le_normalizer_Q1.trans hS.normalizer_Q1_le_normalizer_P1

theorem P1_le_miyamotoRG (_hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ miyamotoPG h L η ≤ miyamotoRG h L η t Q :=
  le_sup_right

theorem miyamotoRG_le_miyamotoS (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ≤ miyamotoS h L η t Q := by
  refine sup_le ((commutator_le).2 fun a ha s hs => ?_) (hS.P1_le_Q1.trans hS.Q1_le_miyamotoS)
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 (hS.IG_le_normalizer_miyamotoS ha) s).1 hs) (inv_mem hs)

theorem miyamotoS_le_normalizer_RG (hS : Setting h L η t Q T) :
    miyamotoS h L η t Q ≤ normalizer (miyamotoRG h L η t Q : Set G) := by
  obtain ⟨-, hcomm⟩ := hS.miyamotoS_mod_P1
  refine fun s hs => mem_normalizer_fintype fun r hr => ?_
  have hrS := hS.miyamotoRG_le_miyamotoS hr
  have e : s * r * s⁻¹ = (s * r * s⁻¹ * r⁻¹) * r := by group
  rw [SetLike.mem_coe, e]
  exact mul_mem (hS.P1_le_miyamotoRG (hcomm s hs r hrS)) hr

theorem t_not_mem_miyamotoRG (hS : Setting h L η t Q T) : t ∉ miyamotoRG h L η t Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcomm⟩ := hS.miyamotoS_mod_P1
  intro htR
  apply hS.t_not_mem_P1
  refine mem_of_mem_commutator_sup_of_fixed (hS.P1_le_Q1.trans hS.Q1_le_miyamotoS) hcomm
    hS.IG_le_normalizer_miyamotoS
    (hS.IG_le_normalizer_Q1.trans hS.normalizer_Q1_le_normalizer_P1) ?_ htR fun a ha => ?_
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hS.isPGroup_miyamotoS)
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hS.odd_card_IG)
  · rw [mem_centralizer_singleton_iff.1 (hS.IG_le_C ha), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem miyamotoS_eq_sup (hS : Setting h L η t Q T) :
    miyamotoS h L η t Q = miyamotoRG h L η t Q ⊔ zpowers t := by
  have : CharP K 2 := h.charP
  have := h.finite
  refine le_antisymm (fun s hs => ?_) (sup_le hS.miyamotoRG_le_miyamotoS
    (zpowers_le.2 (hS.Q1_le_miyamotoS (mem_sup_right hS.t_mem_Q))))
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (hcon x hx)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at h1
    have h2 := Set.ncard_insert_le (0 : K) {1}
    rw [Set.ncard_singleton] at h2
    have h3 : 4 < Nat.card K := by
      rw [h.card_eq_sq]
      have := hS.four_le
      nlinarith
    omega
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.2 ha1
  obtain ⟨p, hp, -, hpA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h (Units.mk0 a ha0)
  obtain ⟨s₀, hs₀, hs₀γ⟩ := hS.exists_crossedQ1_eq (hS.crossedQ1 s / (a - 1))
  set i := hS.torusElt p hp with hi
  have hiI := hS.torusElt_mem_IG p hp
  have hiS : i⁻¹ * s₀ * i ∈ miyamotoS h L η t Q := by
    have := (mem_normalizer_iff.1 (hS.IG_le_normalizer_miyamotoS (inv_mem hiI)) s₀).1 hs₀
    rwa [inv_inv] at this
  set r := i⁻¹ * s₀ * i * s₀⁻¹ with hr
  have hrR : r ∈ miyamotoRG h L η t Q := by
    refine mem_sup_left ?_
    have := commutator_mem_commutator (inv_mem hiI) hs₀
    rwa [commutatorElement_def, inv_inv] at this
  have hrS := hS.miyamotoRG_le_miyamotoS hrR
  have hrγ : hS.crossedQ1 r = hS.crossedQ1 s := by
    rw [hr, hS.crossedQ1_mul hiS (inv_mem hs₀), hS.crossedQ1_inv hs₀, hi,
      hS.crossedQ1_torus_conj p hp (hS.miyamotoS_le_normalizer_Q1 hs₀), hpA, Units.val_mk0,
      hs₀γ]
    field_simp
    ring
  have hsr : s * r⁻¹ ∈ miyamotoF1G h L η t ⊔ Q := by
    refine (hS.crossedQ1_eq_zero_iff (mul_mem hs (inv_mem hrS))).1 ?_
    rw [hS.crossedQ1_mul hs (inv_mem hrS), hS.crossedQ1_inv hrS, hrγ, add_neg_cancel]
  have hmem := hS.mem_P1_sup_zpowers_of_mem_Q1 hsr
  have hle : (miyamotoF1G h L η t ⊔ miyamotoPG h L η) ⊔ zpowers t ≤
      miyamotoRG h L η t Q ⊔ zpowers t := sup_le_sup_right hS.P1_le_miyamotoRG _
  have e : s = (s * r⁻¹) * r := by group
  rw [e]
  exact mul_mem (hle hmem) (mem_sup_left hrR)

theorem miyamotoRG_inf_Q1 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ (miyamotoF1G h L η t ⊔ Q) = miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.P1_le_miyamotoRG hS.P1_le_Q1)
  obtain ⟨hxR, hxQ⟩ := mem_inf.1 hx
  rcases hS.mem_P1_or_of_mem_Q1 hxQ with h1 | h1
  · exact h1
  · exfalso
    apply hS.t_not_mem_miyamotoRG
    have := mul_mem (hS.P1_le_miyamotoRG h1) (inv_mem hxR)
    rwa [mul_inv_cancel_right] at this

theorem card_miyamotoRG (hS : Setting h L η t Q T) :
    Nat.card (miyamotoRG h L η t Q) = (2 ^ f) ^ 12 := by
  have htN : zpowers t ≤ normalizer (miyamotoRG h L η t Q : Set G) :=
    zpowers_le.2 (hS.miyamotoS_le_normalizer_RG
      (hS.Q1_le_miyamotoS (mem_sup_right hS.t_mem_Q)))
  have h1 := card_sup_mul_card_inf_eq htN
  rw [← hS.miyamotoS_eq_sup] at h1
  have hinf : miyamotoRG h L η t Q ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxR, hxt⟩ := mem_inf.1 hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases hS.zpow_t_eq k with hk | hk
    · rw [hk]; exact one_mem _
    · rw [hk] at hxR
      exact absurd hxR hS.t_not_mem_miyamotoRG
  rw [hinf, card_bot, mul_one, hS.card_miyamotoS, hS.card_Q1, hS.card_zpowers_t] at h1
  have : Nat.card (miyamotoRG h L η t Q) * 2 = (2 ^ f) ^ 12 * 2 := by
    rw [← h1]; ring
  omega

theorem normalizer_Q1_le_normalizer_RG (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ≤
      normalizer (miyamotoRG h L η t Q : Set G) := by
  have : CharP K 2 := h.charP
  obtain ⟨-, hcomm⟩ := hS.miyamotoS_mod_P1
  intro g hg
  obtain ⟨c, hcQC, s, hs, rfl⟩ := hS.exists_mul_miyamotoS_of_mem_normalizer_Q1 hg
  obtain ⟨hcQ, hcC⟩ := mem_inf.1 hcQC
  refine mul_mem ?_ (hS.miyamotoS_le_normalizer_RG hs)
  have hcH : c ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) := by
    have := mul_mem hg (inv_mem (hS.miyamotoS_le_normalizer_Q1 hs))
    rwa [mul_inv_cancel_right] at this
  have hcS := hS.normalizer_Q1_le_normalizer_miyamotoS hcH
  have hcP1 := hS.normalizer_Q1_le_normalizer_P1 hcH
  have hcP : c ∈ normalizer (miyamotoPG h L η : Set G) := by
    rw [← hS.Q_inf_L]
    exact mem_normalizer_inf hcQ (hS.centralizer_le_normalizer hcC)
  refine mem_normalizer_fintype fun r hr => ?_
  rw [SetLike.mem_coe] at hr ⊢
  have key : (miyamotoRG h L η t Q).map (MulAut.conj c).toMonoidHom ≤ miyamotoRG h L η t Q := by
    rw [miyamotoRG, Subgroup.map_sup, Subgroup.map_commutator]
    refine sup_le ((commutator_le).2 fun a ha s' hs' => ?_) ?_
    · obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨s₀, hs₀, rfl⟩ := hs'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hs₀' : c * s₀ * c⁻¹ ∈ miyamotoS h L η t Q := (mem_normalizer_iff.1 hcS s₀).1 hs₀
      have ha₀L : a₀ ∈ L := miyamotoPull_le h L η _ ha₀
      have hca : c * a₀ * c⁻¹ ∈ L ⊓ normalizer (miyamotoPG h L η : Set G) := by
        refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hS.centralizer_le_normalizer hcC) a₀).1 ha₀L,
          mul_mem (mul_mem hcP (hS.IG_le_normalizer_PG ha₀)) (inv_mem hcP)⟩
      rw [normalizer_miyamotoPG h L η] at hca
      obtain ⟨p, hp, a', ha', e⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer' hS.IG_le_normalizer_PG hca
      set s₁ := c * s₀ * c⁻¹ with hs₁
      have hpS : p ∈ miyamotoS h L η t Q :=
        hS.Q1_le_miyamotoS (mem_sup_right (hS.P_le_Q hp))
      have h1 : a' * s₁ * a'⁻¹ * s₁⁻¹ ∈ miyamotoRG h L η t Q := by
        refine mem_sup_left ?_
        have := commutator_mem_commutator ha' hs₀'
        rwa [commutatorElement_def] at this
      have h2 : p * (a' * s₁ * a'⁻¹ * s₁⁻¹) * p⁻¹ ∈ miyamotoRG h L η t Q :=
        (mem_normalizer_iff.1 (hS.miyamotoS_le_normalizer_RG hpS) _).1 h1
      have h3 : p * s₁ * p⁻¹ * s₁⁻¹ ∈ miyamotoRG h L η t Q :=
        hS.P1_le_miyamotoRG (hcomm p hpS s₁ hs₀')
      rw [commutatorElement_def, e]
      have e2 : p * a' * s₁ * (p * a')⁻¹ * s₁⁻¹ =
          (p * (a' * s₁ * a'⁻¹ * s₁⁻¹) * p⁻¹) * (p * s₁ * p⁻¹ * s₁⁻¹) := by group
      rw [e2]
      exact mul_mem h2 h3
    · rintro _ ⟨x, hx, rfl⟩
      exact hS.P1_le_miyamotoRG ((mem_normalizer_iff.1 hcP1 x).1 hx)
  exact key ⟨r, hr, rfl⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
