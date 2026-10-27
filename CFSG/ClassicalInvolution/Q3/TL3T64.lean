module

public import CFSG.ClassicalInvolution.Q3.TL3T53A
public import CFSG.ClassicalInvolution.Q3.TL3T60

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] {P Q : Set (Subgroup G)} {n k : ℕ}

theorem subHyp_of_labels (I : AEIdent Q k) (I' : AEIdent P n) (hQP : Q ⊆ P) (hk : 5 ≤ k)
    (c : Fin k ↪ Fin n) (hc : ∃ x, x ∉ Set.range c) (h8 : ∀ L ∈ Q, Nat.card ↥L = 8)
    (hconj : ∀ L ∈ Q, ∀ x ∈ pSpan Q, conjSub x L ∈ Q)
    (hinj' : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I'.φ = (L'.subgroupOf (pSpan P)).map I'.φ → L = L')
    (hlab : ∀ L ∈ Q, ∀ (α : Finset (Fin k)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Q)).map I.φ = memBar α hα b →
      ∃ (hα' : (α.map c).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan P)).map I'.φ = memBar (α.map c) hα' b') :
    SubHyp I' Q c where
  sub := hQP
  miss := hc
  card := h8
  conj := hconj
  inj := fun L hL L' hL' h => hinj' L (hQP hL) L' (hQP hL') h
  lab := fun L hL => by
    obtain ⟨α, hα, b, hl⟩ := I.label L hL
    obtain ⟨hα', b', hl'⟩ := hlab L hL α hα b hl
    exact ⟨α, hα', b', hl'⟩
  surj := by
    intro α hα' b
    have hα : α.card = 4 := by rwa [Finset.card_map] at hα'
    obtain ⟨L₁, hL₁, hl₁⟩ := I.label_surj α hα true
    obtain ⟨L₂, hL₂, hl₂⟩ := I.label_surj α hα false
    obtain ⟨h₁, b₁, hm₁⟩ := hlab L₁ hL₁ α hα true hl₁
    obtain ⟨h₂, b₂, hm₂⟩ := hlab L₂ hL₂ α hα false hl₂
    have hne : b₁ ≠ b₂ := by
      rintro rfl
      have e := hinj' L₁ (hQP hL₁) L₂ (hQP hL₂) (hm₁.trans hm₂.symm)
      subst e
      exact memBar_true_ne_false hk α hα (hl₁.symm.trans hl₂)
    by_cases hb : b₁ = b
    · subst hb
      exact ⟨L₁, hL₁, hm₁⟩
    · have : b₂ = b := by
        cases b <;> cases b₁ <;> cases b₂ <;> first | rfl | exact absurd rfl hb | exact absurd rfl hne
      subst this
      exact ⟨L₂, hL₂, hm₂⟩

section Vec

variable [Finite G]

theorem SubHyp.exists_vec (hM : Model117At k) (hk : 5 ≤ k) (I : AEIdent Q k)
    {I' : AEIdent P n} {c : Fin k ↪ Fin n} (h : SubHyp I' Q c)
    (hlab : ∀ L ∈ Q, ∀ (α : Finset (Fin k)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Q)).map I.φ = memBar α hα b →
      ∃ (hα' : (α.map c).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan P)).map I'.φ = memBar (α.map c) hα' b') :
    ∃ v : Fin k → ZMod 2, ∀ y : ↥(pSpan Q),
      (I'.restrict hk h).φ y = mkQ k (ofVec v) * I.φ y * (mkQ k (ofVec v))⁻¹ := by
  obtain ⟨x, hx⟩ := I.exists_conj_of_model117 hk hM (I'.restrict hk h)
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk'_surjective (piSub k) x
  have hfix : ∀ (α : Finset (Fin k)) (hα : α.card = 4) (b : Bool), ∃ b' : Bool,
      conjSub (mkQ k w₀) (memBar α hα b) = memBar α hα b' := by
    intro α hα b
    obtain ⟨L, hL, hl⟩ := I.label_surj α hα b
    obtain ⟨hα', b₁, hl₁⟩ := hlab L hL α hα b hl
    obtain ⟨hα₂, b₂, hl₂⟩ := h.restrict_label hk hL hα' hl₁
    refine ⟨b₂, ?_⟩
    rw [← hl, ← hl₂]
    ext m
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, hx y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨I.φ y, ⟨y, hy, rfl⟩, (hx y).symm⟩
  have hperm := perm_eq_one_of_conj_fix' hk w₀ hfix
  set v := w₀.vec with hv
  have hw₀ : w₀ = ofVec v := by rw [← ofVec_mul_ofPerm w₀, hperm, ofPerm_one, mul_one]
  have hxv : (QuotientGroup.mk' (piSub k)) w₀ = mkQ k (ofVec v) := by rw [hw₀]
  exact ⟨v, fun y => by rw [hx y, hxv]⟩

end Vec

variable [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

structure PairChart (Ω : Set (Subgroup G)) (K J : Subgroup G) {n : ℕ}
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) where
  t : G
  u : G
  Ks : Subgroup G
  Js : Subgroup G
  IY : AEIdent (centMembers Ω u) (n + 2)
  ι : Fin n ↪ Fin (n + 2)
  γ : Finset (Fin n)
  hγ : γ.card = 4
  b : Bool
  a : Fin n
  c : Fin n
  a' : Fin n
  c' : Fin n
  k₀ : G
  k₀' : G
  ht : conjSub t K = J
  ht' : conjSub t J = K
  hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K
  hKsK : Ks ≠ K
  hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J
  hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z
  hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x
  hJs : Js ∈ orbOf (TC.nbrAdj Ω) K J
  htKs : conjSub t Ks = Js
  htKs' : conjSub t⁻¹ Ks = Js
  hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ b
  hlabJs : (Js.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar γ hγ (!b)
  hk₀ : k₀ ∈ K
  hk₀' : k₀' ∈ Ks
  hu : u = k₀ * k₀'
  hu1 : u ≠ 1
  hXu : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x
  hKu : ¬ ∀ k ∈ K, k * u = u * k
  hKsu : ¬ ∀ k ∈ Ks, k * u = u * k
  hac : a ≠ c
  ha : a ∈ γ
  hc : c ∈ γ
  hac' : a' ≠ c'
  ha' : a' ∈ γ
  hc' : c' ∈ γ
  hw : t * u * t⁻¹ ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)
  hwI : I.φ ⟨t * u * t⁻¹, hw⟩ = mkQ n (ofVec (TL4.pairVec a c))
  hw' : t⁻¹ * u * t ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)
  hwI' : I.φ ⟨t⁻¹ * u * t, hw'⟩ = mkQ n (ofVec (TL4.pairVec a' c'))
  hHY : TL4.AECoverHyp IY
  hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u
  hsub : SubHyp IY (orbOf (TC.nbrAdj Ω) K J) ι
  hlabι : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, ∀ (α : Finset (Fin n)) (hα : α.card = 4) (e : Bool),
    (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar α hα e →
    ∃ (hα' : (α.map ι).card = 4) (e' : Bool),
      (L.subgroupOf (pSpan (centMembers Ω u))).map IY.φ = memBar (α.map ι) hα' e'
  hpair : IY.φ ⟨t * u * t⁻¹, hsub.span_le hw⟩ =
    mkQ (n + 2) (ofVec (TL4.pairVec (ι a) (ι c)))
  hpair' : IY.φ ⟨t⁻¹ * u * t, hsub.span_le hw'⟩ =
    mkQ (n + 2) (ofVec (TL4.pairVec (ι a') (ι c')))

end CFSG.ClassicalInvolution.Q3.TC.Thin
