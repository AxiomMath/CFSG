module

public import CFSG.ClassicalInvolution.Q3.TL3T52
public import CFSG.ClassicalInvolution.Q3.TL4AECoverM

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n k : ℕ}

theorem exists_map_eq_of_subset (c : Fin k ↪ Fin n) {α : Finset (Fin n)}
    (hα : ∀ x ∈ α, x ∈ Set.range c) : ∃ α' : Finset (Fin k), α'.map c = α := by
  classical
  refine ⟨Finset.univ.filter (fun i => c i ∈ α), ?_⟩
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    obtain ⟨i, rfl⟩ := hα x hx
    exact ⟨i, hx, rfl⟩

@[expose] noncomputable def finEmb (Γ : Finset (Fin n)) : Fin Γ.card ↪ Fin n :=
  (Γ.orderEmbOfFin rfl).toEmbedding

theorem range_finEmb (Γ : Finset (Fin n)) : Set.range (finEmb Γ) = (Γ : Set (Fin n)) := by
  rw [← Finset.range_orderEmbOfFin Γ rfl]
  rfl

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section FixOut

variable {n : ℕ}

@[expose] noncomputable def fixOut (Γ : Finset (Fin n)) : Subgroup (AEQ n) where
  carrier := {x | ∀ p, p ∉ Γ → permQ n x p = p}
  one_mem' := fun _ _ => by rw [map_one]; rfl
  mul_mem' := fun {x y} hx hy p hp => by
    rw [map_mul, Equiv.Perm.mul_apply, hy p hp, hx p hp]
  inv_mem' := fun {x} hx p hp => by
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
    exact (hx p hp).symm

theorem permQ_mem_of_mem_fixOut {Γ : Finset (Fin n)} {x : AEQ n} (hx : x ∈ fixOut Γ) {p : Fin n}
    (hp : p ∈ Γ) : permQ n x p ∈ Γ := by
  by_contra h
  have h1 := hx _ h
  exact h (by rw [(permQ n x).injective h1]; exact hp)

theorem memBar_le_fixOut {Γ α : Finset (Fin n)} (hαΓ : α ⊆ Γ) (h : α.card = 4) (b : Bool) :
    memBar α h b ≤ fixOut Γ := by
  rintro _ ⟨a, ha, rfl⟩ p hp
  have hpα : p ∉ Set.range (emb α h) := by
    rw [range_emb]
    exact fun h' => hp (hαΓ h')
  exact ((supportedOn_of_mem_memAt ha) p hpα).2

end FixOut

variable {G : Type} [Group G] {P Q : Set (Subgroup G)} {n k : ℕ}

@[expose] def AEIdent.over (I : AEIdent P n) (Γ : Finset (Fin n)) : Set (Subgroup G) :=
  {L | L ∈ P ∧ ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool), α ⊆ Γ ∧
    (L.subgroupOf (pSpan P)).map I.φ = memBar α h b}

theorem AEIdent.over_subset (I : AEIdent P n) (Γ : Finset (Fin n)) : I.over Γ ⊆ P :=
  fun _ h => h.1

theorem AEIdent.pSpan_over_le (I : AEIdent P n) (Γ : Finset (Fin n)) :
    pSpan (I.over Γ) ≤ pSpan P :=
  pSpan_le fun _ hL => le_pSpan hL.1

theorem AEIdent.map_mem_fixOut (I : AEIdent P n) (Γ : Finset (Fin n)) {x : G}
    (hx : x ∈ pSpan (I.over Γ)) : I.φ ⟨x, I.pSpan_over_le Γ hx⟩ ∈ fixOut Γ := by
  have hle : pSpan (I.over Γ) ≤ ((fixOut Γ).comap I.φ).map (pSpan P).subtype := by
    refine pSpan_le fun L hL l hl => ⟨⟨l, le_pSpan hL.1 hl⟩, ?_, rfl⟩
    obtain ⟨α, h, b, hαΓ, hlab⟩ := hL.2
    have hm : I.φ ⟨l, le_pSpan hL.1 hl⟩ ∈ memBar α h b := by
      rw [← hlab]
      exact I.mem_map hL.1 hl
    exact memBar_le_fixOut hαΓ h b hm
  obtain ⟨y, hy, hyx⟩ := hle hx
  rw [show (⟨x, I.pSpan_over_le Γ hx⟩ : ↥(pSpan P)) = y from Subtype.ext hyx.symm]
  exact hy

theorem AEIdent.conjSub_mem_over (I : AEIdent P n)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (Γ : Finset (Fin n)) {L : Subgroup G}
    (hL : L ∈ I.over Γ) {x : G} (hx : x ∈ pSpan (I.over Γ)) : conjSub x L ∈ I.over Γ := by
  have hxP := I.pSpan_over_le Γ hx
  refine ⟨hconj L hL.1 x hxP, ?_⟩
  obtain ⟨α, h, b, hαΓ, hlab⟩ := hL.2
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (piSub n) (I.φ ⟨x, hxP⟩)
  obtain ⟨b', hb'⟩ := exists_conj_memBar_map w α h b
  have hfix := I.map_mem_fixOut Γ hx
  rw [← hw] at hfix
  refine ⟨α.map w.perm.toEmbedding, by rw [Finset.card_map]; exact h, b', ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact permQ_mem_of_mem_fixOut hfix (hαΓ hp)
  · rw [TL4.AECov.map_conjSub_eq I L ⟨x, hxP⟩, hlab, ← hw]
    exact hb'

theorem AEIdent.subHyp_over (I : AEIdent P n) (Γ : Finset (Fin n)) {p : Fin n} (hp : p ∉ Γ)
    (hcard : ∀ L ∈ P, Nat.card ↥L = 8) (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L') :
    SubHyp I (I.over Γ) (finEmb Γ) where
  sub := I.over_subset Γ
  miss := ⟨p, by rw [range_finEmb]; exact_mod_cast hp⟩
  card := fun L hL => hcard L hL.1
  conj := fun L hL x hx => I.conjSub_mem_over hconj Γ hL hx
  inj := fun L hL L' hL' h => hinj L hL.1 L' hL'.1 h
  lab := by
    intro L hL
    obtain ⟨α, h, b, hαΓ, hlab⟩ := hL.2
    obtain ⟨α', rfl⟩ := exists_map_eq_of_subset (finEmb Γ) (α := α) fun x hx => by
      rw [range_finEmb]
      exact_mod_cast hαΓ hx
    exact ⟨α', h, b, hlab⟩
  surj := by
    intro α' hα' b
    obtain ⟨L, hL, hlab⟩ := I.label_surj (α'.map (finEmb Γ)) hα' b
    refine ⟨L, ⟨hL, α'.map (finEmb Γ), hα', b, ?_, hlab⟩, hlab⟩
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have : finEmb Γ i ∈ Set.range (finEmb Γ) := ⟨i, rfl⟩
    rw [range_finEmb] at this
    exact_mod_cast this

section Restrict

variable [Finite G] {I : AEIdent P n} {c : Fin k ↪ Fin n}

theorem SubHyp.restrict_label_eq (h : SubHyp I Q c) (hk : 5 ≤ k) {L : Subgroup G} (hL : L ∈ Q)
    {α : Finset (Fin k)} (hα : α.card = 4) (hα' : (α.map c).card = 4) {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα' b)
    (hb : memBar (α.map c) hα' b = (memAt α hα b').map (subQ c)) :
    (L.subgroupOf (pSpan Q)).map (I.restrict hk h).φ = memBar α hα b' := by
  rw [show (I.restrict hk h).φ = (mkQ k).comp h.pre from rfl, ← Subgroup.map_map,
    h.map_pre hL hα hα' hlab hb]
  rfl

theorem SubHyp.label_of_restrict_label (h : SubHyp I Q c) (hk : 5 ≤ k) (hk8 : k ≠ 8)
    {L : Subgroup G} (hL : L ∈ Q) {α : Finset (Fin k)} (hα : α.card = 4) {b' : Bool}
    (hr : (L.subgroupOf (pSpan Q)).map (I.restrict hk h).φ = memBar α hα b') :
    ∃ _ : (α.map c).card = 4,
      (L.subgroupOf (pSpan P)).map I.φ = (memAt α hα b').map (subQ c) := by
  obtain ⟨β, hβ', b, hlab⟩ := h.lab L hL
  have hβ : β.card = 4 := by rwa [Finset.card_map] at hβ'
  obtain ⟨b'', hb⟩ := exists_memBar_map_eq c β hβ hβ' b
  have hr' := h.restrict_label_eq hk hL hβ hβ' hlab hb
  have hαβ : β = α := eq_of_memBar_eq hk hk8 (hr'.symm.trans hr)
  subst hαβ
  have hbb : b'' = b' := by
    have e := hr'.symm.trans hr
    cases b'' <;> cases b'
    · rfl
    · exact absurd e.symm (memBar_true_ne_false hk β hβ)
    · exact absurd e (memBar_true_ne_false hk β hβ)
    · rfl
  subst hbb
  exact ⟨hβ', hlab.trans hb⟩

theorem memAt_map_subQ_ne (hk : 5 ≤ k) (hc : ∃ x, x ∉ Set.range c) (α : Finset (Fin k))
    (hα : α.card = 4) : (memAt α hα true).map (subQ c) ≠ (memAt α hα false).map (subQ c) := by
  intro e
  have e' := Subgroup.map_injective (subQ_injective c hc) e
  apply memBar_true_ne_false hk α hα
  show (memAt α hα true).map (mkQ k) = (memAt α hα false).map (mkQ k)
  rw [e']

theorem SubHyp.twin_of_restrict (h : SubHyp I Q c) (hk : 5 ≤ k) (hk8 : k ≠ 8)
    {α : Finset (Fin k)} (hα : α.card = 4) {L L' : Subgroup G} (hL : L ∈ Q) (hL' : L' ∈ Q)
    (hr : (L.subgroupOf (pSpan Q)).map (I.restrict hk h).φ = memBar α hα true)
    (hr' : (L'.subgroupOf (pSpan Q)).map (I.restrict hk h).φ = memBar α hα false) :
    ∃ (hα' : (α.map c).card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα' b ∧
      (L'.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα' (!b) := by
  obtain ⟨hα', hl⟩ := h.label_of_restrict_label hk hk8 hL hα hr
  obtain ⟨-, hl'⟩ := h.label_of_restrict_label hk hk8 hL' hα hr'
  obtain ⟨b₁, hb₁⟩ := exists_memBar_map_eq' (hk.trans (le_of_emb c)) c α hα hα' true
  obtain ⟨b₂, hb₂⟩ := exists_memBar_map_eq' (hk.trans (le_of_emb c)) c α hα hα' false
  have hne : b₁ ≠ b₂ := by
    rintro rfl
    exact memAt_map_subQ_ne hk h.miss α hα (hb₁.symm.trans hb₂)
  refine ⟨hα', b₁, hl.trans hb₁.symm, hl'.trans ?_⟩
  rw [← hb₂]
  cases b₁ <;> cases b₂ <;> first | exact absurd rfl hne | rfl

theorem SubHyp.aeCoverHyp_restrict (h : SubHyp I Q c) (hH : TL4.AECoverHyp I) (hk : 5 ≤ k)
    (hk8 : k ≠ 8) : TL4.AECoverHyp (I.restrict hk h) where
  ker_two := h.isPGroup_ker_restrict hk hH.ker_two
  card := h.card
  conj_mem := h.conj
  label_inj := by
    intro L hL L' hL' he
    obtain ⟨α, hα, b, hr⟩ := (I.restrict hk h).label L hL
    obtain ⟨hα', hl⟩ := h.label_of_restrict_label hk hk8 hL hα hr
    obtain ⟨-, hl'⟩ := h.label_of_restrict_label hk hk8 hL' hα (he.symm.trans hr)
    exact hH.label_inj L (h.sub hL) L' (h.sub hL') (hl.trans hl'.symm)
  twin_comm := by
    intro α hα L hL L' hL' hr hr'
    obtain ⟨hα', b, hl, hl'⟩ := h.twin_of_restrict hk hk8 hα hL hL' hr hr'
    cases b
    · intro x hx y hy
      exact (hH.twin_comm (α.map c) hα' L' (h.sub hL') L (h.sub hL) hl' hl y hy x hx).symm
    · exact hH.twin_comm (α.map c) hα' L (h.sub hL) L' (h.sub hL') hl hl'
  twin_z := by
    intro α hα L hL L' hL' hr hr' u u' hu hu'
    obtain ⟨hα', b, hl, hl'⟩ := h.twin_of_restrict hk hk8 hα hL hL' hr hr'
    cases b
    · exact (hH.twin_z (α.map c) hα' L' (h.sub hL') L (h.sub hL) hl' hl u' u hu' hu).symm
    · exact hH.twin_z (α.map c) hα' L (h.sub hL) L' (h.sub hL') hl hl' u u' hu hu'

theorem SubHyp.restrict_injective (h : SubHyp I Q c) (hH : TL4.AECoverHyp I) (hk : 5 ≤ k)
    (hodd : Odd k) : Function.Injective (I.restrict hk h).φ := by
  have hk8 : k ≠ 8 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hker := TL4.aeCoverOddKer_proved G Q k (I.restrict hk h) hk hodd
    (h.aeCoverHyp_restrict hH hk hk8)
  exact (MonoidHom.ker_eq_bot_iff _).mp hker

theorem SubHyp.eq_of_map_eq (h : SubHyp I Q c) (hH : TL4.AECoverHyp I) (hk : 5 ≤ k)
    (hodd : Odd k) {x y : G} (hx : x ∈ pSpan Q) (hy : y ∈ pSpan Q)
    (hxy : I.φ ⟨x, h.span_le hx⟩ = I.φ ⟨y, h.span_le hy⟩) : x = y := by
  have hpre : h.pre ⟨x, hx⟩ = h.pre ⟨y, hy⟩ := by
    apply subQ_injective c h.miss
    rw [AEIdent.subQ_pre h, AEIdent.subQ_pre h]
    exact hxy
  have he : (I.restrict hk h).φ ⟨x, hx⟩ = (I.restrict hk h).φ ⟨y, hy⟩ := by
    rw [AEIdent.restrict_apply, AEIdent.restrict_apply, hpre]
  exact congrArg Subtype.val (h.restrict_injective hH hk hodd he)

end Restrict

theorem AEIdent.eq_of_map_eq_over [Finite G] (I : AEIdent P n) (hH : TL4.AECoverHyp I)
    {Γ : Finset (Fin n)} (hΓ5 : 5 ≤ Γ.card) (hΓodd : Odd Γ.card) {p : Fin n} (hp : p ∉ Γ)
    {x y : G} (hx : x ∈ pSpan (I.over Γ)) (hy : y ∈ pSpan (I.over Γ))
    (hxy : I.φ ⟨x, I.pSpan_over_le Γ hx⟩ = I.φ ⟨y, I.pSpan_over_le Γ hy⟩) : x = y :=
  (I.subHyp_over Γ hp hH.card hH.conj_mem hH.label_inj).eq_of_map_eq hH hΓ5 hΓodd hx hy hxy

end CFSG.ClassicalInvolution.Q3.TC.Thin
