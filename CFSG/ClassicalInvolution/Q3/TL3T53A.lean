module

public import CFSG.ClassicalInvolution.Q3.TL3T52A
public import CFSG.ClassicalInvolution.Q3.TL3T53
public import CFSG.ClassicalInvolution.Q3.TL3T51

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr CFSG.ClassicalInvolution.Generic

variable {n : ℕ}

theorem perm_eq_one_of_conj_fix' (hn : 5 ≤ n) (w : Wr n)
    (hw : ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool), ∃ b' : Bool,
      conjSub (mkQ n w) (memBar α h b) = memBar α h b') : w.perm = 1 := by
  refine perm_eq_one_of_fix_four hn fun α h => ?_
  obtain ⟨b', hb'⟩ := hw α h true
  obtain ⟨b'', hb''⟩ := exists_conj_memBar_map w α h true
  exact (eq_of_memBar_eq' hn (hb''.symm.trans hb')).symm.symm

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] [Finite G] {P Q : Set (Subgroup G)} {n k : ℕ}
  {I : AEIdent P n} {c : Fin k ↪ Fin n}

theorem SubHyp.label_of_restrict_label' (h : SubHyp I Q c) (hk : 5 ≤ k)
    {L : Subgroup G} (hL : L ∈ Q) {α : Finset (Fin k)} (hα : α.card = 4) {b' : Bool}
    (hr : (L.subgroupOf (pSpan Q)).map (I.restrict hk h).φ = memBar α hα b') :
    ∃ _ : (α.map c).card = 4,
      (L.subgroupOf (pSpan P)).map I.φ = (memAt α hα b').map (subQ c) := by
  obtain ⟨β, hβ', b, hlab⟩ := h.lab L hL
  have hβ : β.card = 4 := by rwa [Finset.card_map] at hβ'
  obtain ⟨b'', hb⟩ := exists_memBar_map_eq c β hβ hβ' b
  have hr' := h.restrict_label_eq hk hL hβ hβ' hlab hb
  have hαβ : β = α := eq_of_memBar_eq' hk (hr'.symm.trans hr)
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

theorem SubHyp.twin_of_restrict' (h : SubHyp I Q c) (hk : 5 ≤ k)
    {α : Finset (Fin k)} (hα : α.card = 4) {L L' : Subgroup G} (hL : L ∈ Q) (hL' : L' ∈ Q)
    (hr : (L.subgroupOf (pSpan Q)).map (I.restrict hk h).φ = memBar α hα true)
    (hr' : (L'.subgroupOf (pSpan Q)).map (I.restrict hk h).φ = memBar α hα false) :
    ∃ (hα' : (α.map c).card = 4) (b : Bool),
      (L.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα' b ∧
      (L'.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα' (!b) := by
  obtain ⟨hα', hl⟩ := h.label_of_restrict_label' hk hL hα hr
  obtain ⟨-, hl'⟩ := h.label_of_restrict_label' hk hL' hα hr'
  obtain ⟨b₁, hb₁⟩ := exists_memBar_map_eq' (hk.trans (le_of_emb c)) c α hα hα' true
  obtain ⟨b₂, hb₂⟩ := exists_memBar_map_eq' (hk.trans (le_of_emb c)) c α hα hα' false
  have hne : b₁ ≠ b₂ := by
    rintro rfl
    exact memAt_map_subQ_ne hk h.miss α hα (hb₁.symm.trans hb₂)
  refine ⟨hα', b₁, hl.trans hb₁.symm, hl'.trans ?_⟩
  rw [← hb₂]
  cases b₁ <;> cases b₂ <;> first | exact absurd rfl hne | rfl

theorem SubHyp.aeCoverHyp_restrict' (h : SubHyp I Q c) (hH : TL4.AECoverHyp I) (hk : 5 ≤ k) :
    TL4.AECoverHyp (I.restrict hk h) where
  ker_two := h.isPGroup_ker_restrict hk hH.ker_two
  card := h.card
  conj_mem := h.conj
  label_inj := by
    intro L hL L' hL' he
    obtain ⟨α, hα, b, hr⟩ := (I.restrict hk h).label L hL
    obtain ⟨hα', hl⟩ := h.label_of_restrict_label' hk hL hα hr
    obtain ⟨-, hl'⟩ := h.label_of_restrict_label' hk hL' hα (he.symm.trans hr)
    exact hH.label_inj L (h.sub hL) L' (h.sub hL') (hl.trans hl'.symm)
  twin_comm := by
    intro α hα L hL L' hL' hr hr'
    obtain ⟨hα', b, hl, hl'⟩ := h.twin_of_restrict' hk hα hL hL' hr hr'
    cases b
    · intro x hx y hy
      exact (hH.twin_comm (α.map c) hα' L' (h.sub hL') L (h.sub hL) hl' hl y hy x hx).symm
    · exact hH.twin_comm (α.map c) hα' L (h.sub hL) L' (h.sub hL') hl hl'
  twin_z := by
    intro α hα L hL L' hL' hr hr' u u' hu hu'
    obtain ⟨hα', b, hl, hl'⟩ := h.twin_of_restrict' hk hα hL hL' hr hr'
    cases b
    · exact (hH.twin_z (α.map c) hα' L' (h.sub hL') L (h.sub hL) hl' hl u' u hu' hu).symm
    · exact hH.twin_z (α.map c) hα' L (h.sub hL) L' (h.sub hL') hl hl' u u' hu hu'

theorem AEIdent.exists_align' {P₁ P₂ Z : Set (Subgroup G)} {N j : ℕ} (hj : 5 ≤ j)
    (hM : Model117At j) (I₁ : AEIdent P₁ N) (I₂ : AEIdent P₂ N)
    (hk₁ : IsPGroup 2 I₁.φ.ker) (hk₂ : IsPGroup 2 I₂.φ.ker)
    {c₁ c₂ : Fin j ↪ Fin N} (h₁ : SubHyp I₁ Z c₁) (h₂ : SubHyp I₂ Z c₂)
    (hsame : ∀ L ∈ Z, ∀ (α : Finset (Fin j)) (hα₁ : (α.map c₁).card = 4) (b : Bool),
      (L.subgroupOf (pSpan P₁)).map I₁.φ = memBar (α.map c₁) hα₁ b →
      ∃ (hα₂ : (α.map c₂).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan P₂)).map I₂.φ = memBar (α.map c₂) hα₂ b')
    (hconj₂ : ∀ L ∈ P₂, ∀ x ∈ pSpan P₂, conjSub x L ∈ P₂)
    (hinj₂ : ∀ L ∈ P₂, ∀ L' ∈ P₂,
      (L.subgroupOf (pSpan P₂)).map I₂.φ = (L'.subgroupOf (pSpan P₂)).map I₂.φ → L = L')
    {s₁ : alternatingGroup (Fin N) →* ↥(pSpan P₁)} {s₂ : alternatingGroup (Fin N) →* ↥(pSpan P₂)}
    (hs₁ : ∀ σ, I₁.φ (s₁ σ) = mkQ N (ofPerm (σ : Equiv.Perm (Fin N))))
    (hs₂ : ∀ σ, I₂.φ (s₂ σ) = mkQ N (ofPerm (σ : Equiv.Perm (Fin N)))) :
    ∃ g : ↥(pSpan P₂), (∃ v : Fin N → ZMod 2, I₂.φ g = mkQ N (ofVec v)) ∧
      ∀ τ : alternatingGroup (Fin j),
        ((s₁ (altExt c₁ τ) : ↥(pSpan P₁)) : G) =
          (g : G) * ((s₂ (altExt c₂ τ) : ↥(pSpan P₂)) : G) * (g : G)⁻¹ := by
  classical
  set J₁ := I₁.restrict hj h₁ with hJ₁
  set J₂ := I₂.restrict hj h₂ with hJ₂
  obtain ⟨x, hx⟩ := J₁.exists_conj_of_model117 hj hM J₂
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk'_surjective (piSub j) x
  have hfix : ∀ (α : Finset (Fin j)) (hα : α.card = 4) (b : Bool), ∃ b' : Bool,
      conjSub (mkQ j w₀) (memBar α hα b) = memBar α hα b' := by
    intro α hα b
    obtain ⟨L, hL, hlab⟩ := J₁.label_surj α hα b
    obtain ⟨β, hβ', b₁, hlab₁⟩ := h₁.lab L hL
    obtain ⟨hβ, b₂, hlab₂⟩ := h₁.restrict_label hj hL hβ' hlab₁
    have hαβ : β = α := eq_of_memBar_eq' hj (hlab₂.symm.trans hlab)
    subst hαβ
    obtain ⟨hβ₂, b₃, hlab₃⟩ := hsame L hL β hβ' b₁ hlab₁
    obtain ⟨hβ₄, b₄, hlab₄⟩ := h₂.restrict_label hj hL hβ₂ hlab₃
    refine ⟨b₄, ?_⟩
    rw [← hlab, ← hlab₄]
    ext m
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, hx y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨J₁.φ y, ⟨y, hy, rfl⟩, (hx y).symm⟩
  have hperm := perm_eq_one_of_conj_fix' hj w₀ hfix
  set v := w₀.vec with hv
  have hw₀ : w₀ = ofVec v := by rw [← ofVec_mul_ofPerm w₀, hperm, ofPerm_one, mul_one]
  obtain ⟨p, hp⟩ := h₂.miss
  have hgm : mkQ N (ofVec (evenExt c₂ p v)) ∈ I₂.φ.range := by
    rw [I₂.range_eq]
    exact ⟨_, ofVec_evenExt_mem c₂ p v, rfl⟩
  obtain ⟨g, hg⟩ := hgm
  refine ⟨g, ⟨_, hg⟩, ?_⟩
  have hgZ : ∀ L ∈ Z, conjSub (g : G) L ∈ Z := by
    intro L hL
    obtain ⟨β, hβ', b₁, hlab₁⟩ := h₂.lab L hL
    have hmem := hconj₂ L (h₂.sub hL) g g.2
    have hlab' : ((conjSub (g : G) L).subgroupOf (pSpan P₂)).map I₂.φ =
        conjSub (mkQ N (ofVec (evenExt c₂ p v))) (memBar (β.map c₂) hβ' b₁) := by
      rw [TL4.AECov.map_conjSub_eq I₂ L g, hg, hlab₁]
    rcases TL4.AECov.conjSub_memBar_of_perm_eq_one (w := ofVec (evenExt c₂ p v)) rfl
      (β.map c₂) hβ' b₁ with h1 | h1
    · obtain ⟨L', hL', hlabL'⟩ := h₂.surj β hβ' true
      rw [hinj₂ _ hmem L' (h₂.sub hL') (by rw [hlab', h1, hlabL'])]
      exact hL'
    · obtain ⟨L', hL', hlabL'⟩ := h₂.surj β hβ' false
      rw [hinj₂ _ hmem L' (h₂.sub hL') (by rw [hlab', h1, hlabL'])]
      exact hL'
  have hconjZ : ∀ (y : G) (hy : y ∈ pSpan Z),
      J₁.φ ⟨(g : G) * y * (g : G)⁻¹, conj_mem_pSpan_of_conj hgZ hy⟩ = J₂.φ ⟨y, hy⟩ := by
    intro y hy
    set y' : ↥(pSpan Z) := ⟨(g : G) * y * (g : G)⁻¹, conj_mem_pSpan_of_conj hgZ hy⟩ with hy'
    have hpre : h₂.pre y' = ofVec v * h₂.pre ⟨y, hy⟩ * (ofVec v)⁻¹ := by
      apply subQ_injective c₂ h₂.miss
      rw [AEIdent.subQ_pre h₂, subQ_apply, ← conj_ofVec_evenExt c₂ hp, map_mul, map_mul,
        map_inv, ← subQ_apply, AEIdent.subQ_pre h₂]
      have e : (⟨(y' : G), h₂.span_le y'.2⟩ : ↥(pSpan P₂)) =
          g * ⟨y, h₂.span_le hy⟩ * g⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hg]
    have h2 : J₂.φ y' = mkQ j (ofVec v) * J₂.φ ⟨y, hy⟩ * (mkQ j (ofVec v))⁻¹ := by
      rw [hJ₂, AEIdent.restrict_apply, AEIdent.restrict_apply, hpre, map_mul, map_mul, map_inv]
    have h3 := hx y'
    rw [h2] at h3
    have hxv : (QuotientGroup.mk' (piSub j)) w₀ = mkQ j (ofVec v) := by rw [hw₀]
    rw [hxv] at h3
    exact (mul_left_cancel (mul_right_cancel h3)).symm
  have hmem₁ : ∀ τ : alternatingGroup (Fin j),
      ((s₁ (altExt c₁ τ) : ↥(pSpan P₁)) : G) ∈ pSpan Z :=
    I₁.section_mem_restrict hj hk₁ h₁ hs₁
  have hmem₂ : ∀ τ : alternatingGroup (Fin j),
      (g : G) * ((s₂ (altExt c₂ τ) : ↥(pSpan P₂)) : G) * (g : G)⁻¹ ∈ pSpan Z :=
    fun τ => conj_mem_pSpan_of_conj hgZ (I₂.section_mem_restrict hj hk₂ h₂ hs₂ τ)
  have hJt₁ : ∀ τ, J₁.φ ⟨_, hmem₁ τ⟩ = mkQ j (ofPerm (τ : Equiv.Perm (Fin j))) := by
    intro τ
    rw [hJ₁, AEIdent.restrict_apply]
    exact congrArg (mkQ j) (I₁.pre_section h₁ hs₁ τ (hmem₁ τ))
  have hJt₂ : ∀ τ, J₁.φ ⟨_, hmem₂ τ⟩ = mkQ j (ofPerm (τ : Equiv.Perm (Fin j))) := by
    intro τ
    have hy := I₂.section_mem_restrict hj hk₂ h₂ hs₂ τ
    rw [hconjZ _ hy, hJ₂, AEIdent.restrict_apply]
    exact congrArg (mkQ j) (I₂.pre_section h₂ hs₂ τ hy)
  set T₁ : alternatingGroup (Fin j) →* G := (pSpan P₁).subtype.comp (s₁.comp (altExt c₁))
    with hT₁
  set T₂ : alternatingGroup (Fin j) →* G :=
    (MulAut.conj (g : G)).toMonoidHom.comp ((pSpan P₂).subtype.comp (s₂.comp (altExt c₂)))
    with hT₂
  have hT₁a : ∀ τ, T₁ τ = ((s₁ (altExt c₁ τ) : ↥(pSpan P₁)) : G) := fun τ => rfl
  have hT₂a : ∀ τ, T₂ τ = (g : G) * ((s₂ (altExt c₂ τ) : ↥(pSpan P₂)) : G) * (g : G)⁻¹ :=
    fun τ => rfl
  have hTT : T₁ = T₂ := by
    refine MonoidHom.eq_of_eqOn_dense (closure_range_carmichaelCycle (by omega : 3 ≤ j)) ?_
    rintro _ ⟨i, rfl⟩
    have hc₁ : ((s₁ (altExt c₁ (carmichaelCycle i)) : ↥(pSpan P₁)) : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, carmichaelCycle_pow_three, map_one, map_one,
        Subgroup.coe_one]
    have hc₂ : ((s₂ (altExt c₂ (carmichaelCycle i)) : ↥(pSpan P₂)) : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, carmichaelCycle_pow_three, map_one, map_one,
        Subgroup.coe_one]
    have h3₁ : (⟨_, hmem₁ (carmichaelCycle i)⟩ : ↥(pSpan Z)) ^ 3 ^ 1 = 1 := by
      apply Subtype.ext
      simpa using hc₁
    have h3₂ : (⟨_, hmem₂ (carmichaelCycle i)⟩ : ↥(pSpan Z)) ^ 3 ^ 1 = 1 := by
      apply Subtype.ext
      have : ((g : G) * ((s₂ (altExt c₂ (carmichaelCycle i)) : ↥(pSpan P₂)) : G) *
          (g : G)⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hc₂, mul_one, mul_inv_cancel]
      simpa using this
    have he := J₁.eq_of_map_eq_of_pow (h₁.isPGroup_ker_restrict hj hk₁) h3₁ h3₂
      ((hJt₁ _).trans (hJt₂ _).symm)
    rw [hT₁a, hT₂a]
    exact congrArg Subtype.val he
  intro τ
  rw [← hT₁a, ← hT₂a, hTT]

end CFSG.ClassicalInvolution.Q3.TC.Thin
