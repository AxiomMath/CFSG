module

public import CFSG.ClassicalInvolution.Q3.TL3T53
public import CFSG.ClassicalInvolution.Q3.TL3T55
public import CFSG.ClassicalInvolution.Q3.TL3T59

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {k n : ℕ}

theorem embWVec_pairVec (ι : Fin k ↪ Fin n) (a c : Fin k) :
    embWVec ι (TL4.pairVec a c) = TL4.pairVec (ι a) (ι c) := by
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨l, rfl⟩ := hx
    rw [embWVec_apply, TL4.pairVec_apply, TL4.pairVec_apply]
    simp only [ι.injective.eq_iff]
  · rw [embWVec_of_not_mem ι _ hx, TL4.pairVec_apply]
    have h1 : x ≠ ι a := fun h => hx ⟨a, h.symm⟩
    have h2 : x ≠ ι c := fun h => hx ⟨c, h.symm⟩
    simp [h1, h2]

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.ncard_over (I : AEIdent P n) (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (Γ : Finset (Fin n)) : (I.over Γ).ncard = Γ.card.choose 4 * 2 := by
  classical
  set S : Finset (Finset (Fin n) × Bool) := Γ.powersetCard 4 ×ˢ Finset.univ with hS
  let f : Finset (Fin n) × Bool → Subgroup G := fun p =>
    if h : p.1.card = 4 then Classical.choose (I.label_surj p.1 h p.2) else ⊥
  have hf : ∀ p ∈ S, ∃ h : p.1.card = 4, f p ∈ P ∧
      ((f p).subgroupOf (pSpan P)).map I.φ = memBar p.1 h p.2 := by
    intro p hp
    have h4 : p.1.card = 4 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    refine ⟨h4, ?_⟩
    simp only [f, h4, ↓reduceDIte]
    exact Classical.choose_spec (I.label_surj p.1 h4 p.2)
  have himage : I.over Γ = f '' (S : Set (Finset (Fin n) × Bool)) := by
    ext L
    constructor
    · rintro ⟨hL, α, h, b, hαΓ, hlab⟩
      have hp : (α, b) ∈ S :=
        Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨hαΓ, h⟩, Finset.mem_univ _⟩
      obtain ⟨h4', hfP, hflab⟩ := hf _ hp
      exact ⟨(α, b), hp, hinj _ hfP L hL (hflab.trans hlab.symm)⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨h4, hfP, hflab⟩ := hf p hp
      exact ⟨hfP, p.1, h4, p.2,
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).1, hflab⟩
  have hinjOn : Set.InjOn f (S : Set (Finset (Fin n) × Bool)) := by
    intro p hp q hq hpq
    obtain ⟨hp4, -, hplab⟩ := hf p hp
    obtain ⟨hq4, -, hqlab⟩ := hf q hq
    have e : memBar p.1 hp4 p.2 = memBar q.1 hq4 q.2 := by rw [← hplab, ← hqlab, hpq]
    have h1 : p.1 = q.1 := eq_of_memBar_eq hn hn8 e
    have h2 : p.2 = q.2 := by
      obtain ⟨α, b⟩ := p
      obtain ⟨β, c⟩ := q
      simp only at h1 e ⊢
      subst h1
      cases b <;> cases c
      · rfl
      · exact absurd e.symm (memBar_true_ne_false hn α hp4)
      · exact absurd e (memBar_true_ne_false hn α hp4)
      · rfl
    exact Prod.ext h1 h2
  rw [himage, hinjOn.ncard_image, Set.ncard_coe_finset, hS, Finset.card_product,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_bool]

theorem AEIdent.ncard_over_le (I : AEIdent P n)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (Γ : Finset (Fin n)) : (I.over Γ).ncard ≤ Γ.card.choose 4 * 2 := by
  classical
  set S : Finset (Finset (Fin n) × Bool) := Γ.powersetCard 4 ×ˢ Finset.univ with hS
  let f : Finset (Fin n) × Bool → Subgroup G := fun p =>
    if h : p.1.card = 4 then Classical.choose (I.label_surj p.1 h p.2) else ⊥
  have hf : ∀ p ∈ S, ∃ h : p.1.card = 4, f p ∈ P ∧
      ((f p).subgroupOf (pSpan P)).map I.φ = memBar p.1 h p.2 := by
    intro p hp
    have h4 : p.1.card = 4 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    refine ⟨h4, ?_⟩
    simp only [f, h4, ↓reduceDIte]
    exact Classical.choose_spec (I.label_surj p.1 h4 p.2)
  have hsub : I.over Γ ⊆ f '' (S : Set (Finset (Fin n) × Bool)) := by
    rintro L ⟨hL, α, h, b, hαΓ, hlab⟩
    have hp : (α, b) ∈ S :=
      Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨hαΓ, h⟩, Finset.mem_univ _⟩
    obtain ⟨h4', hfP, hflab⟩ := hf _ hp
    exact ⟨(α, b), hp, hinj _ hfP L hL (hflab.trans hlab.symm)⟩
  calc (I.over Γ).ncard ≤ (f '' (S : Set (Finset (Fin n) × Bool))).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (S : Set (Finset (Fin n) × Bool)).ncard := Set.ncard_image_le
    _ = Γ.card.choose 4 * 2 := by
        rw [Set.ncard_coe_finset, hS, Finset.card_product, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_bool]

theorem AEIdent.over_univ (I : AEIdent P n) : I.over Finset.univ = P := by
  ext L
  constructor
  · exact fun h => h.1
  · intro hL
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨hL, α, h, b, Finset.subset_univ α, hlab⟩

theorem choose_four_lt {a b : ℕ} (hab : a < b) (hb : 4 ≤ b) : a.choose 4 < b.choose 4 := by
  rcases Nat.lt_or_ge a 3 with ha | ha
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.choose_pos hb
  · calc a.choose 4 < a.choose 3 + a.choose 4 := by
          have := Nat.choose_pos (show 3 ≤ a from ha)
          omega
      _ = (a + 1).choose 4 := (Nat.choose_succ_succ a 3).symm
      _ ≤ b.choose 4 := Nat.choose_le_choose 4 hab

theorem eq_of_choose_four_eq {a b : ℕ} (ha : 4 ≤ a) (hb : 4 ≤ b)
    (h : a.choose 4 = b.choose 4) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (choose_four_lt hab hb).ne
  · exact hab
  · exact absurd h (choose_four_lt hab ha).ne'

theorem AEIdent.comm_pairVec_iff [Finite G] (I : AEIdent P n) (hn : 5 ≤ n)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8) (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {w : ↥(pSpan P)} {a c : Fin n} (hac : a ≠ c)
    (hw : I.φ w = mkQ n (ofVec (TL4.pairVec a c))) {L : Subgroup G} (hL : L ∈ P)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h b) :
    (∀ l ∈ L, (w : G) * l = l * w) ↔ a ∉ α ∧ c ∉ α := by
  constructor
  · intro hc
    have himg : ∀ x ∈ memBar α h b,
        x * mkQ n (ofVec (TL4.pairVec a c)) = mkQ n (ofVec (TL4.pairVec a c)) * x := by
      intro x hx
      rw [← hlab] at hx
      obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL hx
      rw [← hw, ← map_mul, ← map_mul]
      exact congrArg I.φ (Subtype.ext (hc l hl).symm)
    have hfix : conjSub (mkQ n (ofVec (TL4.pairVec a c))) (memBar α h b) = memBar α h b :=
      conjSub_eq_of_comm fun x hx => (himg x hx).symm
    by_contra hne
    rw [not_and_or, not_not, not_not] at hne
    by_cases ha : a ∈ α
    · by_cases hc' : c ∈ α
      · exact not_comm_memBar_pairVec hn h b ha hc' hac himg
      · have hodd := TL4.AECov.conjSub_memBar_of_odd (w := ofVec (TL4.pairVec a c)) rfl α h b
          (TL4.AECov.sum_pairVec_of_mem ha hc')
        rw [hfix] at hodd
        cases b
        · exact memBar_true_ne_false hn α h hodd.symm
        · exact memBar_true_ne_false hn α h hodd
    · have hc' : c ∈ α := hne.resolve_left ha
      have hodd := TL4.AECov.conjSub_memBar_of_odd (w := ofVec (TL4.pairVec a c)) rfl α h b
        (by rw [show TL4.pairVec a c = TL4.pairVec c a from TL4.pairVec_comm a c]
            exact TL4.AECov.sum_pairVec_of_mem hc' ha)
      rw [hfix] at hodd
      cases b
      · exact memBar_true_ne_false hn α h hodd.symm
      · exact memBar_true_ne_false hn α h hodd
  · rintro ⟨ha, hc⟩
    refine I.comm_member hn h8 hconj hinj hL w fun y hy => ?_
    rw [hlab] at hy
    rw [hw]
    exact (vbar_pairVec_comm_memBar (hγ := h) (c := b) ha hc y hy).symm

theorem AEIdent.twin_z_of_trans (I : AEIdent P n) (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    {J₀ J₀' : Subgroup G} (hJ₀ : J₀ ∈ P) (hJ₀' : J₀' ∈ P) {δ : Finset (Fin n)}
    {hδ : δ.card = 4} {c : Bool}
    (hlab₀ : (J₀.subgroupOf (pSpan P)).map I.φ = memBar δ hδ c)
    (hlab₀' : (J₀'.subgroupOf (pSpan P)).map I.φ = memBar δ hδ (!c))
    (hz₀ : ∀ u u' : G, IsUniqueInvolution J₀ u → IsUniqueInvolution J₀' u' → u = u') :
    ∀ (α : Finset (Fin n)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = memBar α h true →
      (L'.subgroupOf (pSpan P)).map I.φ = memBar α h false →
      ∀ u u' : G, IsUniqueInvolution L u → IsUniqueInvolution L' u' → u = u' := by
  intro α h L hL L' hL' hlab hlab' u u' hu hu'
  obtain ⟨x, hx, hxL⟩ := htrans J₀ hJ₀ L hL
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (piSub n) (I.φ ⟨x, hx⟩)
  have hc1 := TL4.AECov.map_conjSub_eq I J₀ ⟨x, hx⟩
  have hc2 := TL4.AECov.map_conjSub_eq I J₀' ⟨x, hx⟩
  rw [hxL, hlab₀, ← hw] at hc1
  rw [hlab₀', ← hw] at hc2
  obtain ⟨c₁, hc₁⟩ := exists_conj_memBar_map w δ hδ c
  obtain ⟨c₂, hc₂⟩ := exists_conj_memBar_map w δ hδ (!c)
  rw [hc₁] at hc1
  rw [hc₂] at hc2
  have hδα : δ.map w.perm.toEmbedding = α := eq_of_memBar_eq hn hn8 (hc1.symm.trans hlab)
  have hne : c₂ ≠ c₁ := by
    intro e
    rw [e] at hc₂
    have := conjSub_injective (mkQ n w) (hc₁.trans hc₂.symm)
    cases c
    · exact memBar_true_ne_false hn δ hδ this.symm
    · exact memBar_true_ne_false hn δ hδ this
  have hc₁t : c₁ = true := by
    by_contra hf
    have : c₁ = false := by cases c₁ <;> simp_all
    subst this
    subst hδα
    exact memBar_true_ne_false hn _ h (hlab.symm.trans hc1)
  have hc₂f : c₂ = false := by cases c₂ <;> simp_all
  subst hc₁t hc₂f
  have hxJ' : conjSub x J₀' = L' := by
    refine hinj _ (hconj J₀' hJ₀' x hx) L' hL' ?_
    rw [hc2, hlab']
    subst hδα
    rfl
  have hJ₀L : conjSub x⁻¹ L = J₀ := by rw [← hxL, conjSub_inv_conjSub]
  have hJ₀L' : conjSub x⁻¹ L' = J₀' := by rw [← hxJ', conjSub_inv_conjSub]
  have hv := hu.conj x⁻¹
  rw [hJ₀L] at hv
  have hv' := hu'.conj x⁻¹
  rw [hJ₀L'] at hv'
  have e := hz₀ _ _ hv hv'
  calc u = x * (x⁻¹ * u * x⁻¹⁻¹) * x⁻¹ := by group
    _ = x * (x⁻¹ * u' * x⁻¹⁻¹) * x⁻¹ := by rw [e]
    _ = u' := by group

end CFSG.ClassicalInvolution.Q3.TC.Thin
