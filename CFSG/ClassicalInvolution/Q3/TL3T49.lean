module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverB
public import CFSG.ClassicalInvolution.Q3.TL3T45

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr Certificates.AE117

variable {k n : ℕ}

@[expose] noncomputable def subQ (c : Fin k ↪ Fin n) : Wr k →* AEQ n := (mkQ n).comp (embW c)

theorem subQ_apply (c : Fin k ↪ Fin n) (w : Wr k) : subQ c w = mkQ n (embW c w) := rfl

theorem subQ_injective (c : Fin k ↪ Fin n) (hc : ∃ x, x ∉ Set.range c) :
    Function.Injective (subQ c) := by
  obtain ⟨x₀, hx₀⟩ := hc
  rw [injective_iff_map_eq_one]
  intro w hw
  rcases (mem_piSub.mp ((QuotientGroup.eq_one_iff _).mp hw)) with h | h
  · exact embW_injective c (by rw [h, map_one])
  · exfalso
    have := congrArg (fun w : Wr n => w.vec x₀) h
    simp only [embW_vec, embWVec_of_not_mem c _ hx₀] at this
    exact absurd this (by show (0 : ZMod 2) ≠ 1; decide)

theorem mem_memAt_iff (α : Finset (Fin k)) (hα : α.card = 4) (b : Bool) (w : Wr k) :
    w ∈ memAt α hα b ↔ w ∈ memLC (emb α hα 0) (emb α hα 1) (emb α hα 2) (emb α hα 3) b := by
  rw [memLC_eq', List.mem_map]
  have key : w ∈ memAt α hα b ↔ ∃ a ∈ (bif b then kQ else kQStar), embed (emb α hα) a = w := by
    cases b <;> rfl
  rw [key]
  exact exists_congr fun a => and_congr_left fun _ => (mem_localList_iff b a).symm

theorem memAt_le_aeSub (α : Finset (Fin k)) (hα : α.card = 4) (b : Bool) :
    memAt α hα b ≤ aeSub k := by
  cases b
  · exact memKStar_le_aeSub _
  · exact memK_le_aeSub _

theorem exists_memBar_map_eq (c : Fin k ↪ Fin n) (α : Finset (Fin k)) (hα : α.card = 4)
    (hα' : (α.map c).card = 4) (b : Bool) :
    ∃ b' : Bool, memBar (α.map c) hα' b = (memAt α hα b').map (subQ c) := by
  classical
  have hr : Set.range ((emb α hα).trans c) = ((α.map c : Finset (Fin n)) : Set (Fin n)) := by
    rw [Finset.coe_map, ← range_emb α hα, ← Set.range_comp]
    rfl
  obtain ⟨b', hb'⟩ := exists_memBar_eq_memLC ((emb α hα).trans c) (α.map c) hα' hr b
  refine ⟨b', ?_⟩
  ext x
  rw [hb' x]
  simp only [Function.Embedding.trans_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_memLC_embW (c := c) (ι := emb α hα) ha
    exact ⟨w, (mem_memAt_iff α hα b' w).mpr hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨embW c w, embW_mem_memLC c (emb α hα) b' ((mem_memAt_iff α hα b' w).mp hw), rfl⟩

theorem exists_memBar_map_eq' (hn : 5 ≤ n) (c : Fin k ↪ Fin n) (α : Finset (Fin k))
    (hα : α.card = 4) (hα' : (α.map c).card = 4) (b' : Bool) :
    ∃ b : Bool, memBar (α.map c) hα' b = (memAt α hα b').map (subQ c) := by
  obtain ⟨b₁, h₁⟩ := exists_memBar_map_eq c α hα hα' true
  obtain ⟨b₂, h₂⟩ := exists_memBar_map_eq c α hα hα' false
  have hne : b₁ ≠ b₂ := by
    rintro rfl
    exact memBar_true_ne_false hn _ hα' (h₁.trans h₂.symm)
  cases b₁ <;> cases b₂ <;> cases b'
  all_goals first | exact absurd rfl hne | exact ⟨true, h₁⟩ | exact ⟨false, h₂⟩

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] {P Q : Set (Subgroup G)} {n k : ℕ}

structure SubHyp (I : AEIdent P n) (Q : Set (Subgroup G)) (c : Fin k ↪ Fin n) : Prop where
  sub : Q ⊆ P
  miss : ∃ x, x ∉ Set.range c
  card : ∀ L ∈ Q, Nat.card ↥L = 8
  conj : ∀ L ∈ Q, ∀ x ∈ pSpan Q, conjSub x L ∈ Q
  inj : ∀ L ∈ Q, ∀ L' ∈ Q,
    (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L'
  lab : ∀ L ∈ Q, ∃ (α : Finset (Fin k)) (hα : (α.map c).card = 4) (b : Bool),
    (L.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα b
  surj : ∀ (α : Finset (Fin k)) (hα : (α.map c).card = 4) (b : Bool), ∃ L ∈ Q,
    (L.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα b

namespace SubHyp

variable {I : AEIdent P n} {c : Fin k ↪ Fin n}

theorem span_le (h : SubHyp I Q c) : pSpan Q ≤ pSpan P := pSpan_le fun _ hL => le_pSpan (h.sub hL)

@[expose] noncomputable def θ (h : SubHyp I Q c) : ↥(pSpan Q) →* AEQ n :=
  I.φ.comp (Subgroup.inclusion h.span_le)

theorem θ_apply (h : SubHyp I Q c) (x : ↥(pSpan Q)) :
    h.θ x = I.φ ⟨(x : G), h.span_le x.2⟩ := rfl

theorem map_θ (h : SubHyp I Q c) {L : Subgroup G} (hL : L ∈ Q) :
    (L.subgroupOf (pSpan Q)).map h.θ = (L.subgroupOf (pSpan P)).map I.φ := by
  ext m
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, h.span_le y.2⟩, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, le_pSpan hL hy⟩, hy, rfl⟩

theorem θ_mem (h : SubHyp I Q c) (x : ↥(pSpan Q)) : h.θ x ∈ (aeSub k).map (subQ c) := by
  have hle : pSpan Q ≤ (((aeSub k).map (subQ c)).comap h.θ).map (pSpan Q).subtype := by
    refine pSpan_le fun L hL l hl => ⟨⟨l, le_pSpan hL hl⟩, ?_, rfl⟩
    show I.φ ⟨l, h.span_le (le_pSpan hL hl)⟩ ∈ (aeSub k).map (subQ c)
    obtain ⟨α, hα, b, hlab⟩ := h.lab L hL
    have hm : I.φ ⟨l, h.span_le (le_pSpan hL hl)⟩ ∈ memBar (α.map c) hα b := by
      rw [← hlab]
      exact ⟨⟨l, _⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    obtain ⟨b', hb'⟩ := exists_memBar_map_eq c α (by rwa [Finset.card_map] at hα) hα b
    rw [hb'] at hm
    obtain ⟨w, hw, hwe⟩ := hm
    exact ⟨w, memAt_le_aeSub _ _ _ hw, hwe⟩
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rw [show y = x from Subtype.ext hyx] at hy
  exact hy

@[expose] noncomputable def pre (h : SubHyp I Q c) : ↥(pSpan Q) →* Wr k :=
  (MonoidHom.ofInjective (subQ_injective c h.miss)).symm.toMonoidHom.comp
    (h.θ.codRestrict (subQ c).range fun x => by
      obtain ⟨w, -, hw⟩ := h.θ_mem x
      exact ⟨w, hw⟩)

theorem subQ_pre (h : SubHyp I Q c) (x : ↥(pSpan Q)) : subQ c (h.pre x) = h.θ x := by
  rw [pre, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.apply_ofInjective_symm]
  rfl

theorem subQ_comp_pre (h : SubHyp I Q c) : (subQ c).comp h.pre = h.θ :=
  MonoidHom.ext h.subQ_pre

theorem pre_mem (h : SubHyp I Q c) (x : ↥(pSpan Q)) : h.pre x ∈ aeSub k := by
  obtain ⟨w, hw, hwe⟩ := h.θ_mem x
  rw [show h.pre x = w from subQ_injective c h.miss (by rw [h.subQ_pre, hwe])]
  exact hw

theorem map_pre (h : SubHyp I Q c) {L : Subgroup G} (hL : L ∈ Q) {α : Finset (Fin k)}
    (hα : α.card = 4) (hα' : (α.map c).card = 4) {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα' b)
    (hb : memBar (α.map c) hα' b = (memAt α hα b').map (subQ c)) :
    (L.subgroupOf (pSpan Q)).map h.pre = memAt α hα b' := by
  apply Subgroup.map_injective (subQ_injective c h.miss)
  rw [Subgroup.map_map, h.subQ_comp_pre, h.map_θ hL, hlab, hb]

end SubHyp

omit [Group G] in
theorem le_of_emb (c : Fin k ↪ Fin n) : k ≤ n := by
  simpa using Fintype.card_le_of_embedding c

theorem conjSub_eq_of_comm {H : Type*} [Group H] {g : H} {S : Subgroup H}
    (hg : ∀ s ∈ S, g * s = s * g) : conjSub g S = S := by
  ext s
  rw [mem_conjSub_iff]
  constructor
  · intro hs
    have e := hg _ hs
    have e' : s = g⁻¹ * s * g :=
      calc s = g * (g⁻¹ * s * g) * g⁻¹ := by group
        _ = g⁻¹ * s * g * g * g⁻¹ := by rw [e]
        _ = g⁻¹ * s * g := by group
    rw [e']
    exact hs
  · intro hs
    have e := hg s hs
    have e' : g⁻¹ * s * g = s :=
      calc g⁻¹ * s * g = g⁻¹ * (g * s) := by rw [mul_assoc, ← e]
        _ = s := by group
    rw [e']
    exact hs

section Restrict

variable [Finite G] {I : AEIdent P n} {c : Fin k ↪ Fin n}

theorem SubHyp.mem_center_of_comm (h : SubHyp I Q c) (hn : 5 ≤ n) (x : ↥(pSpan Q))
    (hx : ∀ y, h.θ x * h.θ y = h.θ y * h.θ x) : x ∈ Subgroup.center ↥(pSpan Q) := by
  have hnorm : ∀ L ∈ Q, conjSub (x : G) L = L := by
    intro L hL
    refine h.inj _ (h.conj L hL x x.2) L hL ?_
    rw [TL4.AECov.map_conjSub_eq I L ⟨x, h.span_le x.2⟩]
    refine conjSub_eq_of_comm fun s hs => ?_
    rw [← h.map_θ hL] at hs
    obtain ⟨y, -, rfl⟩ := hs
    exact hx y
  have hcent : ∀ L ∈ Q, ∀ l ∈ L, l * (x : G) = (x : G) * l := by
    intro L hL l hl
    obtain ⟨α, hα, b, hlab⟩ := h.lab L hL
    have hxl : (x : G) * l * (x : G)⁻¹ ∈ L := by
      rw [← hnorm L hL]
      exact conj_mem_conjSub hl
    have hcm : (x : G) * l * (x : G)⁻¹ * l⁻¹ ∈ L := L.mul_mem hxl (L.inv_mem hl)
    have hlQ : l ∈ pSpan Q := le_pSpan hL hl
    have he : I.φ ⟨(x : G) * l * (x : G)⁻¹ * l⁻¹, le_pSpan (h.sub hL) hcm⟩ =
        I.φ ⟨1, le_pSpan (h.sub hL) L.one_mem⟩ := by
      have e1 : (⟨(x : G) * l * (x : G)⁻¹ * l⁻¹, le_pSpan (h.sub hL) hcm⟩ : ↥(pSpan P)) =
          ⟨x, h.span_le x.2⟩ * ⟨l, h.span_le hlQ⟩ * ⟨x, h.span_le x.2⟩⁻¹ *
            ⟨l, h.span_le hlQ⟩⁻¹ := rfl
      have e2 : (⟨1, le_pSpan (h.sub hL) L.one_mem⟩ : ↥(pSpan P)) = 1 := rfl
      rw [e1, e2, map_one, map_mul, map_mul, map_mul, map_inv, map_inv]
      have := hx ⟨l, hlQ⟩
      rw [θ_apply, θ_apply] at this
      rw [this]
      group
    have h1 := phi_injOn I.φ hn (h.sub hL) (h.card L hL) hlab hcm L.one_mem he
    have h2 : (x : G) * l = l * (x : G) := by
      calc (x : G) * l = ((x : G) * l * (x : G)⁻¹ * l⁻¹) * l * x := by group
        _ = l * (x : G) := by rw [h1, one_mul]
    exact h2.symm
  have hle : pSpan Q ≤ Subgroup.centralizer {(x : G)} :=
    pSpan_le fun L hL l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hcent L hL l hl)
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle y.2))

@[expose] noncomputable def AEIdent.restrict (I : AEIdent P n) (hk : 5 ≤ k) (h : SubHyp I Q c) :
    AEIdent Q k where
  φ := (mkQ k).comp h.pre
  range_eq := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨h.pre x, h.pre_mem x, rfl⟩
    · refine (aeModel_le_memSpan hk).trans ?_
      rw [memSpan, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hz
      obtain ⟨α, hα, b', hz⟩ := hz
      have hα' : (α.map c).card = 4 := by rw [Finset.card_map]; exact hα
      obtain ⟨b, hb⟩ := exists_memBar_map_eq' (hk.trans (le_of_emb c)) c α hα hα' b'
      obtain ⟨L, hL, hlab⟩ := h.surj α hα' b
      obtain ⟨w, hw, rfl⟩ := hz
      rw [← h.map_pre hL hα hα' hlab hb] at hw
      obtain ⟨y, -, rfl⟩ := hw
      exact ⟨y, rfl⟩
  ker_le := fun x hx => h.mem_center_of_comm (hk.trans (le_of_emb c)) x fun y => by
    have hpx : h.pre x ∈ piSub k := (QuotientGroup.eq_one_iff _).mp hx
    have hc : h.pre x * h.pre y = h.pre y * h.pre x := by
      rcases mem_piSub.mp hpx with h1 | h1
      · rw [h1, one_mul, mul_one]
      · rw [h1]
        exact allOnes_comm _
    rw [← h.subQ_pre, ← h.subQ_pre, ← (subQ c).map_mul, hc, (subQ c).map_mul]
  label := by
    intro L hL
    obtain ⟨α, hα', b, hlab⟩ := h.lab L hL
    have hα : α.card = 4 := by rwa [Finset.card_map] at hα'
    obtain ⟨b', hb⟩ := exists_memBar_map_eq c α hα hα' b
    refine ⟨α, hα, b', ?_⟩
    rw [← Subgroup.map_map, h.map_pre hL hα hα' hlab hb]
    rfl
  label_surj := by
    intro α hα b'
    have hα' : (α.map c).card = 4 := by rw [Finset.card_map]; exact hα
    obtain ⟨b, hb⟩ := exists_memBar_map_eq' (hk.trans (le_of_emb c)) c α hα hα' b'
    obtain ⟨L, hL, hlab⟩ := h.surj α hα' b
    refine ⟨L, hL, ?_⟩
    rw [← Subgroup.map_map, h.map_pre hL hα hα' hlab hb]
    rfl

theorem AEIdent.restrict_apply (I : AEIdent P n) (hk : 5 ≤ k) (h : SubHyp I Q c)
    (x : ↥(pSpan Q)) : (I.restrict hk h).φ x = mkQ k (h.pre x) := rfl

omit [Finite G] in
theorem AEIdent.subQ_pre (h : SubHyp I Q c) (x : ↥(pSpan Q)) :
    subQ c (h.pre x) = I.φ ⟨(x : G), h.span_le x.2⟩ :=
  h.subQ_pre x

end Restrict

end CFSG.ClassicalInvolution.Q3.TC.Thin
