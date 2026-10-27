module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

section Pc

variable {G : Type*} [Group G]

@[expose] def pcG : List G → ℕ → G
  | [], _ => 1
  | x :: l, m => (if m % 2 = 1 then x else 1) * pcG l (m / 2)

@[expose] def PcRel : List G → Prop
  | [] => True
  | x :: l => (∃ r, x * x = pcG l r) ∧ (∀ y ∈ l, ∃ c, y * x = x * pcG l c) ∧ PcRel l

@[expose] def PcSep : List G → Prop
  | [] => True
  | x :: l => x ∉ closure {a | a ∈ l} ∧ PcSep l

theorem pcG_zero : ∀ l : List G, pcG l 0 = 1
  | [] => rfl
  | _ :: l => by rw [pcG, ite_eq_right (by decide), Nat.zero_div, pcG_zero l, one_mul]

theorem pcG_mem : ∀ (l : List G) (m : ℕ), pcG l m ∈ closure {a | a ∈ l}
  | [], _ => one_mem _
  | x :: l, m => by
    refine mul_mem ?_ (closure_mono (fun a ha => List.mem_cons_of_mem x ha) (pcG_mem l (m / 2)))
    split_ifs
    · exact subset_closure (List.mem_cons_self ..)
    · exact one_mem _

theorem exists_pcG_of_pcRel :
    ∀ {l : List G}, PcRel l → ∀ g ∈ closure {a | a ∈ l}, ∃ m < 2 ^ l.length, pcG l m = g
  | [], _, g, hg => by
    have : g = 1 := by
      have he : {a : G | a ∈ ([] : List G)} = ∅ := by simp
      rwa [he, Subgroup.closure_empty, mem_bot] at hg
    exact ⟨0, by simp, by rw [this]; rfl⟩
  | x :: l, ⟨⟨r, hr⟩, hc, hl⟩, g, hg => by
    set H := closure {a | a ∈ l}
    have hconj : ∀ h ∈ H, x⁻¹ * h * x ∈ H := by
      intro h hh
      induction hh using closure_induction with
      | mem y hy =>
        obtain ⟨c, hyc⟩ := hc y hy
        rw [mul_assoc, hyc, ← mul_assoc, inv_mul_cancel, one_mul]
        exact pcG_mem l c
      | one => rw [mul_one, inv_mul_cancel]; exact one_mem _
      | mul a b _ _ ha hb =>
        have := mul_mem ha hb
        rwa [show x⁻¹ * a * x * (x⁻¹ * b * x) = x⁻¹ * (a * b) * x by group] at this
      | inv a _ ha =>
        have := inv_mem ha
        rwa [show (x⁻¹ * a * x)⁻¹ = x⁻¹ * a⁻¹ * x by group] at this
    have hx2 : x * x ∈ H := hr ▸ pcG_mem l r
    have key : ∀ g ∈ closure {a | a ∈ x :: l}, g ∈ H ∨ x⁻¹ * g ∈ H := by
      intro g hg
      induction hg using closure_induction with
      | mem y hy =>
        rcases List.mem_cons.1 hy with rfl | hy
        · right
          rw [inv_mul_cancel]
          exact one_mem _
        · exact Or.inl (subset_closure hy)
      | one => exact Or.inl (one_mem _)
      | mul a b _ _ ha hb =>
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (mul_mem ha hb)
        · right
          have := mul_mem (hconj a ha) hb
          rwa [show x⁻¹ * a * x * (x⁻¹ * b) = x⁻¹ * (a * b) by group] at this
        · right
          have := mul_mem ha hb
          rwa [show x⁻¹ * a * b = x⁻¹ * (a * b) by group] at this
        · left
          have := mul_mem (mul_mem hx2 (hconj _ ha)) hb
          rwa [show x * x * (x⁻¹ * (x⁻¹ * a) * x) * (x⁻¹ * b) = a * b by group] at this
      | inv a _ ha =>
        rcases ha with ha | ha
        · exact Or.inl (inv_mem ha)
        · right
          have := mul_mem (hconj _ (inv_mem ha)) (inv_mem hx2)
          rwa [show x⁻¹ * (x⁻¹ * a)⁻¹ * x * (x * x)⁻¹ = x⁻¹ * a⁻¹ by group] at this
    rw [List.length_cons, pow_succ]
    rcases key g hg with hg' | hg'
    · obtain ⟨m, hm, rfl⟩ := exists_pcG_of_pcRel hl g hg'
      refine ⟨2 * m, by omega, ?_⟩
      rw [pcG, ite_eq_right (by omega), show 2 * m / 2 = m by omega, one_mul]
    · obtain ⟨m, hm, he⟩ := exists_pcG_of_pcRel hl _ hg'
      refine ⟨2 * m + 1, by omega, ?_⟩
      rw [pcG, ite_eq_left (by omega), show (2 * m + 1) / 2 = m by omega, he, mul_inv_cancel_left]

theorem pcG_injOn : ∀ {l : List G}, PcSep l → ∀ m₁ < 2 ^ l.length, ∀ m₂ < 2 ^ l.length,
    pcG l m₁ = pcG l m₂ → m₁ = m₂
  | [], _, m₁, h₁, m₂, h₂, _ => by simp at h₁ h₂; omega
  | x :: l, ⟨hx, hl⟩, m₁, h₁, m₂, h₂, he => by
    rw [List.length_cons, pow_succ] at h₁ h₂
    have ih := pcG_injOn hl (m₁ / 2) (by omega) (m₂ / 2) (by omega)
    have hm1 := pcG_mem l (m₁ / 2)
    have hm2 := pcG_mem l (m₂ / 2)
    rw [pcG, pcG] at he
    rcases Nat.mod_two_eq_zero_or_one m₁ with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one m₂ with b | b
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), one_mul, one_mul] at he
      have := ih he
      omega
    · rw [ite_eq_right (by omega), ite_eq_left b, one_mul] at he
      refine absurd ?_ hx
      rw [show x = pcG l (m₁ / 2) * (pcG l (m₂ / 2))⁻¹ by rw [he]; group]
      exact mul_mem hm1 (inv_mem hm2)
    · rw [ite_eq_left a, ite_eq_right (by omega), one_mul] at he
      refine absurd ?_ hx
      rw [show x = pcG l (m₂ / 2) * (pcG l (m₁ / 2))⁻¹ by rw [← he]; group]
      exact mul_mem hm2 (inv_mem hm1)
    · rw [ite_eq_left a, ite_eq_left b] at he
      have := ih (mul_left_cancel he)
      omega

theorem card_closure_of_pc {l : List G} (hr : PcRel l) (hs : PcSep l) :
    Nat.card (closure {a | a ∈ l}) = 2 ^ l.length := by
  let f : Fin (2 ^ l.length) → closure {a | a ∈ l} := fun m => ⟨pcG l m, pcG_mem l m⟩
  have hf : Function.Bijective f := by
    refine ⟨fun m₁ m₂ h => Fin.ext (pcG_injOn hs m₁ m₁.2 m₂ m₂.2 (congrArg Subtype.val h)),
      fun g => ?_⟩
    obtain ⟨m, hm, he⟩ := exists_pcG_of_pcRel hr g g.2
    exact ⟨⟨m, hm⟩, Subtype.ext he⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

end Pc

theorem not_mem_closure_of_block {n : ℕ} {l : List (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    (B : Fin n → Prop) [DecidablePred B] (hl : ∀ y ∈ l, ∀ p, B p → B (y p)) (q : Fin n) (hq : B q)
    (hxq : ¬ B (x q)) : x ∉ closure {a | a ∈ l} := by
  have hiff : ∀ y ∈ l, ∀ p, B (y p) ↔ B p := by
    intro y hy p
    refine ⟨fun h => ?_, hl y hy p⟩
    set F := Finset.univ.filter B
    have hsub : F.image y ⊆ F := by
      intro z hz
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hz
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hp' ⊢
      exact hl y hy p' hp'
    have heq : F.image y = F := Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injective _ y.injective])
    have hyp : y p ∈ F.image y := by
      rw [heq]
      simpa [F] using h
    obtain ⟨p', hp', hpp⟩ := Finset.mem_image.1 hyp
    rw [y.injective hpp] at hp'
    simpa [F] using hp'
  let K : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {g | ∀ p, B (g p) ↔ B p}
      mul_mem' := fun {a b} ha hb p => by
        rw [Equiv.Perm.mul_apply, ha (b p), hb p]
      one_mem' := fun p => by rw [Equiv.Perm.one_apply]
      inv_mem' := fun {g} hg p => by
        have := hg (g⁻¹ p)
        rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
        exact this.symm }
  have hle : closure {a | a ∈ l} ≤ K := (closure_le K).2 fun y hy => hiff y hy
  intro hx
  exact hxq ((hle hx q).2 hq)

variable {n : ℕ}

@[expose] def pcA (n : ℕ) : List (Array ℕ) → ℕ → Array ℕ
  | [], _ => idA n
  | x :: l, m => if m % 2 = 1 then compA n x (pcA n l (m / 2)) else pcA n l (m / 2)

@[expose] def pcOK (n : ℕ) : List (Array ℕ) → List ℕ → List (List ℕ) → List (ℕ × ℕ) → Bool
  | [], _, _, _ => true
  | x :: l, r :: rs, c :: cs, b :: bs =>
    validA n x && eqA n (compA n x x) (pcA n l r) && c.length == l.length &&
      (l.zip c).all (fun yc => eqA n (compA n yc.1 x) (compA n x (pcA n l yc.2))) &&
      decide (b.2 < n) && b.1.testBit b.2 && !(b.1.testBit x[b.2]!) &&
      l.all (fun y => (List.range n).all fun p => !(b.1.testBit p) || b.1.testBit y[p]!) &&
      pcOK n l rs cs bs
  | _, _, _, _ => false

@[expose] def invRest (n : ℕ) (xs : List (Array ℕ)) : ℕ → List ℕ → List ℕ → Option (List ℕ)
  | _, im, [] => some im
  | m, im, x :: wt =>
    if im.head? = some m then invRest n xs (m + 1) im.tail wt
    else if m = 0 ∨ (x < n ∧ (pcA n xs m)[(pcA n xs m)[x]!]! ≠ x) then invRest n xs (m + 1) im wt
    else none

@[expose] def invOK (n : ℕ) (xs : List (Array ℕ)) (us : Array (Array ℕ)) (im wt : List ℕ) :
    Bool :=
  im.length == us.size && (us.toList.zip im).all (fun ua => eqA n (pcA n xs ua.2) ua.1) &&
    wt.length == 2 ^ xs.length && invRest n xs 0 im wt == some []

theorem invRest_spec {n : ℕ} {xs : List (Array ℕ)} : ∀ {m : ℕ} {im wt : List ℕ} {r : List ℕ},
    invRest n xs m im wt = some r → ∀ i < wt.length, m + i ∈ im ∨ m + i = 0 ∨
      (wt[i]! < n ∧ (pcA n xs (m + i))[(pcA n xs (m + i))[wt[i]!]!]! ≠ wt[i]!)
  | _, _, [], _, _, i, hi => absurd hi (by simp)
  | m, im, x :: wt, r, h, i, hi => by
    simp only [invRest] at h
    split_ifs at h with h1 h2
    · rcases i with _ | i
      · left
        rw [Nat.add_zero]
        exact List.mem_of_head? h1
      · have := invRest_spec h i (by simpa using hi)
        rw [show m + 1 + i = m + (i + 1) by omega] at this
        rcases this with h3 | h3
        · exact Or.inl (List.mem_of_mem_tail h3)
        · right
          simpa using h3
    · rcases i with _ | i
      · rcases h2 with h2 | h2
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (by simpa using h2))
      · have := invRest_spec h i (by simpa using hi)
        rw [show m + 1 + i = m + (i + 1) by omega] at this
        simpa using this

@[expose] def conjTabOK (n : ℕ) (xs : List (Array ℕ)) (cm : List ℕ) (cs ci : Array (Array ℕ)) :
    Bool :=
  cm.length == cs.size && ci.size == cs.size &&
    (cs.toList.zip cm).all (fun sm => eqA n (pcA n xs sm.2) sm.1) &&
    (ci.toList.zip cs.toList).all fun p => eqA n (compA n p.1 p.2) (idA n)

@[expose] def rootOKC (n : ℕ) (nodes : Array Node) (cN : Array ArrCert) (cs ci : Array (Array ℕ))
    (u : Array ℕ) (r : ℕ × ℕ) : Bool :=
  decide (r.1 < nodes.size) && decide (r.2 < cs.size) &&
    (allLt nodes[r.1]!.basis.size fun l =>
      eqA n nodes[r.1]!.basis[l]! (compA n cs[r.2]! (compA n u ci[r.2]!)) ||
        eqA n nodes[r.1]!.basis[l]! (idA n)) &&
    memA n cN[r.1]! (compA n cs[r.2]! (compA n u ci[r.2]!))

@[expose] def entOK (n : ℕ) (nodes : Array Node) (cN : Array ArrCert) (cs ci : Array (Array ℕ))
    (i : ℕ) (u : Array ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  if e.1 = 0 then
    decide (e.2.1 < nodes[i]!.basis.size) && decide (e.2.2 < n) &&
      !(u[(nodes[i]!.basis[e.2.1]!)[e.2.2]!]! == (nodes[i]!.basis[e.2.1]!)[u[e.2.2]!]!)
  else if e.1 = 1 then memA n cN[i]! u
  else
    decide (e.2.1 < nodes.size) && decide (e.2.2 < cs.size) &&
      cN[e.2.1]!.pts.size == 2 * cN[i]!.pts.size &&
      (allLt nodes[i]!.basis.size fun l =>
        memA n cN[e.2.1]! (compA n cs[e.2.2]! (compA n nodes[i]!.basis[l]! ci[e.2.2]!))) &&
      memA n cN[e.2.1]! (compA n cs[e.2.2]! (compA n u ci[e.2.2]!))

structure ConjData where
  xs : List (Array ℕ)
  rs : List ℕ
  cjs : List (List ℕ)
  bs : List (ℕ × ℕ)
  us : Array (Array ℕ)
  im : List ℕ
  wt : List ℕ
  cm : List ℕ
  cs : Array (Array ℕ)
  ci : Array (Array ℕ)
  roots : List (ℕ × ℕ)
  nodes : Array Node
  ents : Array (List (ℕ × ℕ × ℕ))
  wcs : Array (Array ArrCert)
  excs : List ExcRef

@[expose] def nodeOKC (n : ℕ) (ps : List ℕ) (inX outX inW : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (d : ConjData) (cN : Array ArrCert) (e0 : Array (Array ℕ))
    (i : ℕ) : Bool :=
  let w := witOKW n ps inX outX allowPW allowInX allowU d.nodes[i]!.basis cN[i]! d.wcs[i]!
    d.nodes[i]!.wit
  enumOKK n d.nodes[i]!.basis ps cN[i]! &&
    ((w && d.nodes[i]!.wit.isMono) ||
      ((w || excOKW n ps inW e0 cN d.excs i) && d.ents[i]!.length == d.us.size &&
        (d.us.toList.zip d.ents[i]!).all fun ue => entOK n d.nodes cN d.cs d.ci i ue.1 ue.2))

@[expose] def conjCensusOKW (n : ℕ) (ps : List ℕ) (inX outX inW : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (d : ConjData) (e0 : Array (Array ℕ)) : Bool :=
  let cN := d.nodes.map fun nd => maskCert n nd.basis
  pcOK n d.xs d.rs d.cjs d.bs && invOK n d.xs d.us d.im d.wt && conjTabOK n d.xs d.cm d.cs d.ci &&
    d.roots.length == d.us.size &&
    (d.us.toList.zip d.roots).all (fun ur => rootOKC n d.nodes cN d.cs d.ci ur.1 ur.2) &&
    allLt d.nodes.size (nodeOKC n ps inX outX inW allowPW allowInX allowU d cN e0)

section Soundness

@[expose] noncomputable def pcSub (n : ℕ) (xs : List (Array ℕ)) : Subgroup (Equiv.Perm (Fin n)) :=
  closure {a | a ∈ xs.map (permOfArr n)}

theorem rep_pcA : ∀ {l : List (Array ℕ)}, (∀ a ∈ l, validA n a = true) → ∀ m,
    Rep n (pcA n l m) (pcG (l.map (permOfArr n)) m)
  | [], _, _ => rep_idA
  | x :: l, h, m => by
    have ih := rep_pcA (fun a ha => h a (List.mem_cons_of_mem x ha)) (m / 2)
    simp only [pcA, List.map_cons, pcG]
    split_ifs
    · exact rep_compA (rep_of_validA (h x (List.mem_cons_self ..))) ih
    · rw [one_mul]
      exact ih

theorem mem_zip_of_lt {α β : Type*} {l₁ : List α} {l₂ : List β} {i : ℕ} (h₁ : i < l₁.length)
    (h₂ : i < l₂.length) : (l₁[i], l₂[i]) ∈ l₁.zip l₂ := by
  rw [List.mem_iff_getElem]
  exact ⟨i, by simp [h₁, h₂], by simp⟩

theorem pc_of_pcOK : ∀ {xs : List (Array ℕ)} {rs : List ℕ} {cjs : List (List ℕ)}
    {bs : List (ℕ × ℕ)}, pcOK n xs rs cjs bs = true →
    (∀ a ∈ xs, validA n a = true) ∧ PcRel (xs.map (permOfArr n)) ∧ PcSep (xs.map (permOfArr n))
  | [], _, _, _, _ => ⟨by simp, trivial, trivial⟩
  | x :: l, r :: rs, cl :: cs, b :: bs, h => by
    simp only [pcOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hx, hsq⟩, hlen⟩, hc⟩, hq⟩, hbq⟩, hbx⟩, hbl⟩, hrest⟩ := h
    obtain ⟨hv, hrel, hsep⟩ := pc_of_pcOK hrest
    have hxr := rep_of_validA hx
    have hrep := rep_pcA hv
    refine ⟨fun a ha => ?_, ⟨⟨r, ?_⟩, fun y hy => ?_, hrel⟩, ?_, hsep⟩
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hx
      · exact hv a ha
    · exact eq_of_eqA (rep_compA hxr hxr) (hrep r) hsq
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hi' : i < cl.length := hlen ▸ hi
      have hz := hc _ (mem_zip_of_lt hi hi')
      exact ⟨cl[i], eq_of_eqA (rep_compA (rep_of_validA (hv _ ha)) hxr)
        (rep_compA hxr (hrep _)) hz⟩
    · refine not_mem_closure_of_block (fun p => b.1.testBit p = true) ?_ ⟨b.2, hq⟩ hbq ?_
      · intro y hy p hp
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
        have := hbl a ha p (List.mem_range.2 p.2)
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
        rcases this with h | h
        · rw [h] at hp
          exact Bool.noConfusion hp
        · rwa [(rep_of_validA (hv a ha)).apply p.2] at h
      · rw [← hxr.apply hq, hbx]
        exact Bool.noConfusion
  | _ :: _, [], _, _, h | _ :: _, _ :: _, [], _, h
  | _ :: _, _ :: _, _ :: _, [], h => by simp [pcOK] at h

theorem rep_inv_of_comp {p q : Array ℕ} {g : Equiv.Perm (Fin n)} (hq : Rep n q g)
    (h : eqA n (compA n p q) (idA n) = true) : Rep n p g⁻¹ := fun x => by
  have := allLt_spec h (g⁻¹ x).2
  rw [beq_iff_eq, compA_get (g⁻¹ x).2, hq (g⁻¹ x), ← Equiv.Perm.mul_apply, mul_inv_cancel,
    Equiv.Perm.one_apply,
    idA_get (g⁻¹ x).2] at this
  exact this

theorem two_mul_card_le_sup {W : Type*} [Group W] [Finite W] {N : Subgroup W} {u : W}
    (hu : u ∉ N) : 2 * Nat.card N ≤ Nat.card ↥(N ⊔ zpowers u) := by
  have hlt : Nat.card N < Nat.card ↥(N ⊔ zpowers u) :=
    card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hu (h ▸ mem_sup_right (mem_zpowers u)))
  obtain ⟨c, hc⟩ := card_dvd_of_le (le_sup_left (b := zpowers u))
  have hpos : 0 < Nat.card N := Nat.card_pos
  rw [hc] at hlt ⊢
  have : 2 ≤ c := by
    by_contra hc2
    interval_cases c <;> omega
  nlinarith

variable {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}

theorem census_of_conjCensusOKW {ps : List ℕ} {allowPW allowInX allowU : Bool} {d : ConjData}
    {e0 : Array (Array ℕ)} {Wg : Subgroup (Equiv.Perm (Fin n))} {inW : Array ℕ → Bool}
    (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ Wg)
    (hSW : pcSub n d.xs ≤ Wg)
    (hSX : ∀ s ∈ pcSub n d.xs, X.map (MulAut.conj s).toMonoidHom = X)
    (h : conjCensusOKW n ps inX outX inW allowPW allowInX allowU d e0 = true) :
    Nat.card (pcSub n d.xs) = 2 ^ d.xs.length ∧
      ∀ E : Subgroup (Equiv.Perm (Fin n)), E ≤ pcSub n d.xs → IsElemAbelian 2 E →
        4 ≤ Nat.card E → WitW X allowPW allowInX allowU E ∨
          ∃ w ∈ Wg, E = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom := by
  simp only [conjCensusOKW, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hpc, hinv⟩, htab⟩, hrlen⟩, hroot⟩, hnodes⟩ := h
  replace hroot := List.all_eq_true.1 hroot
  obtain ⟨hxv, hrel, hsep⟩ := pc_of_pcOK hpc
  set S := pcSub n d.xs
  set nodes := d.nodes
  set cN := nodes.map fun nd => maskCert n nd.basis
  have hrep := rep_pcA hxv
  have hlen : (d.xs.map (permOfArr n)).length = d.xs.length := List.length_map _
  refine ⟨by rw [← hlen]; exact card_closure_of_pc hrel hsep, fun E hES hE hE4 => ?_⟩
  simp only [invOK, Bool.and_eq_true, beq_iff_eq] at hinv
  obtain ⟨⟨⟨himl, hus⟩, hwtl⟩, hwalk⟩ := hinv
  replace hus := List.all_eq_true.1 hus
  have husl : d.im.length = d.us.toList.length := by rw [himl, Array.length_toList]
  have hinvS : ∀ a ∈ S, a ^ 2 = 1 → a ≠ 1 → ∃ k < d.us.size, Rep n d.us[k]! a := by
    intro a ha ha2 ha1
    obtain ⟨m, hm, rfl⟩ := exists_pcG_of_pcRel hrel a ha
    rw [hlen] at hm
    have hw := invRest_spec hwalk m (hwtl ▸ hm)
    rw [Nat.zero_add] at hw
    rcases hw with hc | h0 | ⟨hx, hne⟩
    · obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hc
      have hk' : k < d.us.toList.length := husl ▸ hk
      have := hus _ (mem_zip_of_lt hk' hk)
      refine ⟨k, by simpa using hk', ?_⟩
      rw [hkm] at this
      have e : d.us[k]! = d.us.toList[k] := by
        rw [getElem!_pos d.us k (by simpa using hk'), Array.getElem_toList]
      rw [e]
      exact rep_of_eqA (hrep m) this
    · rw [h0, pcG_zero] at ha1
      exact absurd rfl ha1
    · exfalso
      have hr := hrep m
      rw [hr.apply hx, hr.apply (Fin.isLt _)] at hne
      have : (pcG (d.xs.map (permOfArr n)) m) ((pcG (d.xs.map (permOfArr n)) m) ⟨_, hx⟩) =
          ⟨_, hx⟩ := by
        rw [← Equiv.Perm.mul_apply, ← sq, ha2, Equiv.Perm.one_apply]
      rw [this] at hne
      simp at hne
  simp only [conjTabOK, Bool.and_eq_true, beq_iff_eq] at htab
  obtain ⟨⟨⟨hcml, hcil⟩, hcs⟩, hci⟩ := htab
  replace hcs := List.all_eq_true.1 hcs
  replace hci := List.all_eq_true.1 hci
  have hconjT : ∀ t < d.cs.size, ∃ s ∈ S, Rep n d.cs[t]! s ∧ Rep n d.ci[t]! s⁻¹ := by
    intro t ht
    have ht1 : t < d.cs.toList.length := by simpa using ht
    have ht2 : t < d.cm.length := hcml ▸ ht
    have ht3 : t < d.ci.toList.length := by simpa [hcil] using ht
    have e1 : d.cs[t]! = d.cs.toList[t] := by rw [getElem!_pos d.cs t ht, Array.getElem_toList]
    have e2 : d.ci[t]! = d.ci.toList[t] := by
      rw [getElem!_pos d.ci t (by simpa using ht3), Array.getElem_toList]
    have hs1 : eqA n (pcA n d.xs d.cm[t]) d.cs.toList[t] = true :=
      hcs (d.cs.toList[t], d.cm[t]) (mem_zip_of_lt ht1 ht2)
    have hs := rep_of_eqA (hrep d.cm[t]) hs1
    have hc : eqA n (compA n d.ci.toList[t] d.cs.toList[t]) (idA n) = true :=
      hci (d.ci.toList[t], d.cs.toList[t]) (mem_zip_of_lt ht3 ht1)
    refine ⟨_, pcG_mem _ _, by rw [e1]; exact hs, ?_⟩
    rw [e2]
    exact rep_inv_of_comp hs hc
  have hnode : ∀ i < nodes.size,
      nodeOKC n ps inX outX inW allowPW allowInX allowU d cN e0 i = true :=
    fun i hi => allLt_spec hnodes hi
  have hnodeE : ∀ i < nodes.size, enumOK n nodes[i]!.basis ps cN[i]! = true := by
    intro i hi
    have := hnode i hi
    simp only [nodeOKC, Bool.and_eq_true] at this
    exact enumOK_of_enumOKK this.1
  have hbasis : ∀ i < nodes.size, ∀ k < nodes[i]!.basis.size,
      validA n nodes[i]!.basis[k]! = true := fun i hi k hk => enumOK_gens_valid (hnodeE i hi) hk
  have hmemN : ∀ i < nodes.size, ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
      memA n cN[i]! a = true → g ∈ nodeSub n nodes i :=
    fun i hi a g ha hm => enumOK_mem_of_any hps (hnodeE i hi) ha hm
  have hcardN : ∀ i < nodes.size, Nat.card (nodeSub n nodes i) = cN[i]!.pts.size :=
    fun i hi => (enumOK_spec hps (hnodeE i hi)).2.1
  have huk : ∀ k (hk : k < d.us.size), d.us[k]! = d.us.toList[k]'(by simpa using hk) :=
    fun k hk => by rw [getElem!_pos d.us k hk, Array.getElem_toList]
  refine forall_of_conjTree (S := S)
    (fun E => WitW X allowPW allowInX allowU E ∨
      ∃ w ∈ Wg, E = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom)
    (MonoW X allowPW) ?_ (fun E₀ E hm hle _ _ _ => Or.inl (witW_of_monoW allowInX allowU hm hle))
    (nodeSub n nodes) nodes.size ?_ ?_ ?_ hES hE hE4
  ·
    intro E s hs hw
    rcases hw with hw | ⟨w, hw, heq⟩
    · exact Or.inl (witW_of_map_conj (hSX s hs) hw)
    · refine Or.inr ⟨s⁻¹ * w, Wg.mul_mem (Wg.inv_mem (hSW hs)) hw, ?_⟩
      rw [← map_conj_map_conj, ← heq, map_conj_map_conj, inv_mul_cancel]
      ext x
      simp
  ·
    intro a ha ha2 ha1
    obtain ⟨k, hk, hua⟩ := hinvS a ha ha2 ha1
    have hk' : k < d.us.toList.length := by simpa using hk
    have hrk := hroot _ (mem_zip_of_lt hk' (hrlen ▸ hk))
    rw [← huk k hk] at hrk
    simp only [rootOKC, Bool.and_eq_true, decide_eq_true_eq] at hrk
    obtain ⟨⟨⟨hj, ht⟩, hall⟩, hu⟩ := hrk
    obtain ⟨s, hsS, hs, hsi⟩ := hconjT _ ht
    have hsr := rep_compA hs (rep_compA hua hsi)
    refine ⟨_, hj, s, hsS, le_antisymm ?_ ?_⟩
    · rw [nodeSub, closure_le]
      rintro _ ⟨l, hl, rfl⟩
      dsimp only
      have hbl := rep_of_validA (hbasis _ hj l hl)
      have h2 := allLt_spec hall hl
      simp only [Bool.or_eq_true] at h2
      rw [SetLike.mem_coe, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases h2 with h2 | h2
      · rw [eq_of_eqA hbl hsr h2, ← mul_assoc]
        exact mem_zpowers _
      · rw [eq_of_eqA hbl rep_idA h2]
        exact one_mem _
    · rw [MonoidHom.map_zpowers, zpowers_le, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := hmemN _ hj hsr hu
      rwa [← mul_assoc] at this
  ·
    intro i hi
    have hn := hnode i hi
    simp only [nodeOKC, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at hn
    obtain ⟨hEi, hw | ⟨⟨-, hel⟩, hch⟩⟩ := hn
    · rcases witOKW_sound hps hin hout (enumOK_of_enumOKK hEi) hw.1 with hm | ⟨hnm, -⟩
      · exact Or.inl hm
      · rw [hnm] at hw
        exact Bool.noConfusion hw.2
    refine Or.inr fun u hu hu2 hui hcomm => ?_
    have hu1 : u ≠ 1 := fun h1 => hui (h1 ▸ one_mem _)
    obtain ⟨k, hk, hur⟩ := hinvS u hu hu2 hu1
    have hk' : k < d.us.toList.length := by simpa using hk
    have hck := hch _ (mem_zip_of_lt hk' (by rw [hel]; exact hk))
    rw [← huk k hk] at hck
    simp only [entOK] at hck
    split_ifs at hck with h0 h1
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
        at hck
      obtain ⟨⟨hl, hx⟩, hne⟩ := hck
      have hbl := rep_of_validA (hbasis i hi _ hl)
      have hc := hcomm _ (subset_closure (mem_permsA hl))
      exfalso
      apply hne
      have e1 := hbl ⟨_, hx⟩
      have e2 := hur ⟨_, hx⟩
      rw [e1, e2, hur, hbl]
      have := congrArg (fun g : Equiv.Perm (Fin n) => (g ⟨_, hx⟩ : ℕ)) hc
      simpa only [Equiv.Perm.mul_apply] using this.symm
    · exact absurd (hmemN i hi hur hck) hui
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hck
    obtain ⟨⟨⟨⟨hj, ht⟩, hcard⟩, hib⟩, hu'⟩ := hck
    obtain ⟨s, hsS, hs, hsi⟩ := hconjT _ ht
    refine ⟨_, hj, s, hsS, ?_⟩
    have hle : (nodeSub n nodes i ⊔ zpowers u).map (MulAut.conj s).toMonoidHom ≤
        nodeSub n nodes ((d.ents[i]!)[k]'(by rw [hel]; exact hk)).2.1 := by
      rw [map_le_iff_le_comap]
      refine sup_le ?_ ?_
      · rw [nodeSub, closure_le]
        rintro _ ⟨l, hl, rfl⟩
        dsimp only
        have hbl := rep_of_validA (hbasis i hi l hl)
        rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have := hmemN _ hj (rep_compA hs (rep_compA hbl hsi)) (allLt_spec hib hl)
        rwa [← mul_assoc] at this
      · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have := hmemN _ hj (rep_compA hs (rep_compA hur hsi)) hu'
        rwa [← mul_assoc] at this
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [card_map_of_injective (MulAut.conj s).injective, hcardN _ hj, hcard, ← hcardN i hi]
    exact two_mul_card_le_sup hui
  ·
    intro i hi h4
    have hn := hnode i hi
    simp only [nodeOKC, Bool.and_eq_true, Bool.or_eq_true] at hn
    obtain ⟨hEi, ⟨hw, -⟩ | ⟨⟨hw | hx, -⟩, -⟩⟩ := hn
    · rcases witOKW_sound hps hin hout (enumOK_of_enumOKK hEi) hw with hm | ⟨-, hw'⟩
      · exact Or.inl hm
      · exact Or.inr (Or.inl (hw' h4))
    · rcases witOKW_sound hps hin hout (enumOK_of_enumOKK hEi) hw with hm | ⟨-, hw'⟩
      · exact Or.inl hm
      · exact Or.inr (Or.inl (hw' h4))
    · exact Or.inr (Or.inr (eq_map_of_excOKW hps hinW (enumOK_of_enumOKK hEi) hx))

end Soundness

section Pair

variable {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} {testP : Array ℕ → Bool} {ps : List ℕ}
  {allowPW allowInX : Bool} {d : ConjData} {e0 : Array (Array ℕ)} {u : Array ℕ}
  {uR : Equiv.Perm (Fin n)} {m : ℕ}

theorem witness_pair_conjW (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : conjCensusOKW n ps testP testP (fun a => testP a || testP (compA n u a)) allowPW
      allowInX false d e0 = true)
    (hgen : d.xs.all (fun a => testP a || testP (compA n u a)) = true)
    (hcard : Nat.card R = 2 ^ d.xs.length * m) (hm : Odd m) :
    ∃ S : Subgroup ↥R, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness (P.subgroupOf R) E ∨ (allowPW = true ∧ PWitness (P.subgroupOf R) E) ∨
        (allowInX = true ∧ E ≤ P.subgroupOf R) ∨ ExcClass R (closure (permsA n e0)) E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (P.subgroupOf R).map R.subtype = P := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hPR]
  have hR : ∀ a, validA n a = true → (testP a || testP (compA n u a)) = true →
      permOfArr n a ∈ R := by
    intro a hv h
    have hr := rep_of_validA hv
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact hPR ((htest _ _ hr).1 h)
    · have h' := (htest _ _ (rep_compA hu hr)).1 h
      have : permOfArr n a = uR⁻¹ * (uR * permOfArr n a) := by group
      rw [this]
      exact mul_mem (inv_mem huR) (hPR h')
  have hc' := hc
  simp only [conjCensusOKW, Bool.and_eq_true] at hc'
  obtain ⟨hxv, -, -⟩ := pc_of_pcOK hc'.1.1.1.1.1
  set S' := pcSub n d.xs
  have hS'R : S' ≤ R := by
    refine (closure_le R).2 fun _ hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hR _ (hxv a ha) (List.all_eq_true.1 hgen a ha)
  have hS'le : S' ≤ R.subtype.range := by rwa [range_subtype]
  have hconjP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P := by
    intro r hr x hx
    have := hN.conj_mem ⟨x, hPR hx⟩ (by rwa [mem_subgroupOf]) ⟨r, hr⟩
    rwa [mem_subgroupOf] at this
  have hSX : ∀ s ∈ S', ((P.subgroupOf R).map R.subtype).map (MulAut.conj s).toMonoidHom =
      (P.subgroupOf R).map R.subtype := by
    intro s hs
    rw [hmap]
    refine le_antisymm ?_ fun x hx => ⟨s⁻¹ * x * s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hconjP s (hS'R hs) x hx
    · have := hconjP s⁻¹ (R.inv_mem (hS'R hs)) x hx
      rwa [inv_inv] at this
    · simp [MulAut.conj_apply, mul_assoc]
  have hin : ∀ a, validA n a = true → testP a = true →
      permOfArr n a ∈ (P.subgroupOf R).map R.subtype := fun a hv ha => by
    rw [hmap]
    exact (htest _ _ (rep_of_validA hv)).1 ha
  have hout : ∀ a, validA n a = true → permOfArr n a ∈ (P.subgroupOf R).map R.subtype →
      testP a = true := fun a hv ha => by
    rw [hmap] at ha
    exact (htest _ _ (rep_of_validA hv)).2 ha
  obtain ⟨hS'card, hw⟩ := census_of_conjCensusOKW hps hin hout hR hS'R hSX hc
  set S := S'.comap R.subtype
  have hSmap : S.map R.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ d.xs.length := by
    rw [← card_map_of_injective R.subtype_injective, hSmap, hS'card]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, hcard] at h1
    have hidx : S.index = m := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h1
    rw [hidx] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  · have hES' : E.map R.subtype ≤ S' := hSmap ▸ map_mono hES
    rcases hw _ hES' (isElemAbelian_map hE R.subtype)
        (by rwa [card_map_of_injective R.subtype_injective]) with
      (hw | hw | hw | ⟨h, -⟩) | ⟨w, hwR, heq⟩
    · exact Or.inl ((yWitness_map_iff _ R.subtype_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff _ R.subtype_injective _ _).mp hw.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hw.1, (map_le_map_iff_of_injective R.subtype_injective).mp
        hw.2⟩))
    · exact absurd h (by decide)
    · exact Or.inr (Or.inr (Or.inr ⟨w, hwR, heq⟩))

theorem yCensusExc_pair_conjW (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : conjCensusOKW n ps testP testP (fun a => testP a || testP (compA n u a)) false
      false false d e0 = true)
    (hgen : d.xs.all (fun a => testP a || testP (compA n u a)) = true)
    (hcard : Nat.card R = 2 ^ d.xs.length * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (ExcClass R (closure (permsA n e0))) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_conjW hPR hN hps htest hu huR hc hgen hcard hm
  refine yCensus_of_le_sylow hN hS (fun E w h => excClass_of_map_conj h)
    fun E hES hE hE4 hnot => ?_
  rcases hw E hES hE hE4 with h | ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h hnot

theorem yCensusII_pair_conjW (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : conjCensusOKW n ps testP testP (fun a => testP a || testP (compA n u a)) false
      true false d #[] = true)
    (hgen : d.xs.all (fun a => testP a || testP (compA n u a)) = true)
    (hcard : Nat.card R = 2 ^ d.xs.length * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (· ≤ P.subgroupOf R) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_conjW hPR hN hps htest hu huR hc hgen hcard hm
  refine yCensus_of_le_sylow hN hS (fun E w h => ?_) fun E hES hE hE4 hnot => ?_
  · have := map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) h
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_eq_of_normal hN,
      show (MulAut.conj (1 : ↥R)).toMonoidHom = MonoidHom.id ↥R by ext; simp, map_id] at this
  rcases hw E hES hE hE4 with h | ⟨h, -⟩ | ⟨-, h⟩ | ⟨w, -, heq⟩
  · exact h
  · exact absurd h (by decide)
  · exact absurd h hnot
  · exfalso
    have hbot : closure (permsA n (#[] : Array (Array ℕ))) = ⊥ := by
      rw [closure_eq_bot_iff]
      rintro _ ⟨j, hj, -⟩
      exact absurd hj (by simp)
    rw [hbot, Subgroup.map_bot] at heq
    have hEbot : E = ⊥ := by
      rw [← map_eq_bot_iff_of_injective E R.subtype_injective, heq]
    rw [hEbot, card_bot] at hE4
    omega

end Pair

end CFSG.ComponentClassification.RankTwoSporadic.Cert
