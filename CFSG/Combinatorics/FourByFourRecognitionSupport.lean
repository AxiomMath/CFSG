module

public import CFSG.Combinatorics.AperiodicSixteenRecognitionSupport
public import CFSG.Combinatorics.FourByFourPeriodicGraphSupport
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Combinatorics.FourByFourPeriodicGraph

@[expose] def dmul (p q : Vertex) : Vertex :=
  (if p.2 = 0 then p.1 + q.1 else p.1 - q.1, p.2 + q.2)

@[expose] def dinv (p : Vertex) : Vertex :=
  (if p.2 = 0 then -p.1 else p.1, p.2)

theorem dmul_o : ∀ p : Vertex, dmul p o = p := by
  decide

theorem dmul_nbr : ∀ (p q : Vertex) (i : Fin 3), dmul p (nbr q i) = nbr (dmul p q) i := by
  decide

theorem dmul_dinv : ∀ p : Vertex, dmul p (dinv p) = o := by
  decide

theorem eq_of_dmul_dinv : ∀ p q : Vertex, dmul p (dinv q) = o → p = q := by
  decide

@[expose] def reps : Finset Vertex :=
  {((2, 0), 0), ((0, 2), 0), ((2, 2), 0), ((0, 0), 1), ((1, 0), 1), ((0, 1), 1), ((1, 1), 1)}

theorem exists_conj_mem_reps : ∀ k : Vertex, k ≠ o → ∃ q : Vertex,
    dmul (dmul (dinv q) k) q ∈ reps ∨ dmul (dmul (dinv q) (dmul k k)) q ∈ reps := by
  decide

variable {Ω : Type*}

@[expose] def wordAct (r : Fin 3 → Ω → Ω) : List (Fin 3) → Ω → Ω
  | [], x => x
  | i :: w, x => wordAct r w (r i x)

@[expose] def act (r : Fin 3 → Ω → Ω) (p : Vertex) (x : Ω) : Ω :=
  if p.2 = 0 then (fun z => r 0 (r 2 z))^[p.1.2.val] ((fun z => r 0 (r 1 z))^[p.1.1.val] x)
  else r 0 ((fun z => r 0 (r 2 z))^[p.1.2.val] ((fun z => r 0 (r 1 z))^[p.1.1.val] x))

theorem act_o (r : Fin 3 → Ω → Ω) (x : Ω) : act r o x = x :=
  rfl

theorem iterate_val_add_one {f : Ω → Ω} (hf : ∀ z, f (f (f (f z))) = z) (v : ZMod 4) (x : Ω) :
    f^[(v + 1).val] x = f (f^[v.val] x) := by
  fin_cases v
  · rfl
  · rfl
  · rfl
  · exact (hf x).symm

theorem iterate_val_sub_one {f g : Ω → Ω} (hf : ∀ z, f (f (f (f z))) = z)
    (hg : ∀ z, g (f z) = z) (v : ZMod 4) (x : Ω) : f^[(v - 1).val] x = g (f^[v.val] x) := by
  fin_cases v
  · change f (f (f x)) = g x
    conv_rhs => rw [← hf x]
    exact (hg _).symm
  · exact (hg x).symm
  · exact (hg (f x)).symm
  · exact (hg (f (f x))).symm

section Relations

variable {r : Fin 3 → Ω → Ω} (hinv : ∀ i x, r i (r i x) = x)
  (hrel₁ : ∀ x, r 2 (r 1 (r 0 (r 2 (r 1 (r 0 x))))) = x)
  (hrel₂ : ∀ x, r 1 (r 0 (r 1 (r 0 (r 1 (r 0 (r 1 (r 0 x))))))) = x)
  (hrel₃ : ∀ x, r 2 (r 0 (r 2 (r 0 (r 2 (r 0 (r 2 (r 0 x))))))) = x)

include hinv hrel₂ in
theorem A_pow_four (z : Ω) :
    r 0 (r 1 (r 0 (r 1 (r 0 (r 1 (r 0 (r 1 z))))))) = z := by
  have h := congrArg (r 1) (hrel₂ (r 1 z))
  simp only [hinv] at h
  exact h

include hinv hrel₃ in
theorem B_pow_four (z : Ω) :
    r 0 (r 2 (r 0 (r 2 (r 0 (r 2 (r 0 (r 2 z))))))) = z := by
  have h := congrArg (r 2) (hrel₃ (r 2 z))
  simp only [hinv] at h
  exact h

include hinv hrel₁ in
theorem A_B_comm (z : Ω) : r 0 (r 1 (r 0 (r 2 z))) = r 0 (r 2 (r 0 (r 1 z))) := by
  have h1 : ∀ y, r 1 (r 0 (r 2 (r 1 (r 0 (r 2 y))))) = y := fun y => by
    have h := congrArg (r 2) (hrel₁ (r 2 y))
    simp only [hinv] at h
    exact h
  have h2 : r 1 (r 0 (r 2 z)) = r 2 (r 0 (r 1 z)) := by
    have h := h1 z
    have h' := congrArg (fun w => r 2 (r 0 (r 1 w))) h
    simp only [hinv] at h'
    exact h'
  rw [h2]

include hinv hrel₁ hrel₂ hrel₃ in
theorem act_nbr (p : Vertex) (i : Fin 3) (x : Ω) : act r (nbr p i) x = r i (act r p x) := by
  set A : Ω → Ω := fun z => r 0 (r 1 z) with hA
  set B : Ω → Ω := fun z => r 0 (r 2 z) with hB
  have hA4 : ∀ z, A (A (A (A z))) = z := A_pow_four hinv hrel₂
  have hB4 : ∀ z, B (B (B (B z))) = z := B_pow_four hinv hrel₃
  have hAB : Function.Commute B A := fun z => (A_B_comm hinv hrel₁ z).symm
  have hAiB : Function.Commute B (fun z => r 1 (r 0 z)) := fun z => by
    change r 0 (r 2 (r 1 (r 0 z))) = r 1 (r 0 (r 0 (r 2 z)))
    have h := A_B_comm hinv hrel₁ (r 1 (r 0 z))
    simp only [hinv] at h
    have h' := congrArg (fun w => r 1 (r 0 w)) h
    simp only [hinv] at h'
    rw [hinv]
    exact h'
  obtain ⟨⟨v₁, v₂⟩, e⟩ := p
  fin_cases e <;> fin_cases i
  ·
    show act r ((v₁ + 0, v₂ + 0), 1) x = r 0 (act r ((v₁, v₂), 0) x)
    simp only [add_zero]
    rfl
  ·
    show act r ((v₁ + 1, v₂ + 0), 1) x = r 1 (act r ((v₁, v₂), 0) x)
    simp only [add_zero]
    change r 0 (B^[v₂.val] (A^[(v₁ + 1).val] x)) = r 1 (B^[v₂.val] (A^[v₁.val] x))
    rw [iterate_val_add_one hA4, (hAB.iterate_left v₂.val) (A^[v₁.val] x)]
    exact hinv 0 _
  ·
    show act r ((v₁ + 0, v₂ + 1), 1) x = r 2 (act r ((v₁, v₂), 0) x)
    simp only [add_zero]
    change r 0 (B^[(v₂ + 1).val] (A^[v₁.val] x)) = r 2 (B^[v₂.val] (A^[v₁.val] x))
    rw [iterate_val_add_one hB4]
    exact hinv 0 _
  ·
    show act r ((v₁ - 0, v₂ - 0), 0) x = r 0 (act r ((v₁, v₂), 1) x)
    simp only [sub_zero]
    exact (hinv 0 _).symm
  ·
    show act r ((v₁ - 1, v₂ - 0), 0) x = r 1 (act r ((v₁, v₂), 1) x)
    simp only [sub_zero]
    change B^[v₂.val] (A^[(v₁ - 1).val] x) = r 1 (r 0 (B^[v₂.val] (A^[v₁.val] x)))
    rw [iterate_val_sub_one hA4 (g := fun z => r 1 (r 0 z)) (fun z => by
      simp only [hA, hinv]), (hAiB.iterate_left v₂.val) (A^[v₁.val] x)]
  ·
    show act r ((v₁ - 0, v₂ - 1), 0) x = r 2 (act r ((v₁, v₂), 1) x)
    simp only [sub_zero]
    change B^[(v₂ - 1).val] (A^[v₁.val] x) = r 2 (r 0 (B^[v₂.val] (A^[v₁.val] x)))
    rw [iterate_val_sub_one hB4 (g := fun z => r 2 (r 0 z)) (fun z => by
      simp only [hB, hinv])]

include hinv hrel₁ hrel₂ hrel₃ in
theorem act_wordEnd (p : Vertex) (w : List (Fin 3)) (x : Ω) :
    act r (wordEnd p w) x = wordAct r w (act r p x) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    rw [wordEnd, ih, act_nbr hinv hrel₁ hrel₂ hrel₃]
    rfl

include hinv hrel₁ hrel₂ hrel₃ in
theorem eq_act {ψ : Vertex → Ω} {y : Ω} (ho : ψ o = y) (hψ : ∀ p i, ψ (nbr p i) = r i (ψ p))
    (p : Vertex) : ψ p = act r p y := by
  have key : ∀ (u v : Vertex) (q : P4.Walk u v), ψ u = act r u y → ψ v = act r v y := by
    intro u v q
    induction q with
    | nil => exact id
    | cons h q ih =>
      intro hu
      obtain ⟨i, rfl⟩ := adj_iff.mp h
      exact ih (by rw [hψ, hu, act_nbr hinv hrel₁ hrel₂ hrel₃])
  obtain ⟨q⟩ := connected.preconnected o p
  exact key o p q (by rw [ho, act_o])

include hinv hrel₁ hrel₂ hrel₃ in
theorem act_dmul (q p : Vertex) (x : Ω) : act r (dmul q p) x = act r p (act r q x) :=
  eq_act hinv hrel₁ hrel₂ hrel₃ (ψ := fun p => act r (dmul q p) x) (by rw [dmul_o])
    (fun p i => by rw [dmul_nbr, act_nbr hinv hrel₁ hrel₂ hrel₃]) p

end Relations

theorem exists_isCycle_three {V : Type*} {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 3 := by
  refine ⟨.cons hab (.cons hbc (.cons hca .nil)), ?_, rfl⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  simp [hab.ne, hab.ne.symm, hbc.ne, hca.ne, hca.ne.symm]

theorem exists_isCycle_four {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c)
    (hbd : b ≠ d) : ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 4 := by
  refine ⟨.cons hab (.cons hbc (.cons hcd (.cons hda .nil))), ?_, rfl⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  simp [hab.ne, hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hda.ne.symm, hac, hac.symm, hbd]

variable {Ω : Type*} {r : Fin 3 → Ω → Ω}

theorem rr_ne (hinv : ∀ i x, r i (r i x) = x) (hdist : ∀ x, Function.Injective fun i => r i x)
    {a b : Fin 3} (hab : a ≠ b) (x : Ω) : r b (r a x) ≠ x := by
  intro h
  apply hab
  apply hdist x
  change r a x = r b x
  rw [← hinv b (r a x), h]

theorem alt_four_ne (hinv : ∀ i x, r i (r i x) = x) (hfix : ∀ i x, r i x ≠ x)
    (hdist : ∀ x, Function.Injective fun i => r i x)
    (hcyc : ∀ x (p : (AperiodicSixteenGraph.colourGraph r).Walk x x), p.IsCycle →
      p.length ≠ 3 ∧ p.length ≠ 4)
    {a b : Fin 3} (hab : a ≠ b) (x : Ω) : r b (r a (r b (r a x))) ≠ x := by
  intro h
  have hadj := AperiodicSixteenGraph.colourGraph_adj_r hfix
  have h4 := hadj b (r a (r b (r a x)))
  rw [h] at h4
  obtain ⟨p, hp, hl⟩ := exists_isCycle_four (hadj a x) (hadj b (r a x))
    (hadj a (r b (r a x))) h4 (rr_ne hinv hdist hab x).symm
    (rr_ne hinv hdist hab.symm (r a x)).symm
  exact (hcyc x p hp).2 hl

theorem act_ne (hinv : ∀ i x, r i (r i x) = x) (hfix : ∀ i x, r i x ≠ x)
    (hdist : ∀ x, Function.Injective fun i => r i x)
    (hcyc : ∀ x (p : (AperiodicSixteenGraph.colourGraph r).Walk x x), p.IsCycle →
      p.length ≠ 3 ∧ p.length ≠ 4)
    (hrel₁ : ∀ x, r 2 (r 1 (r 0 (r 2 (r 1 (r 0 x))))) = x)
    (hrel₂ : ∀ x, r 1 (r 0 (r 1 (r 0 (r 1 (r 0 (r 1 (r 0 x))))))) = x)
    (hrel₃ : ∀ x, r 2 (r 0 (r 2 (r 0 (r 2 (r 0 (r 2 (r 0 x))))))) = x)
    {k : Vertex} (hk : k ≠ o) (x : Ω) : act r k x ≠ x := by
  intro hkx
  have hmul := act_dmul hinv hrel₁ hrel₂ hrel₃
  obtain ⟨q, hq⟩ := exists_conj_mem_reps k hk
  obtain ⟨m, hm, hmx⟩ : ∃ m, dmul (dmul (dinv q) m) q ∈ reps ∧ act r m x = x := by
    rcases hq with h | h
    · exact ⟨k, h, hkx⟩
    · exact ⟨dmul k k, h, by rw [hmul, hkx, hkx]⟩
  have hconj : act r (dmul (dmul (dinv q) m) q) (act r q x) = act r q x := by
    rw [hmul, hmul, ← hmul q (dinv q), dmul_dinv, act_o, hmx]
  set y := act r q x
  have hword : ∀ (c : Vertex) (w : List (Fin 3)), wordEnd o w = c →
      act r c y = wordAct r w y := fun c w hc => by
    rw [← hc, act_wordEnd hinv hrel₁ hrel₂ hrel₃, act_o]
  have hadj := AperiodicSixteenGraph.colourGraph_adj_r hfix
  simp only [reps, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h <;> rw [h] at hconj
  · exact alt_four_ne hinv hfix hdist hcyc (by decide : (1 : Fin 3) ≠ 0) y
      ((hword _ [1, 0, 1, 0] (by decide)).symm.trans hconj)
  · exact alt_four_ne hinv hfix hdist hcyc (by decide : (2 : Fin 3) ≠ 0) y
      ((hword _ [2, 0, 2, 0] (by decide)).symm.trans hconj)
  · exact alt_four_ne hinv hfix hdist hcyc (by decide : (1 : Fin 3) ≠ 2) y
      ((hword _ [1, 2, 1, 2] (by decide)).symm.trans hconj)
  · exact hfix 0 y ((hword _ [0] (by decide)).symm.trans hconj)
  · exact hfix 1 y ((hword _ [1] (by decide)).symm.trans hconj)
  · exact hfix 2 y ((hword _ [2] (by decide)).symm.trans hconj)
  ·
    have h3 : r 2 (r 0 (r 1 y)) = y := (hword _ [1, 0, 2] (by decide)).symm.trans hconj
    have hca := hadj 2 (r 0 (r 1 y))
    rw [h3] at hca
    obtain ⟨p, hp, hl⟩ := exists_isCycle_three (hadj 1 y) (hadj 0 (r 1 y)) hca
    exact (hcyc y p hp).1 hl

theorem existsUnique_colour_equiv (hinv : ∀ i x, r i (r i x) = x) (hfix : ∀ i x, r i x ≠ x)
    (hdist : ∀ x, Function.Injective fun i => r i x)
    (hconn : (AperiodicSixteenGraph.colourGraph r).Connected)
    (hcyc : ∀ x (p : (AperiodicSixteenGraph.colourGraph r).Walk x x), p.IsCycle →
      p.length ≠ 3 ∧ p.length ≠ 4)
    (hrel₁ : ∀ x, r 2 (r 1 (r 0 (r 2 (r 1 (r 0 x))))) = x)
    (hrel₂ : ∀ x, r 1 (r 0 (r 1 (r 0 (r 1 (r 0 (r 1 (r 0 x))))))) = x)
    (hrel₃ : ∀ x, r 2 (r 0 (r 2 (r 0 (r 2 (r 0 (r 2 (r 0 x))))))) = x) (ω₀ : Ω) :
    ∃! φ : Vertex ≃ Ω, φ o = ω₀ ∧ ∀ p i, φ (nbr p i) = r i (φ p) := by
  have hmul := act_dmul hinv hrel₁ hrel₂ hrel₃
  have hinj : Function.Injective fun p => act r p ω₀ := by
    intro p q hpq
    have hfix' : act r (dmul p (dinv q)) ω₀ = ω₀ := by
      rw [hmul, show act r p ω₀ = act r q ω₀ from hpq, ← hmul, dmul_dinv, act_o]
    by_contra hne
    exact act_ne hinv hfix hdist hcyc hrel₁ hrel₂ hrel₃
      (fun h1 => hne (eq_of_dmul_dinv p q h1)) ω₀ hfix'
  have hsurj : Function.Surjective fun p => act r p ω₀ := by
    intro x
    obtain ⟨w⟩ := hconn.preconnected ω₀ x
    suffices ∀ y (q : (AperiodicSixteenGraph.colourGraph r).Walk y x),
        (∃ p, act r p ω₀ = y) → ∃ p, act r p ω₀ = x from this ω₀ w ⟨o, act_o r ω₀⟩
    intro y q
    clear w
    induction q with
    | nil => exact id
    | cons h q ih =>
      rintro ⟨p, hp⟩
      obtain ⟨-, i, hi⟩ := (AperiodicSixteenGraph.colourGraph_adj hinv).mp h
      exact ih ⟨nbr p i, by rw [act_nbr hinv hrel₁ hrel₂ hrel₃, hp, hi]⟩
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩,
    ⟨act_o r ω₀, fun p i => act_nbr hinv hrel₁ hrel₂ hrel₃ p i ω₀⟩, ?_⟩
  rintro ψ ⟨hψo, hψ⟩
  ext p
  exact eq_act hinv hrel₁ hrel₂ hrel₃ hψo hψ p

end CFSG.Combinatorics.FourByFourPeriodicGraph
