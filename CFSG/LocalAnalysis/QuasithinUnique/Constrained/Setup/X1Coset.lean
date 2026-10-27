module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CosetNative
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Cert

variable {P : Type*} [Group P]

structure CosetCert (R : Subgroup P) (a b : P) (N : ℕ) where
  r : ℕ → P
  Aa : ℕ → ℕ
  Ab : ℕ → ℕ
  r_zero : r 0 = 1
  hN : Nat.card (P ⧸ R) = N
  hN0 : 0 < N
  edge_a : ∀ i < N, Aa i < N ∧ (r (Aa i))⁻¹ * (a * r i) ∈ R
  edge_b : ∀ i < N, Ab i < N ∧ (r (Ab i))⁻¹ * (b * r i) ∈ R

variable {R : Subgroup P} {a b : P} {N : ℕ}

@[expose] def ActsOn (C : CosetCert R a b N) (g : P) (t : ℕ → ℕ) : Prop :=
  ∀ i < N, t i < N ∧ ((g * C.r i : P) : P ⧸ R) = ((C.r (t i) : P) : P ⧸ R)

theorem coset_eq_of_mem {x y : P} (h : y⁻¹ * x ∈ R) : ((x : P) : P ⧸ R) = ((y : P) : P ⧸ R) := by
  rw [QuotientGroup.eq]
  have := R.inv_mem h
  simpa using this

theorem mem_of_coset_eq {x y : P} (h : ((x : P) : P ⧸ R) = ((y : P) : P ⧸ R)) : y⁻¹ * x ∈ R := by
  rw [QuotientGroup.eq] at h
  have := R.inv_mem h
  simpa using this

theorem actsOn_a (C : CosetCert R a b N) : ActsOn C a C.Aa := fun i hi =>
  ⟨(C.edge_a i hi).1, coset_eq_of_mem (C.edge_a i hi).2⟩

theorem actsOn_b (C : CosetCert R a b N) : ActsOn C b C.Ab := fun i hi =>
  ⟨(C.edge_b i hi).1, coset_eq_of_mem (C.edge_b i hi).2⟩

theorem actsOn_mul (C : CosetCert R a b N) {g h : P} {t s : ℕ → ℕ} (hg : ActsOn C g t)
    (hh : ActsOn C h s) : ActsOn C (g * h) (t ∘ s) := by
  intro i hi
  obtain ⟨hsi, hs⟩ := hh i hi
  obtain ⟨hts, ht⟩ := hg (s i) hsi
  refine ⟨hts, ?_⟩
  have e1 : ((g * h * C.r i : P) : P ⧸ R) = g • ((h * C.r i : P) : P ⧸ R) := by
    rw [mul_assoc]; rfl
  rw [e1, hs]
  exact ht

theorem submonoid_inv_mem [Finite P] (T : Submonoid P) {g : P} (hg : g ∈ T) : g⁻¹ ∈ T := by
  have h1 : g ^ (orderOf g - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
  have h2 : g⁻¹ = g ^ (orderOf g - 1) := (eq_inv_of_mul_eq_one_left h1).symm
  rw [h2]
  exact T.pow_mem hg _

theorem cosets_exhaust [Finite P] (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) (g : P) :
    ∃ i < N, ((g : P) : P ⧸ R) = ((C.r i : P) : P ⧸ R) := by
  let S : Set (P ⧸ R) := {x | ∃ i < N, x = ((C.r i : P) : P ⧸ R)}
  let T : Submonoid P :=
    { carrier := {g | ∀ x ∈ S, g • x ∈ S}
      one_mem' := fun x hx => by simpa using hx
      mul_mem' := fun {g h} hg hh x hx => by
        rw [mul_smul]
        exact hg _ (hh _ hx) }
  have haT : a ∈ T := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨C.Aa i, (C.edge_a i hi).1, ?_⟩
    exact (actsOn_a C i hi).2
  have hbT : b ∈ T := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨C.Ab i, (C.edge_b i hi).1, ?_⟩
    exact (actsOn_b C i hi).2
  have hcl : ∀ g ∈ Subgroup.closure ({a, b} : Set P), g ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact haT
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact hbT
    | one => exact T.one_mem
    | mul x y _ _ hx hy => exact T.mul_mem hx hy
    | inv x _ hx => exact submonoid_inv_mem T hx
  have h0 : ((1 : P) : P ⧸ R) ∈ S := ⟨0, C.hN0, by rw [C.r_zero]⟩
  have := hcl g (hgen ▸ Subgroup.mem_top g) _ h0
  obtain ⟨i, hi, hgi⟩ := this
  exact ⟨i, hi, by simpa using hgi⟩

theorem cosets_injective [Finite P] (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : ((C.r i : P) : P ⧸ R) = ((C.r j : P) : P ⧸ R)) : i = j := by
  classical
  let f : Fin N → P ⧸ R := fun i => ((C.r i : P) : P ⧸ R)
  have hsurj : Function.Surjective f := fun x => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨i, hi, hgi⟩ := cosets_exhaust C hgen g
    exact ⟨⟨i, hi⟩, hgi.symm⟩
  have : Finite (P ⧸ R) := inferInstance
  have hc : Nat.card (Fin N) = Nat.card (P ⧸ R) := by simp [C.hN]
  have hbij : Function.Bijective f := (Function.Surjective.bijective_of_nat_card_le hsurj hc.le)
  have := hbij.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h
  simpa using this

end Cert

section Reach

inductive Reach (ts : List (Array ℕ)) (s : ℕ) : ℕ → Prop
  | base : Reach ts s s
  | step {i : ℕ} (t : Array ℕ) : t ∈ ts → Reach ts s i → Reach ts s (arrImg t i)

variable {P : Type*} [Group P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem reach_lt (C : CosetCert R a b N) (gs : List (P × Array ℕ))
    (hgs : ∀ p ∈ gs, ActsOn C p.1 (arrImg p.2)) {s : ℕ} (hs : s < N) {i : ℕ}
    (h : Reach (gs.map Prod.snd) s i) : i < N := by
  induction h with
  | base => exact hs
  | step t ht _ ih =>
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    exact (hgs p hp _ ih).1

theorem reach_iff_mem [Finite P] (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) (gs : List (P × Array ℕ))
    (hgs : ∀ p ∈ gs, ActsOn C p.1 (arrImg p.2)) {s : ℕ} (hs : s < N) {i : ℕ} (hi : i < N) :
    Reach (gs.map Prod.snd) s i ↔
      ∃ v ∈ Subgroup.closure {g | g ∈ gs.map Prod.fst},
        ((v * C.r s : P) : P ⧸ R) = ((C.r i : P) : P ⧸ R) := by
  constructor
  · intro h
    induction h with
    | base => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | step t ht hi' ih =>
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
      have hlt := reach_lt C gs hgs hs hi'
      obtain ⟨v, hv, hve⟩ := ih hlt
      refine ⟨p.1 * v, Subgroup.mul_mem _ (Subgroup.subset_closure
        (List.mem_map.2 ⟨p, hp, rfl⟩)) hv, ?_⟩
      have e1 : ((p.1 * v * C.r s : P) : P ⧸ R) = p.1 • ((v * C.r s : P) : P ⧸ R) := by
        rw [mul_assoc]; rfl
      rw [e1, hve]
      exact (hgs p hp _ hlt).2
  · rintro ⟨v, hv, hve⟩
    let T : Submonoid P :=
      { carrier := {v | ∀ j < N, Reach (gs.map Prod.snd) s j → ∃ k < N,
          Reach (gs.map Prod.snd) s k ∧ ((v * C.r j : P) : P ⧸ R) = ((C.r k : P) : P ⧸ R)}
        one_mem' := fun j hj hr => ⟨j, hj, hr, by simp⟩
        mul_mem' := fun {g h} hg hh j hj hr => by
          obtain ⟨k, hk, hrk, hhk⟩ := hh j hj hr
          obtain ⟨l, hl, hrl, hgl⟩ := hg k hk hrk
          refine ⟨l, hl, hrl, ?_⟩
          have e1 : ((g * h * C.r j : P) : P ⧸ R) = g • ((h * C.r j : P) : P ⧸ R) := by
            rw [mul_assoc]; rfl
          rw [e1, hhk]
          exact hgl }
    have hcl : ∀ v ∈ Subgroup.closure {g | g ∈ gs.map Prod.fst}, v ∈ T := by
      intro v hv
      induction hv using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        intro j hj hr
        have hk := reach_lt C gs hgs hs (Reach.step p.2 (List.mem_map.2 ⟨p, hp, rfl⟩) hr)
        exact ⟨arrImg p.2 j, hk, Reach.step p.2 (List.mem_map.2 ⟨p, hp, rfl⟩) hr,
          (hgs p hp j hj).2⟩
      | one => exact T.one_mem
      | mul x y _ _ hx hy => exact T.mul_mem hx hy
      | inv x _ hx => exact submonoid_inv_mem T hx
    obtain ⟨k, hk, hrk, hvk⟩ := hcl v hv s hs Reach.base
    have : k = i := cosets_injective C hgen hk hi (hvk.symm.trans hve)
    rw [← this]
    exact hrk

end Reach

theorem getD_set!_true {vis : Array Bool} {y i : ℕ} (h : (vis.set! y true).getD i false = true) :
    i = y ∨ vis.getD i false = true := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at h
  rw [Array.getD_eq_getD_getElem?]
  by_cases hy : y = i
  · left; exact hy.symm
  · right
    simpa [hy] using h

section BFS

variable (ts : List (Array ℕ)) (s : ℕ)

@[expose] def GoodVis (vis : Array Bool) : Prop := ∀ i, vis.getD i false = true → Reach ts s i

theorem bfsExpand_good (x : ℕ) (hx : Reach ts s x) (vis : Array Bool) (q : List ℕ)
    (hv : GoodVis ts s vis) (hq : ∀ y ∈ q, Reach ts s y) :
    GoodVis ts s (bfsExpand ts x (vis, q)).1 ∧ ∀ y ∈ (bfsExpand ts x (vis, q)).2, Reach ts s y := by
  unfold bfsExpand
  have key : ∀ (l : List (Array ℕ)), (∀ t ∈ l, t ∈ ts) → ∀ (st : Array Bool × List ℕ),
      GoodVis ts s st.1 → (∀ y ∈ st.2, Reach ts s y) →
      GoodVis ts s (l.foldl (fun acc t =>
        let y := arrImg t x
        if acc.1.getD y true then acc else (acc.1.set! y true, y :: acc.2)) st).1 ∧
      ∀ y ∈ (l.foldl (fun acc t =>
        let y := arrImg t x
        if acc.1.getD y true then acc else (acc.1.set! y true, y :: acc.2)) st).2,
        Reach ts s y := by
    intro l
    induction l with
    | nil => intro _ st h1 h2; exact ⟨h1, h2⟩
    | cons t l ih =>
      intro hl st h1 h2
      simp only [List.foldl_cons]
      have htl : t ∈ ts := hl t List.mem_cons_self
      have hl' : ∀ t' ∈ l, t' ∈ ts := fun t' ht' => hl t' (List.mem_cons_of_mem t ht')
      by_cases hy : st.1.getD (arrImg t x) true = true
      · simp only [hy, ite_true]
        exact ih hl' st h1 h2
      · simp only [hy]
        refine ih hl' _ ?_ ?_
        · intro i hi
          rcases getD_set!_true hi with rfl | hi
          · exact Reach.step t htl hx
          · exact h1 i hi
        · intro y hy'
          rcases List.mem_cons.1 hy' with rfl | hy'
          · exact Reach.step t htl hx
          · exact h2 y hy'
  exact key ts (fun t ht => ht) (vis, q) hv hq

theorem bfsAux_good : ∀ (f : ℕ) (vis : Array Bool) (q : List ℕ), GoodVis ts s vis →
    (∀ y ∈ q, Reach ts s y) → GoodVis ts s (bfsAux ts f vis q) := by
  intro f
  induction f with
  | zero => intro vis q hv _; exact hv
  | succ f ih =>
    intro vis q hv hq
    cases q with
    | nil => exact hv
    | cons x q =>
      simp only [bfsAux]
      have := bfsExpand_good ts s x (hq x List.mem_cons_self) vis q hv
        (fun y hy => hq y (List.mem_cons_of_mem x hy))
      exact ih _ _ this.1 this.2

theorem bfsVis_good (N : ℕ) : GoodVis ts s (bfsVis N ts s) := by
  unfold bfsVis
  refine bfsAux_good ts s _ _ _ ?_ ?_
  · intro i hi
    rcases getD_set!_true hi with rfl | hi
    · exact Reach.base
    · simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hi
      by_cases hiN : i < N <;> simp [hiN] at hi
  · intro y hy
    rw [List.mem_singleton] at hy
    rw [hy]; exact Reach.base

theorem reach_mem_of_closed (N : ℕ) (vis : Array Bool) (hc : ClosedOK N ts s vis)
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) {i : ℕ} (h : Reach ts s i) (hs : s < N) :
    i < N ∧ vis.getD i false = true := by
  induction h with
  | base => exact ⟨hs, hc.1⟩
  | step t ht _ ih => exact ⟨htab t ht _ ih.1, hc.2 _ ih.1 ih.2 t ht⟩

theorem bfsVis_iff (N : ℕ) (hc : ClosedOK N ts s (bfsVis N ts s))
    (htab : ∀ t ∈ ts, ∀ i < N, arrImg t i < N) (hs : s < N) (i : ℕ) :
    (i < N ∧ (bfsVis N ts s).getD i false = true) ↔ Reach ts s i :=
  ⟨fun h => bfsVis_good ts s N i h.2, fun h => reach_mem_of_closed ts s N _ hc htab h hs⟩

end BFS

section Blocks

variable {P : Type*} [Group P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem mem_iff_of_coset_eq {V : Subgroup P} (hRV : R ≤ V) {x y : P}
    (h : ((x : P) : P ⧸ R) = ((y : P) : P ⧸ R)) : x ∈ V ↔ y ∈ V := by
  have h1 : y⁻¹ * x ∈ V := hRV (mem_of_coset_eq h)
  constructor
  · intro hx
    have : y = x * (y⁻¹ * x)⁻¹ := by group
    rw [this]
    exact V.mul_mem hx (V.inv_mem h1)
  · intro hy
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact V.mul_mem hy h1

theorem eq_of_blocks [Finite P] (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) {V W : Subgroup P} (hV : R ≤ V) (hW : R ≤ W)
    (h : ∀ i < N, C.r i ∈ V ↔ C.r i ∈ W) : V = W := by
  have key : ∀ {V W : Subgroup P}, R ≤ V → R ≤ W → (∀ i < N, C.r i ∈ V → C.r i ∈ W) → V ≤ W := by
    intro V W hV hW h g hg
    obtain ⟨i, hi, hgi⟩ := cosets_exhaust C hgen g
    have h1 : C.r i ∈ V := (mem_iff_of_coset_eq hV hgi).1 hg
    exact (mem_iff_of_coset_eq hW hgi).2 (h i hi h1)
  exact le_antisymm (key hV hW fun i hi => (h i hi).1) (key hW hV fun i hi => (h i hi).2)

theorem reach_zero_iff_mem [Finite P] (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) (gs : List (P × Array ℕ))
    (hgs : ∀ p ∈ gs, ActsOn C p.1 (arrImg p.2))
    (hRV : R ≤ Subgroup.closure {g | g ∈ gs.map Prod.fst}) {i : ℕ} (hi : i < N) :
    Reach (gs.map Prod.snd) 0 i ↔ C.r i ∈ Subgroup.closure {g | g ∈ gs.map Prod.fst} := by
  rw [reach_iff_mem C hgen gs hgs C.hN0 hi]
  constructor
  · rintro ⟨v, hv, hve⟩
    rw [C.r_zero, mul_one] at hve
    exact (mem_iff_of_coset_eq hRV hve).1 hv
  · intro h
    refine ⟨C.r i, h, ?_⟩
    rw [C.r_zero, mul_one]

theorem closure_union_closure (S T : Set P) :
    Subgroup.closure ((Subgroup.closure S : Set P) ∪ T) = Subgroup.closure (S ∪ T) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.closure_mono Set.subset_union_left hx
    · exact Subgroup.subset_closure (Set.mem_union_right _ hx)
  · exact Subgroup.closure_mono (Set.union_subset_union_left _ Subgroup.subset_closure)

theorem exists_eq_of_closed [Finite P] {R : Subgroup P} {m : ℕ} (V : Fin m → Subgroup P)
    (h0 : ∃ h, V h = R)
    (hcl : ∀ (h : Fin m) (g : P), ∃ k, Subgroup.closure ((V h : Set P) ∪ {g}) = V k) :
    ∀ W : Subgroup P, R ≤ W → ∃ h, W = V h := by
  classical
  intro W hRW
  obtain ⟨h0, hh0⟩ := h0
  have hfin : ∀ s : Finset P, (↑s : Set P) ⊆ W → ∃ h, Subgroup.closure ((R : Set P) ∪ ↑s) = V h := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨h0, ?_⟩
      rw [hh0]
      simp
    | insert g s hg ih =>
      intro hs
      obtain ⟨h, hh⟩ := ih (fun x hx => hs (by simp [hx]))
      obtain ⟨k, hk⟩ := hcl h g
      refine ⟨k, ?_⟩
      rw [← hk, ← hh, closure_union_closure]
      congr 1
      ext x
      simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        SetLike.mem_coe]
      tauto
  have hWfin : Set.Finite (W : Set P) := Set.toFinite _
  obtain ⟨h, hh⟩ := hfin hWfin.toFinset (by simp)
  refine ⟨h, ?_⟩
  rw [← hh]
  apply le_antisymm
  · intro x hx
    exact Subgroup.subset_closure (Set.mem_union_right _ (by simpa using hx))
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact hRW hx
    · simpa using hx

end Blocks

section Inventory

variable {P : Type*} [Group P] [Finite P] {R : Subgroup P} {a b : P} {N : ℕ}

omit [Finite P] in
theorem tabs_lt_of_actsOn (C : CosetCert R a b N) {gs : List (P × Array ℕ)}
    (hgs : ∀ p ∈ gs, ActsOn C p.1 (arrImg p.2)) :
    ∀ t ∈ gs.map Prod.snd, ∀ i < N, arrImg t i < N := by
  intro t ht i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  exact (hgs p hp i hi).1

theorem block_iff (C : CosetCert R a b N) (hgen : Subgroup.closure ({a, b} : Set P) = ⊤)
    (gs : List (P × Array ℕ)) (hgs : ∀ p ∈ gs, ActsOn C p.1 (arrImg p.2))
    (hRV : R ≤ Subgroup.closure {g | g ∈ gs.map Prod.fst}) (vis : Array Bool)
    (hvis : vis = bfsVis N (gs.map Prod.snd) 0) (hc : ClosedOK N (gs.map Prod.snd) 0 vis)
    {i : ℕ} (hi : i < N) :
    vis.getD i false = true ↔ C.r i ∈ Subgroup.closure {g | g ∈ gs.map Prod.fst} := by
  rw [← reach_zero_iff_mem C hgen gs hgs hRV hi, ← bfsVis_iff (gs.map Prod.snd) 0 N
    (hvis ▸ hc) (tabs_lt_of_actsOn C hgs) C.hN0 i, hvis]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

omit [Finite P] in
theorem closure_adjoin_eq_of_mul {V : Subgroup P} {g x ρ ρ₁ : P} (hρ : ρ ∈ V) (hρ₁ : ρ₁ ∈ V)
    (h : g = ρ * x * ρ₁) :
    Subgroup.closure ((V : Set P) ∪ {g}) = Subgroup.closure ((V : Set P) ∪ {x}) := by
  have h1 : ∀ {y z : P} {ρ ρ₁ : P}, ρ ∈ V → ρ₁ ∈ V → y = ρ * z * ρ₁ →
      y ∈ Subgroup.closure ((V : Set P) ∪ {z}) := by
    intro y z ρ ρ₁ hρ hρ₁ hy
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_union_left _ hρ))
      (Subgroup.subset_closure (Set.mem_union_right _ rfl)))
      (Subgroup.subset_closure (Set.mem_union_left _ hρ₁))
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · exact Subgroup.subset_closure (Set.mem_union_left _ hy)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h1 hρ hρ₁ h
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · exact Subgroup.subset_closure (Set.mem_union_left _ hy)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine h1 (V.inv_mem hρ) (V.inv_mem hρ₁) ?_
      rw [h]; group

theorem inventory_exhaustive (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤)
    (gsR : List (P × Array ℕ)) (hR : Subgroup.closure {g | g ∈ gsR.map Prod.fst} = R)
    (hgsR : ∀ p ∈ gsR, ActsOn C p.1 (arrImg p.2))
    {m : ℕ} (gens : Fin m → List (P × Array ℕ))
    (hgs : ∀ h, ∀ p ∈ gens h, ActsOn C p.1 (arrImg p.2))
    (hsub : ∀ h, ∀ p ∈ gsR, p ∈ gens h) (h0 : ∃ h, gens h = gsR)
    (blocks : Fin m → Array Bool)
    (hbl : ∀ h, blocks h = bfsVis N ((gens h).map Prod.snd) 0 ∧
      ClosedOK N ((gens h).map Prod.snd) 0 (blocks h))
    (repR : ℕ → ℕ) (hrepR : ∀ i < N, repR i < N ∧ Reach (gsR.map Prod.snd) (repR i) i)
    (reps : List ℕ) (hreps : ∀ i < N, repR i ∈ reps)
    (ox : ℕ → Array ℕ) (hox : ∀ x < N, ActsOn C (C.r x) (arrImg (ox x)))
    (hcl : ∀ (h : Fin m), ∀ x ∈ reps, x < N → ∃ k : Fin m,
      bfsVis N (((gens h) ++ [(C.r x, ox x)]).map Prod.snd) 0 = blocks k ∧
      ClosedOK N (((gens h) ++ [(C.r x, ox x)]).map Prod.snd) 0 (blocks k)) :
    ∀ W : Subgroup P, R ≤ W →
      ∃ h : Fin m, W = Subgroup.closure {g | g ∈ (gens h).map Prod.fst} := by
  let V : Fin m → Subgroup P := fun h => Subgroup.closure {g | g ∈ (gens h).map Prod.fst}
  have hRV : ∀ h, R ≤ V h := by
    intro h
    rw [← hR]
    apply Subgroup.closure_mono
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact List.mem_map.2 ⟨p, hsub h p hp, rfl⟩
  have hV0 : ∃ h, V h = R := by
    obtain ⟨h, hh⟩ := h0
    exact ⟨h, by simp only [V, hh, hR]⟩
  have hcl' : ∀ (h : Fin m) (g : P), ∃ k, Subgroup.closure ((V h : Set P) ∪ {g}) = V k := by
    intro h g
    obtain ⟨i, hi, hgi⟩ := cosets_exhaust C hgen g
    obtain ⟨hx, hreach⟩ := hrepR i hi
    obtain ⟨ρ, hρ, hρe⟩ := (reach_iff_mem C hgen gsR hgsR hx hi).1 hreach
    rw [hR] at hρ
    have hρV : ρ ∈ V h := hRV h hρ
    have hg1 : (ρ * C.r (repR i))⁻¹ * g ∈ V h :=
      hRV h (mem_of_coset_eq (hgi.trans hρe.symm))
    obtain ⟨k, hk0, hk1⟩ := hcl h (repR i) (hreps i hi) hx
    refine ⟨k, ?_⟩
    rw [closure_adjoin_eq_of_mul hρV hg1 (x := C.r (repR i)) (by group)]
    set x := repR i with hxdef
    set gens' : List (P × Array ℕ) := (gens h) ++ [(C.r x, ox x)] with hgens'
    have hgs' : ∀ p ∈ gens', ActsOn C p.1 (arrImg p.2) := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hgs h p hp
      · rw [List.mem_singleton] at hp
        rw [hp]; exact hox x hx
    have hW' : Subgroup.closure ((V h : Set P) ∪ {C.r x}) =
        Subgroup.closure {g | g ∈ gens'.map Prod.fst} := by
      rw [closure_union_closure]
      congr 1
      ext y
      simp [hgens', List.map_append, or_comm]
    have hRW' : R ≤ Subgroup.closure {g | g ∈ gens'.map Prod.fst} := by
      rw [← hW']
      exact le_trans (hRV h) (fun y hy => Subgroup.subset_closure (Set.mem_union_left _ hy))
    rw [hW']
    refine eq_of_blocks C hgen hRW' (hRV k) fun j hj => ?_
    rw [← block_iff C hgen gens' hgs' hRW' _ rfl (hk0 ▸ hk1) hj,
      ← block_iff C hgen (gens k) (hgs k) (hRV k) _ (hbl k).1 (hbl k).2 hj, hk0]
  exact exists_eq_of_closed V hV0 hcl'

end Inventory

end CFSG.QuasithinUnique.Setup.X1
