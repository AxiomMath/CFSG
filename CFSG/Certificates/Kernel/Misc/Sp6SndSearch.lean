module

public import CFSG.Certificates.Kernel.Misc.Sp6SndCode
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataSylow

public section

namespace CFSG.KC.Misc.Sp6.Snd

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O62 CFSG.KC.Misc.Sp6
open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

@[expose] def reach (G : List (List ℕ)) : ℕ → List ℕ → Prop
  | 0, x => x = idT
  | n + 1, x => reach G n x ∨ ∃ y, reach G n y ∧ ∃ g ∈ G, x = compT y g

private theorem foldl_spec {α X : Type} (f : List X → α → List X) (R : α → List X → Prop)
    (I : List X → Prop) (hmono : ∀ a acc acc', (∀ q ∈ acc, q ∈ acc') → R a acc → R a acc') :
    ∀ (l : List α) (acc : List X),
      (∀ a ∈ l, ∀ acc, I acc → I (f acc a) ∧ (∀ q ∈ acc, q ∈ f acc a) ∧ R a (f acc a)) → I acc →
      I (l.foldl f acc) ∧ (∀ q ∈ acc, q ∈ l.foldl f acc) ∧ ∀ a ∈ l, R a (l.foldl f acc) := by
  intro l
  induction l with
  | nil => intro acc _ hI; exact ⟨hI, fun q hq => hq, by simp⟩
  | cons a l ih =>
    intro acc hstep hI
    obtain ⟨h1, h2, h3⟩ := hstep a List.mem_cons_self acc hI
    obtain ⟨i1, i2, i3⟩ := ih (f acc a) (fun b hb => hstep b (List.mem_cons_of_mem _ hb)) h1
    rw [List.foldl_cons]
    refine ⟨i1, fun q hq => i2 q (h2 q hq), ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hmono _ _ _ i2 h3
    · exact i3 b hb

private theorem reach_idT (G : List (List ℕ)) : ∀ j, reach G j idT := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => exact Or.inl ih

private def bfsStep (gens : List (List ℕ)) (known : List (List ℕ × List ℕ)) (p : List ℕ × List ℕ)
    (acc : List (List ℕ × List ℕ)) (i : ℕ) : List (List ℕ × List ℕ) :=
  let y := compT p.1 (gens.getD i [])
  if (known.any fun q => q.1 == y) || (acc.any fun q => q.1 == y) then acc
  else acc ++ [(y, p.2 ++ [i])]

private def bfsNew (gens : List (List ℕ)) (known fr : List (List ℕ × List ℕ)) :
    List (List ℕ × List ℕ) :=
  fr.foldl (fun acc p => (List.range gens.length).foldl (bfsStep gens known p) acc) []

private theorem bfsAux_succ (gens : List (List ℕ)) (n : ℕ) (known fr : List (List ℕ × List ℕ)) :
    bfsAux gens (n + 1) known fr = if (bfsNew gens known fr).isEmpty then known
      else bfsAux gens n (known ++ bfsNew gens known fr) (bfsNew gens known fr) := rfl

private theorem getD_mem {gens : List (List ℕ)} {i : ℕ} (h : i < gens.length) :
    gens.getD i [] ∈ gens := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

private theorem mem_idx {gens : List (List ℕ)} {g : List ℕ} (h : g ∈ gens) :
    ∃ i ∈ List.range gens.length, gens.getD i [] = g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

private theorem bfsNew_spec (gens : List (List ℕ)) (known fr : List (List ℕ × List ℕ)) :
    ((bfsNew gens known fr).map Prod.fst).Nodup ∧
    (∀ q ∈ bfsNew gens known fr, q.1 ∉ known.map Prod.fst) ∧
    (∀ q ∈ bfsNew gens known fr, ∃ p ∈ fr, ∃ g ∈ gens, q.1 = compT p.1 g) ∧
    (∀ p ∈ fr, ∀ g ∈ gens, compT p.1 g ∈ known.map Prod.fst ∨
      compT p.1 g ∈ (bfsNew gens known fr).map Prod.fst) := by
  let I : List (List ℕ × List ℕ) → Prop := fun acc => (acc.map Prod.fst).Nodup ∧
    (∀ q ∈ acc, q.1 ∉ known.map Prod.fst) ∧ ∀ q ∈ acc, ∃ p ∈ fr, ∃ g ∈ gens, q.1 = compT p.1 g
  let Cov : List ℕ → List (List ℕ × List ℕ) → Prop := fun y acc =>
    y ∈ known.map Prod.fst ∨ y ∈ acc.map Prod.fst
  have hCovmono : ∀ y acc acc', (∀ q ∈ acc, q ∈ acc') → Cov y acc → Cov y acc' := by
    intro y acc acc' h hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      exact Or.inr (List.mem_map.mpr ⟨q, h q hq, rfl⟩)
  have inner : ∀ p ∈ fr, ∀ acc, I acc →
      I ((List.range gens.length).foldl (bfsStep gens known p) acc) ∧
      (∀ q ∈ acc, q ∈ (List.range gens.length).foldl (bfsStep gens known p) acc) ∧
      ∀ g ∈ gens, Cov (compT p.1 g) ((List.range gens.length).foldl (bfsStep gens known p) acc) := by
    intro p hp acc hI
    have hstep : ∀ i ∈ List.range gens.length, ∀ acc, I acc →
        I (bfsStep gens known p acc i) ∧ (∀ q ∈ acc, q ∈ bfsStep gens known p acc i) ∧
          Cov (compT p.1 (gens.getD i [])) (bfsStep gens known p acc i) := by
      intro i hi acc hI
      have hig := getD_mem (List.mem_range.mp hi)
      unfold bfsStep
      by_cases h : ((known.any fun q => q.1 == compT p.1 (gens.getD i [])) ||
          (acc.any fun q => q.1 == compT p.1 (gens.getD i []))) = true
      · rw [if_pos h]
        refine ⟨hI, fun q hq => hq, ?_⟩
        simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
        rcases h with ⟨q, hq, hqe⟩ | ⟨q, hq, hqe⟩
        · exact Or.inl (List.mem_map.mpr ⟨q, hq, hqe⟩)
        · exact Or.inr (List.mem_map.mpr ⟨q, hq, hqe⟩)
      · rw [if_neg h]
        simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, not_or, not_exists, not_and] at h
        obtain ⟨hk, ha⟩ := h
        obtain ⟨n1, n2, n3⟩ := hI
        refine ⟨⟨?_, ?_, ?_⟩, fun q hq => List.mem_append_left _ hq, ?_⟩
        · rw [List.map_append, List.nodup_append]
          refine ⟨n1, by simp, ?_⟩
          intro a ha' b hb
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          subst hb
          exact fun e => ha q hq e
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact n2 q hq
          · simp only [List.mem_singleton] at hq
            subst hq
            intro hm
            obtain ⟨q', hq', e⟩ := List.mem_map.mp hm
            exact hk q' hq' e
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact n3 q hq
          · simp only [List.mem_singleton] at hq
            subst hq
            exact ⟨p, hp, _, hig, rfl⟩
        · right
          simp

    obtain ⟨h1, h2, h3⟩ := foldl_spec (bfsStep gens known p)
      (fun i acc => Cov (compT p.1 (gens.getD i [])) acc) I
      (fun i acc acc' h => hCovmono _ _ _ h) (List.range gens.length) acc hstep hI
    refine ⟨h1, h2, fun g hg => ?_⟩
    obtain ⟨i, hi, rfl⟩ := mem_idx hg
    exact h3 i hi
  have outer := foldl_spec (X := List ℕ × List ℕ) (α := List ℕ × List ℕ)
    (fun acc p => (List.range gens.length).foldl (bfsStep gens known p) acc)
    (fun p acc => ∀ g ∈ gens, Cov (compT p.1 g) acc) I
    (fun p acc acc' h hp g hg => hCovmono _ _ _ h (hp g hg)) fr [] (by
      intro p hp acc hI
      exact inner p hp acc hI) ⟨by simp, by simp, by simp⟩
  obtain ⟨⟨o1, o2, o3⟩, -, o4⟩ := outer
  exact ⟨o1, o2, o3, fun p hp g hg => o4 p hp g hg⟩

theorem pListG_nodup (G : List (List ℕ)) : ((bfsAux G 40 [(idT, [])] [(idT, [])]).map Prod.fst).Nodup := by
  have key : ∀ n (known fr : List (List ℕ × List ℕ)), (known.map Prod.fst).Nodup →
      ((bfsAux G n known fr).map Prod.fst).Nodup := by
    intro n
    induction n with
    | zero => intro known fr h; exact h
    | succ n ih =>
      intro known fr h
      rw [bfsAux_succ]
      obtain ⟨n1, n2, -, -⟩ := bfsNew_spec G known fr
      split_ifs
      · exact h
      · apply ih
        rw [List.map_append, List.nodup_append]
        refine ⟨h, n1, ?_⟩
        intro a ha b hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
        intro e
        exact n2 q hq (e ▸ ha)
  exact key _ _ _ (by simp)

theorem pListG_sound (G : List (List ℕ)) (S : List ℕ → Prop) (hid : S idT)
    (hcl : ∀ x, S x → ∀ g ∈ G, S (compT x g)) : ∀ x ∈ (bfsAux G 40 [(idT, [])] [(idT, [])]).map Prod.fst, S x := by
  have key : ∀ n (known fr : List (List ℕ × List ℕ)), (∀ q ∈ known, S q.1) → (∀ q ∈ fr, S q.1) →
      ∀ q ∈ bfsAux G n known fr, S q.1 := by
    intro n
    induction n with
    | zero => intro known fr h _; exact h
    | succ n ih =>
      intro known fr h hf
      rw [bfsAux_succ]
      obtain ⟨-, -, n3, -⟩ := bfsNew_spec G known fr
      have hnew : ∀ q ∈ bfsNew G known fr, S q.1 := by
        intro q hq
        obtain ⟨p, hp, g, hg, e⟩ := n3 q hq
        rw [e]
        exact hcl _ (hf p hp) g hg
      split_ifs
      · exact h
      · apply ih
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact h q hq
          · exact hnew q hq
        · exact hnew
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact key _ _ _ (by simpa using hid) (by simpa using hid) q hq

private theorem bfsAux_complete (G : List (List ℕ)) : ∀ n j (K F : List (List ℕ × List ℕ)),
    (∀ x, reach G j x → x ∈ K.map Prod.fst) →
    (∀ q ∈ K, q ∉ F → ∀ g ∈ G, compT q.1 g ∈ K.map Prod.fst) → (∀ q ∈ F, q ∈ K) →
    ∀ x, reach G (j + n) x → x ∈ (bfsAux G n K F).map Prod.fst := by
  intro n
  induction n with
  | zero => intro j K F h1 _ _ x hx; exact h1 x hx
  | succ n ih =>
    intro j K F h1 h2 h3 x hx
    rw [bfsAux_succ]
    obtain ⟨-, -, -, n4⟩ := bfsNew_spec G K F
    have hstep : ∀ q ∈ K, ∀ g ∈ G, compT q.1 g ∈ K.map Prod.fst ∨
        compT q.1 g ∈ (bfsNew G K F).map Prod.fst := by
      intro q hq g hg
      by_cases hqF : q ∈ F
      · exact n4 q hqF g hg
      · exact Or.inl (h2 q hq hqF g hg)
    split_ifs with hne
    · have hnil : bfsNew G K F = [] := List.isEmpty_iff.mp hne
      have hcl : ∀ q ∈ K, ∀ g ∈ G, compT q.1 g ∈ K.map Prod.fst := by
        intro q hq g hg
        rcases hstep q hq g hg with h | h
        · exact h
        · rw [hnil] at h; simp at h
      have hk : ∀ k x, reach G k x → x ∈ K.map Prod.fst := by
        intro k
        induction k with
        | zero => intro x hx; exact h1 x (by rw [show x = idT from hx]; exact reach_idT G j)
        | succ k ihk =>
          intro x hx
          rcases hx with hx | ⟨y, hy, g, hg, rfl⟩
          · exact ihk x hx
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (ihk y hy)
            exact hcl q hq g hg
      exact hk _ x hx
    · apply ih (j + 1) (K ++ bfsNew G K F) (bfsNew G K F) _ _ (fun q hq => List.mem_append_right _ hq)
        x (by rwa [show j + 1 + n = j + (n + 1) by omega])
      · intro x hx
        rcases hx with hx | ⟨y, hy, g, hg, rfl⟩
        · rw [List.map_append]; exact List.mem_append_left _ (h1 x hx)
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (h1 y hy)
          rw [List.map_append]
          rcases hstep q hq g hg with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ h
      · intro q hq hqn g hg
        have hqK : q ∈ K := by
          rcases List.mem_append.mp hq with h | h
          · exact h
          · exact absurd h hqn
        rw [List.map_append]
        rcases hstep q hqK g hg with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ h

theorem pListG_complete (G : List (List ℕ)) {x : List ℕ} (h : reach G 40 x) : x ∈ (bfsAux G 40 [(idT, [])] [(idT, [])]).map Prod.fst := by
  refine bfsAux_complete G 40 0 _ _ ?_ ?_ ?_ x (by rwa [Nat.zero_add])
  · intro x hx
    rw [show x = idT from hx]
    simp
  · intro q hq hqF
    exact absurd (by simpa using hq) (by simpa using hqF)
  · intro q hq; exact hq

@[expose] def IsEA (P A : List (List ℕ)) : Prop :=
  idT ∈ A ∧ (∀ a ∈ A, a ∈ P) ∧ (∀ a ∈ A, ∀ b ∈ A, compT a b ∈ A) ∧
    (∀ a ∈ A, compT a a = idT) ∧ (∀ a ∈ A, ∀ b ∈ A, compT a b = compT b a) ∧
    (A.map codeT).Pairwise (· < ·)

private theorem insCode_mem (a : List ℕ) : ∀ (l : List (List ℕ)) (c : List ℕ),
    c ∈ insCode a l → c = a ∨ c ∈ l := by
  intro l
  induction l with
  | nil => intro c hc; simpa [insCode] using hc
  | cons b l ih =>
    intro c hc
    unfold insCode at hc
    split_ifs at hc with h1 h2
    · simp only [List.mem_cons] at hc ⊢; tauto
    · simp only [List.mem_cons] at hc ⊢; tauto
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inr List.mem_cons_self
      · rcases ih c hc with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem insCode_sorted (a : List ℕ) : ∀ l : List (List ℕ), (l.map codeT).Pairwise (· < ·) →
    ((insCode a l).map codeT).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; simp [insCode]
  | cons b l ih =>
    intro h
    rw [List.map_cons, List.pairwise_cons] at h
    unfold insCode
    split_ifs with h1 h2
    · rw [List.map_cons, List.map_cons, List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, h.1, h.2⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1
      · exact lt_trans h1 (h.1 y hy)
    · rw [List.map_cons, List.pairwise_cons]; exact h
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih h.2⟩
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      rcases insCode_mem a l c hc with rfl | hc
      · omega
      · exact h.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

private theorem insCode_cover (a : List ℕ) : ∀ (l : List (List ℕ)), ∀ e ∈ a :: l,
    ∃ c ∈ insCode a l, codeT c = codeT e := by
  intro l
  induction l with
  | nil => intro e he; simp at he; subst he; exact ⟨e, by simp [insCode], rfl⟩
  | cons b l ih =>
    intro e he
    unfold insCode
    split_ifs with h1 h2
    · refine ⟨e, ?_, rfl⟩
      simpa using he
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨b, List.mem_cons_self, h2.symm⟩
      · exact ⟨e, he, rfl⟩
    · rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨c, hc, hce⟩ := ih e (List.mem_cons_self)
        exact ⟨c, List.mem_cons_of_mem _ hc, hce⟩
      · rcases List.mem_cons.mp he with rfl | he
        · exact ⟨e, List.mem_cons_self, rfl⟩
        · obtain ⟨c, hc, hce⟩ := ih e (List.mem_cons_of_mem _ he)
          exact ⟨c, List.mem_cons_of_mem _ hc, hce⟩

private theorem foldr_insCode_spec : ∀ L : List (List ℕ),
    ((L.foldr insCode []).map codeT).Pairwise (· < ·) ∧ (∀ c ∈ L.foldr insCode [], c ∈ L) ∧
    ∀ e ∈ L, ∃ c ∈ L.foldr insCode [], codeT c = codeT e := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    rw [List.foldr_cons]
    refine ⟨insCode_sorted a _ i1, ?_, ?_⟩
    · intro c hc
      rcases insCode_mem a _ c hc with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (i2 c h)
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact insCode_cover e _ e List.mem_cons_self
      · obtain ⟨c', hc', hce⟩ := i3 e he
        obtain ⟨c, hc, hce'⟩ := insCode_cover a _ c' (List.mem_cons_of_mem _ hc')
        exact ⟨c, hc, hce'.trans hce⟩

theorem adjoin_sorted (x : List ℕ) (A : List (List ℕ)) :
    ((adjoin x A).map codeT).Pairwise (· < ·) :=
  (foldr_insCode_spec _).1

theorem mem_adjoin {x : List ℕ} {A : List (List ℕ)} (hx : IsTup x) (hA : ∀ a ∈ A, IsTup a)
    (c : List ℕ) : c ∈ adjoin x A ↔ c ∈ A ∨ ∃ a ∈ A, c = compT x a := by
  have hT : ∀ b ∈ A ++ A.map (compT x), IsTup b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hA b hb
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact compT_tup hx.2 (hA a ha)
  obtain ⟨i1, i2, i3⟩ := foldr_insCode_spec (A ++ A.map (compT x))
  constructor
  · intro h
    have := i2 c h
    rcases List.mem_append.mp this with h | h
    · exact Or.inl h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨a, ha, rfl⟩
  · intro h
    have hc : c ∈ A ++ A.map (compT x) := by
      rcases h with h | ⟨a, ha, rfl⟩
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
    obtain ⟨c', hc', e⟩ := i3 c hc
    have : c' = c := by
      apply codeL_inj (hT c' (i2 c' hc')) (hT c hc)
      rw [codeL_eq_codeT, codeL_eq_codeT, e]
    rwa [this] at hc'

private def eaStep (P : List (List ℕ)) (K : List (List (List ℕ))) (A : List (List ℕ))
    (acc : List (List (List ℕ))) (x : List ℕ) : List (List (List ℕ)) :=
  let B := adjoin x A
  if K.contains B || acc.contains B then acc else acc ++ [B]

private def eaNew (P : List (List ℕ)) (K F : List (List (List ℕ))) : List (List (List ℕ)) :=
  F.foldl (fun acc A => (extenders P A).foldl (eaStep P K A) acc) []

private theorem eaClose_succ (P : List (List ℕ)) (n : ℕ) (K F : List (List (List ℕ))) :
    eaClose P (n + 1) K F = if (eaNew P K F).isEmpty then K
      else eaClose P n (K ++ eaNew P K F) (eaNew P K F) := rfl

private theorem eaNew_spec (P : List (List ℕ)) (K F : List (List (List ℕ))) :
    (∀ B ∈ eaNew P K F, ∃ A ∈ F, ∃ x ∈ extenders P A, B = adjoin x A) ∧
    (∀ A ∈ F, ∀ x ∈ extenders P A, adjoin x A ∈ K ∨ adjoin x A ∈ eaNew P K F) := by
  let I : List (List (List ℕ)) → Prop := fun acc => ∀ B ∈ acc, ∃ A ∈ F, ∃ x ∈ extenders P A, B = adjoin x A
  let Cov : List (List ℕ) → List (List (List ℕ)) → Prop := fun B acc => B ∈ K ∨ B ∈ acc
  have hCovmono : ∀ B acc acc', (∀ q ∈ acc, q ∈ acc') → Cov B acc → Cov B acc' := by
    intro B acc acc' h hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (h B hy)
  have inner : ∀ A ∈ F, ∀ acc, I acc →
      I ((extenders P A).foldl (eaStep P K A) acc) ∧
      (∀ q ∈ acc, q ∈ (extenders P A).foldl (eaStep P K A) acc) ∧
      ∀ x ∈ extenders P A, Cov (adjoin x A) ((extenders P A).foldl (eaStep P K A) acc) := by
    intro A hA acc hI
    have hstep : ∀ x ∈ extenders P A, ∀ acc, I acc →
        I (eaStep P K A acc x) ∧ (∀ q ∈ acc, q ∈ eaStep P K A acc x) ∧
          Cov (adjoin x A) (eaStep P K A acc x) := by
      intro x hx acc hI
      unfold eaStep
      by_cases h : (K.contains (adjoin x A) || acc.contains (adjoin x A)) = true
      · rw [if_pos h]
        refine ⟨hI, fun q hq => hq, ?_⟩
        simpa [Bool.or_eq_true, List.contains_iff_mem] using h
      · rw [if_neg h]
        refine ⟨?_, fun q hq => List.mem_append_left _ hq, Or.inr (by simp)⟩
        intro B hB
        rcases List.mem_append.mp hB with hB | hB
        · exact hI B hB
        · simp only [List.mem_singleton] at hB
          subst hB
          exact ⟨A, hA, x, hx, rfl⟩
    obtain ⟨h1, h2, h3⟩ := foldl_spec (eaStep P K A) (fun x acc => Cov (adjoin x A) acc) I
      (fun x acc acc' h => hCovmono _ _ _ h) (extenders P A) acc hstep hI
    exact ⟨h1, h2, h3⟩
  have outer := foldl_spec (X := List (List ℕ)) (α := List (List ℕ))
    (fun acc A => (extenders P A).foldl (eaStep P K A) acc)
    (fun A acc => ∀ x ∈ extenders P A, Cov (adjoin x A) acc) I
    (fun A acc acc' h hp x hx => hCovmono _ _ _ h (hp x hx)) F [] (by
      intro A hA acc hI
      exact inner A hA acc hI) (by simp [I])
  obtain ⟨o1, -, o4⟩ := outer
  exact ⟨o1, fun A hA x hx => o4 A hA x hx⟩

theorem eaClose_induct (P : List (List ℕ)) (Q : List (List ℕ) → Prop)
    (hQ : ∀ A, Q A → ∀ x ∈ extenders P A, Q (adjoin x A)) :
    ∀ n K F, (∀ A ∈ K, Q A) → (∀ A ∈ F, A ∈ K) → ∀ A ∈ eaClose P n K F, Q A := by
  intro n
  induction n with
  | zero => intro K F hK _ A hA; exact hK A hA
  | succ n ih =>
    intro K F hK hF A hA
    rw [eaClose_succ] at hA
    obtain ⟨e1, -⟩ := eaNew_spec P K F
    have hnew : ∀ B ∈ eaNew P K F, Q B := by
      intro B hB
      obtain ⟨A', hA', x, hx, rfl⟩ := e1 B hB
      exact hQ A' (hK A' (hF A' hA')) x hx
    split_ifs at hA
    · exact hK A hA
    · refine ih _ _ ?_ (fun B hB => List.mem_append_right _ hB) A hA
      intro B hB
      rcases List.mem_append.mp hB with h | h
      · exact hK B h
      · exact hnew B h

theorem mem_eaClose_of_mem (P : List (List ℕ)) :
    ∀ n K F, ∀ A ∈ K, A ∈ eaClose P n K F := by
  intro n
  induction n with
  | zero => intro K F A hA; exact hA
  | succ n ih =>
    intro K F A hA
    rw [eaClose_succ]
    split_ifs
    · exact hA
    · exact ih _ _ A (List.mem_append_left _ hA)

private theorem mem_extenders {P A : List (List ℕ)} {x : List ℕ} :
    x ∈ extenders P A ↔ x ∈ P ∧ (compT x x = idT ∧ x ≠ idT) ∧ x ∉ A ∧
      ∀ a ∈ A, compT x a = compT a x := by
  simp [extenders, isInvT, List.contains_iff_mem, and_assoc]

private theorem isEA_length_le {P A : List (List ℕ)} (hA : IsEA P A) : A.length ≤ P.length := by
  have h1 : (A.map codeT).Nodup := hA.2.2.2.2.2.imp fun h => Nat.ne_of_lt h
  exact (List.subperm_of_subset (List.Nodup.of_map _ h1) hA.2.1).length_le

section

variable {P : List (List ℕ)} (hT : ∀ a ∈ P, IsTup a) (hcl : ∀ a ∈ P, ∀ b ∈ P, compT a b ∈ P)
include hT hcl

theorem isEA_adjoin {A : List (List ℕ)} {x : List ℕ} (hA : IsEA P A) (hx : x ∈ extenders P A) :
    IsEA P (adjoin x A) := by
  have hAt : ∀ a ∈ A, IsTup a := fun a ha => hT a (hA.2.1 a ha)
  obtain ⟨hid, hsub, hclA, hsq, hcomm, hsort⟩ := hA
  obtain ⟨hxP, ⟨hxx, hxne⟩, hxA, hxc⟩ := mem_extenders.mp hx
  have hxt := hT x hxP
  have hm : ∀ c, c ∈ adjoin x A ↔ c ∈ A ∨ ∃ a ∈ A, c = compT x a := mem_adjoin hxt hAt
  have tupc : ∀ a ∈ A, ∀ b ∈ A, IsTup (compT a b) := fun a ha b hb => compT_tup (hAt a ha).2 (hAt b hb)
  have e1 : ∀ a ∈ A, ∀ b ∈ A, compT (compT x a) b = compT x (compT a b) :=
    fun a _ b _ => compT_assoc x a b
  have e2 : ∀ a ∈ A, ∀ b ∈ A, compT a (compT x b) = compT x (compT a b) := by
    intro a ha b hb
    rw [← compT_assoc, ← hxc a ha, compT_assoc]
  have e3 : ∀ a ∈ A, ∀ b ∈ A, compT (compT x a) (compT x b) = compT a b := by
    intro a ha b hb
    rw [compT_assoc, e2 a ha b hb, ← compT_assoc, hxx, idT_compT (tupc a ha b hb)]
  refine ⟨(hm _).mpr (Or.inl hid), ?_, ?_, ?_, ?_, adjoin_sorted x A⟩
  · intro c hc
    rcases (hm c).mp hc with h | ⟨a, ha, rfl⟩
    · exact hsub c h
    · exact hcl x hxP a (hsub a ha)
  · intro a ha b hb
    rw [hm] at ha hb ⊢
    rcases ha with ha | ⟨a', ha', rfl⟩ <;> rcases hb with hb | ⟨b', hb', rfl⟩
    · exact Or.inl (hclA a ha b hb)
    · exact Or.inr ⟨compT a b', hclA a ha b' hb', e2 a ha b' hb'⟩
    · exact Or.inr ⟨compT a' b, hclA a' ha' b hb, e1 a' ha' b hb⟩
    · rw [e3 a' ha' b' hb']; exact Or.inl (hclA a' ha' b' hb')
  · intro a ha
    rw [hm] at ha
    rcases ha with ha | ⟨a', ha', rfl⟩
    · exact hsq a ha
    · rw [e3 a' ha' a' ha']; exact hsq a' ha'
  · intro a ha b hb
    rw [hm] at ha hb
    rcases ha with ha | ⟨a', ha', rfl⟩ <;> rcases hb with hb | ⟨b', hb', rfl⟩
    · exact hcomm a ha b hb
    · rw [e2 a ha b' hb', e1 b' hb' a ha, hcomm a ha b' hb']
    · rw [e1 a' ha' b hb, e2 b hb a' ha', hcomm a' ha' b hb]
    · rw [e3 a' ha' b' hb', e3 b' hb' a' ha', hcomm a' ha' b' hb']

theorem length_adjoin {A : List (List ℕ)} {x : List ℕ} (hA : IsEA P A)
    (hx : x ∈ extenders P A) : (adjoin x A).length = 2 * A.length := by
  have hAt : ∀ a ∈ A, IsTup a := fun a ha => hT a (hA.2.1 a ha)
  have hEA := isEA_adjoin hT hcl hA hx
  obtain ⟨hid, hsub, hclA, hsq, hcomm, hsort⟩ := hA
  obtain ⟨hxP, ⟨hxx, hxne⟩, hxA, hxc⟩ := mem_extenders.mp hx
  have hxt := hT x hxP
  have hm : ∀ c, c ∈ adjoin x A ↔ c ∈ A ∨ ∃ a ∈ A, c = compT x a := mem_adjoin hxt hAt
  have hAnd : A.Nodup :=
    List.Nodup.of_map codeT (hsort.imp fun h => Nat.ne_of_lt h)
  have hAdnd : (adjoin x A).Nodup :=
    List.Nodup.of_map codeT ((adjoin_sorted x A).imp fun h => Nat.ne_of_lt h)
  have xx : ∀ a ∈ A, compT x (compT x a) = a := by
    intro a ha
    rw [← compT_assoc, hxx, idT_compT (hAt a ha)]
  have hn2 : (A ++ A.map (compT x)).Nodup := by
    rw [List.nodup_append]
    refine ⟨hAnd, ?_, ?_⟩
    · apply List.Nodup.map_on _ hAnd
      intro a ha b hb e
      rw [← xx a ha, ← xx b hb, e]
    · intro c hc d hd
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
      intro e
      subst e
      apply hxA
      have : compT (compT x a) a = x := by
        rw [compT_assoc, hsq a ha, compT_idT hxt]
      rw [← this]
      exact hclA _ hc a ha
  have hperm : (adjoin x A).Perm (A ++ A.map (compT x)) := by
    rw [List.perm_ext_iff_of_nodup hAdnd hn2]
    intro c
    rw [hm c]
    simp only [List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, rfl⟩
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, rfl⟩
  rw [hperm.length_eq]
  simp only [List.length_append, List.length_map]
  omega

theorem eaClose_isEA (hid : idT ∈ P) : ∀ A ∈ eaClose P 10 [[idT]] [[idT]], IsEA P A := by
  refine eaClose_induct P (IsEA P) (fun A hA x hx => isEA_adjoin hT hcl hA hx) 10 _ _ ?_ ?_
  · intro A hA
    obtain rfl := List.mem_singleton.mp hA
    refine ⟨by simp, ?_, ?_, ?_, ?_, by simp⟩
    · intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hid
    · intro a ha b hb
      obtain rfl := List.mem_singleton.mp ha
      obtain rfl := List.mem_singleton.mp hb
      rw [idT_compT idT_tup]; simp
    · intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact idT_compT idT_tup
    · intro a ha b hb
      obtain rfl := List.mem_singleton.mp ha
      obtain rfl := List.mem_singleton.mp hb
      rfl
  · intro A hA; exact hA

theorem eaClose_closed (hid : idT ∈ P) (hnd : P.Nodup) (hlen : P.length ≤ 128) :
    ∀ A ∈ eaClose P 10 [[idT]] [[idT]], ∀ x ∈ extenders P A,
      adjoin x A ∈ eaClose P 10 [[idT]] [[idT]] := by
  have _ := hnd
  have key : ∀ n j (K F : List (List (List ℕ))), (∀ A ∈ K, IsEA P A) →
      (∀ A ∈ F, A ∈ K ∧ A.length = 2 ^ j) →
      (∀ A ∈ K, A ∉ F → ∀ x ∈ extenders P A, adjoin x A ∈ K) → j + n = 10 →
      ∀ A ∈ eaClose P n K F, ∀ x ∈ extenders P A, adjoin x A ∈ eaClose P n K F := by
    intro n
    induction n with
    | zero =>
      intro j K F hK hF hC hj A hA x hx
      have hFnil : ∀ B ∈ F, False := by
        intro B hB
        obtain ⟨hBK, hBl⟩ := hF B hB
        have := isEA_length_le (hK B hBK)
        have hj' : j = 10 := by omega
        subst hj'
        omega
      have hAF : A ∉ F := fun h => hFnil A h
      exact hC A hA hAF x hx
    | succ n ih =>
      intro j K F hK hF hC hj A hA x hx
      obtain ⟨e1, e2⟩ := eaNew_spec P K F
      rw [eaClose_succ] at hA ⊢
      split_ifs at hA ⊢ with hne
      · have hnil : eaNew P K F = [] := List.isEmpty_iff.mp hne
        by_cases hAF : A ∈ F
        · rcases e2 A hAF x hx with h | h
          · exact h
          · rw [hnil] at h; simp at h
        · exact hC A hA hAF x hx
      · have hnewEA : ∀ B ∈ eaNew P K F, IsEA P B := by
          intro B hB
          obtain ⟨A', hA', x', hx', rfl⟩ := e1 B hB
          exact isEA_adjoin hT hcl (hK A' (hF A' hA').1) hx'
        refine ih (j + 1) (K ++ eaNew P K F) (eaNew P K F) ?_ ?_ ?_ (by omega) A hA x hx
        · intro B hB
          rcases List.mem_append.mp hB with h | h
          · exact hK B h
          · exact hnewEA B h
        · intro B hB
          refine ⟨List.mem_append_right _ hB, ?_⟩
          obtain ⟨A', hA', x', hx', rfl⟩ := e1 B hB
          have := length_adjoin hT hcl (hK A' (hF A' hA').1) hx'
          rw [this, (hF A' hA').2, Nat.pow_succ, Nat.mul_comm]
        · intro B hB hBn y hy
          have hBK : B ∈ K := by
            rcases List.mem_append.mp hB with h | h
            · exact h
            · exact absurd h hBn
          by_cases hBF : B ∈ F
          · rcases e2 B hBF y hy with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ h
          · exact List.mem_append_left _ (hC B hBK hBF y hy)
  refine key 10 0 _ _ ?_ ?_ ?_ rfl
  · intro A hA
    obtain rfl := List.mem_singleton.mp hA
    refine ⟨by simp, ?_, ?_, ?_, ?_, by simp⟩
    · intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hid
    · intro a ha b hb
      obtain rfl := List.mem_singleton.mp ha
      obtain rfl := List.mem_singleton.mp hb
      rw [idT_compT idT_tup]; simp
    · intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact idT_compT idT_tup
    · intro a ha b hb
      obtain rfl := List.mem_singleton.mp ha
      obtain rfl := List.mem_singleton.mp hb
      rfl
  · intro A hA
    obtain rfl := List.mem_singleton.mp hA
    exact ⟨by simp, by simp⟩
  · intro A hA hAF
    exact absurd (by simpa using hA) (by simpa using hAF)

end

end CFSG.KC.Misc.Sp6.Snd

end
