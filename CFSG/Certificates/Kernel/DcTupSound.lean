module

public import Certificates.Data.Kernel.DcTup
public import CFSG.Quasithin.H13.LocDblDcos

public section

namespace CFSG.KC.DcTup

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open DoubleCoset

variable {Γ : Type} [Group Γ]

theorem forceN_eq (y : ℕ) (k : ℕ → ℕ) : forceN y k = k y := by
  cases y <;> rfl

theorem imL_eq (c : ℕ) (ys : List ℕ) : imL c ys = ys.map (im c) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    change im c y :: imL c ys = _
    rw [ih, List.map_cons]

theorem pk_cons {y : ℕ} (hy : y < 2 ^ 14) (t : List ℕ) : pk (y :: t) = pk t * 2 ^ 14 + y := by
  change y ||| (pk t <<< 14) = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hy, Nat.shiftLeft_eq]

theorem pk_inj : ∀ {xs ys : List ℕ}, xs.length = ys.length → (∀ x ∈ xs, x < 2 ^ 14) →
    (∀ y ∈ ys, y < 2 ^ 14) → pk xs = pk ys → xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hl, hx, hy, h => by
    have hx0 := hx x List.mem_cons_self
    have hy0 := hy y List.mem_cons_self
    rw [pk_cons hx0, pk_cons hy0] at h
    have h14 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    rw [h14] at h hx0 hy0
    have e1 : x = y := by omega
    have e2 : pk xs = pk ys := by omega
    rw [e1, pk_inj (by simpa using hl) (fun a ha => hx a (List.mem_cons_of_mem _ ha))
      (fun a ha => hy a (List.mem_cons_of_mem _ ha)) e2]

private theorem foldl_ge {α : Type*} (f : ℕ → α → ℕ) (hf : ∀ a e, 16384 ≤ a → 16384 ≤ f a e) :
    ∀ (l : List α) (acc : ℕ), 16384 ≤ acc → 16384 ≤ l.foldl f acc
  | [], _, h => h
  | e :: l, acc, h => foldl_ge f hf l (f acc e) (hf acc e h)

theorem foldl_step {α : Type*} (P : ℕ → α → Prop) [∀ a e, Decidable (P a e)] (f : ℕ → α → ℕ)
    (hf : ∀ a e, f a e = if P a e then a + 1 else 16384) :
    ∀ (l : List α) (acc : ℕ), l.foldl f acc < 16384 →
      l.foldl f acc = acc + l.length ∧ ∀ k (hk : k < l.length), P (acc + k) l[k]
  | [], acc, _ => by simp
  | e :: l, acc, h => by
    rw [List.foldl_cons] at h ⊢
    by_cases hP : P acc e
    · rw [hf, if_pos hP] at h ⊢
      obtain ⟨h1, h2⟩ := foldl_step P f hf l (acc + 1) h
      refine ⟨by rw [h1, List.length_cons]; omega, fun k hk => ?_⟩
      cases k with
      | zero => simpa using hP
      | succ k =>
        have e1 : acc + (k + 1) = acc + 1 + k := by omega
        rw [e1, List.getElem_cons_succ]
        exact h2 k (by simpa using hk)
    · rw [hf, if_neg hP] at h
      exact absurd h (Nat.not_lt.mpr (foldl_ge f (fun a e ha => by
        rw [hf]; split_ifs <;> omega) l 16384 le_rfl))

variable {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def CodeOf (n : ℕ) [MulAction Γ (Fin n)] (c : ℕ) (g : Γ) : Prop :=
  ∀ p < n, im c p = act n g p

@[expose] def prods : List (List Γ) → List Γ
  | [] => [1]
  | L :: Ls => L.flatMap fun u => (prods Ls).map (· * u)

theorem walk_cons_cons (fin : ℕ → ℕ → List ℕ → ℕ → ℕ) (u : ℕ) (L : List ℕ)
    (Ls : List (List ℕ)) (ya yb : ℕ) (ys : List ℕ) (acc : ℕ) :
    walk fin ((u :: L) :: Ls) ya yb ys acc =
      walk fin (L :: Ls) ya yb ys (walk fin Ls (im u ya) (im u yb) (imL u ys) acc) := by
  change forceN (forceN (im u ya) fun pa => forceN (im u yb) fun pb =>
    walk fin Ls pa pb (imL u ys) acc) (walk fin (L :: Ls) ya yb ys) = _
  simp only [forceN_eq]

theorem walk_eq (fin : ℕ → ℕ → List ℕ → ℕ → ℕ) {Ls : List (List ℕ)} {Gs : List (List Γ)}
    (hLG : List.Forall₂ (List.Forall₂ (CodeOf n)) Ls Gs) :
    ∀ ya yb ys acc, ya < n → yb < n → (∀ y ∈ ys, y < n) →
      walk fin Ls ya yb ys acc = (prods Gs).foldl
        (fun a e => fin (act n e ya) (act n e yb) (ys.map (act n e)) a) acc := by
  induction hLG with
  | nil =>
    intro ya yb ys acc hya hyb hys
    have hm : ys.map (act n (1 : Γ)) = ys := by
      conv_rhs => rw [← List.map_id ys]
      exact List.map_congr_left fun y hy => act_one (hys y hy)
    simp only [prods, List.foldl_cons, List.foldl_nil, act_one hya, act_one hyb, hm]
    rfl
  | @cons L G Ls Gs hL _ ih =>
    intro ya yb ys acc hya hyb hys
    induction hL generalizing acc with
    | nil => rfl
    | @cons u g L' G' hug _ ih2 =>
      have hm : imL u ys = ys.map (act n g) := by
        rw [imL_eq]
        exact List.map_congr_left fun y hy => hug y (hys y hy)
      have hys' : ∀ y ∈ ys.map (act n g), y < n := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact act_lt g (hys z hz)
      rw [walk_cons_cons, ih2, hug ya hya, hug yb hyb, hm,
        ih _ _ _ _ (act_lt g hya) (act_lt g hyb) hys']
      have hp : prods ((g :: G') :: Gs) = (prods Gs).map (· * g) ++ prods (G' :: Gs) := by
        simp [prods]
      rw [hp, List.foldl_append, List.foldl_map]
      congr 1
      congr 1
      funext a e
      have hm2 : (ys.map (act n g)).map (act n e) = ys.map (act n (e * g)) := by
        rw [List.map_map]
        exact List.map_congr_left fun y hy => (act_mul e g (hys y hy)).symm
      rw [act_mul _ _ hya, act_mul _ _ hyb, hm2]

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])

theorem blt_eq_decide (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem ordF_eq (N C Q2 RW ya yb : ℕ) (ys : List ℕ) (acc : ℕ) :
    ordF N C Q2 RW ya yb ys acc =
      if idx N C Q2 ya yb = acc ∧ pk ys = row RW acc then acc + 1 else 16384 := by
  unfold ordF
  rw [beq_eq_decide, beq_eq_decide, ← Bool.decide_and]
  by_cases h : idx N C Q2 ya yb = acc ∧ pk ys = row RW acc
  · rw [decide_eq_true h, if_pos h]
  · rw [decide_eq_false h, if_neg h]

theorem hitN_eq_ite (N C Q2 RW za zb : ℕ) (zs : List ℕ) :
    hitN N C Q2 RW za zb zs =
      if idx N C Q2 za zb < N ∧ pk zs = row RW (idx N C Q2 za zb) then 1 else 0 := by
  simp only [hitN, forceN_eq]
  rw [blt_eq_decide, beq_eq_decide]
  by_cases h1 : idx N C Q2 za zb < N
  · rw [decide_eq_true h1]
    by_cases h2 : pk zs = row RW (idx N C Q2 za zb)
    · rw [decide_eq_true h2, if_pos ⟨h1, h2⟩]
    · rw [decide_eq_false h2, if_neg fun h => h2 h.2]
  · rw [decide_eq_false h1, if_neg fun h => h1 h.1]

theorem ordT_sound {N C Q2 RW q1 q2 : ℕ} {B : List ℕ} {Ls : List (List ℕ)}
    {Gs : List (List Γ)} (hLG : List.Forall₂ (List.Forall₂ (CodeOf n)) Ls Gs) (hq1 : q1 < n)
    (hq2 : q2 < n) (hB : ∀ b ∈ B, b < n) (hN : N < 16384)
    (h : ordT N C Q2 RW Ls (q1 :: q2 :: B) = N) :
    (prods Gs).length = N ∧ ∀ k < N,
      idx N C Q2 (act n ((prods Gs).getD k 1) q1) (act n ((prods Gs).getD k 1) q2) = k ∧
        pk (B.map (act n ((prods Gs).getD k 1))) = row RW k := by
  have h' : walk (ordF N C Q2 RW) Ls q1 q2 B 0 = N := h
  rw [walk_eq _ hLG _ _ _ _ hq1 hq2 hB] at h'
  obtain ⟨hlen, hP⟩ := foldl_step
    (fun (a : ℕ) (e : Γ) =>
      idx N C Q2 (act n e q1) (act n e q2) = a ∧ pk (B.map (act n e)) = row RW a)
    (fun a e => ordF N C Q2 RW (act n e q1) (act n e q2) (B.map (act n e)) a)
    (fun a e => ordF_eq _ _ _ _ _ _ _ _) (prods Gs) 0 (by rw [h']; exact hN)
  rw [h'] at hlen
  refine ⟨by omega, fun k hk => ?_⟩
  have hk' : k < (prods Gs).length := by omega
  rw [List.getD_eq_getElem _ _ hk']
  simpa using hP k hk'

theorem hitN_eq [DecidableEq Γ] {N C Q2 RW q1 q2 : ℕ} {B : List ℕ} {Ls : List (List ℕ)}
    {Gs : List (List Γ)} (hLG : List.Forall₂ (List.Forall₂ (CodeOf n)) Ls Gs) (hq1 : q1 < n)
    (hq2 : q2 < n) (hB : ∀ b ∈ B, b < n) (hN : N < 16384) (hn : n ≤ 2 ^ 14)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (h : ordT N C Q2 RW Ls (q1 :: q2 :: B) = N) (g : Γ) :
    hitN N C Q2 RW (act n g q1) (act n g q2) (B.map (act n g)) =
      if g ∈ prods Gs then 1 else 0 := by
  obtain ⟨hlen, hk⟩ := ordT_sound hLG hq1 hq2 hB hN h
  rw [hitN_eq_ite]
  by_cases hg : g ∈ prods Gs
  · obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hg
    have := hk k (hlen ▸ hk')
    rw [List.getD_eq_getElem _ _ hk'] at this
    rw [if_pos hg, if_pos]
    rw [this.1]
    exact ⟨hlen ▸ hk', this.2⟩
  · rw [if_neg hg, if_neg]
    rintro ⟨hlt, hpk⟩
    obtain ⟨-, hrow⟩ := hk _ hlt
    have hk' : idx N C Q2 (act n g q1) (act n g q2) < (prods Gs).length := hlen ▸ hlt
    rw [List.getD_eq_getElem _ _ hk'] at hrow
    have hlt14 : ∀ (s : Γ), ∀ z ∈ B.map (act n s), z < 2 ^ 14 := by
      intro s z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      exact lt_of_lt_of_le (act_lt s (hB b hb)) hn
    have heq := pk_inj (by simp) (hlt14 _) (hlt14 _) (hpk.trans hrow.symm)
    apply hg
    rw [CFSG.Quasithin.H13.LocDbl.Dc.eq_of_base hB hbase fun b hb => List.map_inj_left.mp heq b hb]
    exact List.getElem_mem hk'

private theorem foldl_add_ite {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (a0 : ℕ),
      l.foldl (fun a e => a + if p e then 1 else 0) a0 = a0 + l.countP p
  | [], a0 => by simp
  | e :: l, a0 => by
    rw [List.foldl_cons, foldl_add_ite p l, List.countP_cons]
    omega

theorem cntT_eq [DecidableEq Γ] {N C Q2 RW q1 q2 : ℕ} {B : List ℕ} {Ls : List (List ℕ)}
    {Gs : List (List Γ)} (hLG : List.Forall₂ (List.Forall₂ (CodeOf n)) Ls Gs) (hq1 : q1 < n)
    (hq2 : q2 < n) (hB : ∀ b ∈ B, b < n) (hN : N < 16384) (hn : n ≤ 2 ^ 14)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (h : ordT N C Q2 RW Ls (q1 :: q2 :: B) = N) {X : ℕ} {x : Γ} (hX : CodeOf n X x) (y : Γ) :
    cntT X N C Q2 RW Ls ((q1 :: q2 :: B).map (act n y⁻¹)) =
      ((prods Gs).filter fun r => x * r * y⁻¹ ∈ prods Gs).length := by
  have hB' : ∀ z ∈ B.map (act n y⁻¹), z < n := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    exact act_lt _ (hB b hb)
  have e0 : cntT X N C Q2 RW Ls ((q1 :: q2 :: B).map (act n y⁻¹)) =
      walk (cntF X N C Q2 RW) Ls (act n y⁻¹ q1) (act n y⁻¹ q2) (B.map (act n y⁻¹)) 0 := rfl
  rw [e0, walk_eq _ hLG _ _ _ _ (act_lt _ hq1) (act_lt _ hq2) hB', ← List.countP_eq_length_filter]
  have hpt : ∀ (e : Γ) {p : ℕ}, p < n → im X (act n e (act n y⁻¹ p)) = act n (x * e * y⁻¹) p :=
    fun e p hp => by
      rw [hX _ (act_lt _ (act_lt _ hp)), act_mul _ _ hp, act_mul _ _ (act_lt _ hp)]
  have hstep : ∀ a (e : Γ), cntF X N C Q2 RW (act n e (act n y⁻¹ q1)) (act n e (act n y⁻¹ q2))
      ((B.map (act n y⁻¹)).map (act n e)) a =
        a + if decide (x * e * y⁻¹ ∈ prods Gs) = true then 1 else 0 := by
    intro a e
    have hl : imL X ((B.map (act n y⁻¹)).map (act n e)) = B.map (act n (x * e * y⁻¹)) := by
      rw [imL_eq, List.map_map, List.map_map]
      exact List.map_congr_left fun b hb => hpt e (hB b hb)
    change a + hitN N C Q2 RW _ _ _ = _
    rw [hpt e hq1, hpt e hq2, hl, hitN_eq hLG hq1 hq2 hB hN hn hbase h]
    by_cases hm : x * e * y⁻¹ ∈ prods Gs <;> simp [hm]
  simp only [hstep]
  rw [foldl_add_ite]
  simp

omit [MulAction Γ (Fin n)] in
theorem prods_cons (L : List Γ) (Ls : List (List Γ)) :
    prods (L :: Ls) = L.flatMap fun u => (prods Ls).map (· * u) := rfl

omit [MulAction Γ (Fin n)] in
theorem prods_mem (S : Subgroup Γ) : ∀ {Gs : List (List Γ)}, (∀ L ∈ Gs, ∀ u ∈ L, u ∈ S) →
    ∀ g ∈ prods Gs, g ∈ S
  | [], _, g, hg => by
    rw [List.mem_singleton.mp hg]
    exact S.one_mem
  | L :: Ls, h, g, hg => by
    rw [prods_cons, List.mem_flatMap] at hg
    obtain ⟨u, hu, hg⟩ := hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    exact S.mul_mem (prods_mem S (fun L' hL' => h L' (List.mem_cons_of_mem _ hL')) v hv)
      (h L List.mem_cons_self u hu)

omit [MulAction Γ (Fin n)] in
theorem prods_head : ∀ {Gs : List (List Γ)}, (∀ L ∈ Gs, L.head? = some 1) →
    ∃ t, prods Gs = 1 :: t
  | [], _ => ⟨[], rfl⟩
  | L :: Ls, h => by
    obtain ⟨t, ht⟩ := prods_head (fun L' hL' => h L' (List.mem_cons_of_mem _ hL'))
    obtain ⟨L', rfl⟩ := List.head?_eq_some_iff.mp (h L List.mem_cons_self)
    exact ⟨_, by rw [prods_cons, List.flatMap_cons, ht, List.map_cons, mul_one, List.cons_append]⟩

theorem prods_closure [Finite Γ] [DecidableEq Γ] {N C Q2 RW q1 q2 : ℕ} {B : List ℕ}
    {Ls : List (List ℕ)} {Gs : List (List Γ)}
    (hLG : List.Forall₂ (List.Forall₂ (CodeOf n)) Ls Gs) (hq1 : q1 < n) (hq2 : q2 < n)
    (hB : ∀ b ∈ B, b < n) (hN : N < 16384) (hn : n ≤ 2 ^ 14)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (h : ordT N C Q2 RW Ls (q1 :: q2 :: B) = N) (h1 : ∀ L ∈ Gs, L.head? = some 1) (rg : List Γ)
    (hlev : ∀ L ∈ Gs, ∀ u ∈ L, u ∈ Subgroup.closure {x | x ∈ rg})
    (hcl : ∀ s ∈ rg, ∃ S, CodeOf n S s ∧ cntT S N C Q2 RW Ls (q1 :: q2 :: B) = N) :
    (∀ g, g ∈ Subgroup.closure {x | x ∈ rg} ↔ g ∈ prods Gs) ∧
      Nat.card (Subgroup.closure {x | x ∈ rg}) = N := by
  obtain ⟨hlen, hk⟩ := ordT_sound hLG hq1 hq2 hB hN h
  obtain ⟨t, ht⟩ := prods_head h1
  have hN0 : 0 < N := by
    rw [← hlen, ht]
    simp
  have hget : ∀ k < N, (prods Gs).getD k 1 ∈ prods Gs := fun k hk' => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have he0 : (prods Gs).getD 0 1 = 1 := by simp [ht]
  have hmem : ∀ k, (prods Gs).getD k 1 ∈ Subgroup.closure {x | x ∈ rg} := by
    intro k
    by_cases hk' : k < N
    · exact prods_mem _ hlev _ (hget k hk')
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Subgroup.one_mem _
  have hinj : ∀ i < N, ∀ j < N, (prods Gs).getD i 1 = (prods Gs).getD j 1 → i = j := by
    intro i hi j hj hij
    rw [← (hk i hi).1, ← (hk j hj).1, hij]
  have hall : ∀ p ∈ q1 :: q2 :: B, p < n := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    exacts [hq1, hq2, hB p hp]
  have hpts : (q1 :: q2 :: B).map (act n (1 : Γ)⁻¹) = q1 :: q2 :: B := by
    rw [inv_one]
    conv_rhs => rw [← List.map_id (q1 :: q2 :: B)]
    exact List.map_congr_left fun p hp => act_one (hall p hp)
  have hcl' : ∀ k < N, ∀ s ∈ rg, ∃ k' < N, (prods Gs).getD k' 1 = s * (prods Gs).getD k 1 := by
    intro k hk' s hs
    obtain ⟨S, hS, hc⟩ := hcl s hs
    rw [← hpts, cntT_eq hLG hq1 hq2 hB hN hn hbase h hS 1, ← List.countP_eq_length_filter,
      ← hlen, List.countP_eq_length] at hc
    have := hc _ (hget k hk')
    simp only [inv_one, mul_one, decide_eq_true_eq] at this
    obtain ⟨k', hk'', hk'e⟩ := List.getElem_of_mem this
    exact ⟨k', by omega, by rw [List.getD_eq_getElem _ _ hk'']; exact hk'e⟩
  obtain ⟨hsurj, hcard⟩ := CFSG.Quasithin.H13.LocDbl.Dc.enum_closure rg
    (fun k => (prods Gs).getD k 1) N hN0 he0 hmem hinj hcl'
  refine ⟨fun g => ⟨fun hg => ?_, fun hg => prods_mem _ hlev g hg⟩, hcard⟩
  obtain ⟨k, hk', rfl⟩ := hsurj g hg
  exact hget k hk'

omit [MulAction Γ (Fin n)] in
theorem card_stab_eq [DecidableEq Γ] (R : Subgroup Γ) (l : List Γ) (hl : l.Nodup)
    (hmem : ∀ g, g ∈ R ↔ g ∈ l) (x : Γ) :
    Nat.card (MulAction.stabilizer R ((x⁻¹ : Γ) : Γ ⧸ R)) =
      (l.filter fun r => x * r * x⁻¹ ∈ l).length := by
  rw [← List.toFinset_card_of_nodup (hl.filter _), ← Nat.card_eq_finsetCard]
  have hst : ∀ r : R, r ∈ MulAction.stabilizer R ((x⁻¹ : Γ) : Γ ⧸ R) ↔ x * r * x⁻¹ ∈ R :=
    fun r => by rw [CFSG.Quasithin.H13.LocDbl.Dc.stab_iff, inv_inv]
  let f : MulAction.stabilizer R ((x⁻¹ : Γ) : Γ ⧸ R) →
      {g // g ∈ (l.filter fun r => x * r * x⁻¹ ∈ l).toFinset} := fun r =>
    ⟨r.1.1, by
      rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨(hmem _).mp r.1.2, (hmem _).mp ((hst r.1).mp r.2)⟩⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun r r' hrr => ?_, fun g => ?_⟩)
  · have h' := congrArg Subtype.val hrr
    exact Subtype.ext (Subtype.ext h')
  · have hg := g.2
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hg
    exact ⟨⟨⟨g.1, (hmem _).mpr hg.1⟩, (hst _).mpr ((hmem _).mpr hg.2)⟩, rfl⟩

omit [MulAction Γ (Fin n)] in
theorem card_stab_of_mem [Finite Γ] (R : Subgroup Γ) {x x' : Γ}
    (hx : x' ∈ doubleCoset x (R : Set Γ) R) :
    Nat.card (MulAction.stabilizer R ((x'⁻¹ : Γ) : Γ ⧸ R)) =
      Nat.card (MulAction.stabilizer R ((x⁻¹ : Γ) : Γ ⧸ R)) := by
  obtain ⟨r1, h1, r2, h2, rfl⟩ := mem_doubleCoset.mp hx
  have hpt : (((r1 * x * r2)⁻¹ : Γ) : Γ ⧸ R) =
      (⟨r2⁻¹, R.inv_mem h2⟩ : R) • ((x⁻¹ : Γ) : Γ ⧸ R) := by
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    have e : (r1 * x * r2)⁻¹⁻¹ * (r2⁻¹ * x⁻¹) = r1 := by group
    change (r1 * x * r2)⁻¹⁻¹ * (r2⁻¹ * x⁻¹) ∈ R
    rw [e]
    exact h1
  rw [hpt]
  have e1 := (MulAction.stabilizer R ((⟨r2⁻¹, R.inv_mem h2⟩ : R) •
    ((x⁻¹ : Γ) : Γ ⧸ R))).card_mul_index
  have e2 := (MulAction.stabilizer R ((x⁻¹ : Γ) : Γ ⧸ R)).card_mul_index
  rw [MulAction.index_stabilizer, MulAction.orbit_smul] at e1
  rw [MulAction.index_stabilizer] at e2
  have hpos : 0 < Nat.card (MulAction.orbit R ((x⁻¹ : Γ) : Γ ⧸ R)) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨_, MulAction.mem_orbit_self _⟩⟩, inferInstance⟩
  exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)

omit [MulAction Γ (Fin n)] in
theorem not_mem_of_count_zero [DecidableEq Γ] (R : Subgroup Γ) (l : List Γ)
    (hmem : ∀ g, g ∈ R ↔ g ∈ l) {x y : Γ}
    (h : (l.filter fun r => x * r * y⁻¹ ∈ l).length = 0) :
    y ∉ doubleCoset x (R : Set Γ) R := by
  intro hy
  obtain ⟨r1, h1, r2, h2, rfl⟩ := mem_doubleCoset.mp hy
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  have e : x * r2 * (r1 * x * r2)⁻¹ = r1⁻¹ := by group
  apply h r2 ((hmem _).mp h2)
  rw [e, decide_eq_true_eq]
  exact (hmem _).mp (R.inv_mem h1)

theorem invK_aux (LB : ℕ) (sel : List ℕ) (X : ℕ) :
    ∀ (k s : ℕ), Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun q ih s => forceN (Bool.rec (motive := fun _ => Nat) s
        (Nat.add s (wtK (im LB q) (im LB (im X q)))) (memN (im LB q) sel)) ih) k s =
      s + ∑ q ∈ Finset.range k,
        (if memN (im LB q) sel = true then wtK (im LB q) (im LB (im X q)) else 0)
  | 0, s => by simp
  | k + 1, s => by
    change forceN (Bool.rec (motive := fun _ => Nat) s
        (Nat.add s (wtK (im LB k) (im LB (im X k)))) (memN (im LB k) sel))
      (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
        (fun q ih s => forceN (Bool.rec (motive := fun _ => Nat) s
          (Nat.add s (wtK (im LB q) (im LB (im X q)))) (memN (im LB q) sel)) ih) k) = _
    rw [forceN_eq, invK_aux LB sel X k, Finset.sum_range_succ]
    cases memN (im LB k) sel
    · simp
    · simp only [if_true]
      change s + _ + _ = _
      omega

theorem invK_eq_sum (n LB : ℕ) (sel : List ℕ) (X : ℕ) :
    invK n LB sel X = ∑ q ∈ Finset.range n,
      (if memN (im LB q) sel = true then wtK (im LB q) (im LB (im X q)) else 0) := by
  unfold invK
  rw [invK_aux]
  simp

theorem sum_lab_eq (lab : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (R : Subgroup Γ)
    (hR : ∀ r ∈ R, ∀ q < n, lab (act n r q) = lab q) (x : Γ) {r1 r2 : Γ} (h1 : r1 ∈ R)
    (h2 : r2 ∈ R) :
    ∑ q ∈ Finset.range n, F (lab q) (lab (act n (r1 * x * r2) q)) =
      ∑ q ∈ Finset.range n, F (lab q) (lab (act n x q)) := by
  have e1 : ∀ q ∈ Finset.range n, F (lab q) (lab (act n (r1 * x * r2) q)) =
      F (lab (act n r2 q)) (lab (act n x (act n r2 q))) := by
    intro q hq
    have hq' := Finset.mem_range.mp hq
    rw [act_mul _ _ hq', act_mul _ _ (act_lt _ hq'), hR r1 h1 _ (act_lt _ (act_lt _ hq')),
      hR r2 h2 q hq']
  rw [Finset.sum_congr rfl e1]
  refine Finset.sum_nbij' (fun q => act n r2 q) (fun q => act n r2⁻¹ q) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_range.mpr (act_lt _ (Finset.mem_range.mp hq))
  · intro q hq
    exact Finset.mem_range.mpr (act_lt _ (Finset.mem_range.mp hq))
  · intro q hq
    have hq' := Finset.mem_range.mp hq
    rw [← act_mul _ _ hq', inv_mul_cancel, act_one hq']
  · intro q hq
    have hq' := Finset.mem_range.mp hq
    rw [← act_mul _ _ hq', mul_inv_cancel, act_one hq']
  · intro q _
    rfl

theorem invK_eq (R : Subgroup Γ) {LB X X' : ℕ} (sel : List ℕ) {x x' : Γ}
    (hR : ∀ r ∈ R, ∀ q < n, im LB (act n r q) = im LB q) (hX : CodeOf n X x)
    (hX' : CodeOf n X' x') (hx : x' ∈ doubleCoset x (R : Set Γ) R) :
    invK n LB sel X' = invK n LB sel X := by
  obtain ⟨r1, h1, r2, h2, rfl⟩ := mem_doubleCoset.mp hx
  rw [invK_eq_sum, invK_eq_sum]
  have e : ∀ (c : ℕ) (g : Γ), CodeOf n c g → ∑ q ∈ Finset.range n,
      (if memN (im LB q) sel = true then wtK (im LB q) (im LB (im c q)) else 0) =
      ∑ q ∈ Finset.range n, (fun a b => if memN a sel = true then wtK a b else 0)
        (im LB q) (im LB (act n g q)) := fun c g hc =>
    Finset.sum_congr rfl fun q hq => by rw [hc q (Finset.mem_range.mp hq)]
  rw [e _ _ hX', e _ _ hX]
  exact sum_lab_eq (fun q => im LB q) (fun a b => if memN a sel = true then wtK a b else 0) R hR
    x h1 h2

theorem massK_eq (N : ℕ) (H : ℕ → ℕ) (js : List ℕ) :
    massK N H js = (js.map fun j => N * (N / H j)).sum := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    rfl

omit [MulAction Γ (Fin n)] in
theorem inv_mem_doubleCoset {R : Subgroup Γ} {x g : Γ} (h : g ∈ doubleCoset x (R : Set Γ) R) :
    g⁻¹ ∈ doubleCoset x⁻¹ (R : Set Γ) R := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp h
  exact mem_doubleCoset.mpr ⟨b⁻¹, R.inv_mem hb, a⁻¹, R.inv_mem ha, by group⟩

omit [MulAction Γ (Fin n)] in
theorem card_doubleCoset_inv (R : Subgroup Γ) (x : Γ) :
    Nat.card (doubleCoset x⁻¹ (R : Set Γ) R) = Nat.card (doubleCoset x (R : Set Γ) R) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.inv Γ) fun g => ⟨fun h => ?_, fun h => ?_⟩)
  · simpa using inv_mem_doubleCoset h
  · simpa using inv_mem_doubleCoset h

omit [MulAction Γ (Fin n)] in
theorem maximal_of_masses [Finite Γ] (R : Subgroup Γ) (N : ℕ) (hN : Nat.card R = N)
    (xs : ℕ → Γ) (m : ℕ) (H : ℕ → ℕ)
    (hH : ∀ j < m, Nat.card (MulAction.stabilizer R (((xs j)⁻¹ : Γ) : Γ ⧸ R)) ≤ H j)
    (hdist : ∀ i < m, ∀ j < m, i < j → xs j ∉ doubleCoset (xs i) (R : Set Γ) R)
    (c0 : ℕ) (E : ℕ → ℕ → Prop) (hE : ∀ s d, E s d → xs d ∈ R ⊔ Subgroup.zpowers (xs s))
    (dIn dOut : ℕ → ℕ) (hin : ∀ i < m, i ≠ c0 → ∃ d < m, E i d ∧ dIn d < dIn i)
    (reach : List ℕ) (hreach : ∀ j ∈ reach, j < m) (hnd : reach.Nodup)
    (hout : ∀ j ∈ reach, j ≠ c0 → ∃ s ∈ reach, E s j ∧ dOut s < dOut j)
    (hbig : Nat.card Γ < 2 * (reach.map fun j => N * (N / H j)).sum)
    (htot : Nat.card Γ ≤ ((List.range m).map fun j => N * (N / H j)).sum + N) :
    ∀ Y : Subgroup Γ, R ≤ Y → Y = R ∨ Y = ⊤ := by
  classical
  have hmass : ∀ j < m, N * (N / H j) ≤ Nat.card (doubleCoset (xs j) (R : Set Γ) R) := by
    intro j hj
    have h1 := CFSG.Quasithin.H13.LocDbl.Dc.card_doubleCoset_ge R (xs j)⁻¹ (hH j hj)
    rw [hN, card_doubleCoset_inv] at h1
    exact h1
  have hdisj : ∀ i < m, ∀ j < m, i ≠ j →
      Disjoint (doubleCoset (xs i) (R : Set Γ) R) (doubleCoset (xs j) (R : Set Γ) R) := by
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact CFSG.Quasithin.H13.LocDbl.Dc.disjoint_of_not_mem R (hdist i hi j hj h)
    · exact (CFSG.Quasithin.H13.LocDbl.Dc.disjoint_of_not_mem R (hdist j hj i hi h)).symm
  have hgen := CFSG.Quasithin.H13.LocDbl.Dc.gen_of_trees R xs m c0 E hE dIn dOut hin reach hout
  have htop : ∀ i < m, R ⊔ Subgroup.zpowers (xs i) = ⊤ := fun i hi =>
    CFSG.Quasithin.H13.LocDbl.Dc.eq_top_of_mass le_sup_left xs reach hnd (hgen i hi)
      (fun i' hi' j' hj' h => hdisj i' (hreach i' hi') j' (hreach j' hj') h) _
      (fun j hj => hmass j (hreach j hj)) hbig
  intro Y hRY
  by_cases hY : Y = ⊤
  · exact Or.inr hY
  left
  have hxY : ∀ j < m, xs j ∉ Y := fun j hj hx => hY (by
    rw [eq_top_iff, ← htop j hj]
    exact sup_le hRY (Subgroup.zpowers_le.mpr hx))
  have hxR : ∀ j < m, ∀ g ∈ doubleCoset (xs j) (R : Set Γ) R, g ∈ Y → xs j ∈ Y := by
    intro j _ g hg hgY
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_doubleCoset.mp hg
    have := Y.mul_mem (Y.mul_mem (Y.inv_mem (hRY hr1)) hgY) (Y.inv_mem (hRY hr2))
    simpa [mul_assoc] using this
  have hA := CFSG.Quasithin.H13.LocDbl.Dc.mass_le_card R xs (List.range m) List.nodup_range
    (fun i hi j hj h => hdisj i (List.mem_range.mp hi) j (List.mem_range.mp hj) h) _
    (fun j hj => hmass j (List.mem_range.mp hj))
  set A := ⋃ j ∈ List.range m, doubleCoset (xs j) (R : Set Γ) R with hAdef
  have hAR : Disjoint A (R : Set Γ) := by
    rw [Set.disjoint_left]
    intro g hgA hgR
    rw [hAdef, Set.mem_iUnion₂] at hgA
    obtain ⟨j, hj, hgj⟩ := hgA
    exact hxY j (List.mem_range.mp hj) (hxR j (List.mem_range.mp hj) g hgj (hRY hgR))
  have hcover : A ∪ (R : Set Γ) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Set.ncard_union_eq hAR (Set.toFinite _) (Set.toFinite _)]
    have h3 : Nat.card R = (R : Set Γ).ncard := Nat.card_coe_set_eq (R : Set Γ)
    omega
  refine le_antisymm (fun g hg => ?_) hRY
  have hg' : g ∈ A ∪ (R : Set Γ) := by
    rw [hcover]
    trivial
  rcases hg' with hgA | hgR
  · exfalso
    rw [hAdef, Set.mem_iUnion₂] at hgA
    obtain ⟨j, hj, hgj⟩ := hgA
    exact hxY j (List.mem_range.mp hj) (hxR j (List.mem_range.mp hj) g hgj hg)
  · exact hgR

end CFSG.KC.DcTup

end
