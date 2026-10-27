module

public import Certificates.Data.Kernel.LocalQT.SylV
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr

import CFSG.Certificates.Kernel.LocalQTTcKSound
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.LQT.SV.Pf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.LQT.TC CFSG.QuasithinUnique.Setup.X1
  CFSG.Monster.B.Co2.Native

private theorem bIf_tt {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = true) : t = true := by
  subst hc; exact h

private theorem bIf_ff {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc; exact h

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem lenTc_eq : ∀ L : List ℕ, lenTc L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenTc_eq L)

private theorem arr_ext {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (hu : u.size = n) (hgt : CFSG.Monster.B.Co2.Rep n t g) (hgu : CFSG.Monster.B.Co2.Rep n u g) :
    t = u := by
  refine Array.ext (ht.trans hu.symm) fun i h1 h2 => ?_
  have e := (hgt ⟨i, ht ▸ h1⟩).trans (hgu ⟨i, ht ▸ h1⟩).symm
  rwa [getElem!_pos t i h1, getElem!_pos u i h2] at e

private theorem size_unpack (n w P : ℕ) : (unpack n w P).size = n := by simp [unpack]

private theorem size_compA (n : ℕ) (t u : Array ℕ) : (compA n t u).size = n := by simp [compA]

private theorem size_idA (n : ℕ) : (idA n).size = n := by simp [idA]

section Gens

variable {n w : ℕ}

private theorem gens_facts : ∀ (G GI : List ℕ), gensTc n w G GI = true →
    ∀ l < G.length, canonK n w (mask w) (n * w) (G.getD l 0) = true ∧
      ∃ σ, CFSG.KC.LQT.TCK.RP n w (G.getD l 0) σ
  | [], _, _, l, hl => absurd hl (by simp)
  | _ :: _, [], h, _, _ => absurd h (by simp [gensTc])
  | g :: G, gi :: GI, h, l, hl => by
    change bAnd(canonK n w (mask w) (n * w) g, bAnd(permOK n w (mask w) (n * w) g gi,
      gensTc n w G GI)) = true at h
    obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hp, h⟩ := (bAnd_iff _ _).1 h
    cases l with
    | zero =>
      obtain ⟨σ, -, hσ, -⟩ := CFSG.KC.LQT.TCK.of_permOK hp
      exact ⟨hc, σ, hσ⟩
    | succ l =>
      exact gens_facts G GI h l (by simpa using hl)

end Gens

section Count

private theorem sqP_iff (w x : ℕ) : ∀ P : List ℕ,
    sqP w x P = true ↔ ∀ p ∈ P, pg w (mask w) x (pg w (mask w) x p) = p
  | [] => by simp [sqP]
  | p :: P => by
    change bAnd(Nat.beq (pg w (mask w) x (pg w (mask w) x p)) p, sqP w x P) = true ↔ _
    rw [bAnd_iff, sqP_iff w x P, Nat.beq_eq, List.forall_mem_cons]

private theorem commP_iff (w x y : ℕ) : ∀ P : List ℕ,
    commP w x y P = true ↔
      ∀ p ∈ P, pg w (mask w) x (pg w (mask w) y p) = pg w (mask w) y (pg w (mask w) x p)
  | [] => by simp [commP]
  | p :: P => by
    change bAnd(Nat.beq (pg w (mask w) x (pg w (mask w) y p))
      (pg w (mask w) y (pg w (mask w) x p)), commP w x y P) = true ↔ _
    rw [bAnd_iff, commP_iff w x y P, Nat.beq_eq, List.forall_mem_cons]

private theorem commP_symm (w x y : ℕ) (P : List ℕ) : commP w x y P = commP w y x P := by
  rw [Bool.eq_iff_iff, commP_iff, commP_iff]
  exact forall₂_congr fun _ _ => eq_comm

private theorem mem_candSV (w : ℕ) (E : ℕ → ℕ) (P : List ℕ) : ∀ (N i : ℕ),
    i ∈ candSV w N E P ↔ i < N ∧ i ≠ 0 ∧ sqP w (E i) P = true
  | 0, i => by simp [candSV]
  | N + 1, i => by
    change i ∈ Bool.rec (motive := fun _ => List ℕ) (candSV w N E P) (N :: candSV w N E P)
      (bAnd(bIf(Nat.beq N 0, false, true), sqP w (E N) P)) ↔ _
    have hc : bAnd(bIf(Nat.beq N 0, false, true), sqP w (E N) P) = true ↔
        N ≠ 0 ∧ sqP w (E N) P = true := by
      rw [bAnd_iff]
      cases h : Nat.beq N 0
      · exact ⟨fun ⟨_, hs⟩ => ⟨fun e => by simp [e] at h, hs⟩, fun ⟨_, hs⟩ => ⟨rfl, hs⟩⟩
      · exact ⟨fun ⟨h', _⟩ => absurd h' (by simp), fun ⟨hN, _⟩ => absurd (Nat.eq_of_beq_eq_true h) hN⟩
    cases hb : bAnd(bIf(Nat.beq N 0, false, true), sqP w (E N) P)
    · change i ∈ candSV w N E P ↔ _
      rw [mem_candSV w E P N i]
      have : ¬ (N ≠ 0 ∧ sqP w (E N) P = true) := fun h' => by simp [hc.2 h'] at hb
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | rfl
        · exact h1
        · exact absurd ⟨h2, h3⟩ this
    · change i ∈ N :: candSV w N E P ↔ _
      rw [List.mem_cons, mem_candSV w E P N i]
      obtain ⟨hN, hs⟩ := hc.1 hb
      constructor
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨by omega, hN, hs⟩
        · exact ⟨by omega, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | rfl
        · exact Or.inr ⟨h1, h2, h3⟩
        · exact Or.inl rfl

private theorem nodup_candSV (w : ℕ) (E : ℕ → ℕ) (P : List ℕ) : ∀ N, (candSV w N E P).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
    change (Bool.rec (motive := fun _ => List ℕ) (candSV w N E P) (N :: candSV w N E P)
      (bAnd(bIf(Nat.beq N 0, false, true), sqP w (E N) P))).Nodup
    cases bAnd(bIf(Nat.beq N 0, false, true), sqP w (E N) P)
    · exact nodup_candSV w E P N
    · refine List.nodup_cons.2 ⟨fun h => ?_, nodup_candSV w E P N⟩
      have := ((mem_candSV w E P N N).1 h).1
      omega

private def cntP (R : ℕ → ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | a :: l => l.countP (R a) + cntP R l

private theorem cntWith_eq (w : ℕ) (E : ℕ → ℕ) (P : List ℕ) (a : ℕ) : ∀ (L : List ℕ) (c : ℕ),
    cntWithSV w E P a L c = c + L.countP fun b => commP w (E a) (E b) P
  | [], c => by simp [cntWithSV]
  | b :: L, c => by
    change strictN (Bool.rec (motive := fun _ => ℕ) c (Nat.succ c) (commP w (E a) (E b) P))
      (fun c => cntWithSV w E P a L c) = _
    rw [strictN_eq', cntWith_eq w E P a L, List.countP_cons]
    cases commP w (E a) (E b) P <;> simp <;> omega

private theorem cnt_eq (w : ℕ) (E : ℕ → ℕ) (P : List ℕ) : ∀ (L : List ℕ) (c : ℕ),
    cntSV w E P L c = c + cntP (fun a b => commP w (E a) (E b) P) L
  | [], c => by simp [cntSV, cntP]
  | a :: L, c => by
    change strictN (cntWithSV w E P a L c) (fun c => cntSV w E P L c) = _
    rw [strictN_eq', cnt_eq w E P L, cntWith_eq, cntP]
    omega

private def OP (L : List ℕ) (R : ℕ → ℕ → Bool) : List (ℕ × ℕ) :=
  L.flatMap fun i => (L.filter fun j => i != j && R i j).map fun j => (i, j)

private theorem mem_OP {L : List ℕ} {R : ℕ → ℕ → Bool} {a b : ℕ} :
    (a, b) ∈ OP L R ↔ a ∈ L ∧ b ∈ L ∧ a ≠ b ∧ R a b = true := by
  simp only [OP, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true, bne_iff_ne,
    ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, ⟨hj, hij, hr⟩, rfl, rfl⟩
    exact ⟨hi, hj, hij, hr⟩
  · rintro ⟨ha, hb, hab, hr⟩
    exact ⟨a, ha, b, ⟨hb, hab, hr⟩, rfl, rfl⟩

private theorem nodup_OP {L : List ℕ} (hL : L.Nodup) (R : ℕ → ℕ → Bool) : (OP L R).Nodup := by
  rw [OP, List.nodup_flatMap]
  refine ⟨fun i _ => (hL.filter _).map (fun _ _ h => (Prod.mk.inj h).2), ?_⟩
  refine hL.imp fun {a b} hab => ?_
  intro x hx hx'
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
  obtain ⟨_, _, e⟩ := List.mem_map.1 hx'
  exact hab (congrArg Prod.fst e).symm

private theorem sum_cons_countP (R : ℕ → ℕ → Bool) (a : ℕ) (l : List ℕ) : ∀ M : List ℕ,
    (M.map fun i => (a :: l).countP fun j => i != j && R i j).sum =
      M.countP (fun i => i != a && R i a) + (M.map fun i => l.countP fun j => i != j && R i j).sum
  | [] => rfl
  | i :: M => by
    rw [List.map_cons, List.sum_cons, sum_cons_countP R a l M, List.countP_cons (l := l),
      List.countP_cons (l := M), List.map_cons, List.sum_cons]
    ring

private theorem length_OP {R : ℕ → ℕ → Bool} (hR : ∀ a b, R a b = R b a) :
    ∀ {L : List ℕ}, L.Nodup → (OP L R).length = 2 * cntP R L
  | [], _ => rfl
  | a :: l, hL => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 hL
    have key : ∀ M : List ℕ, (OP M R).length =
        (M.map fun i => M.countP fun j => i != j && R i j).sum := fun M => by
      rw [OP, List.length_flatMap]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      rw [List.length_map, List.countP_eq_length_filter]
    have h1 : (a :: l).countP (fun j => a != j && R a j) = l.countP (R a) := by
      rw [List.countP_cons]
      simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, add_zero]
      refine List.countP_congr fun j hj => ?_
      have : a ≠ j := fun e => ha (e ▸ hj)
      simp [this]
    have h3 : l.countP (fun i => i != a && R i a) = l.countP (R a) :=
      List.countP_congr fun i hi => by
        have : i ≠ a := fun e => ha (e ▸ hi)
        simp [this, hR i a]
    rw [key, List.map_cons, List.sum_cons, h1, sum_cons_countP, h3, ← key, length_OP hR hl, cntP]
    ring

end Count

private theorem blt_lt {a b : ℕ} (h : Nat.blt a b = true) : a < b := by rwa [Nat.blt_eq] at h

private theorem bIf_cases {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp_all

private theorem sort_inj {N : ℕ} {E IS SR : ℕ → ℕ} (hs : sortAllSV N E IS SR = true) :
    ∀ i < N, ∀ j < N, E i = E j → i = j := by
  unfold sortAllSV at hs
  have h := allBlk_spec hs
  have hS : ∀ i < N, SR i < N ∧ IS (SR i) = i ∧ (i + 1 < N → E (IS i) < E (IS (i + 1))) := by
    intro i hi
    have := h i hi
    rw [show Nat.add 0 i = i from Nat.zero_add i] at this
    unfold sortSV at this
    rw [strictB_eq'] at this
    obtain ⟨h1, h23⟩ := (bAnd_iff _ _).1 this
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h23
    exact ⟨blt_lt h1, Nat.eq_of_beq_eq_true h2,
      fun hi1 => blt_lt (bIf_tt h3 (by rw [Nat.blt_eq]; exact hi1))⟩
  have mono : ∀ a b, a < b → b < N → E (IS a) < E (IS b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact lt_trans (ih h' (by omega)) ((hS b (by omega)).2.2 hb)
      · exact (hS a (by omega)).2.2 hb
  intro i hi j hj he
  obtain ⟨hri, hii, -⟩ := hS i hi
  obtain ⟨hrj, hjj, -⟩ := hS j hj
  rcases lt_trichotomy (SR i) (SR j) with h' | h' | h'
  · have := mono _ _ h' hrj
    rw [hii, hjj] at this
    omega
  · rw [← hii, ← hjj, h']
  · have := mono _ _ h' hri
    rw [hii, hjj] at this
    omega

private theorem build_spec (F : Array (Array ℕ) → ℕ → Array (Array ℕ)) (U : ℕ → Array ℕ) (N : ℕ)
    (hF : ∀ m < N, ∀ A : Array (Array ℕ), A.size = m → (∀ k < m, A[k]! = U k) →
      F A m = A.push (U m)) :
    ∀ m ≤ N, ((List.range m).foldl F #[]).size = m ∧
      ∀ k < m, ((List.range m).foldl F #[])[k]! = U k := by
  intro m
  induction m with
  | zero => intro _; exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨hsz, hval⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      hF m (by omega) _ hsz hval]
    refine ⟨by rw [Array.size_push, hsz], fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [push_get_lt (by rw [hsz]; exact hk)]
      exact hval k hk
    · rw [push_get_eq hsz.symm]

private theorem rp_unique {n w P : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h1 : CFSG.KC.LQT.TCK.RP n w P σ) (h2 : CFSG.KC.LQT.TCK.RP n w P τ) : σ = τ :=
  Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))

section Main

variable {n w N ng r K L : Nat} {G GI : List Nat} {E PT LT TB IS SR : Nat → Nat}
  {P : List Nat} {gens : List PArr} {par lab tab : List Nat}

open CFSG.KC.LQT.TCK CFSG.Monster.B.Co2 in
theorem sylSV_sound' (hg : gens.map Prod.fst = G.map (unpack n w))
    (hh : headSV n w N ng G GI = true)
    (hp : ∀ i < N, par.getD i 0 = PT i) (hl : ∀ i < N, lab.getD i 0 = LT i)
    (ht : ∀ i < N * ng, tab.getD i 0 = TB i)
    (hKL : N ≤ K * L)
    (hc : ∀ s < K, chunkSV n w N ng G E PT LT TB (Nat.mul s L) L = true)
    (hs : sortAllSV N E IS SR = true)
    (hq : pairsSV w N E P r = true) (hP : ∀ p ∈ P, p < n) :
    sylVerify n N gens par lab tab (sylBuild n N gens par lab) r = true ∧
      ∀ k < N, (sylBuild n N gens par lab)[k]! = unpack n w (E k) := by
  unfold headSV at hh
  obtain ⟨hid, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hgt, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hng, hN⟩ := (bAnd_iff _ _).1 hh
  rw [lenTc_eq, Nat.beq_eq] at hng
  have hN0 : 0 < N := blt_lt hN
  have hlen : gens.length = G.length := by simpa using congrArg List.length hg
  have hgf := gens_facts G GI hgt
  have helt : ∀ k < N, eltSV n w N ng G E PT LT TB k = true := by
    intro k hk
    have hL0 : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · subst h0
        rw [Nat.mul_zero] at hKL
        omega
      · exact h0
    have hs' : k / L < K := by
      rw [Nat.div_lt_iff_lt_mul hL0]
      omega
    have h := hc (k / L) hs'
    unfold chunkSV at h
    have := allBlk_spec h (k % L) (Nat.mod_lt _ hL0)
    beta_reduce at this
    have e : Nat.add (Nat.mul (k / L) L) (k % L) = k := Nat.div_add_mod' k L
    rw [e] at this
    exact bIf_tt this (by rw [Nat.blt_eq]; exact hk)
  have he0 : E 0 = pidn n w := by
    have h := helt 0 hN0
    unfold eltSV at h
    obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 h
    exact Nat.eq_of_beq_eq_true h1
  have hek : ∀ k < N, k ≠ 0 → PT k < k ∧ LT k < ng ∧
      E k = pcomp n w (mask w) (E (PT k)) (G.getD (LT k) 0) := by
    intro k hk hk0
    have h := helt k hk
    unfold eltSV at h
    obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 h
    have h2 := bIf_ff h1 (by
      rw [Bool.eq_false_iff]
      exact fun h' => hk0 (Nat.eq_of_beq_eq_true h'))
    rw [strictB_eq', strictB_eq'] at h2
    obtain ⟨h3, h2⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h2
    rw [getTc_eq] at h5
    exact ⟨blt_lt h3, blt_lt h4, Nat.eq_of_beq_eq_true h5⟩
  have het : ∀ k < N, ∀ j < ng, TB (k * ng + j) < N ∧
      pcomp n w (mask w) (E k) (G.getD j 0) = E (TB (k * ng + j)) := by
    intro k hk j hj
    have h := helt k hk
    unfold eltSV at h
    obtain ⟨-, h1⟩ := (bAnd_iff _ _).1 h
    have h2 := allBlk_spec h1 j hj
    beta_reduce at h2
    rw [show Nat.add 0 j = j from Nat.zero_add j, strictB_eq'] at h2
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    have e : Nat.add (Nat.mul k ng) j = k * ng + j := rfl
    rw [e] at h3 h4
    refine ⟨blt_lt h3, ?_⟩
    rw [getTc_eq] at h4
    rcases bIf_cases h4 with ⟨hc1, -⟩ | ⟨-, hc2⟩
    · obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 hc1
      obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h6
      have ht0 : TB (k * ng + j) ≠ 0 := by
        rcases bIf_cases h5 with ⟨-, h9⟩ | ⟨h9, -⟩
        · exact absurd h9 (by simp)
        · exact fun e0 => by rw [e0] at h9; exact absurd h9 (by simp)
      obtain ⟨-, -, hE⟩ := hek _ (blt_lt h3) ht0
      rw [hE, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8]
    · exact Nat.eq_of_beq_eq_true hc2
  have hgen : ∀ l < ng, n < 16777216 ∧ n + 1 < 2 ^ w ∧ ∃ σ, RP n w (G.getD l 0) σ := by
    intro l hl'
    obtain ⟨hcan, hσ⟩ := hgf l (hng ▸ hl')
    obtain ⟨h1, h2, -, -⟩ := CFSG.KS.PF.canon_facts hcan
    exact ⟨h1, h2, hσ⟩
  have hgA : ∀ j < ng, (gens.getD j (pId n)).1 = unpack n w (G.getD j 0) := by
    intro j hj
    have hj1 : j < G.length := hng ▸ hj
    have hj2 : j < gens.length := hlen ▸ hj1
    rw [List.getD_eq_getElem _ _ hj2, List.getD_eq_getElem _ _ hj1]
    have := List.getElem_of_eq hg (by simpa using hj2)
    simpa using this
  have hperm : ∀ k < N, ∃ σ, RP n w (E k) σ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [he0]
        exact ⟨1, rp_idn hid⟩
      · obtain ⟨hpk, hlk, hek'⟩ := hek k hk hk0
        obtain ⟨σ, hσ⟩ := ih _ hpk (by omega)
        obtain ⟨hn1, -, τ, hτ⟩ := hgen _ hlk
        rw [hek']
        exact ⟨σ * τ, rp_pcomp (by omega) hσ hτ⟩
  have hσ0 : ∀ σ, RP n w (E 0) σ → σ = 1 := fun σ hσ => rp_unique hσ (he0 ▸ rp_idn hid)
  have hB := build_spec (fun acc k => acc.push (if k = 0 then idA n else
      compA n acc[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1))
    (fun k => unpack n w (E k)) N (by
      intro m hm A hsz hval
      congr 1
      by_cases hm0 : m = 0
      · subst hm0
        rw [if_pos rfl, he0]
        exact arr_ext (size_idA n) (size_unpack n w _) rep_idA
          (CFSG.KS.Raw.Orb.rep_unpack (rp_idn hid))
      · rw [if_neg hm0]
        obtain ⟨hpk, hlk, hek'⟩ := hek m hm hm0
        rw [hp m hm, hl m hm, hval _ (by rw [hsz] at *; exact hpk), hgA _ hlk, hek']
        obtain ⟨σ, hσ⟩ := hperm _ (by omega : PT m < N)
        obtain ⟨hn1, -, τ, hτ⟩ := hgen _ hlk
        exact arr_ext (size_compA n _ _) (size_unpack n w _)
          (rep_compA (CFSG.KS.Raw.Orb.rep_unpack hσ) (CFSG.KS.Raw.Orb.rep_unpack hτ))
          (CFSG.KS.Raw.Orb.rep_unpack (rp_pcomp (by omega) hσ hτ))) N le_rfl
  have hAl : sylBuild n N gens par lab = (List.range N).foldl (fun acc k => acc.push
      (if k = 0 then idA n else
        compA n acc[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1)) #[] := rfl
  rw [← hAl] at hB
  obtain ⟨hsz, hval⟩ := hB
  have hrep : ∀ k < N, ∃ σ, Rep n (sylBuild n N gens par lab)[k]! σ ∧ RP n w (E k) σ :=
    fun k hk => let ⟨σ, hσ⟩ := hperm k hk
      ⟨σ, by rw [hval k hk]; exact CFSG.KS.Raw.Orb.rep_unpack hσ, hσ⟩
  refine ⟨?_, hval⟩
  have hpairs : (sylPairs n (sylBuild n N gens par lab)
      (sylInv n N (sylBuild n N gens par lab))).length <
      (2 ^ (r + 1) - 1) * (2 ^ (r + 1) - 2) := by
    have hq' : 2 * cntSV w E P (candSV w N E P) 0 < (2 ^ (r + 1) - 1) * (2 ^ (r + 1) - 2) := by
      unfold pairsSV at hq
      rw [strictB_eq'] at hq
      exact blt_lt hq
    rw [cnt_eq, Nat.zero_add, ← length_OP (fun a b => commP_symm w (E a) (E b) P)
      (nodup_candSV w E P N)] at hq'
    refine lt_of_le_of_lt ?_ hq'
    refine List.Subperm.length_le ((nodup_OP (List.nodup_range.filter _) _).subperm ?_)
    rintro ⟨a, b⟩ hab
    rw [mem_OP] at hab ⊢
    obtain ⟨ha, hb, hne, hr⟩ := hab
    have hinv : ∀ i ∈ sylInv n N (sylBuild n N gens par lab), i ∈ candSV w N E P ∧
        ∃ σ, Rep n (sylBuild n N gens par lab)[i]! σ ∧ RP n w (E i) σ := by
      intro i hi
      simp only [sylInv, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true']
        at hi
      obtain ⟨hiN, h1, h2⟩ := hi
      obtain ⟨σ, hσA, hσ⟩ := hrep i hiN
      have hσ1 : σ ≠ 1 := fun e => by
        rw [e] at hσA
        rw [(eqA_iff hσA rep_idA).2 rfl] at h1
        exact absurd h1 (by simp)
      have hσ2 : σ * σ = 1 := (eqA_iff (rep_compA hσA hσA) rep_idA).1 h2
      refine ⟨(mem_candSV w E P N i).2 ⟨hiN, fun e => hσ1 (hσ0 σ (e ▸ hσ)), ?_⟩, σ, hσA, hσ⟩
      rw [sqP_iff]
      intro p hpP
      have hpn := hP p hpP
      have e1 : pg w (mask w) (E i) p = σ ⟨p, hpn⟩ := hσ ⟨p, hpn⟩
      have e2 : pg w (mask w) (E i) (σ ⟨p, hpn⟩) = σ (σ ⟨p, hpn⟩) := hσ (σ ⟨p, hpn⟩)
      rw [e1, e2, ← Equiv.Perm.mul_apply, hσ2]
      rfl
    obtain ⟨ha', σ, hσA, hσ⟩ := hinv a ha
    obtain ⟨hb', τ, hτA, hτ⟩ := hinv b hb
    refine ⟨ha', hb', hne, ?_⟩
    have hcomm : σ * τ = τ * σ := (eqA_iff (rep_compA hσA hτA) (rep_compA hτA hσA)).1 hr
    rw [commP_iff]
    intro p hpP
    have hpn := hP p hpP
    have e1 : pg w (mask w) (E b) p = τ ⟨p, hpn⟩ := hτ ⟨p, hpn⟩
    have e2 : pg w (mask w) (E a) p = σ ⟨p, hpn⟩ := hσ ⟨p, hpn⟩
    have e3 : pg w (mask w) (E a) (τ ⟨p, hpn⟩) = σ (τ ⟨p, hpn⟩) := hσ (τ ⟨p, hpn⟩)
    have e4 : pg w (mask w) (E b) (σ ⟨p, hpn⟩) = τ (σ ⟨p, hpn⟩) := hτ (σ ⟨p, hpn⟩)
    rw [e1, e2, e3, e4, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hcomm]
  unfold sylVerify
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hsz, hN0⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hpairs⟩
  · obtain ⟨σ, hσA, hσ⟩ := hrep 0 hN0
    rw [hσ0 σ hσ] at hσA
    exact (eqA_iff hσA rep_idA).2 rfl
  · intro k hk
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      obtain ⟨hpk, hlk, hek'⟩ := hek k hk hk0
      rw [hp k hk, hl k hk, hlen, hng, hgA _ hlk]
      refine ⟨⟨hpk, hlk⟩, ?_⟩
      obtain ⟨σ, hσA, hσ⟩ := hrep k hk
      obtain ⟨ρ, hρA, hρ⟩ := hrep _ (by omega : PT k < N)
      obtain ⟨hn1, -, τ, hτ⟩ := hgen _ hlk
      have e : σ = ρ * τ := rp_unique hσ (hek' ▸ rp_pcomp (by omega) hρ hτ)
      exact (eqA_iff hσA (rep_compA hρA (CFSG.KS.Raw.Orb.rep_unpack hτ))).2 e
  · rw [hlen, hng]
    intro i hi j hj
    have hij : i * ng + j < N * ng := by
      have h1 : i * ng + j < (i + 1) * ng := by rw [Nat.succ_mul]; omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hi)
    rw [ht _ hij, hgA _ hj]
    obtain ⟨htl, hte⟩ := het i hi j hj
    refine ⟨htl, ?_⟩
    obtain ⟨σ, hσA, hσ⟩ := hrep i hi
    obtain ⟨ρ, hρA, hρ⟩ := hrep _ htl
    obtain ⟨hn1, -, τ, hτ⟩ := hgen _ hj
    have e : σ * τ = ρ := rp_unique (hte ▸ rp_pcomp (by omega) hσ hτ) hρ
    exact (eqA_iff (rep_compA hσA (CFSG.KS.Raw.Orb.rep_unpack hτ)) hρA).2 e
  · intro i hi
    obtain ⟨σ, hσA, -⟩ := hrep i hi
    exact isInvA_of_rep hσA (rep_invCand hσA)
  · intro i hi j hj
    have hne : eqA n (sylBuild n N gens par lab)[i]! (sylBuild n N gens par lab)[j]! = false := by
      rw [Bool.eq_false_iff]
      intro he
      obtain ⟨σ, hσA, hσ⟩ := hrep i hi
      obtain ⟨τ, hτA, hτ⟩ := hrep j (by omega)
      have e := (eqA_iff hσA hτA).1 he
      have hi0 : i ≠ 0 := by omega
      obtain ⟨hn1, hw1, -⟩ := hgen _ (hek i hi hi0).2.1
      have hshr : ∀ k < N, E k >>> (n * w) = 0 := by
        intro k hk
        by_cases hk0 : k = 0
        · rw [hk0, he0]
          exact CFSG.KS.PF.pidn_shr hn1 hw1
        · rw [(hek k hk hk0).2.2]
          exact CFSG.KS.PF.pcomp_shr _ _ (by omega) (CFSG.KS.PF.w_pos hw1)
      have hEq : E i = E j := CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw1) (hshr i hi)
        (hshr j (by omega)) fun x hx => by
          have h1 : pg w (mask w) (E i) x = σ ⟨x, hx⟩ := hσ ⟨x, hx⟩
          have h2 : pg w (mask w) (E j) x = τ ⟨x, hx⟩ := hτ ⟨x, hx⟩
          rw [h1, h2, e]
      have := sort_inj hs i hi j (by omega) hEq
      omega
    simp [hne]

end Main

end CFSG.KC.LQT.SV.Pf

end
