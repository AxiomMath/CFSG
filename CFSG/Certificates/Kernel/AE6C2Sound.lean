module

public import Certificates.Data.Kernel.AE6C2N
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.AE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.KGC31P

def PruneOK (fk : Nat → Bool) : List (List Nat × (Nat → Bool)) → Prop
  | [] => True
  | (_, pr) :: Ts =>
    (∀ h acc, pr h = false → pfilterProducts 360 9 fk (Ts.map Prod.fst) h acc = acc) ∧
      PruneOK fk Ts

theorem pfilterPr_eq {fk : Nat → Bool} :
    ∀ (Ls : List (List Nat × (Nat → Bool))), PruneOK fk Ls → ∀ g acc,
      pfilterPr fk Ls g acc = pfilterProducts 360 9 fk (Ls.map Prod.fst) g acc
  | [], _, g, acc => by simp only [pfilterPr, List.map_nil, pfilterProducts]
  | (T, pr) :: Ts, ⟨hpr, hTs⟩, g, acc => by
    rw [pfilterPr, List.map_cons]
    change _ = pfilterProducts 360 9 fk (T :: Ts.map Prod.fst) g acc
    rw [pfilterProducts]
    suffices ∀ (l : List Nat) a,
        l.foldl (fun acc t => prStep pr (fun h => pfilterPr fk Ts h acc) acc (pc 360 9 g t)) a =
          l.foldl (fun acc t => pfilterProducts 360 9 fk (Ts.map Prod.fst) (pc 360 9 g t) acc) a
      from this T acc
    intro l
    induction l with
    | nil => intro a; rfl
    | cons t l ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons]
      have e : prStep pr (fun h => pfilterPr fk Ts h a) a (pc 360 9 g t) =
          pfilterProducts 360 9 fk (Ts.map Prod.fst) (pc 360 9 g t) a := by
        unfold prStep
        cases hp : pr (pc 360 9 g t)
        · exact (hpr _ _ hp).symm
        · exact pfilterPr_eq Ts hTs _ _
      rw [e]
      exact ih _

theorem pfilterProducts_eq_acc {fk : Nat → Bool} (I : Nat → Prop)
    (hleaf : ∀ g, I g → fk g = false) :
    ∀ (Ls : List (List Nat)), (∀ L ∈ Ls, ∀ t ∈ L, ∀ g, I g → I (pc 360 9 g t)) →
      ∀ g acc, I g → pfilterProducts 360 9 fk Ls g acc = acc
  | [], _, g, acc, hg => by simp [pfilterProducts, hleaf g hg]
  | L :: Ls, hL, g, acc, hg => by
    rw [pfilterProducts]
    have hLs : ∀ L' ∈ Ls, ∀ t ∈ L', ∀ g, I g → I (pc 360 9 g t) := fun L' h =>
      hL L' (List.mem_cons_of_mem _ h)
    suffices ∀ l : List Nat, (∀ t ∈ l, ∀ g, I g → I (pc 360 9 g t)) → ∀ a,
        l.foldl (fun acc t => pfilterProducts 360 9 fk Ls (pc 360 9 g t) acc) a = a from
      this L (hL L List.mem_cons_self) acc
    intro l
    induction l with
    | nil => intro _ a; rfl
    | cons t l ih =>
      intro hl a
      rw [List.foldl_cons, pfilterProducts_eq_acc I hleaf Ls hLs _ a (hl t List.mem_cons_self g hg)]
      exact ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)) a

theorem pt_pc {g t u : Nat} (hu : u < 360) : pt (pc 360 9 g t) u = pt g (pt t u) := by
  unfold pt pc
  exact CFSG.KS.PF.pg_pcomp (by norm_num) hu

theorem prune_sound {Q F : List Nat} (hF : ∀ u ∈ F, u < 360) {Ls : List (List Nat)}
    (hfix : ∀ L ∈ Ls, ∀ t ∈ L, ∀ u ∈ F, pt t u = u) (h : Nat) (acc : List Nat)
    (hh : prOK Q F h = false) : pfilterProducts 360 9 (commAllN Q) Ls h acc = acc := by
  unfold prOK at hh
  obtain ⟨q, hq, hq'⟩ := List.all_eq_false.1 hh
  rw [Bool.not_eq_true, List.all_eq_false] at hq'
  obtain ⟨u, hu, hu'⟩ := hq'
  have hu2 : F.any (Nat.beq (pt q u)) = true ∧
      Nat.beq (pt h (pt q u)) (pt q (pt h u)) = false := by
    unfold prPt at hu'
    cases e1 : F.any (Nat.beq (pt q u)) <;>
      cases e2 : Nat.beq (pt h (pt q u)) (pt q (pt h u)) <;> simp [e1, e2] at hu' ⊢
  obtain ⟨v, hv, hqv⟩ := List.any_eq_true.1 hu2.1
  rw [← Nat.eq_of_beq_eq_true hqv] at hv
  have hne : pt h (pt q u) ≠ pt q (pt h u) := fun e => by
    have := hu2.2
    rw [e] at this
    simp at this
  refine pfilterProducts_eq_acc (fun g => pt g (pt q u) ≠ pt q (pt g u)) ?_ Ls ?_ h acc hne
  · intro g hg
    by_contra hc
    rw [Bool.not_eq_false, commAllN, List.all_eq_true] at hc
    have e := congrArg (fun x => pt x u) (Nat.eq_of_beq_eq_true (hc q hq))
    simp only [pt_pc (hF u hu)] at e
    exact hg e
  · intro L hL t ht g hg
    rw [pt_pc (hF _ hv), pt_pc (hF u hu), hfix L hL t ht _ hv, hfix L hL t ht u hu]
    exact hg

theorem fixLv_all : ∀ (F : List Nat) (Ls : List (List Nat)) (B : List Nat), fixLv F Ls B = true →
    ∀ L ∈ Ls, ∀ t ∈ L, ∀ u ∈ F, pt t u = u
  | _, [], _, _ => fun _ h => absurd h List.not_mem_nil
  | _, _ :: _, [], h => by simp [fixLv] at h
  | F, L :: Ls, b :: B, h => by
    rw [fixLv, Bool.and_eq_true, List.all_eq_true] at h
    intro L' hL' t ht u hu
    rcases List.mem_cons.1 hL' with rfl | hL'
    · have := List.all_eq_true.1 (h.1 t ht) u hu
      exact Nat.eq_of_beq_eq_true this
    · exact fixLv_all (b :: F) Ls B h.2 L' hL' t ht u (List.mem_cons_of_mem _ hu)

theorem map_fst_prLv {Q : List Nat} : ∀ (F : List Nat) (Ls : List (List Nat)) (B : List Nat),
    fixLv F Ls B = true → (prLv Q F Ls B).map Prod.fst = Ls
  | _, [], B, _ => by cases B <;> rfl
  | _, _ :: _, [], h => by simp [fixLv] at h
  | F, L :: Ls, b :: B, h => by
    rw [fixLv, Bool.and_eq_true] at h
    rw [prLv, List.map_cons, map_fst_prLv (b :: F) Ls B h.2]

theorem pruneOK_prLv {Q : List Nat} : ∀ (F : List Nat) (Ls : List (List Nat)) (B : List Nat),
    (∀ u ∈ F, u < 360) → (∀ u ∈ B, u < 360) → fixLv F Ls B = true →
      PruneOK (commAllN Q) (prLv Q F Ls B)
  | _, [], B, _, _, _ => by cases B <;> trivial
  | _, _ :: _, [], _, _, h => by simp [fixLv] at h
  | F, L :: Ls, b :: B, hF, hB, h => by
    have h2 : fixLv (b :: F) Ls B = true := by
      rw [fixLv, Bool.and_eq_true] at h
      exact h.2
    have hbF : ∀ u ∈ b :: F, u < 360 := fun u hu => by
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hB u List.mem_cons_self
      · exact hF u hu
    rw [prLv, PruneOK, map_fst_prLv (b :: F) Ls B h2]
    exact ⟨fun g acc hg => prune_sound hbF (fixLv_all (b :: F) Ls B h2) g acc hg,
      pruneOK_prLv (b :: F) Ls B hbF (fun u hu => hB u (List.mem_cons_of_mem _ hu)) h2⟩

theorem l3N_eq {Q B : List Nat} {Ls : List (List Nat)} (hB : ∀ u ∈ B, u < 360)
    (hfix : fixLv [] Ls B = true) :
    l3N Q B Ls = pfilterProducts 360 9 (commAllN Q) Ls (pidn 360 9) [] := by
  unfold l3N
  rw [pfilterPr_eq _ (pruneOK_prLv [] Ls B (fun _ h => absurd h List.not_mem_nil) hB hfix),
    map_fst_prLv [] Ls B hfix]

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6 (curtisRels curtisRankOne)

theorem foldl_congr_mem {α β : Type} {F G : β → α → β} :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ c, F c a = G c a) → l.foldl F b = l.foldl G b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self b]
    exact foldl_congr_mem l _ fun x hx c => h x (List.mem_cons_of_mem _ hx) c

theorem c2HTN_getD_congr (GT : List (Nat × Nat)) {cs cs' : List Nat} {i : Nat}
    (h : cs.getD i (pidn 360 9) = cs'.getD i (pidn 360 9)) :
    (c2HTN GT cs).getD i (pidn 360 9, pidn 360 9) = (c2HTN GT cs').getD i (pidn 360 9, pidn 360 9) := by
  by_cases hi : i < 8
  · unfold c2HTN
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range, h]
  · rw [List.getD_eq_default _ _ (by simp [c2HTN]; omega),
      List.getD_eq_default _ _ (by simp [c2HTN]; omega)]

theorem wordsN_congr (GT : List (Nat × Nat)) {TG : List (List Nat × Nat)} {cs cs' : List Nat}
    (h : ∀ wt ∈ TG, ∀ i ∈ wt.1, cs.getD i (pidn 360 9) = cs'.getD i (pidn 360 9)) :
    wordsN GT TG cs = wordsN GT TG cs' := by
  unfold wordsN
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun wt => imp_congr_right fun hwt => ?_
  unfold wordHN
  rw [foldl_congr_mem wt.1 _ fun i hi c => by rw [c2HTN_getD_congr GT (h wt hwt i hi)]]

theorem relsN_congr (GT : List (Nat × Nat)) {R : List (List Nat)} {cs cs' : List Nat}
    (h : ∀ r ∈ R, ∀ k ∈ r, cs.getD (k / 2) (pidn 360 9) = cs'.getD (k / 2) (pidn 360 9)) :
    relsN GT R cs = relsN GT R cs' := by
  unfold relsN
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun r => imp_congr_right fun hr => ?_
  unfold evalHN
  rw [foldl_congr_mem r _ fun k hk c => by rw [c2HTN_getD_congr GT (h r hr k hk)]]

theorem relsN_false_of_sub (GT : List (Nat × Nat)) {R R' : List (List Nat)} {cs : List Nat}
    (hR : ∀ r ∈ R, r ∈ R') (h : relsN GT R cs = false) : relsN GT R' cs = false := by
  unfold relsN at *
  rw [List.all_eq_false] at *
  obtain ⟨r, hr, h⟩ := h
  exact ⟨r, hR r hr, h⟩

theorem rankOne_facts : ∀ j < 4, ∀ r ∈ curtisRankOne j, r ∈ curtisRels ∧
    ∀ k ∈ r, k / 2 = 2 * j ∨ k / 2 = 2 * j + 1 := by
  decide

theorem not_true_eq {b : Bool} (h : (!b) = true) : b = false := by simpa using h

theorem sections_of_treeN {GT : List (Nat × Nat)} {TG : List (List Nat × Nat)} {ZC : List Nat}
    {L0 L1 L2 L3 L4 L5 L6 L7 : List Nat}
    (hTG : ∀ wt ∈ TG, ∀ i ∈ wt.1, i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6)
    (h : treeN GT TG ZC [L0, L1, L2, L3, L4, L5, L6, L7] = true) :
    (List.sections [L0, L1, L2, L3, L4, L5, L6, L7]).all (c2PN GT TG ZC) = true := by
  rw [List.all_eq_true]
  intro cs hcs
  rw [List.mem_sections] at hcs
  obtain ⟨c0, s0, h0, hs0, rfl⟩ := List.forall₂_cons_right_iff.1 hcs
  obtain ⟨c1, s1, h1, hs1, rfl⟩ := List.forall₂_cons_right_iff.1 hs0
  obtain ⟨c2, s2, h2, hs2, rfl⟩ := List.forall₂_cons_right_iff.1 hs1
  obtain ⟨c3, s3, h3, hs3, rfl⟩ := List.forall₂_cons_right_iff.1 hs2
  obtain ⟨c4, s4, h4, hs4, rfl⟩ := List.forall₂_cons_right_iff.1 hs3
  obtain ⟨c5, s5, h5, hs5, rfl⟩ := List.forall₂_cons_right_iff.1 hs4
  obtain ⟨c6, s6, h6, hs6, rfl⟩ := List.forall₂_cons_right_iff.1 hs5
  obtain ⟨c7, s7, h7, hs7, rfl⟩ := List.forall₂_cons_right_iff.1 hs6
  rw [List.forall₂_nil_right_iff.1 hs7]
  simp only [treeN, List.getD_cons_zero, List.getD_cons_succ] at h
  have t := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1
    (List.all_eq_true.1 h c0 h0) c2 h2) c4 h4) c6 h6
  have hc2P : ∀ (R : List (List Nat)), relsN GT R [c0, c1, c2, c3, c4, c5, c6, c7] = false →
      (∀ r ∈ R, r ∈ curtisRels) → c2PN GT TG ZC [c0, c1, c2, c3, c4, c5, c6, c7] = true := by
    intro R hR hsub
    unfold c2PN
    rw [relsN_false_of_sub GT hsub hR]
    simp
  have node : ∀ j < 4, ∀ cs' : List Nat, (∀ i, i = 2 * j ∨ i = 2 * j + 1 →
      [c0, c1, c2, c3, c4, c5, c6, c7].getD i (pidn 360 9) = cs'.getD i (pidn 360 9)) →
      relsN GT (curtisRankOne j) cs' = false →
      c2PN GT TG ZC [c0, c1, c2, c3, c4, c5, c6, c7] = true := by
    intro j hj cs' hcs' hr
    refine hc2P (curtisRankOne j) ?_ fun r hr => (rankOne_facts j hj r hr).1
    rw [relsN_congr GT fun r hr k hk => hcs' _ ((rankOne_facts j hj r hr).2 k hk)]
    exact hr
  rcases Bool.or_eq_true_iff.1 t with t | t
  · unfold c2PN
    rw [wordsN_congr GT (cs' := [c0, pidn 360 9, c2, pidn 360 9, c4, pidn 360 9, c6, pidn 360 9])
      fun wt hwt i hi => by rcases hTG wt hwt i hi with rfl | rfl | rfl | rfl <;> rfl,
      not_true_eq t]
    simp
  have t := List.all_eq_true.1 t c1 h1
  rcases Bool.or_eq_true_iff.1 t with t | t
  · exact node 0 (by norm_num) _ (fun i hi => by rcases hi with rfl | rfl <;> rfl) (not_true_eq t)
  have t := List.all_eq_true.1 t c3 h3
  rcases Bool.or_eq_true_iff.1 t with t | t
  · exact node 1 (by norm_num) _ (fun i hi => by rcases hi with rfl | rfl <;> rfl) (not_true_eq t)
  have t := List.all_eq_true.1 t c5 h5
  rcases Bool.or_eq_true_iff.1 t with t | t
  · exact node 2 (by norm_num) _ (fun i hi => by rcases hi with rfl | rfl <;> rfl) (not_true_eq t)
  have t := List.all_eq_true.1 t c7 h7
  rcases Bool.or_eq_true_iff.1 t with t | t
  · exact node 3 (by norm_num) _ (fun i hi => by rcases hi with rfl | rfl <;> rfl) (not_true_eq t)
  rcases Bool.or_eq_true_iff.1 t with t | t
  · exact hc2P curtisRels (not_true_eq t) fun r hr => hr
  · unfold c2PN
    rw [t]
    simp

end CFSG.KC.AE6C2

end
