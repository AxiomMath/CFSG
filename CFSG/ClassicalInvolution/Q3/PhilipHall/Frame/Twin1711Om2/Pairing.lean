module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.FixSet

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA keyF)
open CFSG.ClassicalInvolution.Generic
open scoped Pointwise

set_option linter.unusedSectionVars false

private theorem pr2_lookup {f : ℕ → ℕ} {n : ℕ} (hf : ∀ i < n, ∀ j < n, f i = f j → i = j) :
    ∀ j < n, ((List.range n).foldl (fun m i => m.insert (f i) i)
      (∅ : Std.HashMap ℕ ℕ)).get? (f j) = some j := by
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro j hj
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.get?_insert]
    by_cases hjn : j = n
    · subst hjn
      simp
    · have hjn' : j < n := by omega
      have hne : f n ≠ f j := fun h => hjn (hf n (by omega) j hj h).symm
      have := ih (fun i hi k hk => hf i (by omega) k (by omega)) j hjn'
      rw [if_neg (by simpa using hne)]
      exact this

private theorem pr2_commutes_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    Commutes (Subgroup.closure S) (Subgroup.closure T) := by
  have h1 : ∀ s ∈ S, Subgroup.closure T ≤ Subgroup.centralizer {s} := by
    intro s hs
    rw [Subgroup.closure_le]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.2 (h s hs t ht).symm
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 s hs hy)
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (h2 hx)) y hy).symm


private theorem pr2_invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

private theorem pr2_rep_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [pr2_invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

private theorem pr2_validA_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : Rep n t g) : CFSG.RankThree.Native.validA n t = true := by
  have hr := pr2_rep_invCand ht
  rw [CFSG.RankThree.Native.validA, CFSG.Monster.B.Co2.Native.isInvA,
    CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

private theorem pr2_rep_conjY {S c : Array ℕ} {s g : HY} (hS : Rep 480 S (phi s))
    (hc : Rep 480 c (phi g)) :
    Rep 480 (CFSG.RankThree.Native.conjA 480 S c) (phi (s * g * s⁻¹)) := by
  have h1 := CFSG.RankThree.Native.rep_conjA (pr2_validA_of_rep hS) hc
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hS] at h1
  rw [map_mul, map_mul, map_inv]
  exact h1

private theorem pr2_comm_of_commY {a b : Array ℕ} {x y : HY} (ha : Rep 480 a (phi x))
    (hb : Rep 480 b (phi y)) (h : commY a b = true) : x * y = y * x := by
  unfold commY at h
  have := (eqA_iff (rep_compA ha hb) (rep_compA hb ha)).1 h
  apply phi_injective
  simpa only [map_mul] using this

private theorem pr2_commY_of_comm {a b : Array ℕ} {x y : HY} (ha : Rep 480 a (phi x))
    (hb : Rep 480 b (phi y)) (h : x * y = y * x) : commY a b = true := by
  unfold commY
  refine (eqA_iff (rep_compA ha hb) (rep_compA hb ha)).2 ?_
  rw [← map_mul, ← map_mul, h]

private theorem pr2_word {w : List ℕ} (hw : w ∈ allWordsY) :
    Rep 480 (wY (lettersY (reflTab ())) w) (phi (wordE w)) ∧
      CFSG.RankThree.Native.validA 480 (wY (lettersY (reflTab ())) w) = true :=
  ⟨rep_wordE (wordsCheckY_spec hw).1, (wordsCheckY_spec hw).2⟩

private theorem pr2_validFY_iff {F : Array ℕ} :
    validFY F = true ↔ (∀ x ∈ F.toList, x < 480) ∧ F.toList.Pairwise (· < ·) := by
  have hadj : (∀ i < F.size - 1, F[i]! < F[i + 1]!) ↔ F.toList.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    constructor
    · intro h i j hi hj hij
      simp only [Array.length_toList] at hi hj
      simp only [Array.getElem_toList]
      induction j, (Nat.succ_le_of_lt hij) using Nat.le_induction with
      | base =>
        have := h i (by omega)
        rwa [getElem!_pos F i hi, getElem!_pos F (i + 1) hj] at this
      | succ j hij ih =>
        have h1 := ih (by omega) (by omega)
        have h2 := h j (by omega)
        rw [getElem!_pos F j (by omega), getElem!_pos F (j + 1) hj] at h2
        exact h1.trans h2
    · intro h i hi
      have hi1 : i < F.size := by omega
      have hi2 : i + 1 < F.size := by omega
      have := h i (i + 1) (by simpa using hi1) (by simpa using hi2) (Nat.lt_succ_self i)
      rw [getElem!_pos F i hi1, getElem!_pos F (i + 1) hi2]
      simpa using this
  simp only [validFY, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Array.all_eq_true', hadj, Array.mem_toList_iff]

private theorem pr2_validFY_fCodeY (t : Array ℕ) : validFY (fCodeY t) = true := by
  rw [pr2_validFY_iff]
  simp only [fCodeY, List.toList_toArray]
  exact ⟨fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1,
    List.Pairwise.filter _ List.pairwise_lt_range⟩

private theorem pr2_getElem!_push_lt {α : Type} [Inhabited α] {xs : Array α} {x : α} {i : ℕ}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by simp only [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

private theorem pr2_getElem!_push_eq {α : Type} [Inhabited α] {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos (xs.push x) xs.size (by simp only [Array.size_push]; omega),
    Array.getElem_push_eq]

private def pr2_step (gs : Array (Array ℕ)) (c : ArrCert) (tw : Array (Array ℕ)) (i : ℕ) :
    Array (Array ℕ) :=
  tw.push (compA 480 gs[c.lab[i]!]! tw[c.par[i]!]!)

private def pr2_tw (gs : Array (Array ℕ)) (c : ArrCert) (k : ℕ) : Array (Array ℕ) :=
  (List.range' 1 k).foldl (pr2_step gs c) #[idA 480]

private theorem pr2_treeArrs_eq (gs : Array (Array ℕ)) (c : ArrCert) :
    treeArrs gs c = pr2_tw gs c (c.pts.size - 1) := by
  unfold treeArrs
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.add_sub_cancel, Nat.div_one, bind_pure, pure_bind]
  rfl

private theorem pr2_tw_succ (gs : Array (Array ℕ)) (c : ArrCert) (k : ℕ) :
    pr2_tw gs c (k + 1) = pr2_step gs c (pr2_tw gs c k) (k + 1) := by
  unfold pr2_tw
  rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have : 1 + 1 * k = k + 1 := by omega
  rw [this]

private theorem pr2_tw_spec (gs : Array (Array ℕ)) (c : ArrCert)
    (hpar : ∀ i, 0 < i → i < c.pts.size → c.par[i]! < i) :
    ∀ k, k < c.pts.size →
      (pr2_tw gs c k).size = k + 1 ∧ (pr2_tw gs c k)[0]! = idA 480 ∧
      ∀ i, 0 < i → i ≤ k →
        (pr2_tw gs c k)[i]! = compA 480 gs[c.lab[i]!]! (pr2_tw gs c k)[c.par[i]!]! := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [pr2_tw], by simp [pr2_tw], fun i hi hik => absurd hik (by omega)⟩
  | succ k ih =>
    intro hk
    obtain ⟨hsz, h0, hi⟩ := ih (by omega)
    rw [pr2_tw_succ]
    have hpk := hpar (k + 1) (by omega) hk
    refine ⟨by simp only [pr2_step, Array.size_push, hsz], ?_, ?_⟩
    · rw [pr2_step, pr2_getElem!_push_lt (by omega), h0]
    · intro i hi0 hik
      by_cases hik' : i = k + 1
      · subst hik'
        have e1 : (pr2_step gs c (pr2_tw gs c k) (k + 1))[k + 1]! =
            compA 480 gs[c.lab[k + 1]!]! (pr2_tw gs c k)[c.par[k + 1]!]! := by
          have : k + 1 = (pr2_tw gs c k).size := hsz.symm
          rw [pr2_step, this, pr2_getElem!_push_eq]
        rw [e1, pr2_step, pr2_getElem!_push_lt (by omega)]
      · have hik2 : i ≤ k := by omega
        have hpi := hpar i hi0 (by omega)
        rw [pr2_step, pr2_getElem!_push_lt (by omega), pr2_getElem!_push_lt (by omega),
          hi i hi0 hik2]

private theorem pr2_rep_tw {gs : Array (Array ℕ)} {c : ArrCert} {gens : ℕ → HY}
    (hgens : ∀ k < gs.size, Rep 480 gs[k]! (phi (gens k))) (hpos : 0 < c.pts.size)
    (htree : ∀ i, 0 < i → i < c.pts.size → c.par[i]! < i ∧ c.lab[i]! < gs.size) :
    ∀ j < c.pts.size, Rep 480 (treeArrs gs c)[j]!
      (phi (CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens j)) := by
  have hspec := pr2_tw_spec gs c (fun i h0 hi => (htree i h0 hi).1) (c.pts.size - 1) (by omega)
  rw [← pr2_treeArrs_eq] at hspec
  obtain ⟨-, h0, hstep⟩ := hspec
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [h0, CFSG.Perm.treeWord_zero, map_one]
      exact rep_idA
    · obtain ⟨hp, hl⟩ := htree j hj0 hj
      rw [hstep j hj0 (by omega), CFSG.Perm.treeWord_of_pos (fun i => c.lab[i]!) gens hj0 hp,
        map_mul]
      exact rep_compA (hgens _ hl) (ih _ hp (hp.trans hj))

private def pr2_body (Z : List (Array ℕ)) (t0 i0 j0 : Array ℕ) (c : ArrCert)
    (tw : Array (Array ℕ)) (idx : Std.HashMap ℕ ℕ) (u : Array ℕ) : Bool :=
  !(eqA 480 (compA 480 u u) (idA 480)) ||
    (let F := fCodeY u
     let i := (idx.get? (keyF F)).getD c.pts.size
     !(decide (i < c.pts.size) && c.pts[i]! == F) ||
       (let g := tw[i]!
        eqA 480 (CFSG.RankThree.Native.conjA 480 g t0) u &&
          (!(commY (CFSG.RankThree.Native.conjA 480 g i0) i0 &&
              commY (CFSG.RankThree.Native.conjA 480 g i0) j0 &&
              commY (CFSG.RankThree.Native.conjA 480 g j0) i0 &&
              commY (CFSG.RankThree.Native.conjA 480 g j0) j0) ||
            inLY Z u)))

private theorem pr2_body_spec {Z : List (Array ℕ)} {t0 i0 j0 : Array ℕ} {c : ArrCert}
    {tw : Array (Array ℕ)} {idx : Std.HashMap ℕ ℕ} {a : Array ℕ}
    (hsq : eqA 480 (compA 480 a a) (idA 480) = true) {j : ℕ} (hj : j < c.pts.size)
    (hidx : idx.get? (keyF (fCodeY a)) = some j) (hpt : c.pts[j]! = fCodeY a)
    (hb : pr2_body Z t0 i0 j0 c tw idx a = true) :
    eqA 480 (CFSG.RankThree.Native.conjA 480 tw[j]! t0) a = true ∧
      ((commY (CFSG.RankThree.Native.conjA 480 tw[j]! i0) i0 = true ∧
          commY (CFSG.RankThree.Native.conjA 480 tw[j]! i0) j0 = true ∧
          commY (CFSG.RankThree.Native.conjA 480 tw[j]! j0) i0 = true ∧
          commY (CFSG.RankThree.Native.conjA 480 tw[j]! j0) j0 = true) → inLY Z a = true) := by
  unfold pr2_body at hb
  simp only [hsq, hidx, Option.getD_some, hpt, hj, Bool.not_true, Bool.false_or, beq_self_eq_true,
    decide_true, Bool.and_self, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hb
  obtain ⟨h1, h2⟩ := hb
  refine ⟨h1, fun ⟨c1, c2, c3, c4⟩ => ?_⟩
  rcases h2 with h2 | h2
  · simp [c1, c2, c3, c4] at h2
  · exact h2

private theorem pr2_pair_parts (RT : Array (Array ℕ)) (h : Om2Check.pairCheck RT = true) :
    (∀ w ∈ wFuse0,
      commY (CFSG.RankThree.Native.conjA 480 (wY (lettersY RT) w) (wY (lettersY RT) wI0))
        (wY (lettersY RT) wI0) = true ∧
      commY (CFSG.RankThree.Native.conjA 480 (wY (lettersY RT) w) (wY (lettersY RT) wI0))
        (wY (lettersY RT) wJ0) = true ∧
      commY (CFSG.RankThree.Native.conjA 480 (wY (lettersY RT) w) (wY (lettersY RT) wJ0))
        (wY (lettersY RT) wI0) = true ∧
      commY (CFSG.RankThree.Native.conjA 480 (wY (lettersY RT) w) (wY (lettersY RT) wJ0))
        (wY (lettersY RT) wJ0) = true) ∧
    ∀ (c : ArrCert) (tw : Array (Array ℕ)) (idx : Std.HashMap ℕ ℕ),
      c = orbFY (genY RT) (fCodeY (wY (lettersY RT) wT0)) 6301 →
      tw = treeArrs (genY RT) c →
      idx = (List.range c.pts.size).foldl (fun m i => m.insert (keyF c.pts[i]!) i) ∅ →
      ∀ a ∈ (enumOfY (lettersY RT) wCR 4609).pts,
        pr2_body (zt4 (lettersY RT)) (wY (lettersY RT) wT0) (wY (lettersY RT) wI0)
          (wY (lettersY RT) wJ0) c tw idx a = true := by
  simp only [Om2Check.pairCheck, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun w hw => ?_, ?_⟩
  · have := List.all_eq_true.1 h1 w hw
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · rintro c tw idx rfl rfl rfl a ha
    exact Array.all_eq_true'.1 h2 a ha

private theorem pr2_genY_size : (genY (reflTab ())).size = 8 := by
  simp [genY]

private theorem pr2_decF_F0 :
    decFY (fCodeY (wY (lettersY (reflTab ())) wT0)) = negSetY t0Y :=
  decFY_fCodeY (rep_wordE (wordsCheckY_spec (by simp [allWordsY] : wT0 ∈ allWordsY)).1)

private theorem pr2_orbit_ok :
    arrCertOK (fun k X => actFY (genY (reflTab ()))[k]! X) (genY (reflTab ())).size validFY keyF
      (fCodeY (wY (lettersY (reflTab ())) wT0))
      (orbFY (genY (reflTab ())) (fCodeY (wY (lettersY (reflTab ())) wT0)) 6301) = true := by
  have h := om2A_parts.2.2.2.2.1
  simp only [orbitCheckY, Bool.and_eq_true, orbSizeY] at h
  exact h.2.1

private theorem pr2_enum_CR : enumSizeY (lettersY (reflTab ())) wCR 4608 = true := by
  have h := om2A_parts.2.2.2.1
  simp only [enumCheckY, Bool.and_eq_true] at h
  exact h.2

private theorem pr2_zt4 {a : Array ℕ} {u : HY} (ha : Rep 480 a (phi u))
    (h : inLY (zt4 (lettersY (reflTab ()))) a = true) :
    u = t0Y ∨ ∃ k < 3, u = t0Y * cK k := by
  have hT0 := (pr2_word (w := wT0) (by simp [allWordsY])).1
  unfold inLY at h
  obtain ⟨z, hz, hae⟩ := List.any_eq_true.1 h
  simp only [zt4, List.mem_cons, List.mem_map, List.mem_range] at hz
  rcases hz with rfl | ⟨k, hk, rfl⟩
  · exact Or.inl (phi_injective ((eqA_iff ha hT0).1 hae))
  · refine Or.inr ⟨k, hk, phi_injective ?_⟩
    have := (eqA_iff ha (rep_compA hT0 (rep_cK hk))).1 hae
    rw [this, map_mul]

private theorem pr2_closureG_eq_top : closureG = ⊤ := by
  obtain ⟨hTW, hTstab, -, -, -, -, -, horb, -⟩ := classPkg0Y
  have hlet : ∀ l < 16, letE l ∈ closureG := by
    intro l hl
    unfold letE closureG
    split_ifs with h
    · exact Subgroup.subset_closure ⟨l, h, rfl⟩
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨l - 8, by simp only [Set.mem_setOf_eq]; omega, rfl⟩)
  have hT : closureY wT ≤ closureG := by
    rw [closureY, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hok := wordYOK_of_sub wT_sub w hw
    unfold wordYOK at hok
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    exact hlet l (by simpa using List.all_eq_true.1 hok l hl)
  refine OmGen.eq_top_of_orbit_eq (negSetY t0Y) le_rfl ?_ horb
  rw [← hTstab, ← hTW]
  exact hT

private theorem pr2_phi_mem_Yg (g : HY) : phi g ∈ Om2Facts.Yg := by
  have hws : ∀ w ∈ (List.range 8).map (fun i => [i]), wordYOK w = true := by decide
  have hle : closureG ≤ closureY ((List.range 8).map fun i => [i]) := by
    rw [closureG, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 8 := hk
    have e : wordE [k] = genE k := by simp [wordE, letE, hk']
    rw [SetLike.mem_coe, ← e]
    exact wordE_mem_closureY (List.mem_map.2 ⟨k, List.mem_range.2 hk', rfl⟩)
  have hg : g ∈ closureY ((List.range 8).map fun i => [i]) :=
    hle (by rw [pr2_closureG_eq_top]; exact Subgroup.mem_top g)
  exact (mem_closureY_iff hws).1 hg

private theorem pr2_key {g u : HY} (hu : u = g * t0Y * g⁻¹) (hmem : u ∈ closureY wCR) :
    ∃ x : HY, x * t0Y * x⁻¹ = u ∧
      (x * i0Y * x⁻¹ * i0Y = i0Y * (x * i0Y * x⁻¹) →
        x * i0Y * x⁻¹ * j0Y = j0Y * (x * i0Y * x⁻¹) →
        x * j0Y * x⁻¹ * i0Y = i0Y * (x * j0Y * x⁻¹) →
        x * j0Y * x⁻¹ * j0Y = j0Y * (x * j0Y * x⁻¹) →
        u = t0Y ∨ ∃ k < 3, u = t0Y * cK k) := by
  refine ⟨g, hu.symm, fun _ _ _ _ => ?_⟩
  have hsq : u * u = 1 := by
    rw [hu]
    calc g * t0Y * g⁻¹ * (g * t0Y * g⁻¹) = g * (t0Y * t0Y) * g⁻¹ := by group
      _ = 1 := by rw [t0Y_mul_self, mul_one, mul_inv_cancel]
  have h := Certificates.certificate197003.2.2.2.2.2.1 (phi u)
    ((mem_closureY_iff (wordYOK_of_sub wCR_sub)).1 hmem) (by rw [← map_mul, hsq, map_one])
    ⟨phi g, pr2_phi_mem_Yg g, by rw [hu, map_mul, map_mul, map_inv, phi_t0Y]⟩
  simp only [Om2Facts.Zt4, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h
  · exact Or.inl (phi_injective (h.trans phi_t0Y.symm))
  · exact Or.inr ⟨0, by norm_num, phi_injective (by rw [h, map_mul, phi_t0Y, phi_cK (by norm_num)])⟩
  · exact Or.inr ⟨1, by norm_num, phi_injective (by rw [h, map_mul, phi_t0Y, phi_cK (by norm_num)])⟩
  · exact Or.inr ⟨2, by norm_num, phi_injective (by rw [h, map_mul, phi_t0Y, phi_cK (by norm_num)])⟩

private theorem pr2_conjSub_of_mem_closure {g : HY} (hg : g ∈ closureY wT) :
    conjSub g R0Y = R0Y := by
  rw [closureY] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact conjSub_R0Y_of_mem hw
  | one => exact conjSub_one R0Y
  | mul a b _ _ ha hb => rw [conjSub_mul, hb, ha]
  | inv a _ ha =>
    calc conjSub a⁻¹ R0Y = conjSub a⁻¹ (conjSub a R0Y) := by rw [ha]
      _ = R0Y := conjSub_inv_conjSub a R0Y

theorem normalizer_R0Y (hR : IsUniqueInvolution R0Y t0Y) (g : HY) :
    conjSub g R0Y = R0Y ↔ g ∈ T0Y := by
  constructor
  · intro h
    have h1 := hR.conj_eq h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t0Y = g * t0Y * g⁻¹ * g := by group
      _ = t0Y * g := by rw [h1]
  · intro hg
    exact pr2_conjSub_of_mem_closure (by rw [classPkg0Y.1]; exact hg)

private theorem pr2_i0_mem : i0Y ∈ R0Y :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private theorem pr2_j0_mem : j0Y ∈ R0Y :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem pr2_eq_iff (hR : IsUniqueInvolution R0Y t0Y) {a b : HY} :
    conjSub a R0Y = conjSub b R0Y ↔ a * t0Y * a⁻¹ = b * t0Y * b⁻¹ := by
  constructor
  · intro h
    have h1 : conjSub (b⁻¹ * a) R0Y = R0Y := by
      rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have h3 := hR.conj_eq h1
    calc a * t0Y * a⁻¹ = b * ((b⁻¹ * a) * t0Y * (b⁻¹ * a)⁻¹) * b⁻¹ := by group
      _ = b * t0Y * b⁻¹ := by rw [h3]
  · intro h
    have h1 : b⁻¹ * a ∈ T0Y := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc b⁻¹ * a * t0Y = b⁻¹ * (a * t0Y * a⁻¹) * a := by group
        _ = b⁻¹ * (b * t0Y * b⁻¹) * a := by rw [h]
        _ = t0Y * (b⁻¹ * a) := by group
    have h2 := (normalizer_R0Y hR _).2 h1
    calc conjSub a R0Y = conjSub b (conjSub (b⁻¹ * a) R0Y) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
      _ = conjSub b R0Y := by rw [h2]

private theorem pr2_commutes_fuse0 {m : ℕ} (hm : m < 3) :
    Commutes R0Y (conjSub (fuse0 m) R0Y) := by
  have hlen : m < wFuse0.length := by simpa [wFuse0] using hm
  have hmem : wFuse0.getD m [] ∈ wFuse0 := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  have hok : ∀ w ∈ allWordsY, wordYOK w = true := fun w hw => (wordsCheckY_spec hw).1
  have hc : ∀ a ∈ [wI0, wJ0], ∀ b ∈ [wI0, wJ0],
      fuse0 m * wordE a * (fuse0 m)⁻¹ * wordE b = wordE b * (fuse0 m * wordE a * (fuse0 m)⁻¹) := by
    intro a ha b hb
    have hab : ∀ v ∈ [wI0, wJ0], v ∈ allWordsY := by simp [allWordsY]
    have e := (Certificates.certificate197003.2.2.2.2.2.2 _ hmem a ha b hb).eq
    apply phi_injective
    simp only [map_mul, map_inv]
    rw [phi_wordE (hok _ (hab a ha)), phi_wordE (hok _ (hab b hb)),
      phi_wordE (hok _ (wFuse0_sub _ hmem))]
    exact e
  have e1 := hc wI0 (by simp) wI0 (by simp)
  have e2 := hc wI0 (by simp) wJ0 (by simp)
  have e3 := hc wJ0 (by simp) wI0 (by simp)
  have e4 := hc wJ0 (by simp) wJ0 (by simp)
  rw [conjSub, R0Y, MonoidHom.map_closure]
  apply pr2_commutes_closure
  intro s hs t ht
  obtain ⟨y, hy, rfl⟩ := ht
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rcases hs with rfl | rfl <;> rcases hy with rfl | rfl
  · exact e1.symm
  · exact e3.symm
  · exact e2.symm
  · exact e4.symm

private noncomputable def pr2_f : ℕ → HY
  | 0 => 1
  | k + 1 => fuse0 k

private noncomputable def pr2_w : ℕ → HY
  | 0 => 1
  | k + 1 => cK k

private theorem pr2_f_conj {k : ℕ} (hk : k < 4) : pr2_f k * t0Y * (pr2_f k)⁻¹ = t0Y * pr2_w k := by
  cases k with
  | zero => simp [pr2_f, pr2_w]
  | succ k =>
    simp only [pr2_f, pr2_w]
    exact fuse0_conj (by omega)

private theorem pr2_w_comm (k : ℕ) (x : HY) : x * pr2_w k = pr2_w k * x := by
  cases k with
  | zero => simp [pr2_w]
  | succ k => exact cK_comm k x

private theorem pr2_w_inj {a b : ℕ} (ha : a < 4) (hb : b < 4) (h : pr2_w a = pr2_w b) :
    a = b := by
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ b => exact absurd h.symm (cK_ne_one (by omega))
  | succ a =>
    cases b with
    | zero => exact absurd h (cK_ne_one (by omega))
    | succ b => exact congrArg Nat.succ (cK_inj (by omega) (by omega) h)

private theorem pr2_prod (a b : ℕ) :
    (t0Y * pr2_w a) * (t0Y * pr2_w b) = pr2_w a * pr2_w b := by
  calc (t0Y * pr2_w a) * (t0Y * pr2_w b) = t0Y * (pr2_w a * t0Y) * pr2_w b := by
        simp only [mul_assoc]
    _ = t0Y * (t0Y * pr2_w a) * pr2_w b := by rw [← pr2_w_comm a t0Y]
    _ = (t0Y * t0Y) * pr2_w a * pr2_w b := by simp only [mul_assoc]
    _ = pr2_w a * pr2_w b := by rw [t0Y_mul_self, one_mul]

private theorem pr2_prod_central (a b : ℕ) (x : HY) :
    x * (pr2_w a * pr2_w b) = (pr2_w a * pr2_w b) * x := by
  calc x * (pr2_w a * pr2_w b) = (x * pr2_w a) * pr2_w b := by rw [mul_assoc]
    _ = (pr2_w a * x) * pr2_w b := by rw [pr2_w_comm a x]
    _ = pr2_w a * (x * pr2_w b) := by rw [mul_assoc]
    _ = pr2_w a * (pr2_w b * x) := by rw [pr2_w_comm b x]
    _ = (pr2_w a * pr2_w b) * x := by rw [mul_assoc]

private theorem pr2_commNbrs (hR : IsUniqueInvolution R0Y t0Y) :
    Twin1711.commNbrs (⊤ : Subgroup HY) R0Y =
      (fun k => conjSub (pr2_f k) R0Y) '' {k | k < 4} := by
  ext J
  constructor
  · rintro ⟨⟨g, -, hgJ⟩, hcase⟩
    subst hgJ
    rcases hcase with h | h
    · exact ⟨0, by norm_num, by simp [pr2_f, h]⟩
    · have hu : g * t0Y * g⁻¹ ∈ conjSub g R0Y := conj_mem_conjSub hR.mem
      have hcI : i0Y * (g * t0Y * g⁻¹) = (g * t0Y * g⁻¹) * i0Y := h _ pr2_i0_mem _ hu
      have hcJ : j0Y * (g * t0Y * g⁻¹) = (g * t0Y * g⁻¹) * j0Y := h _ pr2_j0_mem _ hu
      obtain ⟨x, hx, hmain⟩ := pr2_key (g := g) rfl
        (mem_closureY_wCR_of_comm hcI.symm hcJ.symm)
      have hxg : conjSub x R0Y = conjSub g R0Y := (pr2_eq_iff hR).2 hx
      have hxi : x * i0Y * x⁻¹ ∈ conjSub g R0Y := hxg ▸ conj_mem_conjSub pr2_i0_mem
      have hxj : x * j0Y * x⁻¹ ∈ conjSub g R0Y := hxg ▸ conj_mem_conjSub pr2_j0_mem
      rcases hmain (h _ pr2_i0_mem _ hxi).symm (h _ pr2_j0_mem _ hxi).symm
          (h _ pr2_i0_mem _ hxj).symm (h _ pr2_j0_mem _ hxj).symm with h0 | ⟨k, hk, hk'⟩
      · refine ⟨0, by norm_num, ?_⟩
        show conjSub 1 R0Y = conjSub g R0Y
        rw [pr2_eq_iff hR]
        simpa using h0.symm
      · refine ⟨k + 1, show k + 1 < 4 by omega, ?_⟩
        show conjSub (fuse0 k) R0Y = conjSub g R0Y
        rw [pr2_eq_iff hR, fuse0_conj hk]
        exact hk'.symm
  · rintro ⟨k, hk, rfl⟩
    have hk4 : k < 4 := hk
    refine ⟨⟨pr2_f k, Subgroup.mem_top _, rfl⟩, ?_⟩
    cases k with
    | zero => exact Or.inl (by simp [pr2_f])
    | succ m => exact Or.inr (pr2_commutes_fuse0 (by omega))

theorem pairing_R0Y (hR : IsUniqueInvolution R0Y t0Y) :
    (Twin1711.commNbrs (⊤ : Subgroup HY) R0Y).ncard = 4 ∧
      ∀ J ∈ Twin1711.commNbrs (⊤ : Subgroup HY) R0Y, ∀ J' ∈ Twin1711.commNbrs (⊤ : Subgroup HY) R0Y,
        J ≠ J' → ∀ u u' : HY, IsUniqueInvolution J u → IsUniqueInvolution J' u' →
          u ≠ u' ∧ ∀ x ∈ (⊤ : Subgroup HY), x * (u * u') = (u * u') * x := by
  refine ⟨?_, ?_⟩
  · have hinj : Set.InjOn (fun k => conjSub (pr2_f k) R0Y) {k | k < 4} := by
      intro a ha b hb h
      have := (pr2_eq_iff hR).1 h
      rw [pr2_f_conj ha, pr2_f_conj hb] at this
      exact pr2_w_inj ha hb (mul_left_cancel this)
    rw [pr2_commNbrs hR, hinj.ncard_image]
    exact Set.ncard_Iio_nat 4
  · rintro J hJ J' hJ' hne u u' hu hu'
    rw [pr2_commNbrs hR] at hJ hJ'
    obtain ⟨a, ha, rfl⟩ := hJ
    obtain ⟨b, hb, rfl⟩ := hJ'
    have hua : u = t0Y * pr2_w a := (hu.eq (hR.conj (pr2_f a))).trans (pr2_f_conj ha)
    have hub : u' = t0Y * pr2_w b := (hu'.eq (hR.conj (pr2_f b))).trans (pr2_f_conj hb)
    have hab : a ≠ b := fun h => hne (by rw [h])
    refine ⟨?_, fun x _ => ?_⟩
    · rw [hua, hub]
      intro h
      exact hab (pr2_w_inj ha hb (mul_left_cancel h))
    · rw [hua, hub, pr2_prod]
      exact pr2_prod_central a b x

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
