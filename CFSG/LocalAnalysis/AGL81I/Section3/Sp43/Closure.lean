module

public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Group
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Sp43

open CFSG.Sp43.Native Subgroup

@[expose] noncomputable def member (i : ℕ) : Subgroup G := sub2 memGens[i]!.1 memGens[i]!.2

def memSearch (i : ℕ) : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  bfs #[memGens[i]!.1, memGens[i]!.2] 2000

private theorem check_split (h : sp43Check () = true) :
    groupOK (spArr ()) (etree (spArr ()) #[memGens[5]!.1, memGens[5]!.2]) = true ∧
      membersOK (threeArr (spArr ())) ((Array.range 5).map memSearch) = true := by
  unfold sp43Check checkE at h
  exact Bool.and_eq_true _ _ |>.mp h

private theorem groupOK_parts {E : Array ℕ} {tr : Array ℕ × Array ℕ × Array ℕ}
    (h : groupOK E tr = true) :
    E.size = 51840 ∧ incOK E = true ∧ codesOK E = true ∧
      treeOK E #[memGens[5]!.1, memGens[5]!.2] tr.1 tr.2.1 tr.2.2 = true ∧ gOK E = true := by
  unfold groupOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem card_G_of_check (h : sp43Check () = true) : Nat.card G = 51840 := by
  obtain ⟨h1, h2, -⟩ := groupOK_parts (check_split h).1
  exact card_G h1 h2

theorem symp_of_memS {c : ℕ} (h : memS (spArr ()) c = true) : Symp c := by
  obtain ⟨i, hi, rfl⟩ := memS_spec h
  exact symp_spArr hi

private theorem memSearch_get {i : ℕ} (hi : i < 5) : ((Array.range 5).map memSearch)[i]! =
    memSearch i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

private theorem membersOK_parts {T : Array ℕ}
    (h : membersOK T ((Array.range 5).map memSearch) = true) :
    (∀ i < 5, memberOK T (((Array.range 5).map memSearch).map (·.1)) i (memSearch i) = true) ∧
      h3OK (memSearch 3).1 = true ∧ h4OK (memSearch 4).1 = true := by
  unfold membersOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨-, hall⟩, h3⟩, h4⟩ := h
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have := hall i hi
    rwa [memSearch_get hi] at this
  · have e : (((Array.range 5).map memSearch).map (·.1))[3]! = (memSearch 3).1 := by
      rw [getElem!_pos _ 3 (by simp)]
      simp
    rwa [e] at h3
  · have e : (((Array.range 5).map memSearch).map (·.1))[4]! = (memSearch 4).1 := by
      rw [getElem!_pos _ 4 (by simp)]
      simp
    rwa [e] at h4

private theorem memberOK_parts {T : Array ℕ} {Ls : Array (Array ℕ)} {i : ℕ}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : memberOK T Ls i r = true) :
    subOK #[memGens[i]!.1, memGens[i]!.2] memOrders[i]! r = true ∧
      normOK r.1 memGens[i]! normGens[i]! normInvs[i]! = true ∧
      orbitOK r.1 T normGens[i]! normInvs[i]! (cases[i]!.map (·.x))
        (orbits r.1 T normGens[i]! normInvs[i]! (cases[i]!.map (·.x))) = true ∧
      cases[i]!.all (caseOK Ls memGens[i]!) = true := by
  unfold memberOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

structure Facts : Prop where
  card : Nat.card G = 51840
  codes : codesOK (spArr ()) = true
  tree : treeOK (spArr ()) #[memGens[5]!.1, memGens[5]!.2]
    (etree (spArr ()) #[memGens[5]!.1, memGens[5]!.2]).1
    (etree (spArr ()) #[memGens[5]!.1, memGens[5]!.2]).2.1
    (etree (spArr ()) #[memGens[5]!.1, memGens[5]!.2]).2.2 = true
  g : gOK (spArr ()) = true
  mem : ∀ i < 5, memberOK (threeArr (spArr ())) (((Array.range 5).map memSearch).map (·.1)) i
    (memSearch i) = true
  h3 : h3OK (memSearch 3).1 = true
  h4 : h4OK (memSearch 4).1 = true

theorem facts_of_check (h : sp43Check () = true) : Facts := by
  obtain ⟨hg, hm⟩ := check_split h
  obtain ⟨h1, h2, h3, h4, h5⟩ := groupOK_parts hg
  obtain ⟨hm1, hm2, hm3⟩ := membersOK_parts hm
  exact ⟨card_G h1 h2, h3, h4, h5, hm1, hm2, hm3⟩

private theorem codesOK_parts (h : codesOK (spArr ()) = true) :
    memGens.all (fun g => memS (spArr ()) g.1 && memS (spArr ()) g.2) = true ∧
      normGens.all (fun g => memS (spArr ()) g.1 && memS (spArr ()) g.2) = true ∧
      normInvs.all (fun g => memS (spArr ()) g.1 && memS (spArr ()) g.2) = true ∧
      cases.all (fun cs => cs.all fun c =>
        memS (spArr ()) c.x && memS (spArr ()) c.g && memS (spArr ()) c.gi) = true ∧
      [h4Data.1, h4Data.2.1, h4Data.2.2.1, h4Data.2.2.2.1, h4Data.2.2.2.2, p0Data.1,
        p0Data.2.1, p0Data.2.2.1, p0Data.2.2.2.1, p0Data.2.2.2.2.1, p0Data.2.2.2.2.2.1,
        minusOneC].all (memS (spArr ())) = true := by
  unfold codesOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem symp_pair_of_all {A : Array (ℕ × ℕ)}
    (h : A.all (fun g => memS (spArr ()) g.1 && memS (spArr ()) g.2) = true) {i : ℕ}
    (hi : i < A.size) : Symp A[i]!.1 ∧ Symp A[i]!.2 := by
  rw [Array.all_eq_true] at h
  have := h i hi
  simp only [Bool.and_eq_true] at this
  rw [getElem!_pos A i hi]
  exact ⟨symp_of_memS this.1, symp_of_memS this.2⟩

theorem Facts.symp_memGens (F : Facts) {i : ℕ} (hi : i < 6) :
    Symp memGens[i]!.1 ∧ Symp memGens[i]!.2 :=
  symp_pair_of_all (codesOK_parts F.codes).1 (lt_of_lt_of_eq hi rfl)

theorem Facts.symp_normGens (F : Facts) {i : ℕ} (hi : i < 5) :
    Symp normGens[i]!.1 ∧ Symp normGens[i]!.2 :=
  symp_pair_of_all (codesOK_parts F.codes).2.1 (lt_of_lt_of_eq hi rfl)

theorem Facts.symp_normInvs (F : Facts) {i : ℕ} (hi : i < 5) :
    Symp normInvs[i]!.1 ∧ Symp normInvs[i]!.2 :=
  symp_pair_of_all (codesOK_parts F.codes).2.2.1 (lt_of_lt_of_eq hi rfl)

theorem Facts.symp_case (F : Facts) {i : ℕ} (hi : i < 5) {r : ℕ} (hr : r < (cases[i]!).size) :
    Symp (cases[i]!)[r]!.x ∧ Symp (cases[i]!)[r]!.g ∧ Symp (cases[i]!)[r]!.gi := by
  have h := (codesOK_parts F.codes).2.2.2.1
  rw [Array.all_eq_true] at h
  have hi' : i < cases.size := lt_of_lt_of_eq hi rfl
  have h' := h i hi'
  rw [Array.all_eq_true] at h'
  have h'' := h' r (by rwa [getElem!_pos cases i hi'] at hr)
  simp only [Bool.and_eq_true] at h''
  rw [getElem!_pos cases i hi', getElem!_pos _ r (by rwa [getElem!_pos cases i hi'] at hr)]
  exact ⟨symp_of_memS h''.1.1, symp_of_memS h''.1.2, symp_of_memS h''.2⟩

theorem Facts.symp_extra (F : Facts) :
    Symp h4Data.1 ∧ Symp h4Data.2.1 ∧ Symp h4Data.2.2.1 ∧ Symp h4Data.2.2.2.1 ∧
      Symp h4Data.2.2.2.2 ∧ Symp p0Data.1 ∧ Symp p0Data.2.1 ∧ Symp p0Data.2.2.1 ∧
      Symp p0Data.2.2.2.1 ∧ Symp p0Data.2.2.2.2.1 ∧ Symp p0Data.2.2.2.2.2.1 ∧
      Symp minusOneC := by
  have h := (codesOK_parts F.codes).2.2.2.2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨symp_of_memS h1, symp_of_memS h2, symp_of_memS h3, symp_of_memS h4, symp_of_memS h5,
    symp_of_memS h6, symp_of_memS h7, symp_of_memS h8, symp_of_memS h9, symp_of_memS h10,
    symp_of_memS h11, symp_of_memS h12⟩

theorem Facts.subOK (F : Facts) {i : ℕ} (hi : i < 5) :
    subOK #[memGens[i]!.1, memGens[i]!.2] memOrders[i]! (memSearch i) = true :=
  (memberOK_parts (F.mem i hi)).1

theorem Facts.card_member (F : Facts) {i : ℕ} (hi : i < 5) :
    Nat.card (member i) = memOrders[i]! :=
  (subOK_spec (F.symp_memGens (by omega)).1 (F.symp_memGens (by omega)).2 (F.subOK hi)).2.2.2

theorem Facts.mem_member_of_memS (F : Facts) {i : ℕ} (hi : i < 5) {c : ℕ}
    (h : memS (memSearch i).1 c = true) : Symp c ∧ ofCode c ∈ member i :=
  mem_sub2_of_memS (F.symp_memGens (by omega)).1 (F.symp_memGens (by omega)).2 (F.subOK hi) h

theorem Facts.member_five (F : Facts) : member 5 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨i, hi, rfl⟩ := exists_spArr g
  exact (treeOK_spec (F.symp_memGens (by norm_num)).1 (F.symp_memGens (by norm_num)).2 F.tree
    i hi).2

theorem ofCode_inv_of_mulF {a b : ℕ} (ha : Symp a) (hb : Symp b) (h : mulF a b = oneC) :
    ofCode b = (ofCode a)⁻¹ := by
  have : ofCode a * ofCode b = 1 := by rw [← ofCode_mulF ha hb, h, ofCode_oneC]
  exact eq_inv_of_mul_eq_one_right this

theorem symp_conjC {n ni k : ℕ} (hn : Symp n) (hni : Symp ni) (hk : Symp k) :
    Symp (conjC n ni k) :=
  symp_mulF (symp_mulF hn hk) hni

theorem ofCode_conjC {n ni k : ℕ} (hn : Symp n) (hni : Symp ni) (hk : Symp k)
    (h : mulF n ni = oneC) : ofCode (conjC n ni k) = ofCode n * ofCode k * (ofCode n)⁻¹ := by
  unfold conjC
  rw [ofCode_mulF (symp_mulF hn hk) hni, ofCode_mulF hn hk, ofCode_inv_of_mulF hn hni h]

theorem mem_normalizer_of_conj {X : Type*} [Group X] [Finite X] {s : Set X} {n : X}
    (h : ∀ k ∈ s, n * k * n⁻¹ ∈ Subgroup.closure s) :
    n ∈ normalizer (Subgroup.closure s : Set X) := by
  set H := Subgroup.closure s
  have hle : H.map (MulAut.conj n).toMonoidHom ≤ H := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hcard : Nat.card ↥(H.map (MulAut.conj n).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have heq : H.map (MulAut.conj n).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← heq]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', e⟩ := hg
    have : g' = g := by simpa using e
    rwa [← this]

theorem Facts.normGens_le (F : Facts) {i : ℕ} (hi : i < 5) :
    sub2 normGens[i]!.1 normGens[i]!.2 ≤ normalizer (member i : Set G) := by
  have h := (memberOK_parts (F.mem i hi)).2.1
  unfold normOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨⟨hi1, hi2⟩, hall⟩ := h
  obtain ⟨hg1, hg2⟩ := F.symp_memGens (i := i) (by omega)
  obtain ⟨hn1, hn2⟩ := F.symp_normGens hi
  obtain ⟨hm1, hm2⟩ := F.symp_normInvs hi
  have hk : ∀ k < 2, memS (memSearch i).1 (conjC normGens[i]!.1 normInvs[i]!.1
      #[memGens[i]!.1, memGens[i]!.2][k]!) = true ∧
      memS (memSearch i).1 (conjC normGens[i]!.2 normInvs[i]!.2
        #[memGens[i]!.1, memGens[i]!.2][k]!) = true := by
    intro k hk2
    have := hall k (by simpa using hk2)
    rw [getElem!_pos _ k (by simpa using hk2)]
    simpa only [Bool.and_eq_true] using this
  have hgen : ∀ (n ni : ℕ), Symp n → Symp ni → mulF n ni = oneC →
      (∀ k < 2, memS (memSearch i).1 (conjC n ni #[memGens[i]!.1, memGens[i]!.2][k]!) = true) →
      ofCode n ∈ normalizer (member i : Set G) := by
    intro n ni hn hni hnn hmem
    apply mem_normalizer_of_conj
    rintro k (rfl | rfl)
    · have := F.mem_member_of_memS hi (hmem 0 (by norm_num))
      rw [ofCode_conjC hn hni (by simpa using hg1) hnn] at this
      exact this.2
    · have := F.mem_member_of_memS hi (hmem 1 (by norm_num))
      rw [ofCode_conjC hn hni (by simpa using hg2) hnn] at this
      exact this.2
  rw [sub2, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact hgen _ _ hn1 hm1 hi1 fun k hk2 => (hk k hk2).1
  · exact hgen _ _ hn2 hm2 hi2 fun k hk2 => (hk k hk2).2

theorem orbitOK_spec {L T : Array ℕ} {ns nis : ℕ × ℕ} {reps : Array ℕ}
    {w : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ}
    (hT : ∀ t < T.size, Symp T[t]!) (h1 : Symp ns.1) (h2 : Symp ns.2) (h1' : Symp nis.1)
    (h2' : Symp nis.2) (hi1 : mulF ns.1 nis.1 = oneC) (hi2 : mulF ns.2 nis.2 = oneC)
    (h : orbitOK L T ns nis reps w = true) {t : ℕ} (ht : t < T.size) :
    memS L T[t]! = true ∨
      ∃ r < reps.size, ∃ n ∈ sub2 ns.1 ns.2, ofCode T[t]! = n * ofCode reps[r]! * n⁻¹ := by
  obtain ⟨kind, par, lab, rep, dep⟩ := w
  unfold orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨-, hall⟩ := h
  have claim : ∀ d, ∀ u < T.size, dep[u]! = d → kind[u]! = 1 → rep[u]! < reps.size ∧
      ∃ n ∈ sub2 ns.1 ns.2, ofCode T[u]! = n * ofCode reps[rep[u]!]! * n⁻¹ := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro u hu hd hk
      rcases hall u hu with ⟨hk0, -⟩ | ⟨⟨-, hr⟩, h0 | hpar⟩
      · omega
      · refine ⟨hr, 1, Subgroup.one_mem _, ?_⟩
        rw [h0.2]
        simp
      · obtain ⟨⟨⟨⟨hp, hkp⟩, hrp⟩, hdp⟩, hlab⟩ := hpar
        obtain ⟨-, n', hn', e⟩ := ih (dep[par[u]!]!) (by omega) (par[u]!) hp rfl hkp
        refine ⟨hr, ?_⟩
        rw [hrp] at e
        rcases hlab with ⟨-, hT'⟩ | ⟨-, hT'⟩
        · refine ⟨ofCode ns.1 * n',
            Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hn', ?_⟩
          rw [hT', ofCode_conjC h1 h1' (hT _ hp) hi1, e]
          group
        · refine ⟨ofCode ns.2 * n',
            Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hn', ?_⟩
          rw [hT', ofCode_conjC h2 h2' (hT _ hp) hi2, e]
          group
  rcases hall t ht with ⟨-, hm⟩ | ⟨⟨hk, -⟩, -⟩
  · exact Or.inl hm
  · obtain ⟨hr, n, hn, e⟩ := claim _ t ht rfl hk
    exact Or.inr ⟨rep[t]!, hr, n, hn, e⟩

private theorem foldl_mem {gl : Array ℕ} {K : Subgroup G}
    (hgl : ∀ k < gl.size, Symp gl[k]! ∧ ofCode gl[k]! ∈ K) :
    ∀ (w : Word) (acc : ℕ), Symp acc → ofCode acc ∈ K →
      w.all (fun ae => decide (ae.1 < gl.size)) = true →
      Symp (w.foldl (fun acc ae => mulF acc (powC gl[ae.1]! ae.2)) acc) ∧
        ofCode (w.foldl (fun acc ae => mulF acc (powC gl[ae.1]! ae.2)) acc) ∈ K
  | [], _, ha, hK, _ => ⟨ha, hK⟩
  | ae :: w, acc, ha, hK, hw => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hk, hw⟩ := hw
    obtain ⟨hs, hm⟩ := hgl ae.1 hk
    rw [List.foldl_cons]
    refine foldl_mem hgl w _ (symp_mulF ha (symp_powC hs ae.2)) ?_ hw
    rw [ofCode_mulF ha (symp_powC hs ae.2), ofCode_powC hs]
    exact K.mul_mem hK (K.pow_mem hm _)

theorem evalW_mem {gl : Array ℕ} {K : Subgroup G}
    (hgl : ∀ k < gl.size, Symp gl[k]! ∧ ofCode gl[k]! ∈ K) {w : Word}
    (hw : w.all (fun ae => decide (ae.1 < gl.size)) = true) :
    Symp (evalW gl w) ∧ ofCode (evalW gl w) ∈ K :=
  foldl_mem hgl w oneC symp_oneC (by rw [ofCode_oneC]; exact K.one_mem) hw

private theorem Ls_get {j : ℕ} (hj : j < 5) :
    (((Array.range 5).map memSearch).map (·.1))[j]! = (memSearch j).1 := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

private theorem caseOK_parts {Ls : Array (Array ℕ)} {gs : ℕ × ℕ} {c : Case}
    (h : caseOK Ls gs c = true) :
    c.j < 6 ∧ mulF c.g c.gi = oneC ∧ c.w1.all (fun ae => decide (ae.1 < 3)) = true ∧
      c.w2.all (fun ae => decide (ae.1 < 3)) = true ∧
      (c.j = 5 ∨ #[gs.1, gs.2, c.x].all (fun k => memS Ls[c.j]! (conjC c.g c.gi k)) = true) ∧
      evalW #[gs.1, gs.2, c.x] c.w1 = conjC c.gi c.g memGens[c.j]!.1 ∧
      evalW #[gs.1, gs.2, c.x] c.w2 = conjC c.gi c.g memGens[c.j]!.2 := by
  unfold caseOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem Facts.case_spec (F : Facts) {i : ℕ} (hi : i < 5) {r : ℕ} (hr : r < (cases[i]!).size) :
    (cases[i]!)[r]!.j < 6 ∧ member i ⊔ zpowers (ofCode (cases[i]!)[r]!.x) =
      (member (cases[i]!)[r]!.j).map (MulAut.conj (ofCode (cases[i]!)[r]!.g)⁻¹).toMonoidHom := by
  set c := (cases[i]!)[r]!
  have hc : caseOK (((Array.range 5).map memSearch).map (·.1)) memGens[i]! c = true := by
    have h := (memberOK_parts (F.mem i hi)).2.2.2
    rw [Array.all_eq_true] at h
    have := h r hr
    rwa [← getElem!_pos (cases[i]!) r hr] at this
  obtain ⟨hj, hgi, hw1, hw2, hmem, he1, he2⟩ := caseOK_parts hc
  obtain ⟨hx, hg, hgi'⟩ := F.symp_case hi hr
  obtain ⟨ha, hb⟩ := F.symp_memGens (i := i) (by omega)
  obtain ⟨hh1, hh2⟩ := F.symp_memGens hj
  have hginv : ofCode c.gi = (ofCode c.g)⁻¹ := ofCode_inv_of_mulF hg hgi' hgi
  refine ⟨hj, le_antisymm ?_ ?_⟩
  ·
    have key : ∀ k : ℕ, Symp k → ofCode c.g * ofCode k * (ofCode c.g)⁻¹ ∈ member c.j →
        ofCode k ∈ (member c.j).map (MulAut.conj (ofCode c.g)⁻¹).toMonoidHom := by
      intro k _ hk
      refine ⟨_, hk, ?_⟩
      simp [mul_assoc]
    have gens : ∀ k < 3, Symp #[memGens[i]!.1, memGens[i]!.2, c.x][k]! ∧
        ofCode #[memGens[i]!.1, memGens[i]!.2, c.x][k]! ∈
          (member c.j).map (MulAut.conj (ofCode c.g)⁻¹).toMonoidHom := by
      intro k hk3
      have hsk : Symp #[memGens[i]!.1, memGens[i]!.2, c.x][k]! := by
        interval_cases k <;> simpa
      refine ⟨hsk, key _ hsk ?_⟩
      rcases hmem with h5 | hall
      · rw [h5, F.member_five]
        exact Subgroup.mem_top _
      · by_cases hj5 : c.j = 5
        · rw [hj5, F.member_five]
          exact Subgroup.mem_top _
        · have hj5' : c.j < 5 := by omega
          rw [Array.all_eq_true] at hall
          have := hall k (by simpa using hk3)
          rw [← getElem!_pos _ k (by simpa using hk3), Ls_get hj5'] at this
          have hm := F.mem_member_of_memS hj5' this
          rw [ofCode_conjC hg hgi' hsk hgi] at hm
          exact hm.2
    refine sup_le ?_ ?_
    · rw [member, sub2, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · simpa using (gens 0 (by norm_num)).2
      · simpa using (gens 1 (by norm_num)).2
    · rw [Subgroup.zpowers_le]
      simpa using (gens 2 (by norm_num)).2
  ·
    set K := member i ⊔ zpowers (ofCode c.x)
    have hgl : ∀ k < (#[memGens[i]!.1, memGens[i]!.2, c.x] : Array ℕ).size,
        Symp #[memGens[i]!.1, memGens[i]!.2, c.x][k]! ∧
          ofCode #[memGens[i]!.1, memGens[i]!.2, c.x][k]! ∈ K := by
      intro k hk3
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hk3
      interval_cases k
      · exact ⟨by simpa using ha, by simpa using
          (le_sup_left : member i ≤ K) (Subgroup.subset_closure (by simp))⟩
      · exact ⟨by simpa using hb, by simpa using
          (le_sup_left : member i ≤ K) (Subgroup.subset_closure (by simp))⟩
      · exact ⟨by simpa using hx, by simpa using
          (le_sup_right : zpowers (ofCode c.x) ≤ K) (Subgroup.mem_zpowers _)⟩
    have hconj : ∀ h : ℕ, Symp h → ofCode (conjC c.gi c.g h) =
        (MulAut.conj (ofCode c.g)⁻¹).toMonoidHom (ofCode h) := by
      intro h hh
      unfold conjC
      rw [ofCode_mulF (symp_mulF hgi' hh) hg, ofCode_mulF hgi' hh, hginv]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      rfl
    rw [member, sub2, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · rw [← hconj _ hh1, ← he1]
      exact (evalW_mem hgl (by simpa using hw1)).2
    · rw [← hconj _ hh2, ← he2]
      exact (evalW_mem hgl (by simpa using hw2)).2

private theorem gOK_P0 (h : gOK (spArr ()) = true) :
    subOK #[p0Data.1, p0Data.2.1] 81 (bfs #[p0Data.1, p0Data.2.1] 100) = true ∧
      (bfs #[p0Data.1, p0Data.2.1] 100).1.all (fun y => pow9 y == oneC) = true := by
  unfold gOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, h6⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨h5, h6⟩

theorem ofCode_pow9 {c : ℕ} (hc : Symp c) : ofCode (pow9 c) = ofCode c ^ 9 := by
  have h3 : ∀ {a : ℕ}, Symp a → Symp (cubeC a) ∧ ofCode (cubeC a) = ofCode a ^ 3 := by
    intro a ha
    unfold cubeC
    refine ⟨symp_mulF (symp_mulF ha ha) ha, ?_⟩
    rw [ofCode_mulF (symp_mulF ha ha) ha, ofCode_mulF ha ha, pow_three']
  obtain ⟨hs, he⟩ := h3 hc
  unfold pow9
  rw [(h3 hs).2, he, ← pow_mul]

theorem symp_pow9 {c : ℕ} (hc : Symp c) : Symp (pow9 c) := by
  unfold pow9 cubeC
  exact symp_mulF (symp_mulF (symp_mulF (symp_mulF hc hc) hc) (symp_mulF (symp_mulF hc hc) hc))
    (symp_mulF (symp_mulF hc hc) hc)

theorem Facts.pow_nine (F : Facts) {y : G} {k : ℕ} (hy : orderOf y = 3 ^ k) : y ^ 9 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hsub, hall⟩ := gOK_P0 F.g
  obtain ⟨hp1, hp2⟩ : Symp p0Data.1 ∧ Symp p0Data.2.1 :=
    ⟨F.symp_extra.2.2.2.2.2.1, F.symp_extra.2.2.2.2.2.2.1⟩
  obtain ⟨-, hsy, hmem, hcard⟩ := subOK_spec hp1 hp2 hsub
  set P0 := sub2 p0Data.1 p0Data.2.1
  have hP0p : IsPGroup 3 P0 := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hidx : ¬ 3 ∣ P0.index := by
    have h := Subgroup.card_mul_index P0
    rw [hcard, F.card] at h
    have : P0.index = 640 := by omega
    rw [this]
    norm_num
  set S0 : Sylow 3 G := hP0p.toSylow hidx
  have hyP : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hy])
  obtain ⟨S, hS⟩ := hyP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 S
  have hyS : y ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
  have hz' : (MulAut.conj g)⁻¹ • y ∈ P0 := by simpa [S0] using hyS
  set z := (MulAut.conj g)⁻¹ • y with hzdef
  have hyz : y = g * z * g⁻¹ := by
    rw [hzdef]
    simp [MulAut.smul_def, mul_assoc]
  obtain ⟨i, hi, hzi⟩ := (hmem z).1 hz'
  have h9 : pow9 (bfs #[p0Data.1, p0Data.2.1] 100).1[i]! = oneC := by
    rw [Array.all_eq_true] at hall
    have hi' : i < (bfs #[p0Data.1, p0Data.2.1] 100).1.size := by
      rw [(subOK_spec hp1 hp2 hsub).1]; exact hi
    have := hall i hi'
    rw [getElem!_pos _ i hi']
    simpa using this
  have hz9 : ofCode (bfs #[p0Data.1, p0Data.2.1] 100).1[i]! ^ 9 = 1 := by
    rw [← ofCode_pow9 (hsy i hi), h9, ofCode_oneC]
  rw [hyz, ← hzi, conj_pow, hz9, mul_one, mul_inv_cancel]

private theorem mulF_lt' (a b : ℕ) : mulF a b < 3 ^ 16 := by
  rw [mulF_eq_mulC]
  exact mulC_lt a b

private theorem pow9_mem_spCodes {c : ℕ} (hc : Symp c) : pow9 c ∈ spCodes () :=
  (mem_spCodes_iff _).2 ⟨by unfold pow9 cubeC; exact mulF_lt' _ _, symp_pow9 hc⟩

private theorem oneC_mem_spCodes : oneC ∈ spCodes () :=
  (mem_spCodes_iff _).2 ⟨by decide, symp_oneC⟩

private theorem getElem!_eq {xs : Array ℕ} {t : ℕ} (ht : t < xs.size) : xs[t]! = xs[t] :=
  getElem!_pos xs t ht

private theorem threeArr_get_mem {E : Array ℕ} {t : ℕ} (ht : t < (threeArr E).size) :
    (threeArr E)[t] ∈ E := by
  have hmem := Array.getElem_mem ht
  unfold threeArr at hmem ⊢
  exact (Array.mem_filter.1 hmem).1

private theorem mem_threeArr {E : Array ℕ} {c : ℕ} (hc : c ∈ E) (h1 : c ≠ oneC)
    (h9 : pow9 c = oneC) : c ∈ threeArr E := by
  unfold threeArr
  rw [Array.mem_filter]
  exact ⟨hc, by simp [h1, h9]⟩

private theorem symp_threeArr {t : ℕ} (ht : t < (threeArr (spArr ())).size) :
    Symp (threeArr (spArr ()))[t]! := by
  rw [getElem!_eq ht]
  obtain ⟨i, hi, e⟩ := Array.getElem_of_mem (threeArr_get_mem ht)
  rw [← e, ← getElem!_eq hi]
  exact symp_spArr hi

private theorem getElem!_map_x {cs : Array Case} {r : ℕ} (hr : r < (cs.map (·.x)).size) :
    (cs.map (·.x))[r]! = cs[r]!.x := by
  have hr' : r < cs.size := by simpa using hr
  rw [getElem!_eq hr, getElem!_pos cs r hr', Array.getElem_map]

theorem Facts.exists_rep (F : Facts) {i : ℕ} (hi : i < 5) {y : G} {k : ℕ}
    (hy : orderOf y = 3 ^ k) (hy1 : y ≠ 1) :
    y ∈ member i ∨ ∃ r < (cases[i]!).size, ∃ n ∈ normalizer (member i : Set G),
      y = n * ofCode (cases[i]!)[r]!.x * n⁻¹ := by
  obtain ⟨c, hcE, hyc⟩ : ∃ c ∈ spCodes (), ofCode c = y :=
    ⟨_, encode_mem_spCodes y, ofCode_encode y⟩
  have hcs : Symp c := symp_of_mem_spCodes hcE
  have hc1 : c ≠ oneC := by
    intro h
    apply hy1
    rw [← hyc, h, ofCode_oneC]
  have hc9 : pow9 c = oneC := by
    have h1 : ofCode (pow9 c) = ofCode oneC := by
      rw [ofCode_pow9 hcs, hyc, F.pow_nine hy, ofCode_oneC]
    exact ofCode_injOn (pow9_mem_spCodes hcs) oneC_mem_spCodes h1
  have hcT : c ∈ threeArr (spArr ()) := mem_threeArr (List.mem_toArray.2 hcE) hc1 hc9
  obtain ⟨t, ht, htc⟩ := Array.getElem_of_mem hcT
  have htc' : (threeArr (spArr ()))[t]! = c := by rw [getElem!_eq ht, htc]
  obtain ⟨hn1, hn2⟩ := F.symp_normGens hi
  obtain ⟨hm1, hm2⟩ := F.symp_normInvs hi
  have hnorm := (memberOK_parts (F.mem i hi)).2.1
  unfold normOK at hnorm
  simp only [Bool.and_eq_true, beq_iff_eq] at hnorm
  obtain ⟨⟨hi1, hi2⟩, -⟩ := hnorm
  rcases orbitOK_spec (fun t ht => symp_threeArr ht) hn1 hn2 hm1 hm2 hi1 hi2
      (memberOK_parts (F.mem i hi)).2.2.1 ht with hmem | ⟨r, hr, n, hn, e⟩
  · left
    rw [htc'] at hmem
    rw [← hyc]
    exact (F.mem_member_of_memS hi hmem).2
  · right
    have hr' : r < (cases[i]!).size := by simpa using hr
    refine ⟨r, hr', n, F.normGens_le hi hn, ?_⟩
    rw [← hyc, ← htc', e, getElem!_map_x hr]

section Conj

variable {X : Type*} [Group X]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup X} {n : X}
    (hn : n ∈ normalizer (H : Set X)) : H.map (MulAut.conj n).toMonoidHom = H := by
  ext h
  rw [Subgroup.mem_normalizer_iff] at hn
  constructor
  · rintro ⟨h', hh', rfl⟩
    exact (hn h').1 hh'
  · intro hh
    refine ⟨n⁻¹ * h * n, ?_, by simp [mul_assoc]⟩
    apply (hn (n⁻¹ * h * n)).2
    simpa [mul_assoc] using hh

theorem map_conj_map_conj (H : Subgroup X) (g g' : X) :
    (H.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * g')).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (H : Subgroup X) : H.map (MulAut.conj (1 : X)).toMonoidHom = H :=
  map_conj_eq_of_mem_normalizer (one_mem _)

theorem conj_conj_inv_apply (g σ : X) : MulAut.conj g ((MulAut.conj g)⁻¹ σ) = σ := by
  simp [mul_assoc]

end Conj

@[expose] def family : Set (Subgroup G) :=
  {K | ∃ j < 6, ∃ g : G, K = (member j).map (MulAut.conj g).toMonoidHom}

theorem mem_family_conj {K : Subgroup G} (hK : K ∈ family) (g : G) :
    K.map (MulAut.conj g).toMonoidHom ∈ family := by
  obtain ⟨j, hj, g', rfl⟩ := hK
  exact ⟨j, hj, g * g', map_conj_map_conj _ g g'⟩

theorem member_mem_family {j : ℕ} (hj : j < 6) : member j ∈ family :=
  ⟨j, hj, 1, (map_conj_one _).symm⟩

theorem Facts.join_closed (F : Facts) :
    ∀ K ∈ family, ∀ σ : G, (∃ k, orderOf σ = 3 ^ k) → K ⊔ zpowers σ ∈ family := by
  rintro K ⟨j, hj, g, rfl⟩ σ ⟨k, hk⟩
  obtain ⟨y, hσ⟩ : ∃ y, MulAut.conj g y = σ := ⟨_, conj_conj_inv_apply g σ⟩
  have hyk : orderOf y = 3 ^ k := by rw [← hk, ← hσ, MulEquiv.orderOf_eq]
  have hsup : (member j).map (MulAut.conj g).toMonoidHom ⊔ zpowers σ =
      (member j ⊔ zpowers y).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hσ]
  rw [hsup]
  refine mem_family_conj ?_ g
  by_cases hj5 : j = 5
  · subst hj5
    rw [F.member_five, top_sup_eq, ← F.member_five]
    exact member_mem_family (by norm_num)
  have hj5' : j < 5 := by omega
  by_cases hy1 : y = 1
  · rw [hy1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    exact member_mem_family hj
  rcases F.exists_rep hj5' hyk hy1 with hmem | ⟨r, hr, n, hn, e⟩
  · rw [sup_eq_left.2 ((Subgroup.zpowers_le).2 hmem)]
    exact member_mem_family hj
  · obtain ⟨hjr, hcase⟩ := F.case_spec hj5' hr
    have : member j ⊔ zpowers y =
        (member j ⊔ zpowers (ofCode (cases[j]!)[r]!.x)).map (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hn, MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← e]
    rw [this, hcase]
    exact mem_family_conj (mem_family_conj (member_mem_family hjr) _) n

end CFSG.Sp43
