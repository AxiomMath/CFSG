module

public import Certificates.Data.Kernel.SmithE8MK

public section

namespace CFSG.SmithE8M.K

open CFSG.Blueprint.Chevalley

theorem range_map_get! {α : Type} [Inhabited α] (f : ℕ → α) {k : ℕ} (hk : k < 126) :
    ((Array.range 126).map f)[k]! = f k := by
  rw [getElem!_pos ((Array.range 126).map f) k (by simpa using hk)]
  simp

theorem rootArr_get {k : ℕ} (hk : k < 126) : (e8mRootArr ())[k]! = e8mRoot k :=
  range_map_get! _ hk

theorem confTab_get {A : Array (Fin (Tag.rank .E7) → ℤ)} {a b : ℕ} (ha : a < 126)
    (hb : b < 126) : e8mCf (e8mConfTab A) a b = e8mConfA A a b := by
  unfold e8mCf e8mConfTab
  rw [range_map_get! _ ha, range_map_get! _ hb]

theorem e8mTabOK_true : e8mTabOK () = true := by
  unfold e8mTabOK
  dsimp only
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨fun k hk => rootArr_get hk, fun a ha b hb => confTab_get ha hb⟩

theorem confA_iff {a b : ℕ} (ha : a < 126) (hb : b < 126) :
    e8mConfA (e8mRootArr ()) a b = true ↔
      ∃ m < 126, e8mRoot m = fun i => e8mRoot a i + e8mRoot b i := by
  unfold e8mConfA
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  rw [rootArr_get ha, rootArr_get hb]
  constructor
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, by rw [← rootArr_get hm, h]⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, by rw [rootArr_get hm, h]⟩

theorem confA_symm {A : Array (Fin (Tag.rank .E7) → ℤ)} (a b : ℕ) :
    e8mConfA A a b = e8mConfA A b a := by
  have h : (fun i => A[a]! i + A[b]! i) = (fun i => A[b]! i + A[a]! i) :=
    funext fun i => add_comm _ _
  simp only [e8mConfA, h]

theorem foldl_pick (g : ℕ → ℕ) : ∀ (L : List ℕ) (b : ℕ × ℕ),
    b.2 ≤ (L.foldl (fun best v => if best.2 < g v then (v, g v) else best) b).2 ∧
      (∀ v ∈ L, g v ≤ (L.foldl (fun best v => if best.2 < g v then (v, g v) else best) b).2) ∧
      (L.foldl (fun best v => if best.2 < g v then (v, g v) else best) b = b ∨
        (L.foldl (fun best v => if best.2 < g v then (v, g v) else best) b).1 ∈ L)
  | [], b => by simp
  | x :: L, b => by
    obtain ⟨h1, h2, h3⟩ := foldl_pick g L (if b.2 < g x then (x, g x) else b)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    by_cases hx : b.2 < g x
    · rw [if_pos hx] at h1 h2 h3 ⊢
      refine ⟨by simp at h1; omega, ⟨h1, h2⟩, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inr (Or.inl (by rw [h3]))
      · exact Or.inr (Or.inr h3)
    · rw [if_neg hx] at h1 h2 h3 ⊢
      exact ⟨h1, ⟨by omega, h2⟩, h3.imp_right Or.inr⟩

theorem pick_ge (cf : ℕ → ℕ → Bool) (P : List ℕ) :
    ∀ v ∈ P, (P.filter (cf v)).length ≤ (e8mPick cf P).2 :=
  (foldl_pick (fun v => (P.filter (cf v)).length) P (0, 0)).2.1

theorem pick_mem (cf : ℕ → ℕ → Bool) (P : List ℕ) (h : (e8mPick cf P).2 ≠ 0) :
    (e8mPick cf P).1 ∈ P := by
  rcases (foldl_pick (fun v => (P.filter (cf v)).length) P (0, 0)).2.2 with h' | h'
  · exact absurd (congrArg Prod.snd h') h
  · exact h'

theorem e8mNoIndep_complete (cf : ℕ → ℕ → Bool) :
    ∀ (fuel : ℕ) (P : List ℕ) (k : ℕ), P.Nodup → P.length < fuel →
      (∀ a ∈ P, ∀ b ∈ P, cf a b = cf b a) →
      (∀ S : Finset ℕ, (∀ s ∈ S, s ∈ P) → (∀ a ∈ S, ∀ b ∈ S, a ≠ b → cf a b = false) →
        S.card < k) →
      e8mNoIndep cf fuel P k = true := by
  intro fuel
  induction fuel with
  | zero => intro P k _ hl; omega
  | succ n ih =>
    intro P k hnd hl hsym hS
    unfold e8mNoIndep
    by_cases hk : k = 0
    · exact absurd (hS ∅ (by simp) (by simp)) (by omega)
    by_cases hP : P.length < k
    · rw [if_neg hk, if_pos hP]
    by_cases hd : (e8mPick cf P).2 = 0
    · exfalso
      have hind : ∀ a ∈ P, ∀ b ∈ P, cf a b = false := by
        intro a ha b hb
        have h0 := pick_ge cf P a ha
        rw [hd, Nat.le_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
        simpa using h0 b hb
      have := hS P.toFinset (fun s hs => List.mem_toFinset.mp hs)
        (fun a ha b hb _ => hind a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb))
      rw [List.toFinset_card_of_nodup hnd] at this
      omega
    rw [if_neg hk, if_neg hP, if_neg hd, Bool.and_eq_true]
    obtain ⟨v, hv⟩ : ∃ v, v = (e8mPick cf P).1 := ⟨_, rfl⟩
    rw [← hv]
    have hvP : v ∈ P := hv ▸ pick_mem cf P hd
    constructor
    · refine ih _ k (hnd.erase v) ?_ (fun a ha b hb => hsym a (List.mem_of_mem_erase ha) b
        (List.mem_of_mem_erase hb)) (fun S hSP hSi => hS S (fun s hs =>
          List.mem_of_mem_erase (hSP s hs)) hSi)
      rw [List.length_erase_of_mem hvP]
      omega
    · refine ih _ (k - 1) (hnd.filter _) ?_ (fun a ha b hb => hsym a (List.mem_of_mem_filter ha)
        b (List.mem_of_mem_filter hb)) (fun S hSP hSi => ?_)
      · have : (P.filter fun u => u != v && !cf v u).length < P.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨v, hvP, by simp⟩
        omega
      · have hvS : v ∉ S := fun h => by simpa using (List.mem_filter.mp (hSP v h)).2
        have hc := hS (insert v S) (fun s hs => by
            rcases Finset.mem_insert.mp hs with rfl | hs
            · exact hvP
            · exact List.mem_of_mem_filter (hSP s hs)) (fun a ha b hb hab => by
            have hcv : ∀ s ∈ S, cf v s = false := fun s hs => by
              have := (List.mem_filter.mp (hSP s hs)).2
              simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at this
              exact this.2
            rcases Finset.mem_insert.mp ha with ha' | ha' <;>
              rcases Finset.mem_insert.mp hb with hb' | hb'
            · exact absurd (ha'.trans hb'.symm) hab
            · rw [ha']
              exact hcv b hb'
            · rw [hb', hsym a (List.mem_of_mem_filter (hSP a ha')) v hvP]
              exact hcv a ha'
            · exact hSi a ha' b hb' hab)
        rw [Finset.card_insert_of_notMem hvS] at hc
        omega

theorem testBit_rowOf : ∀ (r : List (ℕ × ℕ)) (b : ℕ), (rowOf r).testBit b = true →
    ∃ m, (b, m) ∈ r
  | [], b, h => by simp [rowOf] at h
  | p :: r, b, h => by
    rw [rowOf, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at h
    rcases h with h | h
    · exact ⟨p.2, by simp at h; simp [← h]⟩
    · obtain ⟨m, hm⟩ := testBit_rowOf r b h
      exact ⟨m, List.mem_cons_of_mem _ hm⟩

theorem sumRootC_sound {ca cb cm : ℕ} (h : sumRootC ca cb cm = true) (i : Fin (Tag.rank .E7)) :
    decodeVec (τ := .E7) ca i + decodeVec (τ := .E7) cb i = decodeVec (τ := .E7) cm i := by
  unfold sumRootC at h
  rw [List.all_eq_true] at h
  have hi : (i : ℕ) < 7 := i.isLt
  have := h i (List.mem_range.mpr hi)
  rw [beq_iff_eq] at this
  have hz := congrArg (Nat.cast : ℕ → ℤ) this
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_ofNat] at hz
  unfold decodeVec
  linarith

theorem e8mRoot_eq (k : ℕ) : e8mRoot k = decodeVec (τ := .E7) (codes.getD k 0) := rfl

theorem eK_conf {rows : List ℕ} {edges : List (List (ℕ × ℕ))} (hR : rowsOK rows edges = true)
    {a b : ℕ} (h : eK rows a b = true) :
    a < 126 ∧ b < 126 ∧ ∃ m < 126, e8mRoot m = fun i => e8mRoot a i + e8mRoot b i := by
  unfold rowsOK at hR
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hR
  obtain ⟨hlen, hR⟩ := hR
  unfold eK at h
  have ha : a < 126 := by
    by_contra ha
    rw [List.getD_eq_default _ _ (by omega)] at h
    simp at h
  obtain ⟨hrow, hed⟩ := hR a ha
  rw [hrow] at h
  obtain ⟨m, hm⟩ := testBit_rowOf _ b h
  obtain ⟨⟨hb, hm126⟩, hs⟩ := hed (b, m) hm
  refine ⟨ha, hb, m, hm126, funext fun i => ?_⟩
  rw [e8mRoot_eq, e8mRoot_eq, e8mRoot_eq]
  exact (sumRootC_sound hs i).symm

theorem card_le_prs (E : ℕ → ℕ → Bool) : ∀ (Q : List (ℕ × ℕ)) (S : Finset ℕ),
    (∀ x ∈ S, ∃ p ∈ Q, p.1 = x ∨ p.2 = x) → (∀ p ∈ Q, p.1 = p.2 ∨ E p.1 p.2 = true) →
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → E a b = false) → S.card ≤ Q.length
  | [], S, hcov, _, _ => by
    have : S = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by
      obtain ⟨p, hp, _⟩ := hcov x hx
      simp at hp
    simp [this]
  | p :: Q, S, hcov, hQ, hS => by
    classical
    have h2 := card_le_prs E Q (S.filter fun x => ¬(p.1 = x ∨ p.2 = x)) (fun x hx => by
        obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
        obtain ⟨p', hp', h'⟩ := hcov x hxS
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact absurd h' hxp
        · exact ⟨p', hp', h'⟩) (fun q hq => hQ q (List.mem_cons_of_mem _ hq))
      (fun a ha b hb hab => hS a (Finset.mem_of_mem_filter a ha) b
        (Finset.mem_of_mem_filter b hb) hab)
    have h1 : (S.filter fun x => p.1 = x ∨ p.2 = x).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      obtain ⟨haS, ha'⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbS, hb'⟩ := Finset.mem_filter.mp hb
      by_contra hab
      have hp12 : p.1 ≠ p.2 := by rcases ha' with rfl | rfl <;> rcases hb' with h | h <;> grind
      have hE : E p.1 p.2 = true := (hQ p List.mem_cons_self).resolve_left hp12
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact hab rfl
      · rw [hS _ haS _ hbS hab] at hE
        exact absurd hE (by decide)
      · rw [hS _ hbS _ haS (Ne.symm hab)] at hE
        exact absurd hE (by decide)
      · exact hab rfl
    have hsub : S ⊆ (S.filter fun x => p.1 = x ∨ p.2 = x) ∪
        (S.filter fun x => ¬(p.1 = x ∨ p.2 = x)) := fun x hx => by
      by_cases hq : p.1 = x ∨ p.2 = x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hq⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hq⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [List.length_cons]
    omega

theorem card_lt_of_length {S : Finset ℕ} {P : List ℕ} {k : ℕ} (h : ∀ s ∈ S, s ∈ P)
    (hk : P.length < k) : S.card < k :=
  lt_of_le_of_lt ((Finset.card_le_card (fun s hs => List.mem_toFinset.mpr (h s hs))).trans
    (List.toFinset_card_le P)) hk

theorem mem_filtK {rows : List ℕ} {v u : ℕ} {P : List ℕ} :
    u ∈ filtK (rows.getD v 0) v P ↔ u ∈ P ∧ u ≠ v ∧ eK rows v u = false := by
  simp [filtK, eK, List.mem_filter]

theorem abChk_sound (rows : List ℕ) : ∀ (f : ℕ) (s P : List ℕ) (k : ℕ) (r : List ℕ),
    abChk rows f s P k = some r → ∀ S : Finset ℕ, (∀ x ∈ S, x ∈ P) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → eK rows a b = false) → S.card < k := by
  intro f
  induction f with
  | zero => intro s P k r h; simp [abChk] at h
  | succ f ih =>
    intro s P k r h S hSP hSi
    unfold abChk at h
    split at h
    · split at h
      · exact card_lt_of_length hSP (by assumption)
      · simp at h
    · split at h
      · rename_i hc
        simp only [coverOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨hlt, hcov⟩, hpr⟩ := hc
        refine lt_of_le_of_lt (card_le_prs (eK rows) _ S (fun x hx => ?_) hpr hSi) hlt
        exact hcov x (hSP x hx)
      · simp at h
    · rename_i v rest
      split at h
      · rename_i r' hr'
        by_cases hvS : v ∈ S
        · have h' := ih _ _ _ _ h (S.erase v) (fun x hx => by
              have hxS := Finset.mem_of_mem_erase hx
              exact mem_filtK.mpr ⟨hSP x hxS, Finset.ne_of_mem_erase hx,
                hSi v hvS x hxS (Ne.symm (Finset.ne_of_mem_erase hx))⟩)
            (fun a ha b hb hab => hSi a (Finset.mem_of_mem_erase ha) b
              (Finset.mem_of_mem_erase hb) hab)
          have := Finset.card_erase_of_mem hvS
          have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hvS⟩
          omega
        · exact ih _ _ _ _ hr' S (fun x hx => (List.mem_erase_of_ne
            (fun h => hvS (by rw [← h]; exact hx))).mpr (hSP x hx)) hSi
      · simp at h
    · simp at h

theorem e8mRACheck_of (h1 : ((List.range 126).filter e8mIsRA).length = 27)
    (h2 : ((List.range 126).filter e8mIsRA).all e8mIsPos = true)
    (h3 : (List.range 126).all (fun m => decide (e8mRoot m ⟨6, by decide⟩ ≤ 1)) = true) :
    e8mRACheck () = true := by
  unfold e8mRACheck
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨h1, h2⟩, ?_⟩
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  simp only [List.mem_filter, List.mem_range, e8mIsRA, decide_eq_true_eq] at ha hb
  rw [Bool.not_eq_true']
  by_contra hc
  obtain ⟨m, hm, hmab⟩ := (confA_iff ha.1 hb.1).mp (by simpa using hc)
  have h7 := congrFun hmab ⟨6, by decide⟩
  rw [ha.2, hb.2] at h7
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h3
  have := h3 m hm
  omega

theorem e8mAbelCheck_of {rows : List ℕ} {edges : List (List (ℕ × ℕ))} {pos nra t28 : List ℕ}
    {t26 : List (List ℕ)} (hR : rowsOK rows edges = true) (hP : e8mPos () = pos)
    (hN : pos.filter (fun v => !e8mIsRA v) = nra) (h28 : chk28 rows pos t28 = true)
    (h26 : chk26 rows pos nra t26 = true) : e8mAbelCheck () = true := by
  have hpos : ∀ u ∈ pos, u < 126 := fun u hu => by
    rw [← hP] at hu
    exact List.mem_range.mp (List.mem_of_mem_filter hu)
  have hnd : pos.Nodup := hP ▸ List.nodup_range.filter _
  have hlen : pos.length < 1000 := by
    rw [← hP]
    exact lt_of_le_of_lt (List.length_filter_le _ _) (by simp)
  set cf := e8mCf (e8mConfTab (e8mRootArr ())) with hcf
  have hsym : ∀ a ∈ pos, ∀ b ∈ pos, cf a b = cf b a := fun a ha b hb => by
    rw [hcf, confTab_get (hpos a ha) (hpos b hb), confTab_get (hpos b hb) (hpos a ha),
      confA_symm]
  have hEcf : ∀ a b, cf a b = false → a < 126 → b < 126 → eK rows a b = false :=
    fun a b h ha hb => by
      by_contra hE
      obtain ⟨-, -, hm⟩ := eK_conf hR (by simpa using hE)
      rw [hcf, confTab_get ha hb] at h
      rw [(confA_iff ha hb).mpr hm] at h
      exact absurd h (by decide)
  have hind : ∀ (Q : List ℕ), (∀ u ∈ Q, u < 126) → ∀ S : Finset ℕ, (∀ s ∈ S, s ∈ Q) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → cf a b = false) →
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → eK rows a b = false :=
    fun Q hQ S hSQ hSi a ha b hb hab =>
      hEcf a b (hSi a ha b hb hab) (hQ a (hSQ a ha)) (hQ b (hSQ b hb))
  unfold e8mAbelCheck
  dsimp only
  rw [← hcf, hP, Bool.and_eq_true, List.all_eq_true, hN]
  constructor
  · refine e8mNoIndep_complete cf 1000 pos 28 hnd hlen hsym fun S hSP hSi => ?_
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h28
    exact abChk_sound rows _ _ _ _ _ hr S hSP (hind pos hpos S hSP hSi)
  · intro v hv
    unfold chk26 at h26
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h26
    have hvpos : v ∈ pos := by
      rw [← hN] at hv
      exact List.mem_of_mem_filter hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hmem : (nra[i], t26[i]'(h26.1 ▸ hi)) ∈ nra.zip t26 := by
      have hz : i < (nra.zip t26).length := by simp [List.length_zip, ← h26.1, hi]
      simpa only [List.getElem_zip] using List.getElem_mem hz
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (h26.2 _ hmem)
    have hQ : ∀ u ∈ pos.filter (fun u => u != nra[i] && !cf nra[i] u), u < 126 :=
      fun u hu => hpos u (List.mem_of_mem_filter hu)
    refine e8mNoIndep_complete cf 1000 _ 26 (hnd.filter _)
      (lt_of_le_of_lt (List.length_filter_le _ _) hlen)
      (fun a ha b hb => hsym a (List.mem_of_mem_filter ha) b (List.mem_of_mem_filter hb))
      fun S hSP hSi => ?_
    refine abChk_sound rows _ _ _ _ _ hr S (fun s hs => ?_) (hind _ hQ S hSP hSi)
    have hs' := List.mem_filter.mp (hSP s hs)
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at hs'
    exact mem_filtK.mpr ⟨hs'.1, hs'.2.1, hEcf _ _ hs'.2.2 (hpos _ hvpos) (hpos _ hs'.1)⟩

end CFSG.SmithE8M.K
