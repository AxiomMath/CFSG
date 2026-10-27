module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutECore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableDefs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.AutETable

theorem tab_getD {n k : ℕ} (f : ℕ → ℕ) (hk : k < n) : (tab n f).getD k 0 = f k := by
  simp [tab, hk]

theorem mt_tab2 {n a b : ℕ} (mul : ℕ → ℕ → ℕ) (ha : a < n) (hb : b < n) :
    mt (tab2 n mul) a b = mul a b := by
  have : (tab2 n mul).getD a #[] = tab n (mul a) := by simp [tab2, ha]
  rw [mt, this, tab_getD _ hb]

theorem ix_tab {n k : ℕ} (f : ℕ → ℕ) (hk : k < n) : ix (tab n f) k = f k := tab_getD f hk

section ev

variable {M : Array (Array ℕ)} {n : ℕ}

theorem ev_congr {g g' : ℕ → ℕ} {w : List ℕ} (h : ∀ i ∈ w, g i = g' i) :
    ev M g w = ev M g' w := by
  unfold ev
  suffices H : ∀ acc, w.foldl (fun acc i => mt M acc (g i)) acc =
      w.foldl (fun acc i => mt M acc (g' i)) acc from H 0
  induction w with
  | nil => intro acc; rfl
  | cons i w ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [h i (List.mem_cons_self ..)]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

theorem sigma_ev (hlt : ∀ a b, a < n → b < n → mt M a b < n) (hn : 0 < n) {σ : ℕ → ℕ}
    (hσm : ∀ k l, k < n → l < n → σ (mt M k l) = mt M (σ k) (σ l)) (hσ0 : σ 0 = 0)
    {g : ℕ → ℕ} (hg : ∀ i, g i < n) (w : List ℕ) :
    σ (ev M g w) = ev M (fun i => σ (g i)) w := by
  unfold ev
  suffices H : ∀ acc, acc < n → σ (w.foldl (fun acc i => mt M acc (g i)) acc) =
      w.foldl (fun acc i => mt M acc (σ (g i))) (σ acc) from by
    rw [H 0 hn, hσ0]
  induction w with
  | nil => intro acc _; rfl
  | cons i w ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    rw [ih _ (hlt _ _ hacc (hg i)), hσm _ _ hacc (hg i)]

end ev

structure Realizes (H : Type*) [Group H] (n : ℕ) (M : Array (Array ℕ)) (elt : ℕ → H) : Prop where
  pos : 0 < n
  lt : ∀ a b, a < n → b < n → mt M a b < n
  mul : ∀ a b, a < n → b < n → elt (mt M a b) = elt a * elt b
  inj : ∀ a b, a < n → b < n → elt a = elt b → a = b
  surj : ∀ h : H, ∃ a, a < n ∧ elt a = h
  one : elt 0 = 1

section sigma

variable {H : Type*} [Group H] {n : ℕ} {M : Array (Array ℕ)} {elt : ℕ → H}

open Classical in
noncomputable def sg (_R : Realizes H n M elt) (a : MulAut H) (k : ℕ) : ℕ :=
  if h : ∃ m, m < n ∧ elt m = a (elt k) then Classical.choose h else 0

theorem sg_spec (R : Realizes H n M elt) (a : MulAut H) (k : ℕ) :
    sg R a k < n ∧ elt (sg R a k) = a (elt k) := by
  have h : ∃ m, m < n ∧ elt m = a (elt k) := R.surj (a (elt k))
  have := Classical.choose_spec h
  simpa only [sg, h, ↓reduceDIte] using this

theorem sg_lt (R : Realizes H n M elt) (a : MulAut H) (k : ℕ) : sg R a k < n :=
  (sg_spec R a k).1

theorem sg_elt (R : Realizes H n M elt) (a : MulAut H) (k : ℕ) :
    elt (sg R a k) = a (elt k) :=
  (sg_spec R a k).2

theorem sg_mt (R : Realizes H n M elt) (a : MulAut H) {k l : ℕ} (hk : k < n) (hl : l < n) :
    sg R a (mt M k l) = mt M (sg R a k) (sg R a l) := by
  apply R.inj _ _ (sg_lt R a _) (R.lt _ _ (sg_lt R a _) (sg_lt R a _))
  rw [sg_elt R a, R.mul _ _ hk hl, map_mul, R.mul _ _ (sg_lt R a _) (sg_lt R a _),
    sg_elt R a, sg_elt R a]

theorem sg_zero (R : Realizes H n M elt) (a : MulAut H) : sg R a 0 = 0 := by
  apply R.inj _ _ (sg_lt R a _) R.pos
  rw [sg_elt R a, R.one, map_one]

theorem sg_ne_zero (R : Realizes H n M elt) (a : MulAut H) {k : ℕ} (hk : k < n) (hk0 : k ≠ 0) :
    sg R a k ≠ 0 := by
  intro h
  apply hk0
  apply R.inj _ _ hk R.pos
  have := sg_elt R a k
  rw [h, R.one] at this
  rw [R.one]
  exact (a.injective (this.symm.trans (map_one a).symm))

theorem sg_mul (R : Realizes H n M elt) (a b : MulAut H) (k : ℕ) :
    sg R (a * b) k = sg R a (sg R b k) := by
  apply R.inj _ _ (sg_lt R _ _) (sg_lt R _ _)
  rw [sg_elt R _ _, sg_elt R _ _, sg_elt R _ _]
  rfl

theorem sg_one (R : Realizes H n M elt) {k : ℕ} (hk : k < n) : sg R (1 : MulAut H) k = k := by
  apply R.inj _ _ (sg_lt R _ _) hk
  rw [sg_elt R _ _]
  rfl

end sigma

section complete

variable {H : Type*} [Group H] {n : ℕ} {M : Array (Array ℕ)} {elt : ℕ → H}

theorem gensOk_spec {gens : List ℕ} {W : Array (List ℕ)} (h : gensOk n M gens W = true) :
    (∀ g ∈ gens, g < n) ∧ ∀ k, k < n → ev M (fun i => gens.getD i 0) (wd W k) = k := by
  simp only [gensOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    beq_iff_eq] at h
  exact h

theorem getD_lt {l : List ℕ} (hl : ∀ g ∈ l, g < n) (hn : 0 < n) (i : ℕ) : l.getD i 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simpa using hn
  | some x => simpa using hl x (List.mem_of_getElem? h)

theorem map_getD (σ : ℕ → ℕ) (hσ0 : σ 0 = 0) (l : List ℕ) (i : ℕ) :
    (l.map σ).getD i 0 = σ (l.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hσ0]

theorem take_getD (l : List ℕ) {d i : ℕ} (hi : i < d) : (l.take d).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ↓reduceIte]


theorem inLv_iff {W : Array (List ℕ)} {d k : ℕ} :
    inLv W d k = true ↔ ∀ i ∈ wd W k, i ≤ d := by
  simp [inLv, List.all_eq_true]

theorem lvlOk_complete (R : Realizes H n M elt) {gens : List ℕ} {W : Array (List ℕ)}
    (hg : gensOk n M gens W = true) (a : MulAut H) (d : ℕ) :
    lvlOk n M gens W d ((gens.map (sg R a)).take (d + 1)) = true := by
  obtain ⟨hgl, hW⟩ := gensOk_spec hg
  have hgv : ∀ i, gens.getD i 0 < n := getD_lt hgl R.pos
  set σ := sg R a with hσ
  set q := (gens.map σ).take (d + 1) with hq
  have hqi : ∀ i, i ≤ d → q.getD i 0 = σ (gens.getD i 0) := by
    intro i hi
    rw [hq, take_getD _ (Nat.lt_succ_of_le hi), map_getD σ (sg_zero R a)]
  have hX : ∀ k, k < n → inLv W d k = true →
      ev M (fun i => q.getD i 0) (wd W k) = σ k := by
    intro k hk hlv
    have h1 : ev M (fun i => q.getD i 0) (wd W k) =
        ev M (fun i => σ (gens.getD i 0)) (wd W k) :=
      ev_congr fun i hi => hqi i (inLv_iff.1 hlv i hi)
    have h2 := sigma_ev R.lt R.pos (σ := σ) (fun k l hk hl => sg_mt R a hk hl) (sg_zero R a)
      hgv (wd W k)
    rw [h1, ← h2, hW k hk]
  have hX' : ∀ k, k < n → inLv W d k = true → ix (tab n fun k => if inLv W d k then
      ev M (fun i => q.getD i 0) (wd W k) else 0) k = σ k := by
    intro k hk hlv
    rw [ix_tab _ hk]
    simp only [hlv, ↓reduceIte]
    exact hX k hk hlv
  unfold lvlOk
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq]
  intro k hk
  cases hlv : inLv W d k
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, ?_⟩
    · by_cases hk0 : k = 0
      · exact Or.inl hk0
      · refine Or.inr ?_
        rw [hX' k hk hlv]
        exact sg_ne_zero R a hk hk0
    · intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 hi
      cases hlm : inLv W d (mt M k (gens.getD i 0))
      · exact Or.inl rfl
      · refine Or.inr ?_
        have hm : mt M k (gens.getD i 0) < n := R.lt _ _ hk (hgv i)
        rw [hX' _ hm hlm, hX' k hk hlv, hqi i hi']
        exact sg_mt R a hk (hgv i)


theorem take_mem_levels (R : Realizes H n M elt) {gens : List ℕ} {W : Array (List ℕ)}
    (hg : gensOk n M gens W = true) (a : MulAut H) (d : ℕ) (hd : d ≤ gens.length) :
    (gens.map (sg R a)).take d ∈
      (List.range d).foldl (fun ps d => extendLv n M gens W d ps) [[]] := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hdl : d < gens.length := hd
    have hmem := ih (Nat.le_of_lt hdl)
    have htake : (gens.map (sg R a)).take (d + 1) =
        (gens.map (sg R a)).take d ++ [sg R a (gens.getD d 0)] := by
      rw [List.take_add_one]
      have : (gens.map (sg R a))[d]? = some (sg R a (gens.getD d 0)) := by
        rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hdl]
        simp
      rw [this]
      rfl
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [extendLv, List.mem_flatMap, List.mem_filterMap, List.mem_range]
    refine ⟨_, hmem, sg R a (gens.getD d 0), sg_lt R a _, ?_⟩
    rw [← htake, lvlOk_complete R hg a d]
    rfl


theorem aut_mem (R : Realizes H n M elt) {gens : List ℕ} {W : Array (List ℕ)}
    (hg : gensOk n M gens W = true) (a : MulAut H) :
    ∃ A ∈ autArrs n M gens W, ∀ k, k < n → ix A k = sg R a k := by
  obtain ⟨hgl, hW⟩ := gensOk_spec hg
  have hgv : ∀ i, gens.getD i 0 < n := getD_lt hgl R.pos
  have hq : gens.map (sg R a) ∈ tuples n M gens W := by
    have := take_mem_levels R hg a gens.length le_rfl
    rwa [List.take_of_length_le (by simp)] at this
  refine ⟨_, List.mem_map_of_mem hq, fun k hk => ?_⟩
  rw [ix_tab _ hk]
  have h1 : ev M (fun i => (gens.map (sg R a)).getD i 0) (wd W k) =
      ev M (fun i => sg R a (gens.getD i 0)) (wd W k) :=
    ev_congr fun i _ => map_getD _ (sg_zero R a) gens i
  have h2 := sigma_ev R.lt R.pos (σ := sg R a) (fun k l hk hl => sg_mt R a hk hl)
    (sg_zero R a) hgv (wd W k)
  rw [h1, ← h2, hW k hk]


theorem pairOk_spec {B A : Array ℕ} (h : pairOk n M B A = true)
    (h1 : ∀ k, k < n → ix A (ix B k) = ix B (ix A k))
    (h2 : ∃ d, d < n ∧ ix B d = d ∧ ∀ e, e < n → ix B e = e → mt M (ix A e) d = mt M d e) :
    ∃ d, d < n ∧ ix B d = d ∧ ((∀ e, e < n → mt M (ix A e) d = mt M d e) ∨
      (∀ e, e < n → mt M (ix A e) d = mt M d (ix B e)) ∨
      (∀ e, e < n → mt M (ix A e) d = mt M d (ix B (ix B e)))) := by
  have hP1 : ((List.range n).all fun k => ix A (ix B k) == ix B (ix A k)) = true := by
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    exact h1
  have hP2 : ((List.range n).any fun d => ix B d == d &&
      (List.range n).all fun e => ix B e != e || mt M (ix A e) d == mt M d e) = true := by
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      Bool.or_eq_true, bne_iff_ne, ne_eq]
    obtain ⟨d, hd, hBd, he⟩ := h2
    refine ⟨d, hd, hBd, fun e he' => ?_⟩
    by_cases hBe : ix B e = e
    · exact Or.inr (he e he' hBe)
    · exact Or.inl hBe
  unfold pairOk at h
  rw [hP1, hP2] at h
  simp only [Bool.not_true, Bool.or_false, Bool.false_or, conclOk, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true, id] at h
  obtain ⟨d, hd, hBd, hc⟩ := h
  exact ⟨d, hd, hBd, by tauto⟩


theorem isOrd3_of {B : Array ℕ} (h1 : ∀ k, k < n → ix B (ix B (ix B k)) = k)
    (h2 : ∃ k, k < n ∧ ix B k ≠ k) : isOrd3 n B = true := by
  unfold isOrd3
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq,
    bne_iff_ne, ne_eq]
  exact ⟨h1, h2⟩

theorem autEFact_of_chk (R : Realizes H n M elt) {gens : List ℕ} {W : Array (List ℕ)}
    (h : autChk n M gens W = true) : AutEFact H := by
  unfold autChk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hg, hall⟩ := h
  intro b a hb3 hb1 hab ⟨d, hbd, hin⟩
  obtain ⟨B, hBmem, hB⟩ := aut_mem R hg b
  obtain ⟨A, hAmem, hA⟩ := aut_mem R hg a
  have hBlt : ∀ k, k < n → ix B k < n := fun k hk => by rw [hB k hk]; exact sg_lt R b k
  have hAlt : ∀ k, k < n → ix A k < n := fun k hk => by rw [hA k hk]; exact sg_lt R a k
  have hBB : ∀ k, k < n → ix B (ix B k) = sg R b (sg R b k) := fun k hk => by
    rw [hB k hk, hB _ (sg_lt R b k)]
  have hBBB : ∀ k, k < n → ix B (ix B (ix B k)) = sg R b (sg R b (sg R b k)) := fun k hk => by
    rw [hB k hk, hB _ (sg_lt R b k), hB _ (sg_lt R b _)]
  have hAB : ∀ k, k < n → ix A (ix B k) = sg R a (sg R b k) := fun k hk => by
    rw [hB k hk, hA _ (sg_lt R b k)]
  have hBA : ∀ k, k < n → ix B (ix A k) = sg R b (sg R a k) := fun k hk => by
    rw [hA k hk, hB _ (sg_lt R a k)]
  have hord : isOrd3 n B = true := by
    refine isOrd3_of (fun k hk => ?_) ?_
    · rw [hBBB k hk, ← sg_mul R b b k, ← sg_mul R b (b * b) k, ← pow_three b, hb3, sg_one R hk]
    · by_contra hcon
      push Not at hcon
      apply hb1
      refine DFunLike.ext _ _ fun x => ?_
      obtain ⟨k, hk, rfl⟩ := R.surj x
      rw [← sg_elt R b k, ← hB k hk, hcon k hk]
      rfl
  have hcomm : ∀ k, k < n → ix A (ix B k) = ix B (ix A k) := fun k hk => by
    rw [hAB k hk, hBA k hk, ← sg_mul R a b k, ← sg_mul R b a k, hab]
  have hprem : ∃ d, d < n ∧ ix B d = d ∧
      ∀ e, e < n → ix B e = e → mt M (ix A e) d = mt M d e := by
    obtain ⟨d₀, hd₀, rfl⟩ := R.surj d
    refine ⟨d₀, hd₀, ?_, fun e he hBe => ?_⟩
    · rw [hB d₀ hd₀]
      exact R.inj _ _ (sg_lt R b d₀) hd₀ (by rw [sg_elt R b d₀]; exact hbd)
    · have hbe : b (elt e) = elt e := by
        rw [← sg_elt R b e, ← hB e he, hBe]
      apply R.inj _ _ (R.lt _ _ (hAlt e he) hd₀) (R.lt _ _ hd₀ he)
      rw [R.mul _ _ (hAlt e he) hd₀, R.mul _ _ hd₀ he, hA e he, sg_elt R a e, hin _ hbe,
        inv_mul_cancel_right]
  have hpair : pairOk n M B A = true := by
    have h1 := List.all_eq_true.1 hall B hBmem
    rw [hord, Bool.not_true, Bool.false_or] at h1
    exact List.all_eq_true.1 h1 A hAmem
  obtain ⟨d₁, hd₁, hBd₁, hconcl⟩ := pairOk_spec hpair hcomm hprem
  have hbd₁ : b (elt d₁) = elt d₁ := by
    rw [← sg_elt R b d₁, ← hB d₁ hd₁, hBd₁]
  refine ⟨elt d₁, hbd₁, ?_⟩
  have key : ∀ e, e < n → ∀ r : ℕ, r < n → mt M (ix A e) d₁ = mt M d₁ r →
      a (elt e) = elt d₁ * elt r * (elt d₁)⁻¹ := by
    intro e he r hr hc
    apply eq_mul_inv_of_mul_eq
    have := congrArg elt hc
    rw [R.mul _ _ (hAlt e he) hd₁, R.mul _ _ hd₁ hr, hA e he, sg_elt R a e] at this
    exact this
  rcases hconcl with hc | hc | hc
  · refine ⟨0, fun x => ?_⟩
    obtain ⟨e, he, rfl⟩ := R.surj x
    rw [key e he e he (hc e he)]
    rfl
  · refine ⟨1, fun x => ?_⟩
    obtain ⟨e, he, rfl⟩ := R.surj x
    rw [key e he _ (hBlt e he) (hc e he), hB e he, sg_elt R b e]
    rfl
  · refine ⟨2, fun x => ?_⟩
    obtain ⟨e, he, rfl⟩ := R.surj x
    rw [key e he _ (hBlt _ (hBlt e he)) (hc e he), hBB e he, sg_elt R b _, sg_elt R b e]
    rfl

end complete
end CFSG.EvenSporadicStandard.Fin76b.AutETable
