module

public import CFSG.Certificates.Kernel.D43.TreeGlue
public import CFSG.Certificates.Kernel.D43.BaseSound
public import Certificates.Data.Kernel.D43.TreeDisj
public import Certificates.Data.Kernel.D43.TreePt
public import Certificates.Data.Kernel.D43.TreeRel

public section

namespace CFSG.KC.D43

open CFSG.ASVolI

section Trees

variable {G : Type*} [Group G] [MulAction G (Fin 26572)]

theorem treeChunks_chk {F W R Q : ℕ → ℕ} {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C)
    (h : ∀ c < C, treeChunk F W R Q ℓ o s b M c = true) :
    ∀ t < s, treeChk F W R Q ℓ o b M t = true := by
  intro t ht
  have hc := tree_allBlk (h (t / 256) (by omega)) (t % 256) (Nat.mod_lt t (by decide))
  beta_reduce at hc
  have e : Nat.mul (nat_lit 256) (t / 256) + t % 256 = t := Nat.div_add_mod t 256
  rw [e] at hc
  have hts : Nat.blt t s = true := Nat.blt_eq.mpr ht
  rw [hts] at hc
  exact hc

theorem treeChunks_pos {F W R Q : ℕ → ℕ} {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C)
    (h : ∀ c < C, treeChunk F W R Q ℓ o s b M c = true) :
    ∀ t < s, posAt Q ℓ (ptAt R o t) = t :=
  fun t ht => (treeChk_facts (treeChunks_chk hs h t ht)).2.1

@[expose] noncomputable def treePts (R : ℕ → ℕ) (o s : ℕ) : Finset (Fin 26572) :=
  (Finset.range s).image fun t => (⟨ptAt R o t % 26572, Nat.mod_lt _ (by norm_num)⟩ : Fin 26572)

theorem mem_treePts {R : ℕ → ℕ} {o s : ℕ} (hlt : ∀ t < s, ptAt R o t < 26572) {q : Fin 26572} :
    q ∈ treePts R o s ↔ ∃ t < s, ptAt R o t = q := by
  unfold treePts
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Finset.mem_range] at ht
    exact ⟨t, ht, (Nat.mod_eq_of_lt (hlt t ht)).symm⟩
  · rintro ⟨t, ht, e⟩
    exact ⟨t, Finset.mem_range.2 ht, Fin.ext (by rw [← e]; exact Nat.mod_eq_of_lt (hlt t ht))⟩

theorem treePts_card {F W R Q : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ)
    {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C) (hb : b < 26572)
    (h : ∀ c < C, treeChunk F W R Q ℓ o s b M c = true) : (treePts R o s).card = s := by
  obtain ⟨hlt, hinj, -⟩ := treeChunks_spec hγ hs hb h
  unfold treePts
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro t ht t' ht' he
  simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
  have e := congrArg Fin.val he
  simp only [Nat.mod_eq_of_lt (hlt t ht), Nat.mod_eq_of_lt (hlt t' ht')] at e
  exact hinj t ht t' ht' e

theorem treePts_sub {F W R Q : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ)
    {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C) (hb : b < 26572)
    (h : ∀ c < C, treeChunk F W R Q ℓ o s b M c = true) :
    (treePts R o s : Set (Fin 26572)) ⊆
      MulAction.orbit ↥(maskGroup γ W M) (⟨b, hb⟩ : Fin 26572) := by
  obtain ⟨hlt, -, hmem⟩ := treeChunks_spec hγ hs hb h
  intro q hq
  obtain ⟨t, ht, e⟩ := (mem_treePts hlt).1 hq
  obtain ⟨g, hg, hgt⟩ := hmem t ht
  exact ⟨⟨g, hg⟩, Fin.ext (hgt.trans e)⟩

theorem treeChunks_lt {F W R Q : ℕ → ℕ} {ℓ o s b M C : ℕ} (hs : s ≤ 256 * C)
    (h : ∀ c < C, treeChunk F W R Q ℓ o s b M c = true) : ∀ t < s, ptAt R o t < 26572 :=
  fun t ht => (treeChk_facts (treeChunks_chk hs h t ht)).1

theorem disjChk_spec {Ra Rb Qb : ℕ → ℕ} {oa ℓb ob sb t : ℕ}
    (h : disjChk Ra oa Rb Qb ℓb ob sb t = true)
    (hpos : ∀ t' < sb, posAt Qb ℓb (ptAt Rb ob t') = t') :
    ∀ t' < sb, ptAt Ra oa t ≠ ptAt Rb ob t' := by
  intro t' ht' e
  unfold disjChk at h
  rw [tree_strictB] at h
  beta_reduce at h
  rw [tree_strictB] at h
  beta_reduce at h
  rw [e, hpos t' ht', Nat.blt_eq.mpr ht', Nat.beq_refl] at h
  exact absurd h (by decide)

theorem disjChunks_spec {Ra Rb Qb : ℕ → ℕ} {oa sa ℓb ob sb C : ℕ} (hs : sa ≤ 256 * C)
    (h : ∀ c < C, disjChunk Ra oa sa Rb Qb ℓb ob sb c = true)
    (hpos : ∀ t' < sb, posAt Qb ℓb (ptAt Rb ob t') = t') :
    ∀ t < sa, ∀ t' < sb, ptAt Ra oa t ≠ ptAt Rb ob t' := by
  intro t ht
  have hc := tree_allBlk (h (t / 256) (by omega)) (t % 256) (Nat.mod_lt t (by decide))
  beta_reduce at hc
  have e : Nat.mul (nat_lit 256) (t / 256) + t % 256 = t := Nat.div_add_mod t 256
  rw [e, Nat.blt_eq.mpr ht] at hc
  exact disjChk_spec hc hpos

theorem disjoint_treePts {Ra Rb Qb : ℕ → ℕ} {oa sa ℓb ob sb C : ℕ} (hs : sa ≤ 256 * C)
    (h : ∀ c < C, disjChunk Ra oa sa Rb Qb ℓb ob sb c = true)
    (hpos : ∀ t' < sb, posAt Qb ℓb (ptAt Rb ob t') = t')
    (hla : ∀ t < sa, ptAt Ra oa t < 26572) (hlb : ∀ t < sb, ptAt Rb ob t < 26572) :
    Disjoint (treePts Ra oa sa) (treePts Rb ob sb) := by
  rw [Finset.disjoint_left]
  intro q hqa hqb
  obtain ⟨t, ht, e1⟩ := (mem_treePts hla).1 hqa
  obtain ⟨t', ht', e⟩ := (mem_treePts hlb).1 hqb
  exact disjChunks_spec hs h hpos t ht t' ht' (e1.trans e.symm)

theorem memChk_spec {R Q : ℕ → ℕ} {ℓ o s q : ℕ}
    (h : CFSG.KC.Enum.strictB (posAt Q ℓ q)
      (fun u => Bool.rec (motive := fun _ => Bool) false (Nat.beq (ptAt R o u) q) (Nat.blt u s)) =
        true) : ∃ t < s, ptAt R o t = q := by
  rw [tree_strictB] at h
  beta_reduce at h
  obtain ⟨h1, h2⟩ := tree_bAnd h
  exact ⟨_, Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

end Trees

section Points

variable {G : Type*} [Group G] [MulAction G (Fin 26572)]

theorem movesB_spec {F W : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) {j : ℕ} {p : Fin 26572}
    (h : movesB F W j p = true) : lG γ W j • p ≠ p := by
  unfold movesB at h
  rw [tree_strictB] at h
  beta_reduce at h
  obtain ⟨h1, h2⟩ := tree_bAnd h
  have hlt : lAp F W j p < 26572 := Nat.le_of_ble_eq_true h1
  intro e
  have hs := lAp_spec hγ hlt
  rw [e] at hs
  rw [hs, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem ptChunks_spec {F W : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ)
    (h : ∀ c < 104, ptChunk F W c = true) (p : Fin 26572) :
    aptB p = true ∨ lG γ W 2 • p ≠ p ∨ lG γ W 3 • p ≠ p := by
  have hp := p.isLt
  have hc := tree_allBlk (h ((p : ℕ) / 256) (by omega)) ((p : ℕ) % 256) (Nat.mod_lt _ (by decide))
  beta_reduce at hc
  have e : Nat.mul (nat_lit 256) ((p : ℕ) / 256) + (p : ℕ) % 256 = p := Nat.div_add_mod _ 256
  rw [e, Nat.blt_eq.mpr hp] at hc
  change ptChk F W p = true at hc
  unfold ptChk at hc
  revert hc
  rcases ha : aptB p with _ | _
  · rcases hm : movesB F W (nat_lit 2) p with _ | _
    · intro hc
      exact Or.inr (Or.inr (movesB_spec (j := 3) (p := p) hγ hc))
    · intro _
      exact Or.inr (Or.inl (movesB_spec (j := 2) (p := p) hγ hm))
  · intro _
    exact Or.inl rfl

theorem lineB_cases {q : ℕ} (h : lineB q = true) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 6 := by
  unfold lineB at h
  revert h
  rcases h0 : Nat.beq q (nat_lit 0) with _ | _
  · rcases h1 : Nat.beq q (nat_lit 1) with _ | _
    · rcases h2 : Nat.beq q (nat_lit 2) with _ | _
      · intro h
        exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h)))
      · intro _
        exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2)))
    · intro _
      exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h1))
  · intro _
    exact Or.inl (Nat.eq_of_beq_eq_true h0)

theorem lineAll_spec {F W : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) (h : lineAll F W = true)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 16) {p : Fin 26572} (hp : lineB p = true) :
    lineB ((lG γ W j • p : Fin 26572) : ℕ) = true := by
  have hc := tree_allBlk h (j - 1) (by change j - 1 < 16; omega)
  beta_reduce at hc
  have e : (nat_lit 1) + (j - 1) = j := by change 1 + (j - 1) = j; omega
  rw [e] at hc
  obtain ⟨h0, hc⟩ := tree_bAnd hc
  obtain ⟨h1, hc⟩ := tree_bAnd hc
  obtain ⟨h2, h6⟩ := tree_bAnd hc
  have key : ∀ q : Fin 26572, lineChk F W j q = true →
      lineB ((lG γ W j • q : Fin 26572) : ℕ) = true := by
    intro q hq
    unfold lineChk at hq
    rw [tree_strictB] at hq
    beta_reduce at hq
    obtain ⟨hq1, hq2⟩ := tree_bAnd hq
    rw [← lAp_spec hγ (Nat.le_of_ble_eq_true hq1)]
    exact hq2
  rcases lineB_cases hp with e | e | e | e
  · exact key p (by rw [e]; exact h0)
  · exact key p (by rw [e]; exact h1)
  · exact key p (by rw [e]; exact h2)
  · exact key p (by rw [e]; exact h6)

end Points

section Words

variable {G : Type*} [Group G]

theorem invW_length (w : List (Fin 8 × Bool)) : (invW w).length = w.length := by
  simp [invW]

theorem dInv_digW (l : Fin 8 × Bool) : dInv (digW l) = digW (l.1, !l.2) := by
  obtain ⟨k, b⟩ := l
  have hk := k.2
  cases b
  · have e : digW (k, false) = k.val + 9 := rfl
    have e' : digW (k, !false) = k.val + 1 := rfl
    rw [e, e']
    unfold dInv
    rw [Nat.blt_eq.mpr (by omega : 8 < k.val + 9)]
    change k.val + 9 - 8 = k.val + 1
    omega
  · change dInv (k.val + 1) = k.val + 9
    unfold dInv
    have hb : Nat.blt (nat_lit 8) (k.val + 1) = false := by
      rcases hc : Nat.blt (nat_lit 8) (k.val + 1) with _ | _
      · rfl
      · have h8 := Nat.blt_eq.mp hc
        change 8 < k.val + 1 at h8
        omega
    rw [hb]

theorem digW_pos (l : Fin 8 × Bool) : 1 ≤ digW l := by
  unfold digW
  split <;> omega

theorem digW_lt (l : Fin 8 × Bool) : digW l < 32 := by
  unfold digW
  have := l.1.2
  split <;> omega

theorem wInvF_encW : ∀ (w : List (Fin 8 × Bool)) (f acc : ℕ), w.length ≤ f →
    wInvF f (encW w) acc = (invW w).foldl (fun a l => a * 32 + digW l) acc := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro f acc _
    cases f <;> rfl
  | append_singleton w l ih =>
    intro f acc hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rw [encW_append]
    have hd1 := digW_pos l
    have hd2 := digW_lt l
    change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Enum.strictN (Nat.add (Nat.shiftLeft acc 5)
      (dInv (Nat.land (encW w * 32 + digW l) 31))) fun a =>
        wInvF f (Nat.shiftRight (encW w * 32 + digW l) 5) a) acc
      (Nat.beq (encW w * 32 + digW l) 0) = _
    have h0 : Nat.beq (encW w * 32 + digW l) 0 = false := by
      rcases hc : Nat.beq (encW w * 32 + digW l) 0 with _ | _
      · rfl
      · have := Nat.eq_of_beq_eq_true hc
        omega
    rw [h0]
    dsimp only
    rw [tree_strictN]
    have h31 : Nat.land (encW w * 32 + digW l) 31 = digW l := by
      rw [show Nat.land (encW w * 32 + digW l) 31 = (encW w * 32 + digW l) % 32 from
        Nat.and_two_pow_sub_one_eq_mod _ 5]
      omega
    have h5 : Nat.shiftRight (encW w * 32 + digW l) 5 = encW w := by
      rw [show Nat.shiftRight (encW w * 32 + digW l) 5 = (encW w * 32 + digW l) / 32 from
        Nat.shiftRight_eq_div_pow _ 5]
      omega
    have hs : Nat.add (Nat.shiftLeft acc 5) (dInv (digW l)) = acc * 32 + digW (l.1, !l.2) := by
      rw [dInv_digW]
      change acc <<< 5 + _ = _
      rw [Nat.shiftLeft_eq]
    rw [h31, h5, hs, ih f _ (by simp at hf; omega)]
    simp [invW]

theorem wInv_encW (w : List (Fin 8 × Bool)) (hw : w.length ≤ 24) : wInv (encW w) = encW (invW w) :=
  wInvF_encW w 24 0 hw

theorem wG_wInv (γ : ℕ → G) {W : ℕ → ℕ} {LW : ℕ → List (Fin 8 × Bool)}
    (hW : ∀ j < 17, W j = encW (LW j)) (hL : ∀ j < 17, (LW j).length ≤ 24) {j : ℕ} (hj : j < 17) :
    wG γ 24 (wInv (W j)) = (lG γ W j)⁻¹ := by
  rw [lG, hW j hj, wInv_encW _ (hL j hj), wG_encW γ _ 24 (by rw [invW_length]; exact hL j hj),
    ev_invW, wG_encW γ _ 24 (hL j hj)]

@[expose] def enc3 (w : List (Fin 17 × Bool)) : ℕ :=
  w.foldl (fun acc l => acc * 64 + (2 * l.1.val + (if l.2 then 1 else 2))) 0

theorem enc3_append (w : List (Fin 17 × Bool)) (l : Fin 17 × Bool) :
    enc3 (w ++ [l]) = enc3 w * 64 + (2 * l.1.val + (if l.2 then 1 else 2)) := by
  simp [enc3, List.foldl_append]

end Words

section Eval

variable {G : Type*} [Group G] [MulAction G (Fin 26572)]

theorem le_boolRec {n a b : ℕ} (c : Bool) (ha : n ≤ a) (hb : n ≤ b) :
    n ≤ Bool.rec (motive := fun _ => ℕ) a b c := by
  cases c <;> assumption

theorem letAp_ge (F W : ℕ → ℕ) (d p : ℕ) (hp : 26572 ≤ p) : 26572 ≤ letAp F W d p := by
  unfold letAp
  rw [tree_strictN]
  beta_reduce
  rw [tree_strictN]
  beta_reduce
  exact le_boolRec _ (wAp_ge F _ _ _ hp) (wAp_ge F _ _ _ hp)

theorem evRF_ge (F W : ℕ → ℕ) : ∀ (f w p : ℕ), 26572 ≤ p → 26572 ≤ evRF F W f w p
  | 0, _, _, hp => hp
  | f + 1, w, p, hp => by
    change 26572 ≤ Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Enum.strictN
      (letAp F W (Nat.land w 63) p) fun q => evRF F W f (Nat.shiftRight w 6) q) p (Nat.beq w 0)
    refine le_boolRec _ ?_ hp
    rw [tree_strictN]
    exact evRF_ge F W f _ _ (letAp_ge F W _ _ hp)

theorem letAp_pos (F W : ℕ → ℕ) (j p : ℕ) : letAp F W (2 * j + 1) p = lAp F W j p := by
  unfold letAp
  rw [tree_strictN]
  beta_reduce
  rw [tree_strictN]
  beta_reduce
  have e1 : Nat.sub (2 * j + 1) (nat_lit 1) = 2 * j := Nat.add_sub_cancel (2 * j) 1
  rw [e1]
  have e2 : Nat.shiftRight (2 * j) (nat_lit 1) = j :=
    (Nat.shiftRight_eq_div_pow (2 * j) 1).trans (by rw [pow_one]; omega)
  have e3 : Nat.land (2 * j) (nat_lit 1) = 0 := (Nat.and_one_is_mod (2 * j)).trans (by omega)
  rw [e2, e3]
  rfl

theorem letAp_neg (F W : ℕ → ℕ) (j p : ℕ) :
    letAp F W (2 * j + 2) p = wAp F 24 (wInv (W j)) p := by
  unfold letAp
  rw [tree_strictN]
  beta_reduce
  rw [tree_strictN]
  beta_reduce
  have e1 : Nat.sub (2 * j + 2) (nat_lit 1) = 2 * j + 1 := by
    change 2 * j + 2 - 1 = 2 * j + 1
    omega
  rw [e1]
  have e2 : Nat.shiftRight (2 * j + 1) (nat_lit 1) = j :=
    (Nat.shiftRight_eq_div_pow (2 * j + 1) 1).trans (by rw [pow_one]; omega)
  have e3 : Nat.land (2 * j + 1) (nat_lit 1) = 1 :=
    (Nat.and_one_is_mod (2 * j + 1)).trans (by omega)
  rw [e2, e3]
  rfl

theorem letAp_spec {F W : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) {LW : ℕ → List (Fin 8 × Bool)}
    (hW : ∀ j < 17, W j = encW (LW j)) (hL : ∀ j < 17, (LW j).length ≤ 24)
    (l : Fin 17 × Bool) (p : Fin 26572)
    (h : letAp F W (2 * l.1.val + (if l.2 then 1 else 2)) p < 26572) :
    letAp F W (2 * l.1.val + (if l.2 then 1 else 2)) p =
      ((cond l.2 (lG γ W l.1) (lG γ W l.1)⁻¹ • p : Fin 26572) : ℕ) := by
  obtain ⟨j, b⟩ := l
  cases b
  · change letAp F W (2 * j.val + 2) p < 26572 at h
    change letAp F W (2 * j.val + 2) p = (((lG γ W j)⁻¹ • p : Fin 26572) : ℕ)
    rw [letAp_neg] at h ⊢
    rw [wAp_spec hγ 24 _ p h, wG_wInv γ hW hL j.2]
  · change letAp F W (2 * j.val + 1) p < 26572 at h
    change letAp F W (2 * j.val + 1) p = ((lG γ W j • p : Fin 26572) : ℕ)
    rw [letAp_pos] at h ⊢
    exact lAp_spec hγ h

theorem evRF_enc3 {F W : ℕ → ℕ} {γ : ℕ → G} (hγ : TabRep F γ) {LW : ℕ → List (Fin 8 × Bool)}
    (hW : ∀ j < 17, W j = encW (LW j)) (hL : ∀ j < 17, (LW j).length ≤ 24) :
    ∀ (w : List (Fin 17 × Bool)) (f : ℕ) (p : Fin 26572), w.length ≤ f →
      evRF F W f (enc3 w) p < 26572 →
      evRF F W f (enc3 w) p = ((burnsideF48s_ev (fun j : Fin 17 => lG γ W j) w • p : Fin 26572) : ℕ) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro f p _ _
    have e : evRF F W f (enc3 []) p = p := by cases f <;> rfl
    rw [e, burnsideF48s_ev_nil, one_smul]
  | append_singleton w l ih =>
    intro f p hf h
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rw [enc3_append] at h ⊢
    set d := 2 * l.1.val + (if l.2 then 1 else 2) with hd
    have hd1 : 1 ≤ d := by rw [hd]; split <;> omega
    have hd2 : d < 64 := by rw [hd]; have := l.1.2; split <;> omega
    have h0 : Nat.beq (enc3 w * 64 + d) 0 = false := by
      rcases hc : Nat.beq (enc3 w * 64 + d) 0 with _ | _
      · rfl
      · have := Nat.eq_of_beq_eq_true hc
        omega
    have h63 : Nat.land (enc3 w * 64 + d) 63 = d := by
      rw [show Nat.land (enc3 w * 64 + d) 63 = (enc3 w * 64 + d) % 64 from
        Nat.and_two_pow_sub_one_eq_mod _ 6]
      omega
    have h6 : Nat.shiftRight (enc3 w * 64 + d) 6 = enc3 w := by
      rw [show Nat.shiftRight (enc3 w * 64 + d) 6 = (enc3 w * 64 + d) / 64 from
        Nat.shiftRight_eq_div_pow _ 6]
      omega
    have eR : evRF F W (f + 1) (enc3 w * 64 + d) p =
        evRF F W f (enc3 w) (letAp F W d p) := by
      change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.Enum.strictN
        (letAp F W (Nat.land (enc3 w * 64 + d) 63) p) fun q =>
          evRF F W f (Nat.shiftRight (enc3 w * 64 + d) 6) q) p (Nat.beq (enc3 w * 64 + d) 0) = _
      rw [h0]
      dsimp only
      rw [tree_strictN, h63, h6]
    rw [eR] at h ⊢
    have hq : letAp F W d p < 26572 := by
      by_contra hc
      exact absurd h (Nat.not_lt.2 (evRF_ge F W f _ _ (Nat.not_lt.1 hc)))
    have hl := letAp_spec hγ hW hL l p hq
    have hfin : (⟨letAp F W d p, hq⟩ : Fin 26572) =
        cond l.2 (lG γ W l.1) (lG γ W l.1)⁻¹ • p := Fin.ext hl
    have ih' := ih f ⟨letAp F W d p, hq⟩ (by simp at hf; omega) h
    refine ih'.trans ?_
    rw [hfin, ← mul_smul, burnsideF48s_ev_append, burnsideF48s_ev_cons, burnsideF48s_ev_nil,
      mul_one]

end Eval

section Rels

theorem brelChunks_spec {F W : ℕ → ℕ} {B : ℕ} {R : ℕ → ℕ} {n C : ℕ} (hn : n ≤ 16 * C)
    (h : ∀ c < C, brelChunk F W B R n c = true) :
    ∀ i < n, R i < 2 ^ 240 ∧ ∀ u < 8, evR F W (R i) (bAt B u) = bAt B u := by
  intro i hi
  have hc := tree_allBlk (h (i / 16) (by omega)) (i % 16) (Nat.mod_lt i (by decide))
  beta_reduce at hc
  have e : Nat.mul (nat_lit 16) (i / 16) + i % 16 = i := Nat.div_add_mod i 16
  rw [e, Nat.blt_eq.mpr hi] at hc
  change relChk F W B (R i) = true at hc
  unfold relChk at hc
  obtain ⟨h1, hc⟩ := tree_bAnd hc
  refine ⟨?_, fun u hu => ?_⟩
  · have h1' := Nat.le_of_ble_eq_true h1
    change R i + 1 ≤ 1 <<< 240 at h1'
    rw [Nat.one_shiftLeft] at h1'
    omega
  · have hu' := tree_allBlk hc u hu
    beta_reduce at hu'
    rw [tree_strictB] at hu'
    beta_reduce at hu'
    rw [Nat.zero_add] at hu'
    exact Nat.eq_of_beq_eq_true hu'

theorem valid8_spec {F W : ℕ → ℕ} {B r : ℕ} (h : valid8 F W B r = true) :
    r < 2 ^ 240 ∧ ∀ u < 8, evR F W r (bAt B u) < 26572 := by
  unfold valid8 at h
  obtain ⟨h1, hc⟩ := tree_bAnd h
  refine ⟨?_, fun u hu => ?_⟩
  · have h1' := Nat.le_of_ble_eq_true h1
    change r + 1 ≤ 1 <<< 240 at h1'
    rw [Nat.one_shiftLeft] at h1'
    omega
  · have hu' := tree_allBlk hc u hu
    beta_reduce at hu'
    rw [Nat.zero_add] at hu'
    exact Nat.le_of_ble_eq_true hu'

theorem bkeyChunks_spec {F W : ℕ → ℕ} {B : ℕ} {KW KK : ℕ → ℕ} {n C : ℕ} (hn : n ≤ 13 * C)
    (h : ∀ c < C, bkeyChunk F W B KW KK n c = true) :
    ∀ i < n, valid8 F W B (KW i) = true ∧ key8 F W B (KW i) = KK i := by
  intro i hi
  have hc := tree_allBlk (h (i / 13) (by omega)) (i % 13) (Nat.mod_lt i (by decide))
  beta_reduce at hc
  have e : Nat.mul (nat_lit 13) (i / 13) + i % 13 = i := Nat.div_add_mod i 13
  rw [e, Nat.blt_eq.mpr hi] at hc
  obtain ⟨h1, h2⟩ := tree_bAnd hc
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

theorem neqChunks_spec {F W : ℕ → ℕ} {B : ℕ} {X Y : ℕ → ℕ} {n C : ℕ} (hn : n ≤ 17 * C)
    (h : ∀ c < C, neqChunk F W B X Y n c = true) :
    ∀ i < n, valid8 F W B (X i) = true ∧ valid8 F W B (Y i) = true ∧
      key8 F W B (X i) ≠ key8 F W B (Y i) := by
  intro i hi
  have hc := tree_allBlk (h (i / 17) (by omega)) (i % 17) (Nat.mod_lt i (by decide))
  beta_reduce at hc
  have e : Nat.mul (nat_lit 17) (i / 17) + i % 17 = i := Nat.div_add_mod i 17
  rw [e, Nat.blt_eq.mpr hi] at hc
  obtain ⟨h1, hc⟩ := tree_bAnd hc
  obtain ⟨h2, h3⟩ := tree_bAnd hc
  refine ⟨h1, h2, fun he => ?_⟩
  rw [he, Nat.beq_refl] at h3
  exact absurd h3 (by decide)

theorem distinctAll_lt {KK : ℕ → ℕ} {n : ℕ} (h : distinctAll KK n = true) {i j : ℕ} (hij : i < j)
    (hj : j < n) : KK i ≠ KK j := by
  intro e
  have hi := tree_allBlk h i (by omega)
  beta_reduce at hi
  rw [Nat.zero_add, tree_strictB] at hi
  beta_reduce at hi
  have hj' := tree_allBlk hi (j - (i + 1)) (by omega)
  beta_reduce at hj'
  have e2 : Nat.add i (nat_lit 1) + (j - (i + 1)) = j := by change i + 1 + (j - (i + 1)) = j; omega
  rw [e2, Nat.blt_eq.mpr hj, e, Nat.beq_refl] at hj'
  exact absurd hj' (by decide)

theorem distinctAll_spec {KK : ℕ → ℕ} {n : ℕ} (h : distinctAll KK n = true) :
    ∀ i < n, ∀ j < n, KK i = KK j → i = j := by
  intro i hi j hj e
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd e (distinctAll_lt h hij hj)
  · exact hij
  · exact absurd e.symm (distinctAll_lt h hij hi)

theorem key8F_congr {F W : ℕ → ℕ} {B r r' : ℕ} :
    ∀ n, (∀ u < n, evR F W r (bAt B u) = evR F W r' (bAt B u)) →
      key8F F W B r n = key8F F W B r' n
  | 0, _ => rfl
  | n + 1, h => by
    change CFSG.KC.Enum.strictN (key8F F W B r n) (fun a =>
        Nat.lor a (Nat.shiftLeft (evR F W r (bAt B n)) (Nat.mul 16 n))) =
      CFSG.KC.Enum.strictN (key8F F W B r' n) (fun a =>
        Nat.lor a (Nat.shiftLeft (evR F W r' (bAt B n)) (Nat.mul 16 n)))
    rw [tree_strictN, tree_strictN, key8F_congr n (fun u hu => h u (by omega)), h n (by omega)]

end Rels

end CFSG.KC.D43

end
