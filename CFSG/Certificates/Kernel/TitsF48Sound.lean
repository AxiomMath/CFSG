module

public import Certificates.Data.Kernel.TitsF48K
public import CFSG.Certificates.Kernel.TitsDSound

public section

namespace CFSG.KC.TitsF48Sound

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TitsDK CFSG.KC.TitsF48K
  CFSG.KC.TwoF4LieSound CFSG.KC.TitsOctSound CFSG.KC.TitsDSound

section Eqs

variable {FA FAI : ℕ → ℕ} {LAY PA LB PS : ℕ}

theorem sgR_succ (k kp n j : ℕ) : sgR FA PA LB k kp (n + 1) j =
    if fw 4 LB j = 15 then (if j < 512 then k else kp)
    else gp (FA (fw 4 LB j)) (sgR FA PA LB k kp n (fw 12 PA j)) := by
  change Bool.rec (motive := fun _ => ℕ) (strictN (sgR FA PA LB k kp n (fw 12 PA j))
    (fun y => gp (FA (fw 4 LB j)) y)) (Bool.rec (motive := fun _ => ℕ) kp k (Nat.blt j 512))
    (Nat.beq (fw 4 LB j) 15) = _
  rw [strictN_eq', nIf_d, nIf_d, beq_d, blt_d]
  by_cases h : fw 4 LB j = 15 <;> simp [h]

theorem fiR_succ (n j v : ℕ) : fiR FAI PA LB (n + 1) j v =
    if fw 4 LB j = 15 then v else fiR FAI PA LB n (fw 12 PA j) (gp (FAI (fw 4 LB j)) v) := by
  change Bool.rec (motive := fun _ => ℕ) (strictN (gp (FAI (fw 4 LB j)) v)
    (fun w => fiR FAI PA LB n (fw 12 PA j) w)) v (Nat.beq (fw 4 LB j) 15) = _
  rw [strictN_eq', nIf_d, beq_d]
  by_cases h : fw 4 LB j = 15 <;> simp [h]

theorem sF_eq (k kp x : ℕ) : sF FA LAY PA LB PS k kp x =
    if x < 1755 then (if layAt LAY x ≤ 6 then x
      else sgR FA PA LB k kp (fw 13 PS x + 1) (fw 13 PS x)) else 8191 := by
  unfold sF
  rw [strictN_eq', nIf_d, nIf_d, blt_d, ble_d]
  by_cases h1 : x < 1755 <;> by_cases h2 : layAt LAY x ≤ 6 <;> simp [h1, h2]

theorem sH_true_eq (kv x : ℕ) : sH FA LAY PA LB PS true kv x =
    if x < 1755 then (if layAt LAY x ≤ 6 then x
      else if fw 13 PS x < 512 then sgR FA PA LB kv kv (fw 13 PS x + 1) (fw 13 PS x) else 8191)
    else 8191 := by
  unfold sH
  rw [strictN_eq', nIf_d, nIf_d, nIf_d, blt_d, ble_d]
  change (if decide (x < 1755) = true then (if decide (layAt LAY x ≤ 6) = true then x else
    if Nat.blt (fw 13 PS x) 512 = true then _ else 8191) else 8191) = _
  rw [blt_d]
  by_cases h1 : x < 1755 <;> by_cases h2 : layAt LAY x ≤ 6 <;> simp [h1, h2]

theorem sH_false_eq (kv x : ℕ) : sH FA LAY PA LB PS false kv x =
    if x < 1755 then (if layAt LAY x ≤ 6 then x
      else if 512 ≤ fw 13 PS x then sgR FA PA LB kv kv (fw 13 PS x + 1) (fw 13 PS x) else 8191)
    else 8191 := by
  unfold sH
  rw [strictN_eq', nIf_d, nIf_d, nIf_d, blt_d, ble_d]
  change (if decide (x < 1755) = true then (if decide (layAt LAY x ≤ 6) = true then x else
    if Nat.ble 512 (fw 13 PS x) = true then _ else 8191) else 8191) = _
  rw [ble_d]
  by_cases h1 : x < 1755 <;> by_cases h2 : layAt LAY x ≤ 6 <;> simp [h1, h2]

theorem gpS_eq (a x : ℕ) : gpS a x = if x < 1755 then gp a x else 8191 := by
  unfold gpS
  rw [nIf_d, blt_d]
  by_cases h : x < 1755 <;> simp [h]

theorem itP_succ (g : ℕ → ℕ) (m x : ℕ) : itP g (m + 1) x = g (itP g m x) := strictN_eq' _ _

theorem itP_zero (g : ℕ → ℕ) (x : ℕ) : itP g 0 x = x := rfl

end Eqs

theorem halfF_sound {ORD PA LB : ℕ} (h : halfF ORD PA LB = true) :
    ∀ i < 1024, (fw 4 LB i = 15 → fw 13 ORD i = if i < 512 then 87 else 133) ∧
      (fw 4 LB i ≠ 15 → 512 ≤ i → 512 ≤ fw 12 PA i) := by
  unfold halfF at h
  rw [allN_iff'] at h
  intro i hi
  have h' := h i hi
  clear h
  simp only [bIf_d, nIf_d, beq_d, blt_d, ble_d] at h'
  by_cases hr : fw 4 LB i = 15 <;> by_cases h5 : i < 512 <;> simp_all <;> omega

theorem invF_sound {FA FAI : ℕ → ℕ} (h : invF FA FAI = true) :
    ∀ j < 6, ∀ x < 1755, gp (FAI j) (gp (FA j) x) = x := by
  unfold invF at h
  simp only [allN_iff', strictB_eq', beq_d, decide_eq_true_eq] at h
  exact h

theorem smallF_sound {lp FA : ℕ → ℕ} {PL nG t b1 b2 : ℕ} (h : smallF lp FA PL nG t b1 b2 = true) :
    (∀ x < 1755, gp nG (gp nG x) = x) ∧
    (∀ j < 6, lineMap lp (gp (FA j)) 0 0 = true ∧
      lineMap lp (fun x => gp nG (gp (FA j) (gp nG x))) 0 0 = true) ∧
    lineMap lp (gp t) 0 0 = true ∧ lineMap lp (gp b1) 0 0 = true ∧ lineMap lp (gp b2) 0 0 = true ∧
    (∀ x < 1755, itP (fun y => gp nG (gp b1 y)) 4 x = x) ∧
    (∀ x < 1755, itP (fun y => gp nG (gp b2 y)) 5 x = x) ∧
    (∀ k < 5, plK PL 0 k ≠ 0 → ∃ i < 4, lineMap lp (tn1 t nG i) 0 (plK PL 0 k) = true) ∧
    ∀ p < 1755, p ≠ 0 → gp t p = p → ∃ j < 6, gp (FA j) p ≠ p := by
  unfold smallF at h
  simp only [bAnd_eq', bNotD, Bool.and_eq_true, allN_iff', strictB_eq', beq_d,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun k hk hne => ?_, fun p hp hp0 hfix => ?_⟩
  · have h' := h8 k hk
    rw [bIf_d, if_neg (by simpa using hne)] at h'
    exact anyN_iffD.1 h'
  · have h' := h9 p hp
    rw [bIf_d (decide (p = 0)), if_neg (by simpa using hp0), bIf_d,
      if_pos (decide_eq_true hfix)] at h'
    obtain ⟨j, hj, hm⟩ := anyN_iffD.1 h'
    exact ⟨j, hj, by simpa using hm⟩

theorem witS_sound {nG q0 b1 b2 : ℕ} {s : ℕ → ℕ} {r : List ℕ} {full : Bool}
    (h : witS nG q0 b1 b2 s r full = true) :
    (∃ a < 1755, gpS nG (s (gpS nG (s a))) < 1755 ∧ gpS nG (s (gpS nG (s a))) ≠ a) ∨
    (∃ c < 1755, itP (fun y => gpS nG (s (gpS b1 y))) 4 c < 1755 ∧
      itP (fun y => gpS nG (s (gpS b1 y))) 4 c ≠ c) ∨
    (∃ c < 1755, itP (fun y => gpS nG (s (gpS b2 y))) 5 c < 1755 ∧
      itP (fun y => gpS nG (s (gpS b2 y))) 5 c ≠ c) ∨
    (full = true ∧ ∃ a < 1755, ∃ L, 0 < L ∧ ¬ L ∣ 17971200 ∧
      cycFrom (fun y => gp nG (s (gp q0 y))) a (L - 1) (gp nG (s (gp q0 a))) = true) := by
  unfold witS at h
  simp only [strictB_eq', bAnd_eq', bNotD, blt_d, beq_d, nIf_d] at h
  rw [bIf_d, bIf_d] at h
  split_ifs at h <;>
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at h <;>
    first
    | exact Or.inl ⟨_, h.1, h.2.1, h.2.2⟩
    | exact Or.inr (Or.inl ⟨_, h.2.1, h.2.2.1, h.2.2.2⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, h.2.1, h.2.2.1, h.2.2.2⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨h.1, _, h.2.2.1, _, h.2.2.2.1,
        fun hd => h.2.2.2.2.1 (Nat.mod_eq_zero_of_dvd hd), h.2.2.2.2.2⟩))

theorem rowA_sound {FA FAI : ℕ → ℕ} {LAY ORD PA LB PS nG q0 b1 b2 : ℕ} {S1 : List ℕ} {i : ℕ}
    {r : List ℕ} (h : rowA FA FAI LAY ORD PA LB PS nG q0 b1 b2 S1 i r = true) :
    (i < 512 → (r.headD 0 = 0 ∧ r.getD 1 0 < 16 ∧ S1.getD (r.getD 1 0) 0 = i) ∨
      witS nG q0 b1 b2 (sH FA LAY PA LB PS true (fw 13 ORD i)) r false = true) ∧
    (¬ i < 512 → 512 ≤ fw 13 PS (gp nG (fw 13 ORD i)) ∧ fw 13 PS (gp nG (fw 13 ORD i)) < 1024 ∧
      fw 13 ORD (fw 13 PS (gp nG (fw 13 ORD i))) = gp nG (fw 13 ORD i) ∧
      witS nG q0 b1 b2 (sF FA LAY PA LB PS (fw 13 ORD i)
        (fiR FAI PA LB (fw 13 PS (gp nG (fw 13 ORD i)) + 1) (fw 13 PS (gp nG (fw 13 ORD i)))
          (gp nG 87))) r true = true) := by
  unfold rowA at h
  simp only [strictB_eq', bAnd_eq', blt_d, ble_d, beq_d] at h
  rw [bIf_d (decide (i < 512))] at h
  constructor
  · intro hi
    rw [if_pos (decide_eq_true hi), bIf_d] at h
    split_ifs at h with h0
    · left
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h h0
      exact ⟨h0, h.1, h.2⟩
    · exact Or.inr h
  · intro hi
    rw [if_neg (by simpa using hi)] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h

theorem rowB_sound {FA FAI : ℕ → ℕ} {LAY ORD PA LB PS nG q0 b1 b2 : ℕ} {S2 : List ℕ} {i : ℕ}
    {r : List ℕ} (h : rowB FA FAI LAY ORD PA LB PS nG q0 b1 b2 S2 i r = true) :
    (512 ≤ i → (r.headD 0 = 0 ∧ r.getD 1 0 < 16 ∧ S2.getD (r.getD 1 0) 0 = i) ∨
      witS nG q0 b1 b2 (sH FA LAY PA LB PS false (fw 13 ORD i)) r false = true) ∧
    (i < 512 → fw 13 PS (gp nG (fw 13 ORD i)) < 512 ∧
      fw 13 ORD (fw 13 PS (gp nG (fw 13 ORD i))) = gp nG (fw 13 ORD i) ∧
      witS nG q0 b1 b2 (sF FA LAY PA LB PS
        (fiR FAI PA LB (fw 13 PS (gp nG (fw 13 ORD i)) + 1) (fw 13 PS (gp nG (fw 13 ORD i)))
          (gp nG 133)) (fw 13 ORD i)) r true = true) := by
  unfold rowB at h
  simp only [strictB_eq', bAnd_eq', blt_d, ble_d, beq_d] at h
  rw [bIf_d (decide (512 ≤ i))] at h
  constructor
  · intro hi
    rw [if_pos (decide_eq_true hi), bIf_d] at h
    split_ifs at h with h0
    · left
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h h0
      exact ⟨h0, h.1, h.2⟩
    · exact Or.inr h
  · intro hi
    rw [if_neg (by simp only [decide_eq_true_eq]; omega)] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h

theorem rowC_sound {FA : ℕ → ℕ} {LAY ORD PA LB PS nG q0 b1 b2 : ℕ} {S1 S2 : List ℕ} {i : ℕ}
    {r : List ℕ} (h : rowC FA LAY ORD PA LB PS nG q0 b1 b2 S1 S2 i r = true) :
    (fw 13 ORD (S1.getD (i / 16) 0) = 87 ∧ fw 13 ORD (S2.getD (i % 16) 0) = 133) ∨
      witS nG q0 b1 b2 (sF FA LAY PA LB PS (fw 13 ORD (S1.getD (i / 16) 0))
        (fw 13 ORD (S2.getD (i % 16) 0))) r true = true := by
  unfold rowC at h
  simp only [strictB_eq', bAnd_eq'] at h
  rw [bIf_d] at h
  split_ifs at h
  · left
    simp only [Bool.and_eq_true, beq_d, decide_eq_true_eq] at h
    exact h
  · exact Or.inr h

theorem rowsK_sound {f : ℕ → List ℕ → Bool} {i₀ : ℕ} {R : List (List ℕ)}
    (h : rowsK f i₀ R = true) : ∀ i (hi : i < R.length), f (i₀ + i) R[i] = true := by
  intro i hi
  have := (allL_iff R 0).1 h i hi
  rwa [Nat.zero_add] at this

@[expose] def PartOf (σ : Pm) (s : ℕ → ℕ) : Prop := ∀ x, s x = 8191 ∨ (x < 1755 ∧ s x = ev σ x)

theorem part_big {σ : Pm} {s : ℕ → ℕ} (hs : PartOf σ s) : s 8191 = 8191 :=
  (hs 8191).resolve_right (fun h => absurd h.1 (by norm_num))

theorem gpS_P {a : ℕ} {g : Pm} (ha : PR a g) : PartOf g (gpS a) := by
  intro y
  rw [gpS_eq]
  by_cases hy : y < 1755
  · rw [if_pos hy, gp_ev ha hy]
    exact Or.inr ⟨hy, rfl⟩
  · rw [if_neg hy]
    exact Or.inl rfl

theorem part_comp {σ τ ρ : Pm} {s t : ℕ → ℕ} (hs : PartOf σ s) (ht : PartOf τ t) (ρ_eq : ρ = σ * τ) :
    PartOf ρ (fun y => s (t y)) := by
  intro y
  rcases ht y with h1 | ⟨hy, h1⟩
  · left
    simp only
    rw [h1, part_big hs]
  · rcases hs (t y) with h2 | ⟨-, h2⟩
    · exact Or.inl h2
    · right
      refine ⟨hy, ?_⟩
      simp only
      rw [h2, h1, ρ_eq, ev_mul _ _ hy]

theorem part_it {g : Pm} {T : ℕ → ℕ} (hT : PartOf g T) {c : ℕ} (hc : c < 1755) :
    ∀ m, itP T m c = 8191 ∨ itP T m c = ev (g ^ m) c
  | 0 => Or.inr (by rw [itP_zero, pow_zero, ev_one])
  | m + 1 => by
    rw [itP_succ]
    rcases part_it hT hc m with h | h
    · left
      rw [h, part_big hT]
    · rcases hT (itP T m c) with h' | ⟨-, h'⟩
      · exact Or.inl h'
      · right
        rw [h', h, pow_succ', ev_mul _ _ hc]

theorem kill {nG q0 b1 b2 : ℕ} {n q β1 β2 σ : Pm} (hn : PR nG n) (hq : PR q0 q)
    (hb1 : PR b1 β1) (hb2 : PR b2 β2) (h2 : (n * σ) ^ 2 = 1) (hr1 : (n * σ * β1) ^ 4 = 1)
    (hr2 : (n * σ * β2) ^ 5 = 1) (hX : (n * σ * q) ^ 17971200 = 1) {s : ℕ → ℕ}
    (hs : PartOf σ s) {r : List ℕ} {full : Bool} (hfull : full = true → ∀ x < 1755, s x = ev σ x)
    (h : witS nG q0 b1 b2 s r full = true) : False := by
  have hU : PartOf (n * σ) (fun y => gpS nG (s y)) := part_comp (gpS_P hn) hs rfl
  rcases witS_sound h with ⟨a, ha, hy, hne⟩ | ⟨c, hc, hy, hne⟩ | ⟨c, hc, hy, hne⟩ |
    ⟨hf, a, ha, L, hL0, hLd, hcyc⟩
  · have := part_it hU ha 2
    rw [itP_succ, itP_succ, itP_zero, h2, ev_one] at this
    rcases this with h' | h'
    · rw [h'] at hy
      omega
    · exact hne h'
  · have hT : PartOf (n * σ * β1) (fun y => gpS nG (s (gpS b1 y))) :=
      part_comp (s := fun y => gpS nG (s y)) (t := gpS b1) hU (gpS_P hb1) rfl
    rcases part_it hT hc 4 with h' | h'
    · rw [h'] at hy
      omega
    · rw [hr1, ev_one] at h'
      exact hne h'
  · have hT : PartOf (n * σ * β2) (fun y => gpS nG (s (gpS b2 y))) :=
      part_comp (s := fun y => gpS nG (s y)) (t := gpS b2) hU (gpS_P hb2) rfl
    rcases part_it hT hc 5 with h' | h'
    · rw [h'] at hy
      omega
    · rw [hr2, ev_one] at h'
      exact hne h'
  · have hs' := hfull hf
    set g := n * σ * q with hg
    have hG : ∀ y < 1755, gp nG (s (gp q0 y)) = ev g y := by
      intro y hy
      rw [gp_ev hq hy, hs' _ (ev_lt q hy), gp_ev hn (ev_lt σ (ev_lt q hy)), hg,
        ev_mul (n * σ) q hy, ev_mul n σ (ev_lt q hy)]
    have hit : ∀ m, (fun y => gp nG (s (gp q0 y)))^[m] a = ev (g ^ m) a := by
      intro m
      induction m with
      | zero => simp [ev_one]
      | succ m ihm =>
        rw [Function.iterate_succ_apply', ihm, hG _ (ev_lt _ ha), pow_succ', ev_mul _ _ ha]
    obtain ⟨hmin, hret⟩ := (cycFrom_iff (L - 1) _).1 hcyc
    have hret' : ev (g ^ L) a = a := by
      rw [← hit, show L = (L - 1) + 1 by omega, Function.iterate_succ_apply]
      exact hret
    have hmin' : ∀ m, 0 < m → m < L → ev (g ^ m) a ≠ a := by
      intro m hm0 hmL
      rw [← hit, show m = (m - 1) + 1 by omega, Function.iterate_succ_apply]
      exact hmin (m - 1) (by omega)
    have hgN : ev (g ^ 17971200) a = a := by rw [hX, ev_one]
    have hgm : ∀ m, ev (g ^ (L * m)) a = a := by
      intro m
      induction m with
      | zero => simp [ev_one]
      | succ m ihm => rw [Nat.mul_succ, pow_add, ev_mul _ _ ha, hret', ihm]
    have hlt' := Nat.mod_lt 17971200 hL0
    have hmod : ev (g ^ (17971200 % L)) a = a := by
      have e := Nat.mod_add_div 17971200 L
      rw [← e, pow_add, ev_mul _ _ ha, hgm] at hgN
      exact hgN
    have hpos : 0 < 17971200 % L :=
      Nat.pos_of_ne_zero (fun h0' => hLd (Nat.dvd_of_mod_eq_zero h0'))
    exact hmin' _ hpos hlt' hmod

section Rigid

variable {lp FA FAI : ℕ → ℕ} {f : ℕ → Pm} {isR : ℕ → Bool} {LAY ORD PA LB PS : ℕ}

theorem rec_pts2 (hFA : ∀ j < 6, PR (FA j) (f j))
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) (hhalf : halfF ORD PA LB = true) :
    ∀ i < 1024, fw 13 ORD i < 1755 ∧ (fw 4 LB i ≠ 15 → fw 12 PA i < i ∧ fw 4 LB i < 6 ∧
      ev (f (fw 4 LB i)) (fw 13 ORD (fw 12 PA i)) = fw 13 ORD i) := by
  obtain ⟨hst, -⟩ := recR_sound hrec
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hr : fw 4 LB i = 15
    · refine ⟨?_, fun h => absurd hr h⟩
      rw [(halfF_sound hhalf i hi).1 hr]
      split_ifs <;> norm_num
    · obtain ⟨hpi, hlb, hav⟩ := (hst i hi).2.2 hr
      have hp := (ih _ hpi (by omega)).1
      obtain ⟨hlt, e⟩ := (actV_pt hp).1 hav
      refine ⟨hlt, fun _ => ⟨hpi, hlb, ?_⟩⟩
      rw [← gp_ev (hFA _ hlb) hp]
      exact e

theorem sgR_half (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true)
    (hhalf : halfF ORD PA LB = true) (k kp : ℕ) : ∀ n j, j < 1024 → j < n →
    (j < 512 → sgR FA PA LB k kp n j = sgR FA PA LB k k n j) ∧
    (512 ≤ j → sgR FA PA LB k kp n j = sgR FA PA LB kp kp n j) := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j hj hjn
    rw [sgR_succ, sgR_succ, sgR_succ]
    by_cases hr : fw 4 LB j = 15
    · simp only [hr, if_true]
      constructor
      · intro h
        simp [h]
      · intro h
        simp [show ¬ j < 512 by omega]
    · simp only [hr, if_false]
      obtain ⟨hp, -, -⟩ := ((recR_sound hrec).1 j hj).2.2 hr
      have hhp := (halfF_sound hhalf j hj).2 hr
      have e := ih (fw 12 PA j) (by omega) (by omega)
      constructor
      · intro h
        rw [e.1 (by omega)]
      · intro h
        rw [e.2 (hhp h)]

theorem sgR_lt (hFA : ∀ j < 6, PR (FA j) (f j))
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) {c c' : ℕ} (hc : c < 1755)
    (hc' : c' < 1755) : ∀ n j, j < 1024 → j < n → sgR FA PA LB c c' n j < 1755 := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j hj hjn
    rw [sgR_succ]
    by_cases hr : fw 4 LB j = 15
    · simp only [hr, if_true]
      split_ifs <;> assumption
    · simp only [hr, if_false]
      obtain ⟨hp, hlb, -⟩ := ((recR_sound hrec).1 j hj).2.2 hr
      have hu := ih (fw 12 PA j) (by omega) (by omega)
      rw [gp_ev (hFA _ hlb) hu]
      exact ev_lt _ hu

theorem fiR_inv (hFA : ∀ j < 6, PR (FA j) (f j))
    (hinv : ∀ j < 6, ∀ x < 1755, gp (FAI j) (gp (FA j) x) = x)
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) {c : ℕ} (hc : c < 1755) :
    ∀ n j, j < 1024 → j < n → fiR FAI PA LB n j (sgR FA PA LB c c n j) = c := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j hj hjn
    rw [sgR_succ, fiR_succ]
    by_cases hr : fw 4 LB j = 15
    · simp only [hr, if_true]
      split_ifs <;> rfl
    · simp only [hr, if_false]
      obtain ⟨hp, hlb, -⟩ := ((recR_sound hrec).1 j hj).2.2 hr
      rw [hinv _ hlb _ (sgR_lt hFA hrec hc hc n _ (by omega) (by omega))]
      exact ih _ (by omega) (by omega)

theorem sig_rec (hFA : ∀ j < 6, PR (FA j) (f j))
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) (hhalf : halfF ORD PA LB = true)
    {σ : Pm} (hc : ∀ j < 6, σ * f j = f j * σ) :
    ∀ n j, j < 1024 → j < n → ev σ (fw 13 ORD j) = sgR FA PA LB (ev σ 87) (ev σ 133) n j := by
  have hpts := rec_pts2 hFA hrec hhalf
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j hj hjn
    rw [sgR_succ]
    by_cases hr : fw 4 LB j = 15
    · rw [if_pos hr, (halfF_sound hhalf j hj).1 hr]
      by_cases h5 : j < 512 <;> simp [h5]
    · rw [if_neg hr]
      obtain ⟨hpi, hlb, e⟩ := (hpts j hj).2 hr
      have hp := (hpts (fw 12 PA j) (by omega)).1
      rw [← ih _ (by omega) (by omega), gp_ev (hFA _ hlb) (ev_lt σ hp), ← e, ← ev_mul _ _ hp,
        ← ev_mul _ _ hp, hc _ hlb]

theorem sig_eq2 (hFA : ∀ j < 6, PR (FA j) (f j))
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) (hhalf : halfF ORD PA LB = true)
    (hfar : farK LAY = true) {σ : Pm} (h6 : ∀ x < 1755, layAt LAY x ≤ 6 → ev σ x = x)
    (hc : ∀ j < 6, σ * f j = f j * σ) :
    ∀ x < 1755, ev σ x = sF FA LAY PA LB PS (ev σ 87) (ev σ 133) x := by
  obtain ⟨-, hcov⟩ := recR_sound hrec
  obtain ⟨-, hfar'⟩ := farK_sound hfar
  intro x hx
  rw [sF_eq, if_pos hx]
  by_cases hl : layAt LAY x ≤ 6
  · rw [if_pos hl]
    exact h6 x hx hl
  · rw [if_neg hl]
    obtain ⟨hq, e⟩ := hcov x (by omega) ((hfar' x hx).resolve_left hl)
    rw [← sig_rec hFA hrec hhalf hc _ _ hq (by omega), e]

theorem half_true (hFA : ∀ j < 6, PR (FA j) (f j))
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) (hhalf : halfF ORD PA LB = true)
    (hfar : farK LAY = true) {σ : Pm} (h6 : ∀ x < 1755, layAt LAY x ≤ 6 → ev σ x = x)
    (hc : ∀ j < 6, σ * f j = f j * σ) : PartOf σ (sH FA LAY PA LB PS true (ev σ 87)) := by
  obtain ⟨-, hcov⟩ := recR_sound hrec
  obtain ⟨-, hfar'⟩ := farK_sound hfar
  intro x
  rw [sH_true_eq]
  by_cases hx : x < 1755
  · rw [if_pos hx]
    by_cases hl : layAt LAY x ≤ 6
    · rw [if_pos hl]
      exact Or.inr ⟨hx, (h6 x hx hl).symm⟩
    · rw [if_neg hl]
      obtain ⟨hq, e⟩ := hcov x (by omega) ((hfar' x hx).resolve_left hl)
      by_cases hj : fw 13 PS x < 512
      · rw [if_pos hj]
        refine Or.inr ⟨hx, ?_⟩
        rw [← (sgR_half hrec hhalf (ev σ 87) (ev σ 133) _ _ hq (by omega)).1 hj,
          ← sig_rec hFA hrec hhalf hc _ _ hq (by omega), e]
      · rw [if_neg hj]
        exact Or.inl rfl
  · rw [if_neg hx]
    exact Or.inl rfl

theorem half_false (hFA : ∀ j < 6, PR (FA j) (f j))
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) (hhalf : halfF ORD PA LB = true)
    (hfar : farK LAY = true) {σ : Pm} (h6 : ∀ x < 1755, layAt LAY x ≤ 6 → ev σ x = x)
    (hc : ∀ j < 6, σ * f j = f j * σ) : PartOf σ (sH FA LAY PA LB PS false (ev σ 133)) := by
  obtain ⟨-, hcov⟩ := recR_sound hrec
  obtain ⟨-, hfar'⟩ := farK_sound hfar
  intro x
  rw [sH_false_eq]
  by_cases hx : x < 1755
  · rw [if_pos hx]
    by_cases hl : layAt LAY x ≤ 6
    · rw [if_pos hl]
      exact Or.inr ⟨hx, (h6 x hx hl).symm⟩
    · rw [if_neg hl]
      obtain ⟨hq, e⟩ := hcov x (by omega) ((hfar' x hx).resolve_left hl)
      by_cases hj : 512 ≤ fw 13 PS x
      · rw [if_pos hj]
        refine Or.inr ⟨hx, ?_⟩
        rw [← (sgR_half hrec hhalf (ev σ 87) (ev σ 133) _ _ hq (by omega)).2 hj,
          ← sig_rec hFA hrec hhalf hc _ _ hq (by omega), e]
      · rw [if_neg hj]
        exact Or.inl rfl
  · rw [if_neg hx]
    exact Or.inl rfl

theorem lay8 (hfar : farK LAY = true) {σ : Pm} (h6 : ∀ x < 1755, layAt LAY x ≤ 6 → ev σ x = x)
    {p : ℕ} (hp : p < 1755) (h8 : layAt LAY p = 8) : layAt LAY (ev σ p) = 8 := by
  obtain ⟨-, hfar'⟩ := farK_sound hfar
  rcases hfar' _ (ev_lt σ hp) with hl | hl
  · exfalso
    have e' := ev_inj σ (ev_lt σ hp) hp (h6 _ (ev_lt σ hp) hl)
    rw [e', h8] at hl
    omega
  · exact hl

theorem rigid2 (hFA : ∀ j < 6, PR (FA j) (f j)) (hinv : invF FA FAI = true)
    (hrec : recR lp FA 6 isR 8 1024 LAY ORD PA LB PS = true) (hhalf : halfF ORD PA LB = true)
    (hfar : farK LAY = true) (h133 : layAt LAY 133 = 8)
    {nG q0 b1 b2 : ℕ} {n q β1 β2 : Pm} (hn : PR nG n) (hq : PR q0 q) (hb1 : PR b1 β1)
    (hb2 : PR b2 β2) (hnn : n * n = 1) {S1 S2 : List ℕ}
    (hA : ∀ i < 1024, ∃ r, rowA FA FAI LAY ORD PA LB PS nG q0 b1 b2 S1 i r = true)
    (hB : ∀ i < 1024, ∃ r, rowB FA FAI LAY ORD PA LB PS nG q0 b1 b2 S2 i r = true)
    (hC : ∀ i < 256, ∃ r, rowC FA LAY ORD PA LB PS nG q0 b1 b2 S1 S2 i r = true)
    {σ : Pm} (h6 : ∀ x < 1755, layAt LAY x ≤ 6 → ev σ x = x) (hc : ∀ j < 6, σ * f j = f j * σ)
    (h2 : (n * σ) ^ 2 = 1) (hr1 : (n * σ * β1) ^ 4 = 1) (hr2 : (n * σ * β2) ^ 5 = 1)
    (hX : (n * σ * q) ^ 17971200 = 1) : σ = 1 := by
  have hinv' := invF_sound hinv
  obtain ⟨-, hcov⟩ := recR_sound hrec
  obtain ⟨h87, -⟩ := farK_sound hfar
  have hs := sig_eq2 hFA hrec hhalf hfar h6 hc
  have h1 := sig_eq2 (σ := 1) hFA hrec hhalf hfar (fun n _ _ => ev_one n) (fun j _ => by simp)
  simp only [ev_one] at h1
  have kF : ∀ r, witS nG q0 b1 b2 (sF FA LAY PA LB PS (ev σ 87) (ev σ 133)) r true = true →
      False := by
    intro r hw
    refine kill hn hq hb1 hb2 h2 hr1 hr2 hX ?_ (fun _ x hx => (hs x hx).symm) hw
    intro x
    by_cases hx : x < 1755
    · exact Or.inr ⟨hx, (hs x hx).symm⟩
    · left
      rw [sF_eq, if_neg hx]
  have kH : ∀ r s, PartOf σ s → witS nG q0 b1 b2 s r false = true → False := fun r s hs' hw =>
    kill hn hq hb1 hb2 h2 hr1 hr2 hX hs' (fun h => absurd h Bool.false_ne_true) hw
  have hn2 : ∀ z < 1755, ev n (ev n z) = z := by
    intro z hz
    rw [← ev_mul _ _ hz, hnn, ev_one]
  have hnk : ∀ p < 1755, ev σ (ev n (ev σ p)) = ev n p := by
    intro p hp
    have e : ev ((n * σ) ^ 2) p = p := by rw [h2, ev_one]
    rw [sq, ev_mul _ _ hp, ev_mul n σ hp, ev_mul n σ (ev_lt _ (ev_lt _ hp))] at e
    have e' := congrArg (ev n) e
    rw [hn2 _ (ev_lt σ (ev_lt n (ev_lt σ hp)))] at e'
    exact e'
  have hk1 : ev σ 87 < 1755 := ev_lt σ (by norm_num)
  have hkp1 : ev σ 133 < 1755 := ev_lt σ (by norm_num)
  obtain ⟨hi, ei⟩ := hcov _ (by omega) (lay8 hfar h6 (by norm_num) h87)
  obtain ⟨hi', ei'⟩ := hcov _ (by omega) (lay8 hfar h6 (by norm_num) h133)
  by_cases hiA : fw 13 PS (ev σ 87) < 512
  · by_cases hiB : fw 13 PS (ev σ 133) < 512
    ·
      obtain ⟨r, hr⟩ := hB _ hi'
      obtain ⟨hj, hjo, hw⟩ := (rowB_sound hr).2 hiB
      rw [ei'] at hj hjo hw
      rw [gp_ev hn hkp1] at hj hjo hw
      have hsj := sig_rec hFA hrec hhalf hc _ (fw 13 PS (ev n (ev σ 133))) (by omega)
        (Nat.lt_succ_self _)
      rw [hjo, hnk 133 (by norm_num),
        (sgR_half hrec hhalf (ev σ 87) (ev σ 133) _ _ (by omega) (Nat.lt_succ_self _)).1 hj]
        at hsj
      have hforce : fiR FAI PA LB (fw 13 PS (ev n (ev σ 133)) + 1) (fw 13 PS (ev n (ev σ 133)))
          (gp nG 133) = ev σ 87 := by
        rw [gp_ev hn (by norm_num), hsj]
        exact fiR_inv hFA hinv' hrec hk1 _ _ (by omega) (Nat.lt_succ_self _)
      rw [hforce] at hw
      exact (kF r hw).elim
    ·
      obtain ⟨r, hr⟩ := hA _ hi
      rcases (rowA_sound hr).1 hiA with ⟨-, ha16, ea⟩ | hw
      swap
      · rw [ei] at hw
        exact (kH r _ (half_true hFA hrec hhalf hfar h6 hc) hw).elim
      obtain ⟨r', hr'⟩ := hB _ hi'
      rcases (rowB_sound hr').1 (by omega) with ⟨-, hb16, eb⟩ | hw
      swap
      · rw [ei'] at hw
        exact (kH r' _ (half_false hFA hrec hhalf hfar h6 hc) hw).elim
      obtain ⟨rc, hrc⟩ := hC (16 * r.getD 1 0 + r'.getD 1 0) (by omega)
      have hd : (16 * r.getD 1 0 + r'.getD 1 0) / 16 = r.getD 1 0 := by omega
      have hm : (16 * r.getD 1 0 + r'.getD 1 0) % 16 = r'.getD 1 0 := by omega
      rcases rowC_sound hrc with ⟨e87, e133⟩ | hw
      · rw [hd, ea, ei] at e87
        rw [hm, eb, ei'] at e133
        apply ev_eq_one
        intro x hx
        rw [hs x hx, e87, e133, ← h1 x hx]
      · rw [hd, ea, ei, hm, eb, ei'] at hw
        exact (kF rc hw).elim
  ·
    obtain ⟨r, hr⟩ := hA _ hi
    obtain ⟨hj1, hj2, hjo, hw⟩ := (rowA_sound hr).2 hiA
    rw [ei] at hj1 hj2 hjo hw
    rw [gp_ev hn hk1] at hj1 hj2 hjo hw
    have hsj := sig_rec hFA hrec hhalf hc _ (fw 13 PS (ev n (ev σ 87))) hj2 (Nat.lt_succ_self _)
    rw [hjo, hnk 87 (by norm_num),
      (sgR_half hrec hhalf (ev σ 87) (ev σ 133) _ _ hj2 (Nat.lt_succ_self _)).2 hj1] at hsj
    have hforce : fiR FAI PA LB (fw 13 PS (ev n (ev σ 87)) + 1) (fw 13 PS (ev n (ev σ 87)))
        (gp nG 87) = ev σ 133 := by
      rw [gp_ev hn (by norm_num), hsj]
      exact fiR_inv hFA hinv' hrec hkp1 _ _ hj2 (Nat.lt_succ_self _)
    rw [hforce] at hw
    exact (kF r hw).elim

end Rigid

end CFSG.KC.TitsF48Sound

end
