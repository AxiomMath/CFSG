module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineGreedy
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermCode
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineBasis

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporLine

open CFSG.QuasithinUnique.A5.Kc3SporPerm

theorem el_get (f : ℕ → ℕ) {a : ℕ} (ha : a < 16) : ((List.range 16).map f).toArray[a]! = f a := by
  simp [ha]

theorem nodup_pairsL : pairsL.Nodup := by decide +kernel

theorem mem_pairsL {p : ℕ × ℕ} : p ∈ pairsL ↔ p ∈ pairs4 := by
  rw [mem_pairs4]
  simp only [pairsL, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, ⟨h1, h2⟩, h3⟩
    exact ⟨⟨ha, hb⟩, h1, h2, h3⟩
  · rintro ⟨⟨ha, hb⟩, h1, h2, h3⟩
    exact ⟨⟨p.1, ha, p.2, hb, rfl⟩, ⟨h1, h2⟩, h3⟩

theorem count_pairsL (F : ℕ → ℕ → ℕ) (v : ℕ) :
    (pairsL.map fun p => F p.1 p.2).count v = (pairs4.filter fun p => F p.1 p.2 = v).card := by
  have h1 : (pairsL.map fun p => F p.1 p.2).count v =
      (pairsL.filter fun p => F p.1 p.2 = v).length := by
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    rfl
  rw [h1]
  have h2 : (pairsL.filter fun p => F p.1 p.2 = v).Nodup := nodup_pairsL.filter _
  rw [← List.toFinset_card_of_nodup h2]
  congr 1
  ext p
  simp [mem_pairsL]

theorem okSize_iff {c : ℕ} : okSize c = true ↔ AllowedFibre c := by
  simp [okSize, AllowedFibre, or_assoc]

@[expose] def elArr (pr : ℕ → ℕ → ℕ) (i j k l : ℕ) : Array ℕ :=
  ((List.range 16).map (elF pr i j k l)).toArray

@[expose] def valsOf (pr ct : ℕ → ℕ → ℕ) (i j k l : ℕ) : List ℕ :=
  pairsL.map fun p => ct (elArr pr i j k l)[p.1]! (elArr pr i j k l)[p.2]!

theorem leafBad_eq (pr ct : ℕ → ℕ → ℕ) (i j k l : ℕ) :
    leafBad pr ct i j k l =
      !(okSize ((valsOf pr ct i j k l).count (witness (valsOf pr ct i j k l)))) := rfl

theorem leafBad_spec {pr ct : ℕ → ℕ → ℕ} {i j k l : ℕ} (h : leafBad pr ct i j k l = true)
    (F : ℕ → ℕ → ℕ)
    (hF : ∀ a b, 1 ≤ a → a < 16 → 1 ≤ b → b < 16 → a ≠ b →
      ct (elF pr i j k l a) (elF pr i j k l b) = F a b) :
    ∃ v : ℕ, ¬ AllowedFibre (pairs4.filter fun p => F p.1 p.2 = v).card := by
  rw [leafBad_eq] at h
  have hvals : valsOf pr ct i j k l = pairsL.map fun p => F p.1 p.2 := by
    unfold valsOf
    apply List.map_congr_left
    intro p hp
    have hp4 := mem_pairs4.1 (mem_pairsL.1 hp)
    unfold elArr
    rw [el_get _ hp4.1.1, el_get _ hp4.1.2]
    exact hF p.1 p.2 hp4.2.1 hp4.1.1 hp4.2.2.1 hp4.1.2 hp4.2.2.2
  rw [hvals] at h
  refine ⟨witness (pairsL.map fun p => F p.1 p.2), fun hallow => ?_⟩
  rw [← count_pairsL, ← okSize_iff] at hallow
  rw [hallow] at h
  exact absurd h (by simp)

theorem elF_eq {pr : ℕ → ℕ → ℕ} {n : ℕ → ℕ}
    (hp : ∀ a b, 1 ≤ a → a < 16 → 1 ≤ b → b < 16 → a ≠ b → pr (n a) (n b) = n (a ^^^ b))
    {a : ℕ} (ha1 : 1 ≤ a) (ha : a < 16) : elF pr (n 1) (n 2) (n 4) (n 8) a = n a := by
  have h : ∀ a b c : ℕ, (1 ≤ a ∧ a < 16 ∧ 1 ≤ b ∧ b < 16 ∧ a ≠ b ∧ a ^^^ b = c) →
      pr (n a) (n b) = n c := by
    rintro a b c ⟨ha1, ha, hb1, hb, hne, hc⟩
    rw [hp a b ha1 ha hb1 hb hne, hc]
  have h3 : pr (n 1) (n 2) = n 3 := h 1 2 3 (by decide)
  have h5 : pr (n 1) (n 4) = n 5 := h 1 4 5 (by decide)
  have h6 : pr (n 2) (n 4) = n 6 := h 2 4 6 (by decide)
  have h7 : pr (n 3) (n 4) = n 7 := h 3 4 7 (by decide)
  have h9 : pr (n 1) (n 8) = n 9 := h 1 8 9 (by decide)
  have h10 : pr (n 2) (n 8) = n 10 := h 2 8 10 (by decide)
  have h11 : pr (n 3) (n 8) = n 11 := h 3 8 11 (by decide)
  have h12 : pr (n 4) (n 8) = n 12 := h 4 8 12 (by decide)
  have h13 : pr (n 5) (n 8) = n 13 := h 5 8 13 (by decide)
  have h14 : pr (n 6) (n 8) = n 14 := h 6 8 14 (by decide)
  have h15 : pr (n 7) (n 8) = n 15 := h 7 8 15 (by decide)
  interval_cases a <;> simp [elF, h3, h5, h6, h7, h9, h10, h11, h12, h13, h14, h15]

section Sound

variable {Γ : Type} [Group Γ] [Finite Γ] (X : Type) [MulAction Γ X] [Fintype X] [DecidableEq X]

theorem hall_of_dfs_of_specs {R : Subgroup Γ} (M : ℕ) (elt : ℕ → Γ) (pr ct : ℕ → ℕ → ℕ)
    (nbr : ℕ → List ℕ)
    (hlist : ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∃ k < M, elt k = x)
    (hinj : ∀ k < M, ∀ k' < M, elt k = elt k' → k = k')
    (hpr : ∀ i < M, ∀ j < M, i ≠ j → elt i * elt j = elt j * elt i →
      pr i j < M ∧ elt (pr i j) = elt i * elt j)
    (hnbr : ∀ i < M, ∀ j < M, i ≠ j → elt i * elt j = elt j * elt i → j ∈ nbr i)
    (hct : ∀ i < M, ∀ j < M, i ≠ j → pr i j < M → ct i j = fixc X (elt i) (elt j))
    (h : dfsB M pr ct nbr = true) :
    ∀ E : Subgroup Γ, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E = 16 → ¬ PairFibersAllowed X E := by
  classical
  intro E hER hcomm hsq hcard
  let num : Γ → ℕ := fun x => if hx : ∃ k, k < M ∧ elt k = x then hx.choose else M
  have hnum : ∀ x ∈ E, x ≠ 1 → num x < M ∧ elt (num x) = x := by
    intro x hx hx1
    have hex : ∃ k, k < M ∧ elt k = x := by
      obtain ⟨k, hk, hkx⟩ := hlist x (hER hx) (hsq x hx) hx1
      exact ⟨k, hk, hkx⟩
    have hnx : num x = hex.choose := by simp [num, hex]
    rw [hnx]
    exact hex.choose_spec
  have hnumE : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 → num x = num y → x = y := by
    intro x hx hx1 y hy hy1 hxy
    calc x = elt (num x) := ((hnum x hx hx1).2).symm
      _ = elt (num y) := by rw [hxy]
      _ = y := (hnum y hy hy1).2
  obtain ⟨g, hgE, hEg, hgreedy⟩ := exists_greedy hcomm hsq hcard num hnumE
  have hsq' : ∀ t, g t * g t = 1 := fun t => hsq _ (hgE t)
  have hc' : ∀ s t, g s * g t = g t * g s := fun s t => hcomm _ (hgE s) _ (hgE t)
  have hcard' : Nat.card (E4 g) = 16 := by rw [hEg]; exact hcard
  have hinjL := gE_inj g hsq' hc' hcard'
  have hmemL : ∀ a, gE g a ∈ E := fun a => hEg ▸ gE_mem g a
  have hne1 : ∀ a, 1 ≤ a → a < 16 → gE g a ≠ 1 := by
    intro a ha1 ha h1
    have := hinjL a ha 0 (by norm_num) (by rw [h1, gE_zero])
    omega
  have hcommL : ∀ a b, gE g a * gE g b = gE g b * gE g a := fun a b =>
    hcomm _ (hmemL a) _ (hmemL b)
  have hnL : ∀ a, 1 ≤ a → a < 16 → num (gE g a) < M ∧ elt (num (gE g a)) = gE g a :=
    fun a ha1 ha => hnum _ (hmemL a) (hne1 a ha1 ha)
  have hnL_ne : ∀ a b, 1 ≤ a → a < 16 → 1 ≤ b → b < 16 → a ≠ b →
      num (gE g a) ≠ num (gE g b) := by
    intro a b ha1 ha hb1 hb hab hn
    apply hab
    apply hinjL a ha b hb
    calc gE g a = elt (num (gE g a)) := ((hnL a ha1 ha).2).symm
      _ = elt (num (gE g b)) := by rw [hn]
      _ = gE g b := (hnL b hb1 hb).2
  have hcmL : ∀ a b, 1 ≤ a → a < 16 → 1 ≤ b → b < 16 →
      elt (num (gE g a)) * elt (num (gE g b)) = elt (num (gE g b)) * elt (num (gE g a)) := by
    intro a b ha1 ha hb1 hb
    rw [(hnL a ha1 ha).2, (hnL b hb1 hb).2]
    exact hcommL a b
  have hprL : ∀ a b, 1 ≤ a → a < 16 → 1 ≤ b → b < 16 → a ≠ b →
      pr (num (gE g a)) (num (gE g b)) < M ∧
        pr (num (gE g a)) (num (gE g b)) = num (gE g (a ^^^ b)) := by
    intro a b ha1 ha hb1 hb hab
    obtain ⟨hia, hea⟩ := hnL a ha1 ha
    obtain ⟨hib, heb⟩ := hnL b hb1 hb
    obtain ⟨hlt, hel⟩ := hpr _ hia _ hib (hnL_ne a b ha1 ha hb1 hb hab) (hcmL a b ha1 ha hb1 hb)
    have hc1 : 1 ≤ a ^^^ b := Nat.pos_of_ne_zero fun h0 => hab (Nat.eq_of_xor_eq_zero h0)
    obtain ⟨hic, hec⟩ := hnL (a ^^^ b) hc1 (xor_lt_16 ha hb)
    refine ⟨hlt, hinj _ hlt _ hic ?_⟩
    rw [hel, hea, heb, ← gE_xor g hsq' hc', hec]
  have hctL : ∀ a b, 1 ≤ a → a < 16 → 1 ≤ b → b < 16 → a ≠ b →
      ct (num (gE g a)) (num (gE g b)) = fixc X (gE g a) (gE g b) := by
    intro a b ha1 ha hb1 hb hab
    have := hct _ (hnL a ha1 ha).1 _ (hnL b hb1 hb).1 (hnL_ne a b ha1 ha hb1 hb hab)
      (hprL a b ha1 ha hb1 hb hab).1
    rw [this, (hnL a ha1 ha).2, (hnL b hb1 hb).2]
  have hel : ∀ a, 1 ≤ a → a < 16 →
      elF pr (num (gE g 1)) (num (gE g 2)) (num (gE g 4)) (num (gE g 8)) a = num (gE g a) :=
    fun a ha1 ha => elF_eq (n := fun a => num (gE g a))
      (fun a b ha1 ha hb1 hb hab => (hprL a b ha1 ha hb1 hb hab).2) ha1 ha
  have hP : ∀ a b c : ℕ, (1 ≤ a ∧ a < 16 ∧ 1 ≤ b ∧ b < 16 ∧ a ≠ b ∧ a ^^^ b = c) →
      pr (num (gE g a)) (num (gE g b)) = num (gE g c) := by
    rintro a b c ⟨ha1, ha, hb1, hb, hab, hc⟩
    rw [(hprL a b ha1 ha hb1 hb hab).2, hc]
  have e3 : pr (num (gE g 1)) (num (gE g 2)) = num (gE g 3) := hP 1 2 3 (by decide)
  have e5 : pr (num (gE g 1)) (num (gE g 4)) = num (gE g 5) := hP 1 4 5 (by decide)
  have e6 : pr (num (gE g 2)) (num (gE g 4)) = num (gE g 6) := hP 2 4 6 (by decide)
  have e7 : pr (num (gE g 3)) (num (gE g 4)) = num (gE g 7) := hP 3 4 7 (by decide)
  have e9 : pr (num (gE g 1)) (num (gE g 8)) = num (gE g 9) := hP 1 8 9 (by decide)
  have e10 : pr (num (gE g 2)) (num (gE g 8)) = num (gE g 10) := hP 2 8 10 (by decide)
  have e11 : pr (num (gE g 3)) (num (gE g 8)) = num (gE g 11) := hP 3 8 11 (by decide)
  have e12 : pr (num (gE g 4)) (num (gE g 8)) = num (gE g 12) := hP 4 8 12 (by decide)
  have e13 : pr (num (gE g 5)) (num (gE g 8)) = num (gE g 13) := hP 5 8 13 (by decide)
  have e14 : pr (num (gE g 6)) (num (gE g 8)) = num (gE g 14) := hP 6 8 14 (by decide)
  have e15 : pr (num (gE g 7)) (num (gE g 8)) = num (gE g 15) := hP 7 8 15 (by decide)
  have lt3 := (hnL 3 (by norm_num) (by norm_num)).1
  have lt5 := (hnL 5 (by norm_num) (by norm_num)).1
  have lt6 := (hnL 6 (by norm_num) (by norm_num)).1
  have lt7 := (hnL 7 (by norm_num) (by norm_num)).1
  have lt9 := (hnL 9 (by norm_num) (by norm_num)).1
  have lt10 := (hnL 10 (by norm_num) (by norm_num)).1
  have lt11 := (hnL 11 (by norm_num) (by norm_num)).1
  have lt12 := (hnL 12 (by norm_num) (by norm_num)).1
  have lt13 := (hnL 13 (by norm_num) (by norm_num)).1
  have lt14 := (hnL 14 (by norm_num) (by norm_num)).1
  have lt15 := (hnL 15 (by norm_num) (by norm_num)).1
  have hG : ∀ a q : ℕ, (a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8) → q < 16 → a < q →
      num (gE g a) < num (gE g q) := by
    intro a q ha hq haq
    rcases ha with rfl | rfl | rfl | rfl
    · simpa using hgreedy 0 (by norm_num) q hq (by simpa using haq)
    · simpa using hgreedy 1 (by norm_num) q hq (by simpa using haq)
    · simpa using hgreedy 2 (by norm_num) q hq (by simpa using haq)
    · simpa using hgreedy 3 (by norm_num) q hq (by simpa using haq)
  have g12 := hG 1 2 (by decide) (by norm_num) (by norm_num)
  have g23 := hG 2 3 (by decide) (by norm_num) (by norm_num)
  have g24 := hG 2 4 (by decide) (by norm_num) (by norm_num)
  have g45 := hG 4 5 (by decide) (by norm_num) (by norm_num)
  have g46 := hG 4 6 (by decide) (by norm_num) (by norm_num)
  have g47 := hG 4 7 (by decide) (by norm_num) (by norm_num)
  have g48 := hG 4 8 (by decide) (by norm_num) (by norm_num)
  have g89 := hG 8 9 (by decide) (by norm_num) (by norm_num)
  have g810 := hG 8 10 (by decide) (by norm_num) (by norm_num)
  have g811 := hG 8 11 (by decide) (by norm_num) (by norm_num)
  have g812 := hG 8 12 (by decide) (by norm_num) (by norm_num)
  have g813 := hG 8 13 (by decide) (by norm_num) (by norm_num)
  have g814 := hG 8 14 (by decide) (by norm_num) (by norm_num)
  have g815 := hG 8 15 (by decide) (by norm_num) (by norm_num)
  have hdfs := h
  simp only [dfsB, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hdfs
  have hi : num (gE g 1) < M := (hnL 1 (by norm_num) (by norm_num)).1
  have hj : num (gE g 2) < M := (hnL 2 (by norm_num) (by norm_num)).1
  have hk : num (gE g 4) < M := (hnL 4 (by norm_num) (by norm_num)).1
  have hl : num (gE g 8) < M := (hnL 8 (by norm_num) (by norm_num)).1
  have s1 := hdfs _ hi
  have s2 := s1 (num (gE g 2)) (hnbr _ hi _ hj (hnL_ne 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)) (hcmL 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)))
  have t2 : g2 M pr (num (gE g 1)) (num (gE g 2)) = true := by
    simp only [g2, Bool.and_eq_true, decide_eq_true_eq]
    rw [e3]
    exact ⟨⟨g12, lt3⟩, g23⟩
  rcases s2 with s2 | s2
  · rw [t2] at s2
    exact absurd s2 (by simp)
  have s3 := s2 (num (gE g 4)) (hnbr _ hi _ hk (hnL_ne 1 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)) (hcmL 1 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)))
  have t3 : g3 M pr (num (gE g 1)) (num (gE g 2)) (num (gE g 4)) = true := by
    simp only [g3, Bool.and_eq_true, decide_eq_true_eq]
    rw [e3, e5, e6, e7]
    exact ⟨⟨⟨⟨⟨⟨g24, lt5⟩, lt6⟩, lt7⟩, g45⟩, g46⟩, g47⟩
  rcases s3 with s3 | s3
  · rw [t3] at s3
    exact absurd s3 (by simp)
  have s4 := s3 (num (gE g 8)) (hnbr _ hi _ hl (hnL_ne 1 8 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)) (hcmL 1 8 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)))
  have t4 : g4 M pr (num (gE g 1)) (num (gE g 2)) (num (gE g 4)) (num (gE g 8)) = true := by
    simp only [g4, Bool.and_eq_true, decide_eq_true_eq]
    rw [e3, e5, e6, e7, e9, e10, e11, e12, e13, e14, e15]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g48, lt9⟩, lt10⟩, lt11⟩, lt12⟩, lt13⟩, lt14⟩, lt15⟩, g89⟩, g810⟩,
      g811⟩, g812⟩, g813⟩, g814⟩, g815⟩
  rcases s4 with s4 | s4
  · rw [t4] at s4
    exact absurd s4 (by simp)
  obtain ⟨v, hv⟩ := leafBad_spec s4 (fun a b => fixc X (gE g a) (gE g b))
    (fun a b ha1 ha hb1 hb hab => by
      rw [hel a ha1 ha, hel b hb1 hb]
      exact hctL a b ha1 ha hb1 hb hab)
  have := not_pairFibersAllowed_of_basis g X hsq' hc' hcard' v hv
  rwa [hEg] at this

end Sound

end CFSG.QuasithinUnique.A5.Kc3SporLine
