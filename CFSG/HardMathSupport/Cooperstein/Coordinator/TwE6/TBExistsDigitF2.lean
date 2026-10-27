module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def TwExistsDigitF2 : Prop :=
  ∀ (s : Fin Tag.F4.rank), (s.val = 0 ∨ s.val = 3) → ∀ J' : Finset ℕ,
    (∀ i ∈ J', i < twNdig 2 (twNode s)) → J'.card = 2 →
    ∃ dg ∈ J', ∀ (i i' : Fin 12), i ≠ i' → ∀ (j j' : Fin 8), ¬ ∀ c : TwN,
      ((2 ^ twNdig 2 c - 1 : ℕ) : ℤ) ∣
        twV 2 s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i j c -
          twV 2 s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i' j' c

@[expose] def twDF2Refl (f : ℕ) (a : TwN) (l : List ℤ) : List ℤ :=
  List.ofFn fun b : TwN => l.getD b 0 - twA f b a * l.getD a 0

@[expose] def twDF2V (f : ℕ) (s : Fin Tag.F4.rank) (a : ℤ) (b i j : ℕ) : List ℤ :=
  (F4Exc.gamWord s i).foldr (fun l v => twDF2Refl f (twNode l) v)
    ((F4Exc.uWord s j).foldr (fun l v => twDF2Refl f (twNode l) v)
      (List.ofFn fun c : TwN => (if c = twNode s then a else 0) - 2 ^ b * twRoot f (twNode s) c))

@[expose] def twDF2Key (l : List ℤ) : ℕ :=
  (l.getD 0 0 % 15).toNat + 15 * (l.getD 1 0 % 15).toNat + 225 * (l.getD 2 0 % 3).toNat +
    675 * (l.getD 3 0 % 3).toNat

@[expose] def twDF2Pairs (s : Fin Tag.F4.rank) (a : ℤ) (dg : ℕ) : List (ℕ × ℕ) :=
  (List.range 12).flatMap fun i => (List.range 8).map fun j => (twDF2Key (twDF2V 2 s a dg i j), i)

@[expose] def twDF2Chk (s : Fin Tag.F4.rank) (a : ℤ) (dg : ℕ) : Bool :=
  (twDF2Pairs s a dg).all fun p => (twDF2Pairs s a dg).all fun q => p.1 != q.1 || p.2 == q.2

theorem twDF2_getD_ofFn (e : TwN → ℤ) (c : TwN) : (List.ofFn e).getD c 0 = e c := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]

theorem twDF2_ofFn_twRefl (f : ℕ) (a : TwN) (e : TwN → ℤ) :
    List.ofFn (twRefl f a e) = twDF2Refl f a (List.ofFn e) := by
  unfold twDF2Refl twRefl
  refine congrArg List.ofFn (funext fun b => ?_)
  rw [twDF2_getD_ofFn, twDF2_getD_ofFn]

theorem twDF2_ofFn_foldr (f : ℕ) (w : List (Fin Tag.F4.rank)) (e : TwN → ℤ) :
    List.ofFn (w.foldr (fun l v => twRefl f (twNode l) v) e) =
      w.foldr (fun l v => twDF2Refl f (twNode l) v) (List.ofFn e) := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.foldr_cons, List.foldr_cons, twDF2_ofFn_twRefl, ih]

theorem twDF2_twAct_twWd (f : ℕ) (w : List (Fin Tag.F4.rank)) (e : TwN → ℤ) :
    twAct f (twWd w) e = w.foldr (fun l v => twRefl f (twNode l) v) e := by
  unfold twAct twWd
  rw [List.foldr_map]

theorem twDF2_ofFn_V (f : ℕ) (s : Fin Tag.F4.rank) (a : ℤ) (b i j : ℕ) :
    List.ofFn (twV f s (fun c => if c = twNode s then a else 0) b i j) = twDF2V f s a b i j := by
  unfold twV twDF2V
  rw [twDF2_twAct_twWd, twDF2_twAct_twWd, twDF2_ofFn_foldr, twDF2_ofFn_foldr]

theorem twDF2_V_getD (f : ℕ) (s : Fin Tag.F4.rank) (a : ℤ) (b i j : ℕ) (c : TwN) :
    (twDF2V f s a b i j).getD c 0 = twV f s (fun c => if c = twNode s then a else 0) b i j c := by
  rw [← twDF2_ofFn_V, twDF2_getD_ofFn]

theorem twDF2_key_eq (l l' : List ℤ)
    (h : ∀ c : TwN, ((2 ^ twNdig 2 c - 1 : ℕ) : ℤ) ∣ l.getD c 0 - l'.getD c 0) :
    twDF2Key l = twDF2Key l' := by
  have h0 : (15 : ℤ) ∣ l.getD 0 0 - l'.getD 0 0 := by
    simpa [twNdig] using h ⟨0, by decide⟩
  have h1 : (15 : ℤ) ∣ l.getD 1 0 - l'.getD 1 0 := by
    simpa [twNdig] using h ⟨1, by decide⟩
  have h2 : (3 : ℤ) ∣ l.getD 2 0 - l'.getD 2 0 := by
    simpa [twNdig] using h ⟨2, by decide⟩
  have h3 : (3 : ℤ) ∣ l.getD 3 0 - l'.getD 3 0 := by
    simpa [twNdig] using h ⟨3, by decide⟩
  unfold twDF2Key
  rw [(Int.modEq_iff_dvd.2 h0).symm, (Int.modEq_iff_dvd.2 h1).symm,
    (Int.modEq_iff_dvd.2 h2).symm, (Int.modEq_iff_dvd.2 h3).symm]

theorem twDF2_chk_sound {s : Fin Tag.F4.rank} {a : ℤ} {dg : ℕ} (h : twDF2Chk s a dg = true)
    {i i' : ℕ} (hi : i < 12) (hi' : i' < 12) (hne : i ≠ i') {j j' : ℕ} (hj : j < 8) (hj' : j' < 8) :
    twDF2Key (twDF2V 2 s a dg i j) ≠ twDF2Key (twDF2V 2 s a dg i' j') := by
  intro heq
  have hmem : ∀ i < 12, ∀ j < 8,
      (twDF2Key (twDF2V 2 s a dg i j), i) ∈ twDF2Pairs s a dg := fun i hi j hj => by
    simp only [twDF2Pairs, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨i, hi, j, hj, rfl⟩
  have := List.all_eq_true.1 (List.all_eq_true.1 h _ (hmem i hi j hj)) _ (hmem i' hi' j' hj')
  simp [heq, hne] at this

theorem twDF2_core (s : Fin Tag.F4.rank) (a : ℤ) (dg : ℕ) (h : twDF2Chk s a dg = true) :
    ∀ (i i' : Fin 12), i ≠ i' → ∀ (j j' : Fin 8), ¬ ∀ c : TwN,
      ((2 ^ twNdig 2 c - 1 : ℕ) : ℤ) ∣
        twV 2 s (fun c => if c = twNode s then a else 0) dg i j c -
          twV 2 s (fun c => if c = twNode s then a else 0) dg i' j' c := by
  intro i i' hii j j' hdiv
  refine twDF2_chk_sound h i.2 i'.2 (fun e => hii (Fin.ext e)) j.2 j'.2
    (twDF2_key_eq _ _ fun c => ?_)
  rw [twDF2_V_getD, twDF2_V_getD]
  exact hdiv c

theorem twDF2_chk0 : ∀ x < 2, ∀ y < 2, x < y →
    twDF2Chk (F4Exc.f4n 0) ((2 ^ x + 2 ^ y : ℕ) : ℤ) x = true := by
  decide +kernel

theorem twDF2_chk3 : ∀ x < 4, ∀ y < 4, x < y →
    twDF2Chk (F4Exc.f4n 3) ((2 ^ x + 2 ^ y : ℕ) : ℤ) x = true := by
  decide +kernel

theorem twDF2_pair (n : ℕ) (Q : ℕ → ℕ → Prop) (H : ∀ x y, x < y → y < n → Q (2 ^ x + 2 ^ y) x)
    (J' : Finset ℕ) (hJ' : ∀ i ∈ J', i < n) (hc : J'.card = 2) :
    ∃ dg ∈ J', Q (∑ b ∈ J', 2 ^ b) dg := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hc
  have hx : x < n := hJ' x (by simp)
  have hy : y < n := hJ' y (by simp)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, by simp, by rw [Finset.sum_pair hxy]; exact H x y h hy⟩
  · exact ⟨y, by simp, by rw [Finset.pair_comm, Finset.sum_pair hxy.symm]; exact H y x h hx⟩

theorem twDF2_end (s : Fin Tag.F4.rank) (n : ℕ) (hn : twNdig 2 (twNode s) = n)
    (H : ∀ x y, x < y → y < n → twDF2Chk s ((2 ^ x + 2 ^ y : ℕ) : ℤ) x = true) (J' : Finset ℕ)
    (hJ' : ∀ i ∈ J', i < twNdig 2 (twNode s)) (hc : J'.card = 2) :
    ∃ dg ∈ J', ∀ (i i' : Fin 12), i ≠ i' → ∀ (j j' : Fin 8), ¬ ∀ c : TwN,
      ((2 ^ twNdig 2 c - 1 : ℕ) : ℤ) ∣
        twV 2 s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i j c -
          twV 2 s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i' j'
            c := by
  rw [hn] at hJ'
  obtain ⟨dg, hdg, hQ⟩ := twDF2_pair n (fun a dg => twDF2Chk s (a : ℤ) dg = true) H J' hJ' hc
  exact ⟨dg, hdg, twDF2_core s _ dg hQ⟩

theorem twExistsDigitF2_holds : TwExistsDigitF2 := by
  intro s hs J' hJ' hcard
  rcases hs with hs | hs
  · have hs0 : s = F4Exc.f4n 0 := Fin.ext hs
    refine twDF2_end s 2 (by rw [hs0]; decide) (fun x y hxy hy => ?_) J' hJ' hcard
    rw [hs0]
    exact twDF2_chk0 x (by omega) y hy hxy
  · have hs3 : s = F4Exc.f4n 3 := Fin.ext hs
    refine twDF2_end s 4 (by rw [hs3]; decide) (fun x y hxy hy => ?_) J' hJ' hcard
    rw [hs3]
    exact twDF2_chk3 x (by omega) y hy hxy

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
