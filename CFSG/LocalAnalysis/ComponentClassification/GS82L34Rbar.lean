module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutionsBase

public section

namespace CFSG.ComponentClassification.PSL3Four

open Subgroup CFSG.PSL3Four.Native

namespace RbarCore

@[expose] def incMask : Array ℕ :=
  #[293202821120, 1008730112, 2269965713408, 1142561964032, 691573620736, 65011712,
    586401447936, 2345593208832, 1172798701568, 16108224512, 1238166929408, 620119457792,
    2234741948416, 4123170701312, 352338313216, 314077872128, 414766333952, 257700134912,
    2220665864192, 1119392628736, 575802441728, 139810, 481, 1082404,
    544816, 329768, 31, 279618, 1118466, 559234,
    7681, 590404, 295696, 1065608, 1966081, 168008,
    149764, 197776, 122881, 1058896, 533768, 274564]

@[expose] def repT : Array ℕ :=
  #[0, 0, 0, 3, 3, 0, 0, 3, 3, 0, 0, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 21, 21, 21, 24, 24, 21, 21,
    24, 24, 21, 21, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24]

@[expose] def wordT : Array (List Bool) :=
  #[[], [false, false], [false, false, true, false], [],
    [false, false, true, false], [false], [false, false, true, false, false], [false, false, true, false, false],
    [false], [false, false, true], [false, false, true, false, true], [true],
    [false, false, true, false, true], [false, false], [true, false, false], [true, false, true],
    [true, false, true, false, true], [false, false, true], [true, false, true, false], [true, false, false, true],
    [true, false], [], [false, false], [false, true, false],
    [], [false, false, true, false], [false], [false, true, false, false],
    [false, false, true, false, false], [false], [false, true], [false, true, false, false, true],
    [false, false, true, false, false, true], [false, true], [false, false], [false, true, false, false, true],
    [false, true, false], [false, false, true, false, false, true, false, true], [false, false, true], [false, true, false, false],
    [false, true, false, true], [false, false, true, false, false, true, false]]


@[expose] def incN (x y : ℕ) : Bool := Nat.testBit incMask[x]! y

@[expose] def presInc (t : Tab) : Bool :=
  (List.range 42).all fun x => (List.range 42).all fun y => incN t[x]! t[y]! == incN x y

@[expose] def applyW (w : List Bool) (a : ℕ) : ℕ :=
  w.foldl (fun a j => (if j then g₂T else g₁T)[a]!) a

@[expose] def orbT (r : ℕ) : List ℕ :=
  if r = 0 then [0, 1, 2, 5, 6, 9, 10]
  else if r = 3 then [3, 4, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
  else if r = 21 then [21, 22, 23, 26, 27, 30, 31]
  else [24, 25, 28, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]

@[expose] def ok (r a : ℕ) : Bool := (orbT r).all fun y =>
  applyW wordT[g₁T[y]!]! a == g₁T[applyW wordT[y]! a]! &&
    applyW wordT[g₂T[y]!]! a == g₂T[applyW wordT[y]! a]!

theorem presInc_g₁ : presInc g₁T = true := by decide
theorem presInc_g₂ : presInc g₂T = true := by decide
theorem presInc_g₃ : presInc g₃T = true := by decide
theorem presInc_g₄ : presInc g₄T = true := by decide
theorem presInc_g₅ : presInc g₅T = true := by decide
theorem presInc_g₆ : presInc g₆T = true := by decide

theorem presInc_spec {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g)
    (h : presInc t = true) (x y : Fin 42) : incN (g x) (g y) = incN x y := by
  unfold presInc at h
  rw [List.all_eq_true] at h
  have h' := h x (List.mem_range.2 x.2)
  rw [List.all_eq_true] at h'
  have h'' := h' y (List.mem_range.2 y.2)
  rw [ht.apply x, ht.apply y] at h''
  exact beq_iff_eq.1 h''

theorem R_presInc {σ : Equiv.Perm (Fin 42)} (hσ : σ ∈ R) (x y : Fin 42) :
    incN (σ x) (σ y) = incN x y := by
  induction hσ using Subgroup.closure_induction generalizing x y with
  | mem s hs =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact presInc_spec tabRep_g₁ presInc_g₁ x y
    · exact presInc_spec tabRep_g₂ presInc_g₂ x y
    · exact presInc_spec tabRep_g₃ presInc_g₃ x y
    · exact presInc_spec tabRep_g₄ presInc_g₄ x y
    · exact presInc_spec tabRep_g₅ presInc_g₅ x y
    · exact presInc_spec tabRep_g₆ presInc_g₆ x y
  | one => rfl
  | mul a b _ _ ha hb =>
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha, hb]
  | inv a _ ha =>
    rw [← ha (a⁻¹ x) (a⁻¹ y)]
    simp

theorem g₁_mem_C₂ : g₁ ∈ C₂ := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, g₁_mem_S⟩
  exact ((tabRep_g₁.comp tabRep_g₅).eq_iff (tabRep_g₅.comp tabRep_g₁)).1 (by decide)

theorem g₂_mem_C₂ : g₂ ∈ C₂ := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, g₂_mem_S⟩
  exact ((tabRep_g₂.comp tabRep_g₅).eq_iff (tabRep_g₅.comp tabRep_g₂)).1 (by decide)

theorem applyW_wordT : ∀ y < 42, applyW wordT[y]! repT[y]! = y := by decide

theorem applyW_wordT_g₅ : ∀ y < 42, applyW wordT[y]! g₅T[repT[y]!]! = g₅T[y]! := by decide

theorem repT_cases : ∀ y < 42, repT[y]! = 0 ∨ repT[y]! = 3 ∨ repT[y]! = 21 ∨ repT[y]! = 24 := by
  decide

theorem orbT_facts : ∀ r ∈ [0, 3, 21, 24], ∀ y ∈ orbT r,
    y < 42 ∧ repT[y]! = r ∧ repT[g₁T[y]!]! = r ∧ repT[g₂T[y]!]! = r := by decide

theorem ok_0 : ∀ a < 42, ok 0 a = true → a = 0 := by decide
theorem ok_3 : ∀ a < 42, ok 3 a = true → a = 3 ∨ a = 4 ∨ a = 26 := by decide
theorem ok_21 : ∀ a < 42, ok 21 a = true → a = 21 := by decide
theorem ok_24 : ∀ a < 42, ok 24 a = true → a = 5 ∨ a = 24 ∨ a = 25 := by decide

theorem inc_key : ∀ b ∈ [3, 4, 26], ∀ d ∈ [5, 24, 25],
    incN 0 (applyW wordT[34]! d) = incN 0 34 → incN b d = incN 3 24 → incN 0 b = incN 0 3 →
      (b = 3 ∧ d = 24) ∨ (b = 4 ∧ d = 25) := by decide

theorem comm_tab {ρ g : Equiv.Perm (Fin 42)} {t : Tab} (ht : TabRep t g)
    (hc : ∀ x, ρ (g x) = g (ρ x)) (f : ℕ → ℕ)
    (hf : ∀ x : Fin 42, f x = ρ x) (n : ℕ) (hn : n < 42) :
    f t[n]! = t[f n]! ∧ t[n]! < 42 := by
  have e := ht.apply ⟨n, hn⟩
  have e' := ht.apply (ρ ⟨n, hn⟩)
  have hfn : f n = ρ ⟨n, hn⟩ := hf ⟨n, hn⟩
  simp only at e
  refine ⟨?_, by rw [e]; exact (g ⟨n, hn⟩).2⟩
  rw [e, hf, hc, hfn, e']

end RbarCore

open RbarCore in
theorem centralizer_C₂_inf_R (ρ : Equiv.Perm (Fin 42)) (hρ : ρ ∈ R)
    (hc : ∀ s ∈ C₂, ρ * s = s * ρ) : ρ = 1 ∨ ρ = r₂ := by
  have h1 : ∀ x, ρ (g₁ x) = g₁ (ρ x) := fun x => by
    have := congrArg (fun p : Equiv.Perm (Fin 42) => p x) (hc g₁ g₁_mem_C₂)
    simpa only [Equiv.Perm.mul_apply] using this
  have h2 : ∀ x, ρ (g₂ x) = g₂ (ρ x) := fun x => by
    have := congrArg (fun p : Equiv.Perm (Fin 42) => p x) (hc g₂ g₂_mem_C₂)
    simpa only [Equiv.Perm.mul_apply] using this
  let f : ℕ → ℕ := fun n => if h : n < 42 then (ρ ⟨n, h⟩ : ℕ) else 0
  have hf : ∀ x : Fin 42, f x = ρ x := fun x => by simp [f, x.2]
  have hflt : ∀ n, n < 42 → f n < 42 := fun n hn => by
    rw [show n = ((⟨n, hn⟩ : Fin 42) : ℕ) from rfl, hf]
    exact (ρ _).2
  have hW : ∀ w n, n < 42 → f (applyW w n) = applyW w (f n) ∧ applyW w n < 42 := by
    intro w
    induction w with
    | nil => intro n hn; exact ⟨rfl, hn⟩
    | cons j w ih =>
      intro n hn
      cases j
      · obtain ⟨e, hl⟩ := comm_tab tabRep_g₁ h1 f hf n hn
        have := ih _ hl
        simp only [applyW, List.foldl_cons, Bool.false_eq_true, ↓reduceIte] at this ⊢
        rw [this.1, e]
        exact ⟨rfl, this.2⟩
      · obtain ⟨e, hl⟩ := comm_tab tabRep_g₂ h2 f hf n hn
        have := ih _ hl
        simp only [applyW, List.foldl_cons, ↓reduceIte] at this ⊢
        rw [this.1, e]
        exact ⟨rfl, this.2⟩
  have hkey : ∀ y < 42, f y = applyW wordT[y]! (f repT[y]!) := by
    intro y hy
    have hr : repT[y]! < 42 := by
      rcases repT_cases y hy with h | h | h | h <;> rw [h] <;> norm_num
    conv_lhs => rw [← applyW_wordT y hy]
    exact (hW _ _ hr).1
  have hok : ∀ r ∈ [0, 3, 21, 24], ok r (f r) = true := by
    intro r hr
    unfold ok
    rw [List.all_eq_true]
    intro y hy
    obtain ⟨hy42, hry, hr1, hr2⟩ := orbT_facts r hr y hy
    obtain ⟨e1, l1⟩ := comm_tab tabRep_g₁ h1 f hf y hy42
    obtain ⟨e2, l2⟩ := comm_tab tabRep_g₂ h2 f hf y hy42
    have k1 := hkey _ l1
    have k2 := hkey _ l2
    have ky := hkey _ hy42
    rw [hr1] at k1
    rw [hr2] at k2
    rw [hry] at ky
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ← k1, ← k2, ← ky, e1, e2]
    exact ⟨rfl, rfl⟩
  have f0 := ok_0 _ (hflt 0 (by norm_num)) (hok 0 (by simp))
  have f21 := ok_21 _ (hflt 21 (by norm_num)) (hok 21 (by simp))
  have f3 := ok_3 _ (hflt 3 (by norm_num)) (hok 3 (by simp))
  have f24 := ok_24 _ (hflt 24 (by norm_num)) (hok 24 (by simp))
  have hinc : ∀ x y, x < 42 → y < 42 → incN (f x) (f y) = incN x y := by
    intro x y hx hy
    have := R_presInc hρ ⟨x, hx⟩ ⟨y, hy⟩
    rwa [← hf, ← hf] at this
  have f34 : f 34 = applyW wordT[34]! (f 24) := hkey 34 (by norm_num)
  have i1 := hinc 0 34 (by norm_num) (by norm_num)
  have i2 := hinc 3 24 (by norm_num) (by norm_num)
  have i3 := hinc 0 3 (by norm_num) (by norm_num)
  rw [f0, f34] at i1
  rw [f0] at i3
  have hb : f 3 ∈ [3, 4, 26] := by simpa using f3
  have hd : f 24 ∈ [5, 24, 25] := by simpa using f24
  rcases inc_key _ hb _ hd i1 i2 i3 with ⟨e3, e24⟩ | ⟨e3, e24⟩
  · left
    apply Equiv.ext
    intro x
    apply Fin.ext
    rw [← hf, hkey x x.2, Equiv.Perm.one_apply]
    have hr : f repT[x.val]! = repT[x.val]! := by
      rcases repT_cases x x.2 with h | h | h | h <;> rw [h] <;> assumption
    rw [hr, applyW_wordT x x.2]
  · right
    apply Equiv.ext
    intro x
    apply Fin.ext
    rw [← hf, hkey x x.2, r₂, ← tabRep_g₅.apply x]
    have hr : f repT[x.val]! = g₅T[repT[x.val]!]! := by
      rcases repT_cases x x.2 with h | h | h | h <;> rw [h]
      · rw [f0]; decide
      · rw [e3]; decide
      · rw [f21]; decide
      · rw [e24]; decide
    rw [hr, applyW_wordT_g₅ x x.2]

end CFSG.ComponentClassification.PSL3Four
