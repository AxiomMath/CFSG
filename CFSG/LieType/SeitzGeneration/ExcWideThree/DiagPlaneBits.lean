module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.RootChecks

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcHighThree

@[expose] def allVecs : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range 3).flatMap fun c => (allVecs n).map (c :: ·)

theorem mem_allVecs : ∀ (n : ℕ) (v : List ℕ), v.length = n → (∀ x ∈ v, x < 3) → v ∈ allVecs n
  | 0, v, hl, _ => by
    rw [List.eq_nil_of_length_eq_zero hl, allVecs]
    simp
  | n + 1, [], hl, _ => by simp at hl
  | n + 1, c :: t, hl, hv => by
    have htl : t.length = n := by simpa using hl
    have hc : c < 3 := hv c (by simp)
    have ht : ∀ x ∈ t, x < 3 := fun x hx => hv x (by simp [hx])
    rw [allVecs, List.mem_flatMap]
    exact ⟨c, List.mem_range.2 hc, List.mem_map.2 ⟨t, mem_allVecs n t htl ht, rfl⟩⟩

@[expose] def comb (a b : ℕ) (k₁ k₂ : List ℕ) : List ℕ :=
  List.zipWith (fun x y => (a * x + b * y) % 3) k₁ k₂

theorem length_comb {a b : ℕ} {k₁ k₂ : List ℕ} (h : k₁.length = k₂.length) :
    (comb a b k₁ k₂).length = k₁.length := by
  unfold comb
  rw [List.length_zipWith, h, min_self]

theorem comb_lt {a b : ℕ} {k₁ k₂ : List ℕ} : ∀ x ∈ comb a b k₁ k₂, x < 3 := by
  induction k₁ generalizing k₂ with
  | nil => intro x hx; simp [comb] at hx
  | cons p ps ih =>
    cases k₂ with
    | nil => intro x hx; simp [comb] at hx
    | cons q qs =>
      intro z hz
      have hz' : z ∈ (a * p + b * q) % 3 :: comb a b ps qs := hz
      rcases List.mem_cons.1 hz' with rfl | hz''
      · exact Nat.mod_lt _ (by norm_num)
      · exact ih z hz''

theorem digitPair_eq {c d r r' W : ℕ} (hW : 0 < W) (hr : r < W) (hr' : r' < W)
    (h : c * W + r = d * W + r') : c = d ∧ r = r' := by
  have h1 : (r + c * W) / W = c := by
    rw [Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hr, zero_add]
  have h2 : (r' + d * W) / W = d := by
    rw [Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hr', zero_add]
  have hcd : c = d := by
    calc c = (r + c * W) / W := h1.symm
      _ = (r' + d * W) / W := by rw [Nat.add_comm r, Nat.add_comm r', h]
      _ = d := h2
  refine ⟨hcd, ?_⟩
  rw [hcd] at h
  exact Nat.add_left_cancel h

theorem vecIdx_injective : ∀ (v u : List ℕ), v.length = u.length → (∀ x ∈ v, x < 3) →
    (∀ x ∈ u, x < 3) → vecIdx v = vecIdx u → v = u
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | c :: t, d :: s, hl, hv, hu, h => by
    have hlen : t.length = s.length := by simpa using hl
    have ht : ∀ x ∈ t, x < 3 := fun x hx => hv x (by simp [hx])
    have hs : ∀ x ∈ s, x < 3 := fun x hx => hu x (by simp [hx])
    have hr : vecIdx t < 3 ^ t.length := vecIdx_lt t ht
    have hr' : vecIdx s < 3 ^ t.length := by rw [hlen]; exact vecIdx_lt s hs
    have hW : 0 < 3 ^ t.length := by positivity
    have hvc : vecIdx (c :: t) = c * 3 ^ t.length + vecIdx t := rfl
    have hvd : vecIdx (d :: s) = d * 3 ^ t.length + vecIdx s := by
      rw [show vecIdx (d :: s) = d * 3 ^ s.length + vecIdx s from rfl, hlen]
    rw [hvc, hvd] at h
    obtain ⟨hcd, hrr⟩ := digitPair_eq hW hr hr' h
    subst hcd
    have ih := vecIdx_injective t s hlen ht hs hrr
    subst ih
    rfl

theorem testBit_or_shiftLeft (acc x i : ℕ) :
    Nat.testBit (acc ||| (1 <<< x)) i = true ↔ Nat.testBit acc i = true ∨ x = i := by
  rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow]
  simp

theorem testBit_foldl_step {α : Type} (S : ℕ → α → ℕ) (Q : α → ℕ → Prop)
    (hS : ∀ acc a i, Nat.testBit (S acc a) i = true ↔ Nat.testBit acc i = true ∨ Q a i) :
    ∀ (l : List α) (acc i : ℕ), Nat.testBit (l.foldl S acc) i = true ↔
      Nat.testBit acc i = true ∨ ∃ a ∈ l, Q a i
  | [], acc, i => by simp
  | a :: l, acc, i => by
    have hcons : (∃ x ∈ a :: l, Q x i) ↔ Q a i ∨ ∃ x ∈ l, Q x i := by
      constructor
      · rintro ⟨x, hx, hQ⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl hQ
        · exact Or.inr ⟨x, hx, hQ⟩
      · rintro (hQ | ⟨x, hx, hQ⟩)
        · exact ⟨a, List.mem_cons_self, hQ⟩
        · exact ⟨x, List.mem_cons_of_mem a hx, hQ⟩
    rw [List.foldl_cons, testBit_foldl_step S Q hS l, hS, hcons]
    tauto

@[expose] def planeBits (k₁ k₂ : List ℕ) : ℕ :=
  (List.range 3).foldl (fun acc a =>
    (List.range 3).foldl (fun acc b => acc ||| (1 <<< vecIdx (comb a b k₁ k₂))) acc) 0

theorem planeBits_spec {k₁ k₂ v : List ℕ} (h : k₁.length = k₂.length) (hv : v.length = k₁.length)
    (hv3 : ∀ x ∈ v, x < 3) :
    Nat.testBit (planeBits k₁ k₂) (vecIdx v) = true ↔
      ∃ a b, a < 3 ∧ b < 3 ∧ comb a b k₁ k₂ = v := by
  have hin : ∀ (acc a i : ℕ), Nat.testBit ((List.range 3).foldl
      (fun acc b => acc ||| (1 <<< vecIdx (comb a b k₁ k₂))) acc) i = true ↔
      Nat.testBit acc i = true ∨ ∃ b ∈ List.range 3, vecIdx (comb a b k₁ k₂) = i :=
    fun acc a i => testBit_foldl_step (fun acc b => acc ||| (1 <<< vecIdx (comb a b k₁ k₂)))
      (fun b i => vecIdx (comb a b k₁ k₂) = i) (fun acc b i => testBit_or_shiftLeft _ _ _)
      (List.range 3) acc i
  unfold planeBits
  rw [testBit_foldl_step (fun acc a => (List.range 3).foldl
      (fun acc b => acc ||| (1 <<< vecIdx (comb a b k₁ k₂))) acc)
    (fun a i => ∃ b ∈ List.range 3, vecIdx (comb a b k₁ k₂) = i) hin (List.range 3) 0 (vecIdx v)]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, b, ha, hb, vecIdx_injective (comb a b k₁ k₂) v
      ((length_comb h).trans hv.symm) comb_lt hv3 hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨a, ha, b, hb, by rw [hab]⟩

end CFSG.LieType.SeitzGeneration.ExcWideThree
