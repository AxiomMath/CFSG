module

public import CFSG.Certificates.Kernel.Misc.O62SoundBits

public section

namespace CFSG.KC.Misc.O62

open CFSG.KC.Ord CFSG.KC.Misc
open CFSG.KC.LQT.P (letB impB allN anyN allL anyL)
open CFSG.LargeExtraspecial.O62

@[expose] noncomputable def e8List (E : ℕ) : List ℕ := (List.range 8).map (e8 E)

theorem mem8_iff (E y : ℕ) : mem8 E y = true ↔ y ∈ e8List E := by
  unfold mem8 e8List
  rw [letB_eq, anyN_iff]
  simp [beq_eq_decide]

theorem nodup8_iff (E : ℕ) : nodup8 E = true ↔ (e8List E).Nodup := by
  unfold nodup8 e8List
  rw [allN_iff, List.nodup_map_iff_inj_on List.nodup_range]
  simp only [allN_iff, notB_eq, beq_eq_decide, Bool.not_eq_true', decide_eq_false_iff_not,
    List.mem_range]
  constructor
  · intro h x hx y hy hxy
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact h y hy x hlt hxy.symm
    · exact h x hx y hlt hxy
  · intro h i hi j hj heq
    exact absurd (h i hi j (by omega) heq) (by omega)

theorem key8_aux (E n : ℕ) : Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.add acc (Nat.mul (Nat.mul (e8 E i) (e8 E i)) (e8 E i))) n =
    (((List.range n).map (e8 E)).map (· ^ 3)).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : Nat.rec (motive := fun _ => ℕ) 0
        (fun i acc => Nat.add acc (Nat.mul (Nat.mul (e8 E i) (e8 E i)) (e8 E i))) (n + 1) =
        Nat.add (Nat.rec (motive := fun _ => ℕ) 0
          (fun i acc => Nat.add acc (Nat.mul (Nat.mul (e8 E i) (e8 E i)) (e8 E i))) n)
          (Nat.mul (Nat.mul (e8 E n) (e8 E n)) (e8 E n)) := rfl
    rw [e, ih, List.range_succ]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil]
    show _ + e8 E n * e8 E n * e8 E n = _
    ring

theorem key8_eq (E : ℕ) : key8 E = ((e8List E).map (· ^ 3)).sum := key8_aux E 8

theorem e8_eq (E i : ℕ) : e8 E i = E / 2 ^ (36 * i) % 2 ^ 36 := by
  show (E >>> (36 * i)) &&& (68719476735 : ℕ) = _
  rw [show (68719476735 : ℕ) = 2 ^ 36 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

theorem lor_add_of {A B s : ℕ} (hA : 2 ^ s ∣ A) (hB : B < 2 ^ s) : A ||| B = A + B := by
  obtain ⟨X, rfl⟩ := hA
  exact (Nat.two_pow_add_eq_or_of_lt hB X).symm

theorem pack8_eq {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℕ} (h₀ : a₀ < 2 ^ 36) (h₁ : a₁ < 2 ^ 36)
    (h₂ : a₂ < 2 ^ 36) (h₃ : a₃ < 2 ^ 36) (h₄ : a₄ < 2 ^ 36) (h₅ : a₅ < 2 ^ 36)
    (h₆ : a₆ < 2 ^ 36) :
    (Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft a₇ 252) (Nat.shiftLeft a₆ 216))
      (Nat.lor (Nat.shiftLeft a₅ 180) (Nat.shiftLeft a₄ 144)))
      (Nat.lor (Nat.lor (Nat.shiftLeft a₃ 108) (Nat.shiftLeft a₂ 72))
      (Nat.lor (Nat.shiftLeft a₁ 36) a₀))) =
    a₇ * 2 ^ 252 + a₆ * 2 ^ 216 + a₅ * 2 ^ 180 + a₄ * 2 ^ 144 + a₃ * 2 ^ 108 + a₂ * 2 ^ 72 +
      a₁ * 2 ^ 36 + a₀ := by
  simp only [raw_lor, raw_shl, Nat.shiftLeft_eq]
  have e1 : (a₇ * 2 ^ 252) ||| (a₆ * 2 ^ 216) = a₇ * 2 ^ 252 + a₆ * 2 ^ 216 :=
    lor_add_of (s := 252) ⟨a₇, by ring⟩ (by omega)
  have e2 : (a₅ * 2 ^ 180) ||| (a₄ * 2 ^ 144) = a₅ * 2 ^ 180 + a₄ * 2 ^ 144 :=
    lor_add_of (s := 180) ⟨a₅, by ring⟩ (by omega)
  have e3 : (a₇ * 2 ^ 252 + a₆ * 2 ^ 216) ||| (a₅ * 2 ^ 180 + a₄ * 2 ^ 144) =
      a₇ * 2 ^ 252 + a₆ * 2 ^ 216 + (a₅ * 2 ^ 180 + a₄ * 2 ^ 144) :=
    lor_add_of (s := 216) ⟨a₇ * 2 ^ 36 + a₆, by ring⟩ (by omega)
  have e4 : (a₃ * 2 ^ 108) ||| (a₂ * 2 ^ 72) = a₃ * 2 ^ 108 + a₂ * 2 ^ 72 :=
    lor_add_of (s := 108) ⟨a₃, by ring⟩ (by omega)
  have e5 : (a₁ * 2 ^ 36) ||| a₀ = a₁ * 2 ^ 36 + a₀ :=
    lor_add_of (s := 36) ⟨a₁, by ring⟩ h₀
  have e6 : (a₃ * 2 ^ 108 + a₂ * 2 ^ 72) ||| (a₁ * 2 ^ 36 + a₀) =
      a₃ * 2 ^ 108 + a₂ * 2 ^ 72 + (a₁ * 2 ^ 36 + a₀) :=
    lor_add_of (s := 72) ⟨a₃ * 2 ^ 36 + a₂, by ring⟩ (by omega)
  have e7 : (a₇ * 2 ^ 252 + a₆ * 2 ^ 216 + (a₅ * 2 ^ 180 + a₄ * 2 ^ 144)) |||
      (a₃ * 2 ^ 108 + a₂ * 2 ^ 72 + (a₁ * 2 ^ 36 + a₀)) =
      a₇ * 2 ^ 252 + a₆ * 2 ^ 216 + (a₅ * 2 ^ 180 + a₄ * 2 ^ 144) +
        (a₃ * 2 ^ 108 + a₂ * 2 ^ 72 + (a₁ * 2 ^ 36 + a₀)) :=
    lor_add_of (s := 144) ⟨a₇ * 2 ^ 108 + a₆ * 2 ^ 72 + a₅ * 2 ^ 36 + a₄, by ring⟩ (by omega)
  rw [e1, e2, e3, e4, e5, e6, e7]
  ring

theorem e8List_sum {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℕ} (h₀ : a₀ < 2 ^ 36) (h₁ : a₁ < 2 ^ 36)
    (h₂ : a₂ < 2 ^ 36) (h₃ : a₃ < 2 ^ 36) (h₄ : a₄ < 2 ^ 36) (h₅ : a₅ < 2 ^ 36)
    (h₆ : a₆ < 2 ^ 36) (h₇ : a₇ < 2 ^ 36) :
    e8List (a₇ * 2 ^ 252 + a₆ * 2 ^ 216 + a₅ * 2 ^ 180 + a₄ * 2 ^ 144 + a₃ * 2 ^ 108 +
      a₂ * 2 ^ 72 + a₁ * 2 ^ 36 + a₀) = [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇] := by
  unfold e8List
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, e8_eq, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem e8List_spanE (x y z : ℕ) :
    e8List (spanE x y z) = (Check.spanC [z, y, x]).reverse := by
  have hl : ∀ a b : ℕ, Code.mul a b < 2 ^ 36 := fun a b => Code.mul_lt a b
  have h1 : Code.one < 2 ^ 36 := Code.one_lt
  unfold spanE
  simp only [letN_eq, mulK_eq, oneK_eq]
  rw [pack8_eq (hl _ _) (hl _ _) (hl _ _) (hl _ _) (hl _ _) (hl _ _) (hl _ _),
    e8List_sum (hl _ _) (hl _ _) (hl _ _) (hl _ _) (hl _ _) (hl _ _) (hl _ _) h1]
  rfl

theorem certOK_iff (E k : List ℕ) :
    Check.certOK E k = true ↔
      (∀ e ∈ E, ∀ f ∈ E,
        Code.mul (Code.mul (Code.mul (Code.mul (wordC k) e) (wordC k.reverse)) f)
          (Code.mul (Code.mul (wordC k) e) (wordC k.reverse)) ∈ E) ∧
      ∃ e ∈ E, Code.mul (Code.mul (wordC k) e) (wordC k.reverse) ∉ E := by
  unfold Check.certOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_map,
    List.contains_eq_mem, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, x, ⟨a, ha, rfl⟩, hx⟩
    exact ⟨fun e he f hf => h1 _ ⟨e, he, rfl⟩ f hf, a, ha, hx⟩
  · rintro ⟨h1, a, ha, hx⟩
    exact ⟨fun x ⟨e, he, hex⟩ f hf => hex ▸ h1 e he f hf, _, ⟨a, ha, rfl⟩, hx⟩

theorem certOK_congr {E F : List ℕ} (h : ∀ a, a ∈ E ↔ a ∈ F) (k : List ℕ) :
    Check.certOK E k = Check.certOK F k := by
  apply Bool.eq_iff_iff.2
  rw [certOK_iff, certOK_iff]
  simp only [h]

theorem certOK8_iff (E : ℕ) (k : List ℕ) :
    certOK8 E k = true ↔ Check.certOK (e8List E) k = true := by
  rw [certOK_iff]
  unfold certOK8
  simp only [letB_eq, wordCK_eq, revN_eq, andB_eq, Bool.and_eq_true, allN_iff, anyN_iff, mem8_iff,
    notB_eq, mulK_eq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, e8List, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨h1, i, hi, hn⟩
    refine ⟨?_, e8 E i, ⟨i, hi, rfl⟩, hn⟩
    rintro e ⟨i, hi, rfl⟩ f ⟨j, hj, rfl⟩
    exact h1 i hi j hj
  · rintro ⟨h1, e, ⟨i, hi, rfl⟩, hn⟩
    exact ⟨fun i hi j hj => h1 _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩, i, hi, hn⟩

end CFSG.KC.Misc.O62

end
