module

public import CFSG.CGT.A8S.L2Code
public import CFSG.CGT.A8S.Interfaces

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

abbrev mkW (w : List (Fin 5 × Bool)) : PG 5 relsN0A8 := PresentedGroup.mk _ (FreeGroup.mk w)

theorem mkW_append (w w' : List (Fin 5 × Bool)) : mkW (w ++ w') = mkW w * mkW w' := by
  rw [mkW, ← FreeGroup.mul_mk, map_mul]

theorem mkW_single (i : Fin 5) : mkW [(i, true)] = PresentedGroup.of i := rfl

abbrev T0 : Subgroup (PG 5 relsN0A8) := Subgroup.closure (Set.range tGenA8)

@[expose] def isTc (c : ℕ) : Bool := Nat.beq (c / 8) 273

@[expose] def tW (v : ℕ) : List (Fin 5 × Bool) :=
  (if v.testBit 0 then [(2, true)] else []) ++ (if v.testBit 1 then [(3, true)] else []) ++
    (if v.testBit 2 then [(4, true)] else [])

theorem avc_tW : ∀ v < 8, affCode (affEval (tW v)) = v + 2184 := by decide +kernel

theorem cmul_isTc : ∀ v < 8, ∀ v' < 8, isTc (cmul (v + 2184) (v' + 2184)) = true := by
  decide +kernel

theorem cmul_isTc_self : ∀ v < 8, cmul (v + 2184) (v + 2184) = 2184 := by decide +kernel

theorem tW_letters : ∀ v < 8, (tW v).all (fun l => decide (2 ≤ l.1.val) && l.2) = true := by
  decide +kernel

theorem eq_of_isTc {c : ℕ} (h : isTc c = true) : c = c % 8 + 2184 := by
  simp only [isTc, Nat.beq_eq] at h
  omega

theorem mkW_mem_T0 : ∀ w : List (Fin 5 × Bool), (∀ l ∈ w, 2 ≤ l.1.val ∧ l.2 = true) →
    mkW w ∈ T0
  | [], _ => by
    show (1 : PG 5 relsN0A8) ∈ T0
    exact T0.one_mem
  | l :: w, h => by
    rw [show l :: w = [l] ++ w from rfl, mkW_append]
    refine T0.mul_mem ?_ (mkW_mem_T0 w fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨⟨i, hi⟩, b⟩ := l
    obtain ⟨h1, h2⟩ := h _ List.mem_cons_self
    simp only at h1 h2
    subst h2
    rw [mkW_single]
    refine Subgroup.subset_closure ⟨⟨i - 2, by omega⟩, ?_⟩
    simp only [tGenA8]
    congr 1
    exact Fin.ext (by simp only; omega)

theorem mem_T0_iff (x : PG 5 relsN0A8) :
    x ∈ T0 ↔ isTc (avc x) = true := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      fin_cases j <;> rfl
    | one => rw [avc_one]; rfl
    | mul y z _ _ hy hz =>
      rw [avc_mul, eq_of_isTc hy, eq_of_isTc hz]
      exact cmul_isTc _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    | inv y _ hy =>
      have hyy : y * y = 1 := avc_inj (by
        rw [avc_mul, avc_one, eq_of_isTc hy]
        exact cmul_isTc_self _ (Nat.mod_lt _ (by norm_num)))
      rwa [inv_eq_of_mul_eq_one_right hyy]
  · intro hx
    have hv : avc x % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have e : x = mkW (tW (avc x % 8)) := avc_inj (by
      rw [avc_mk, avc_tW _ hv]
      exact eq_of_isTc hx)
    rw [e]
    refine mkW_mem_T0 _ fun l hl => ?_
    have h := List.all_eq_true.1 (tW_letters _ hv) l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h

@[expose] def beta1W : List (Fin 5 × Bool) :=
  [(0, true), (1, false), (0, true), (1, true), (0, true), (2, true), (1, false), (0, true),
    (1, true)]

abbrev b0 : PG 5 relsN0A8 := mkW [(0, true), (3, true)]

abbrev beta1 : PG 5 relsN0A8 := mkW beta1W

abbrev B0 : Subgroup (PG 5 relsN0A8) := Subgroup.closure {beta1, b0}

@[expose] def b0Codes : List ℕ := [2184, 3211, 2698, 3721]

theorem avc_b0 : avc b0 = 2698 := by rw [avc_mk]; decide +kernel

theorem avc_beta1 : avc beta1 = 3211 := by rw [avc_mk]; decide +kernel

theorem b0Codes_mul : ∀ a ∈ b0Codes, ∀ b ∈ b0Codes, cmul a b ∈ b0Codes := by decide +kernel

theorem b0Codes_sq : ∀ a ∈ b0Codes, cmul a a = 2184 := by decide +kernel

theorem b0Codes_valid : ∀ a ∈ b0Codes, validC a = true := by decide +kernel

theorem mem_B0_iff (x : PG 5 relsN0A8) :
    x ∈ B0 ↔ avc x ∈ b0Codes := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · rw [avc_beta1]; decide
      · rw [avc_b0]; decide
    | one => rw [avc_one]; decide
    | mul y z _ _ hy hz => rw [avc_mul]; exact b0Codes_mul _ hy _ hz
    | inv y _ hy =>
      have hyy : y * y = 1 := avc_inj (by rw [avc_mul, avc_one]; exact b0Codes_sq _ hy)
      rwa [inv_eq_of_mul_eq_one_right hyy]
  · intro hx
    obtain ⟨y, hy⟩ := exists_avc_eq_of_validC (b0Codes_valid _ hx)
    have hb : beta1 ∈ B0 := Subgroup.subset_closure (by simp)
    have hb' : b0 ∈ B0 := Subgroup.subset_closure (by simp)
    simp only [b0Codes, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h
    · rw [avc_inj (h.trans avc_one.symm)]; exact B0.one_mem
    · rw [avc_inj (h.trans avc_beta1.symm)]; exact hb
    · rw [avc_inj (h.trans avc_b0.symm)]; exact hb'
    · rw [avc_inj (h.trans (by rw [avc_mul, avc_beta1, avc_b0]; decide +kernel :
        3721 = avc (beta1 * b0)))]
      exact B0.mul_mem hb hb'

theorem exists_mem_B0 {s : ℕ} (hs : s ∈ b0Codes) :
    ∃ b ∈ B0, avc b = s := by
  obtain ⟨b, rfl⟩ := exists_avc_eq_of_validC (b0Codes_valid _ hs)
  exact ⟨b, (mem_B0_iff b).2 hs, rfl⟩

theorem card_B0_le : Nat.card B0 ≤ 4 := by
  classical
  have h : Nat.card B0 ≤ Nat.card b0Codes.toFinset := by
    refine Nat.card_le_card_of_injective (fun x : B0 =>
      (⟨avc x, List.mem_toFinset.2 ((mem_B0_iff x).1 x.2)⟩ : b0Codes.toFinset)) ?_
    intro x y hxy
    exact Subtype.ext (avc_inj (congrArg Subtype.val hxy))
  rw [Nat.card_eq_finsetCard] at h
  exact h.trans (by decide)

end CFSG.CGT.A8S.L2
