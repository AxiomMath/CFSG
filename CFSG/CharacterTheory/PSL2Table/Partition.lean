module

public import CFSG.CharacterTheory.PSL2Table.ClassSum
public import CFSG.CharacterTheory.PSL2Table.Tori
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups

section Normalizer

variable {G : Type} [Group G]

theorem card_eq_two_mul_of_mem_iff [Finite G] {H N : Subgroup G} {w : G} (hw : w ∉ H)
    (hN : ∀ g, g ∈ N ↔ g ∈ H ∨ w⁻¹ * g ∈ H) : Nat.card N = 2 * Nat.card H := by
  classical
  have hwh : ∀ h ∈ H, w * h ∉ H := fun h hh hwh => hw (by
    simpa using H.mul_mem hwh (H.inv_mem hh))
  let e : N ≃ H ⊕ H :=
    { toFun := fun g => if hg : (g : G) ∈ H then Sum.inl ⟨g, hg⟩
        else Sum.inr ⟨w⁻¹ * g, ((hN g).mp g.2).resolve_left hg⟩
      invFun := fun s => match s with
        | Sum.inl h => ⟨h, (hN h).mpr (Or.inl h.2)⟩
        | Sum.inr h => ⟨w * h, (hN _).mpr (Or.inr (by simp))⟩
      left_inv := by
        intro g
        by_cases hg : (g : G) ∈ H
        · simp [hg]
        · simp [hg]
      right_inv := by
        intro s
        cases s with
        | inl h => simp [h.2]
        | inr h => simp [hwh h h.2] }
  rw [Nat.card_congr e, Nat.card_sum, two_mul]

theorem mem_normalizer_iff_of_TI {H : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hinv : ∀ x ∈ H, w * x * w⁻¹ = x⁻¹)
    {x₀ : G} (hx₀ : x₀ ∈ H)
    (hTI : ∀ g, g * x₀ * g⁻¹ ∈ H ↔ g ∈ H ∨ w⁻¹ * g ∈ H) (g : G) :
    g ∈ Subgroup.normalizer (H : Set G) ↔ g ∈ H ∨ w⁻¹ * g ∈ H := by
  have hwN : w ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hinv h hh]
      exact H.inv_mem hh
    · intro hh
      have h1 : w * (w * h * w⁻¹) * w⁻¹ = h := by
        calc w * (w * h * w⁻¹) * w⁻¹ = (w * w) * h * (w * w)⁻¹ := by group
          _ = h := by rw [hw2]; group
      rw [← h1, hinv _ hh]
      exact H.inv_mem hh
  constructor
  · intro hg
    exact (hTI g).mp ((Subgroup.mem_normalizer_iff.mp hg x₀).mp hx₀)
  · rintro (hg | hg)
    · exact Subgroup.le_normalizer hg
    · have : g = w * (w⁻¹ * g) := by group
      rw [this]
      exact (Subgroup.normalizer (H : Set G)).mul_mem hwN (Subgroup.le_normalizer hg)

end Normalizer

section PSL

variable {F : Type} [Field F] [Fintype F]

theorem exists_ne_one_of_two_le_card {G : Type} [Group G] {H : Subgroup G}
    (h : 2 ≤ Nat.card H) : ∃ x ∈ H, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact hcon x hx
  rw [this, Subgroup.card_bot] at h
  omega

theorem exists_ne_one_splitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    ∃ x ∈ splitTorus F, x ≠ 1 := by
  apply exists_ne_one_of_two_le_card
  have := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  omega

theorem exists_ne_one_nonsplitTorus (hF : ringChar F ≠ 2)
    (hq : 5 ≤ Fintype.card F) {ν : F} (hν : ¬ IsSquare ν) :
    ∃ x ∈ nonsplitTorus ν, x ≠ 1 := by
  apply exists_ne_one_of_two_le_card
  have := card_nonsplitTorus hF hν
  omega

theorem splitTorus_TI (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    ∀ x ∈ splitTorus F, x ≠ 1 → ∀ g : PSL(2, F),
      g * x * g⁻¹ ∈ splitTorus F ↔ g ∈ Subgroup.normalizer (splitTorus F : Set PSL(2, F)) := by
  intro x hx hx1 g
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_splitTorus hF hq
  rw [splitTorus_conj_mem_iff hx hx1,
    mem_normalizer_iff_of_TI splitWeyl_mul_self (fun y hy => splitWeyl_conj hy) hx₀
      (splitTorus_conj_mem_iff hx₀ hx₀1)]

theorem card_normalizer_splitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    Nat.card (Subgroup.normalizer (splitTorus F : Set PSL(2, F))) =
      2 * Nat.card (splitTorus F) := by
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_splitTorus hF hq
  exact card_eq_two_mul_of_mem_iff splitWeyl_not_mem
    (mem_normalizer_iff_of_TI splitWeyl_mul_self (fun y hy => splitWeyl_conj hy) hx₀
      (splitTorus_conj_mem_iff hx₀ hx₀1))

theorem nonsplitTorus_TI (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) :
    ∀ x ∈ nonsplitTorus ν, x ≠ 1 → ∀ g : PSL(2, F),
      g * x * g⁻¹ ∈ nonsplitTorus ν ↔
        g ∈ Subgroup.normalizer (nonsplitTorus ν : Set PSL(2, F)) := by
  intro x hx hx1 g
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_nonsplitTorus hF hq hν
  obtain ⟨w, -, hw2, hinv, hTI⟩ := exists_nonsplitWeyl hF hν
  rw [hTI x hx hx1, mem_normalizer_iff_of_TI hw2 hinv hx₀ (hTI x₀ hx₀ hx₀1)]

theorem card_normalizer_nonsplitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) :
    Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set PSL(2, F))) =
      2 * Nat.card (nonsplitTorus ν) := by
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_nonsplitTorus hF hq hν
  obtain ⟨w, hw, hw2, hinv, hTI⟩ := exists_nonsplitWeyl hF hν
  exact card_eq_two_mul_of_mem_iff hw (mem_normalizer_iff_of_TI hw2 hinv hx₀ (hTI x₀ hx₀ hx₀1))

omit [Fintype F] in
theorem unipotent_TI (hF : ringChar F ≠ 2) :
    ∀ x ∈ unipotent F, x ≠ 1 → ∀ g : PSL(2, F), g * x * g⁻¹ ∈ unipotent F ↔ g ∈ borel F :=
  fun _ hx hx1 g => unipotent_conj_mem_iff (Ring.two_ne_zero hF) hx hx1 g

theorem coprime_card_unipotent_splitTorus (hF : ringChar F ≠ 2) :
    Nat.Coprime (Nat.card (unipotent F)) (Nat.card (splitTorus F)) := by
  have h2 := Ring.two_ne_zero hF
  rw [card_unipotent h2]
  have hT := card_splitTorus h2 (F := F)
  have hq : Fintype.card F = 1 + 2 * Nat.card (splitTorus F) := by
    have := Fintype.one_lt_card (α := F)
    omega
  rw [hq, Nat.coprime_add_mul_right_left]
  exact Nat.coprime_one_left _

theorem coprime_card_unipotent_nonsplitTorus (hF : ringChar F ≠ 2) {ν : F}
    (hν : ¬ IsSquare ν) :
    Nat.Coprime (Nat.card (unipotent F)) (Nat.card (nonsplitTorus ν)) := by
  have h2 := Ring.two_ne_zero hF
  rw [card_unipotent h2]
  have hS := card_nonsplitTorus hF hν
  obtain ⟨r, hr⟩ : ∃ r, Nat.card (nonsplitTorus ν) = r + 1 :=
    ⟨Nat.card (nonsplitTorus ν) - 1, by have := Fintype.one_lt_card (α := F); omega⟩
  have hq : Fintype.card F = r + 1 * (r + 1) := by omega
  rw [hq, hr, Nat.coprime_add_mul_right_left]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right r)

theorem coprime_card_splitTorus_nonsplitTorus (hF : ringChar F ≠ 2) {ν : F}
    (hν : ¬ IsSquare ν) :
    Nat.Coprime (Nat.card (splitTorus F)) (Nat.card (nonsplitTorus ν)) := by
  have h2 := Ring.two_ne_zero hF
  have hT := card_splitTorus h2 (F := F)
  have hS := card_nonsplitTorus hF hν
  have : Nat.card (nonsplitTorus ν) = Nat.card (splitTorus F) + 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  rw [this]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

variable [DecidableEq F]

theorem card_conjSet_sum (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) [DecidablePred (· ∈ conjSet (unipotent F))]
    [DecidablePred (· ∈ conjSet (splitTorus F))]
    [DecidablePred (· ∈ conjSet (nonsplitTorus ν))] :
    (Finset.univ.filter (· ∈ conjSet (unipotent F))).card +
      (Finset.univ.filter (· ∈ conjSet (splitTorus F))).card +
      (Finset.univ.filter (· ∈ conjSet (nonsplitTorus ν))).card + 1 = Nat.card PSL(2, F) := by
  classical
  have h2 := Ring.two_ne_zero hF
  have e1 := card_conjSet_of_TI (unipotent F) (borel F) (unipotent_TI hF)
  have e2 := card_conjSet_of_TI _ _ (splitTorus_TI hF hq)
  have e3 := card_conjSet_of_TI _ _ (nonsplitTorus_TI hF hq hν)
  rw [card_unipotent h2] at e1
  rw [card_normalizer_splitTorus hF hq] at e2
  rw [card_normalizer_nonsplitTorus hF hq hν] at e3
  have hG := card_PSL h2 (F := F)
  have hB := card_borel h2 (F := F)
  have hT := card_splitTorus h2 (F := F)
  have hS := card_nonsplitTorus hF hν
  set q := Fintype.card F
  set cP := (Finset.univ.filter (· ∈ conjSet (unipotent F))).card
  set cT := (Finset.univ.filter (· ∈ conjSet (splitTorus F))).card
  set cS := (Finset.univ.filter (· ∈ conjSet (nonsplitTorus ν))).card
  set g := Nat.card PSL(2, F)
  set b := Nat.card (borel F)
  set t := Nat.card (splitTorus F)
  set s := Nat.card (nonsplitTorus ν)
  have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have e1' : (b : ℚ) * cP = g * (q - 1) := by
    have := congrArg (Nat.cast (R := ℚ)) e1
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at this
    exact this
  have e2' : (2 * t : ℚ) * cT = g * (t - 1) := by
    have := congrArg (Nat.cast (R := ℚ)) e2
    push_cast [Nat.cast_sub (by omega : 1 ≤ t)] at this
    exact this
  have e3' : (2 * s : ℚ) * cS = g * (s - 1) := by
    have := congrArg (Nat.cast (R := ℚ)) e3
    push_cast [Nat.cast_sub (by omega : 1 ≤ s)] at this
    exact this
  have hG' : (g : ℚ) * 2 = q * (q ^ 2 - 1) := by
    have := congrArg (Nat.cast (R := ℚ)) hG
    push_cast [Nat.cast_sub (by nlinarith : 1 ≤ q ^ 2)] at this
    exact this
  have hB' : (b : ℚ) * 2 = (q - 1) * q := by
    have := congrArg (Nat.cast (R := ℚ)) hB
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at this
    exact this
  have hT' : (t : ℚ) * 2 = q - 1 := by
    have := congrArg (Nat.cast (R := ℚ)) hT
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at this
    exact this
  have hS' : (s : ℚ) * 2 = q + 1 := by exact_mod_cast hS
  have hq5 : (5 : ℚ) ≤ q := by exact_mod_cast hq
  have hg : (g : ℚ) = q * (q ^ 2 - 1) / 2 := by linear_combination hG' / 2
  have hb : (b : ℚ) = (q - 1) * q / 2 := by linear_combination hB' / 2
  have ht : (t : ℚ) = (q - 1) / 2 := by linear_combination hT' / 2
  have hs : (s : ℚ) = (q + 1) / 2 := by linear_combination hS' / 2
  rw [hb, hg] at e1'
  rw [ht, hg] at e2'
  rw [hs, hg] at e3'
  have hcP : (cP : ℚ) = q ^ 2 - 1 := by
    have h : ((q - 1) * q / 2) * ((cP : ℚ) - (q ^ 2 - 1)) = 0 := by linear_combination e1'
    have hne : ((q : ℚ) - 1) * q / 2 ≠ 0 := by
      apply div_ne_zero _ two_ne_zero
      exact mul_ne_zero (by linarith) (by linarith)
    linear_combination (mul_eq_zero.mp h).resolve_left hne
  have hcT : (cT : ℚ) * 4 = q * (q + 1) * (q - 3) := by
    have h : (q - 1) * ((cT : ℚ) * 4 - q * (q + 1) * (q - 3)) = 0 := by
      linear_combination 4 * e2'
    linear_combination (mul_eq_zero.mp h).resolve_left (by linarith)
  have hcS : (cS : ℚ) * 4 = q * (q - 1) * (q - 1) := by
    have h : (q + 1) * ((cS : ℚ) * 4 - q * (q - 1) * (q - 1)) = 0 := by
      linear_combination 4 * e3'
    linear_combination (mul_eq_zero.mp h).resolve_left (by linarith)
  have : ((cP + cT + cS + 1 : ℕ) : ℚ) = (g : ℚ) := by
    push_cast
    linear_combination hcP + hcT / 4 + hcS / 4 - hg
  exact_mod_cast this

theorem mem_conjSet_cases (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (g : PSL(2, F)) :
    g = 1 ∨ g ∈ conjSet (unipotent F) ∨ g ∈ conjSet (splitTorus F) ∨
      g ∈ conjSet (nonsplitTorus ν) := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hg1, hgP, hgT, hgS⟩ := hcon
  set U := (Finset.univ.filter (· ∈ conjSet (unipotent F))) ∪
    (Finset.univ.filter (· ∈ conjSet (splitTorus F))) ∪
    (Finset.univ.filter (· ∈ conjSet (nonsplitTorus ν))) with hU
  have hdisj1 : Disjoint (Finset.univ.filter (· ∈ conjSet (unipotent F)))
      (Finset.univ.filter (· ∈ conjSet (splitTorus F))) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact disjoint_conjSet (coprime_card_unipotent_splitTorus hF) h1 h2
  have hdisj2 : Disjoint ((Finset.univ.filter (· ∈ conjSet (unipotent F))) ∪
      (Finset.univ.filter (· ∈ conjSet (splitTorus F))))
      (Finset.univ.filter (· ∈ conjSet (nonsplitTorus ν))) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_filter, Finset.disjoint_filter]
    exact ⟨fun x _ h1 h2 => disjoint_conjSet (coprime_card_unipotent_nonsplitTorus hF hν) h1 h2,
      fun x _ h1 h2 => disjoint_conjSet (coprime_card_splitTorus_nonsplitTorus hF hν) h1 h2⟩
  have hcard : U.card = (Finset.univ.erase (1 : PSL(2, F))).card := by
    rw [hU, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← card_conjSet_sum hF hq hν]
    rfl
  have hsub : U ⊆ Finset.univ.erase 1 := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    simp only [hU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with (h | h) | h
    · exact h.1
    · exact h.1
    · exact h.1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hg : g ∈ U := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hg1, Finset.mem_univ _⟩
  simp only [hU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hg
  rcases hg with (h | h) | h
  · exact hgP h
  · exact hgT h
  · exact hgS h

omit [Fintype F] [DecidableEq F] in
theorem sum_ite_mem_and_ne_one {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [DecidablePred (· ∈ H)] (f : G → ℂ) :
    ∑ x : G, (if x ∈ H ∧ x ≠ 1 then f x else 0) = ∑ x : H, f x - f 1 := by
  have h1 : ∑ x : G, (if x ∈ H ∧ x ≠ 1 then f x else 0) =
      ∑ x : G, (if x ∈ H then f x else 0) - f 1 := by
    rw [eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte, H.one_mem, zero_add]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_erase] at hx
    simp [hx.1]
  rw [h1, ← Finset.sum_filter]
  congr 1
  exact Finset.sum_subtype _ (fun x => by simp) f

theorem sum_classFunction (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (f : PSL(2, F) → ℂ) (hf : ∀ g x, f (g * x * g⁻¹) = f x) :
    ∑ g : PSL(2, F), f g = f 1 +
      ((Fintype.card F : ℂ) + 1) * (∑ x : unipotent F, f x - f 1) +
      ((Fintype.card F : ℂ) * (Fintype.card F + 1) / 2) * (∑ x : splitTorus F, f x - f 1) +
      ((Fintype.card F : ℂ) * (Fintype.card F - 1) / 2) * (∑ x : nonsplitTorus ν, f x - f 1) := by
  classical
  have h2 := Ring.two_ne_zero hF
  have hpt : ∀ g : PSL(2, F), f g = (if g = 1 then f g else 0) +
      (if g ∈ conjSet (unipotent F) then f g else 0) +
      (if g ∈ conjSet (splitTorus F) then f g else 0) +
      (if g ∈ conjSet (nonsplitTorus ν) then f g else 0) := by
    intro g
    rcases mem_conjSet_cases hF hq hν g with h | h | h | h
    · subst h
      have h' : ∀ H : Subgroup PSL(2, F), (1 : PSL(2, F)) ∉ conjSet H := fun H hH => hH.1 rfl
      simp [h']
    · have hT : g ∉ conjSet (splitTorus F) :=
        fun h' => disjoint_conjSet (coprime_card_unipotent_splitTorus hF) h h'
      have hS : g ∉ conjSet (nonsplitTorus ν) :=
        fun h' => disjoint_conjSet (coprime_card_unipotent_nonsplitTorus hF hν) h h'
      simp [h, hT, hS, h.1]
    · have hP : g ∉ conjSet (unipotent F) :=
        fun h' => disjoint_conjSet (coprime_card_unipotent_splitTorus hF) h' h
      have hS : g ∉ conjSet (nonsplitTorus ν) :=
        fun h' => disjoint_conjSet (coprime_card_splitTorus_nonsplitTorus hF hν) h h'
      simp [h, hP, hS, h.1]
    · have hP : g ∉ conjSet (unipotent F) :=
        fun h' => disjoint_conjSet (coprime_card_unipotent_nonsplitTorus hF hν) h' h
      have hT : g ∉ conjSet (splitTorus F) :=
        fun h' => disjoint_conjSet (coprime_card_splitTorus_nonsplitTorus hF hν) h' h
      simp [h, hP, hT, h.1]
  rw [Finset.sum_congr rfl (fun g _ => hpt g)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have eP := sum_conjSet_of_TI (unipotent F) (borel F) (unipotent_TI hF) f hf
  have eT := sum_conjSet_of_TI _ _ (splitTorus_TI hF hq) f hf
  have eS := sum_conjSet_of_TI _ _ (nonsplitTorus_TI hF hq hν) f hf
  rw [sum_ite_mem_and_ne_one] at eP eT eS
  rw [card_normalizer_splitTorus hF hq] at eT
  rw [card_normalizer_nonsplitTorus hF hq hν] at eS
  have hG := card_PSL h2 (F := F)
  have hB := card_borel h2 (F := F)
  have hT := card_splitTorus h2 (F := F)
  have hS := card_nonsplitTorus hF hν
  have hq1 : 1 ≤ Fintype.card F := by omega
  have hG' : (Nat.card PSL(2, F) : ℂ) * 2 =
      Fintype.card F * ((Fintype.card F : ℂ) ^ 2 - 1) := by
    have := congrArg (Nat.cast (R := ℂ)) hG
    push_cast [Nat.cast_sub (by nlinarith : 1 ≤ Fintype.card F ^ 2)] at this
    exact this
  have hB' : (Nat.card (borel F) : ℂ) * 2 = ((Fintype.card F : ℂ) - 1) * Fintype.card F := by
    have := congrArg (Nat.cast (R := ℂ)) hB
    push_cast [Nat.cast_sub hq1] at this
    exact this
  have hT' : (Nat.card (splitTorus F) : ℂ) * 2 = (Fintype.card F : ℂ) - 1 := by
    have := congrArg (Nat.cast (R := ℂ)) hT
    push_cast [Nat.cast_sub hq1] at this
    exact this
  have hS' : (Nat.card (nonsplitTorus ν) : ℂ) * 2 = (Fintype.card F : ℂ) + 1 := by
    exact_mod_cast hS
  have hq5 : (5 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
  have hqC : (Fintype.card F : ℂ) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hqC' : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card F ≠ 0)
  have hqC'' : (Fintype.card F : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card F + 1 ≠ 0)
  set g := (Nat.card PSL(2, F) : ℂ)
  set q := (Fintype.card F : ℂ)
  have hBne : (Nat.card (borel F) : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hB'
    exact mul_ne_zero hqC hqC' hB'.symm
  have hTne : (Nat.card (splitTorus F) : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hT'
    exact hqC hT'.symm
  have hSne : (Nat.card (nonsplitTorus ν) : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hS'
    exact hqC'' hS'.symm
  have sP : ∑ y : PSL(2, F), (if y ∈ conjSet (unipotent F) then f y else 0) =
      (q + 1) * (∑ x : unipotent F, f x - f 1) := by
    apply mul_left_cancel₀ hBne
    rw [eP]
    linear_combination (∑ x : unipotent F, f x - f 1) * (hG' - (q + 1) * hB') / 2
  have sT : ∑ y : PSL(2, F), (if y ∈ conjSet (splitTorus F) then f y else 0) =
      (q * (q + 1) / 2) * (∑ x : splitTorus F, f x - f 1) := by
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hTne)
    rw [Nat.cast_mul, Nat.cast_ofNat] at eT
    rw [eT]
    linear_combination (∑ x : splitTorus F, f x - f 1) * (hG' - q * (q + 1) / 2 * 2 * hT') / 2
  have sS : ∑ y : PSL(2, F), (if y ∈ conjSet (nonsplitTorus ν) then f y else 0) =
      (q * (q - 1) / 2) * (∑ x : nonsplitTorus ν, f x - f 1) := by
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hSne)
    rw [Nat.cast_mul, Nat.cast_ofNat] at eS
    rw [eS]
    linear_combination (∑ x : nonsplitTorus ν, f x - f 1) * (hG' - q * (q - 1) / 2 * 2 * hS') / 2
  rw [sP, sT, sS]

end PSL

end CFSG.PSL2Table
