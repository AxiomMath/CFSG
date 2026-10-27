module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseOpen

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

namespace FuseConj

section PermCore

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem swap_mul_comm_of_mul_self_eq_one {σ : Perm α} (hσ : σ * σ = 1) (a : α) :
    swap a (σ a) * σ = σ * swap a (σ a) := by
  have h1 : σ (σ a) = a := by
    have := congrArg (fun f : Perm α => f a) hσ
    simpa using this
  have h2 := swap_apply_apply σ a (σ a)
  rw [h1, swap_comm] at h2
  rw [eq_mul_inv_iff_mul_eq] at h2
  exact h2

omit [Fintype α] [DecidableEq α] in
theorem mul_self_eq_one_of_orderOf_eq_two {σ : Perm α} (hσ : orderOf σ = 2) : σ * σ = 1 := by
  rw [← pow_two, ← hσ]
  exact pow_orderOf_eq_one σ

omit [Fintype α] [DecidableEq α] in
theorem ne_one_of_orderOf_eq_two {σ : Perm α} (hσ : orderOf σ = 2) : σ ≠ 1 := by
  rintro rfl
  simp at hσ

theorem exists_even_conj_eq {σ : Perm α} (hσ : orderOf σ = 2) (π : Perm α) :
    ∃ g : Perm α, Perm.sign g = 1 ∧ g * σ * g⁻¹ = π * σ * π⁻¹ := by
  have hσσ := mul_self_eq_one_of_orderOf_eq_two hσ
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact ne_one_of_orderOf_eq_two hσ (Equiv.ext h)
  rcases Int.units_eq_one_or (Perm.sign π) with h | h
  · exact ⟨π, h, rfl⟩
  · refine ⟨π * swap a (σ a), ?_, ?_⟩
    · rw [Perm.sign_mul, h, Perm.sign_swap (Ne.symm ha)]
      decide
    · have hc := swap_mul_comm_of_mul_self_eq_one hσσ a
      have hs : swap a (σ a) * σ * (swap a (σ a))⁻¹ = σ := by
        rw [mul_inv_eq_iff_eq_mul, hc]
      calc π * swap a (σ a) * σ * (π * swap a (σ a))⁻¹
          = π * (swap a (σ a) * σ * (swap a (σ a))⁻¹) * π⁻¹ := by group
        _ = π * σ * π⁻¹ := by rw [hs]

theorem natCard_fixedPoints_eq (σ : Perm α) :
    Nat.card (Function.fixedPoints σ) = Fintype.card α - σ.support.card := by
  rw [Nat.card_eq_fintype_card, Perm.card_fixedPoints, Perm.sum_cycleType]

theorem natCard_fixedPoints_conj (σ π : Perm α) :
    Nat.card (Function.fixedPoints (π * σ * π⁻¹)) = Nat.card (Function.fixedPoints σ) := by
  rw [natCard_fixedPoints_eq, natCard_fixedPoints_eq, Perm.card_support_conj]

theorem isConj_of_orderOf_eq_two {σ τ : Perm α} (hσ : orderOf σ = 2) (hτ : orderOf τ = 2)
    (h : Nat.card (Function.fixedPoints σ) = Nat.card (Function.fixedPoints τ)) :
    IsConj σ τ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have h1 := Perm.cycleType_of_pow_prime_eq_one hσ2
  have h2 := Perm.cycleType_of_pow_prime_eq_one hτ2
  have e1 : σ.cycleType.sum = σ.cycleType.card * 2 := by rw [h1]; simp
  have e2 : τ.cycleType.sum = τ.cycleType.card * 2 := by rw [h2]; simp
  rw [natCard_fixedPoints_eq, natCard_fixedPoints_eq] at h
  rw [Perm.sum_cycleType] at e1 e2
  have hσle := Finset.card_le_univ σ.support
  have hτle := Finset.card_le_univ τ.support
  have hcard : σ.cycleType.card = τ.cycleType.card := by omega
  rw [Perm.isConj_iff_cycleType_eq]
  calc σ.cycleType = Multiset.replicate σ.cycleType.card 2 := h1
    _ = Multiset.replicate τ.cycleType.card 2 := by rw [hcard]
    _ = τ.cycleType := h2.symm

theorem exists_even_conj {σ τ : Perm α} (hσ : orderOf σ = 2) (hτ : orderOf τ = 2)
    (h : Nat.card (Function.fixedPoints σ) = Nat.card (Function.fixedPoints τ)) :
    ∃ g : Perm α, Perm.sign g = 1 ∧ g * σ * g⁻¹ = τ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_orderOf_eq_two hσ hτ h)
  obtain ⟨g, hg, hgc⟩ := exists_even_conj_eq hσ c
  exact ⟨g, hg, hgc.trans hc⟩

theorem natCard_fixedPoints_eq_mod_four {σ : Perm α} (hσ : orderOf σ = 2)
    (hs : Perm.sign σ = 1) (h4 : Nat.card (Function.fixedPoints σ) < 4) :
    Nat.card (Function.fixedPoints σ) = Fintype.card α % 4 := by
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have e1 := Perm.sign_of_pow_two_eq_one hσ2
  rw [hs] at e1
  have he : Even ((Fintype.card α - Fintype.card (Function.fixedPoints σ)) / 2) :=
    (neg_one_pow_eq_one_iff_even (by decide)).1 e1.symm
  have hd := Perm.two_dvd_card_support hσ2
  have hc := Perm.card_fixedPoints σ
  rw [Perm.sum_cycleType] at hc
  have hle := Finset.card_le_univ σ.support
  rw [Nat.card_eq_fintype_card] at h4 ⊢
  obtain ⟨k, hk⟩ := he
  omega

theorem le_natCard_fixedPoints {σ : Perm α} (X : Finset α) (hX : ∀ i ∉ X, σ i = i) :
    Fintype.card α - X.card ≤ Nat.card (Function.fixedPoints σ) := by
  rw [natCard_fixedPoints_eq]
  have hsub : σ.support ⊆ X := fun i hi => by
    by_contra hiX
    exact (Perm.mem_support.1 hi) (hX i hiX)
  have := Finset.card_le_card hsub
  omega

theorem exists_moved_not_mem {σ : Perm α} (hF : Nat.card (Function.fixedPoints σ) < 4)
    (X : Finset α) (hX : X.card + 4 ≤ Fintype.card α) : ∃ x ∉ X, σ x ≠ x := by
  by_contra h
  push Not at h
  have := le_natCard_fixedPoints X h
  omega

theorem exists_even_perm_fixing {σ : Perm α} (hσ : orderOf σ = 2) (S : Finset α)
    (hS : S.card ≤ Nat.card (Function.fixedPoints σ)) :
    ∃ g : Perm α, Perm.sign g = 1 ∧ ∀ s ∈ S, (g * σ * g⁻¹) s = s := by
  have hcard : Fintype.card S ≤ Fintype.card (Function.fixedPoints σ) := by
    rw [Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact hS
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨π, hπ⟩ := Perm.exists_extending_pair (fun s : S => (s : α))
    (fun s : S => ((φ s : Function.fixedPoints σ) : α)) Subtype.val_injective
    (Subtype.val_injective.comp φ.injective)
  obtain ⟨g, hg, hgσ⟩ := exists_even_conj_eq hσ π⁻¹
  refine ⟨g, hg, fun s hs => ?_⟩
  rw [hgσ]
  have h1 : σ (π s) = π s := by
    have := (φ ⟨s, hs⟩).2
    have h2 := hπ ⟨s, hs⟩
    simp only at h2
    rw [h2]
    exact this
  simp [Perm.mul_apply, h1]

end PermCore

section PermFour

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem perm_inv_apply_self (π : Perm α) (x : α) : π⁻¹ (π x) = x := π.symm_apply_apply x

theorem sign_swap_mul_swap {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    Perm.sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  decide

omit [Fintype α] in
theorem swap_mul_swap_apply_of_ne {a b c d x : α} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hxd : x ≠ d) : (swap a b * swap c d) x = x := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]

omit [Fintype α] in
theorem swap_mul_swap_apply_fst {a b c d : α} (hac : a ≠ c) (had : a ≠ d) :
    (swap a b * swap c d) a = b := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]

omit [Fintype α] in
theorem swap_mul_swap_apply_snd {a b c d : α} (hbc : b ≠ c) (hbd : b ≠ d) :
    (swap a b * swap c d) b = a := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]

omit [Fintype α] in
theorem swap_mul_swap_apply_third {a b c d : α} (hda : d ≠ a) (hdb : d ≠ b) :
    (swap a b * swap c d) c = d := by
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hda hdb]

omit [Fintype α] in
theorem swap_mul_swap_apply_fourth {a b c d : α} (hca : c ≠ a) (hcb : c ≠ b) :
    (swap a b * swap c d) d = c := by
  rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hca hcb]

omit [Fintype α] in
theorem swap_mul_swap_mul_self {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : (swap a b * swap c d) * (swap a b * swap c d) = 1 := by
  have hcomm : Commute (swap a b) (swap c d) := by
    refine Perm.Disjoint.commute (fun x => ?_)
    by_cases hx : x = a ∨ x = b
    · right
      rcases hx with rfl | rfl
      · exact swap_apply_of_ne_of_ne hac had
      · exact swap_apply_of_ne_of_ne hbc hbd
    · left
      push Not at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2
  rw [← pow_two, hcomm.mul_pow, pow_two, pow_two, swap_mul_self, swap_mul_self, mul_one]

omit [Fintype α] in
theorem conj_swap_mul_swap (τ : Perm α) (a b c d : α) :
    τ * (swap a b * swap c d) * τ⁻¹ = swap (τ a) (τ b) * swap (τ c) (τ d) := by
  rw [swap_apply_apply, swap_apply_apply]
  group

theorem exists_far_decomp {σ : Perm α} (hσ : orderOf σ = 2) (hs : Perm.sign σ = 1)
    (hF : Nat.card (Function.fixedPoints σ) < 4) {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hα : 8 ≤ Fintype.card α) :
    ∃ b' : Perm α, Perm.sign b' = 1 ∧ b' * b' = 1 ∧ b' ≠ 1 ∧
      (∀ x ∈ ({a, b, c, d} : Finset α), b' x = x) ∧
      ∃ g : Perm α, Perm.sign g = 1 ∧ g * σ * g⁻¹ = b' * (swap a b * swap c d) := by
  have hσσ := mul_self_eq_one_of_orderOf_eq_two hσ
  have hσσ' : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : Perm α => f x) hσσ
    simpa using this
  obtain ⟨p, -, hp⟩ := exists_moved_not_mem hF ∅ (by simp; omega)
  obtain ⟨r, hr', hr⟩ := exists_moved_not_mem hF {p, σ p} (by
    have := Finset.card_le_two (a := p) (b := σ p); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr'
  have hf : Function.Injective ![p, σ p, r, σ r] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind
  have hg : Function.Injective ![a, b, c, d] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind
  obtain ⟨π, hπ⟩ := Perm.exists_extending_pair _ _ hf hg
  have hπ0 : π p = a := by simpa using hπ 0
  have hπ1 : π (σ p) = b := by simpa using hπ 1
  have hπ2 : π r = c := by simpa using hπ 2
  have hπ3 : π (σ r) = d := by simpa using hπ 3
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm α, τ = π * σ * π⁻¹ := ⟨_, rfl⟩
  have hτa : τ a = b := by
    rw [hτ, Perm.mul_apply, Perm.mul_apply, ← hπ0, perm_inv_apply_self, hπ1]
  have hτb : τ b = a := by
    rw [hτ, Perm.mul_apply, Perm.mul_apply, ← hπ1, perm_inv_apply_self, hσσ', hπ0]
  have hτc : τ c = d := by
    rw [hτ, Perm.mul_apply, Perm.mul_apply, ← hπ2, perm_inv_apply_self, hπ3]
  have hτd : τ d = c := by
    rw [hτ, Perm.mul_apply, Perm.mul_apply, ← hπ3, perm_inv_apply_self, hσσ', hπ2]
  have hττ : τ * τ = 1 := by
    calc τ * τ = π * (σ * σ) * π⁻¹ := by rw [hτ]; group
      _ = 1 := by rw [hσσ]; group
  have hτs : Perm.sign τ = 1 := by
    rw [hτ, Perm.sign_mul, Perm.sign_mul, hs, Perm.sign_inv, mul_one]
    exact Int.units_mul_self _
  have hτF : Nat.card (Function.fixedPoints τ) < 4 := by
    rw [hτ, natCard_fixedPoints_conj]
    exact hF
  have hww := swap_mul_swap_mul_self hac had hbc hbd
  have hcomm : τ * (swap a b * swap c d) = (swap a b * swap c d) * τ := by
    have h1 := conj_swap_mul_swap τ a b c d
    rw [hτa, hτb, hτc, hτd, swap_comm b a, swap_comm d c] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  refine ⟨τ * (swap a b * swap c d), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Perm.sign_mul, hτs, sign_swap_mul_swap hab hcd, mul_one]
  · calc τ * (swap a b * swap c d) * (τ * (swap a b * swap c d))
        = τ * ((swap a b * swap c d) * τ) * (swap a b * swap c d) := by group
      _ = τ * (τ * (swap a b * swap c d)) * (swap a b * swap c d) := by rw [← hcomm]
      _ = (τ * τ) * ((swap a b * swap c d) * (swap a b * swap c d)) := by group
      _ = 1 := by rw [hττ, hww, mul_one]
  · obtain ⟨x, hx, hτx⟩ := exists_moved_not_mem hτF {a, b, c, d} (by
      have := Finset.card_le_four (a := a) (b := b) (c := c) (d := d); omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    intro h
    apply hτx
    have h1 := congrArg (fun f : Perm α => f x) h
    simpa [Perm.mul_apply, swap_mul_swap_apply_of_ne hx.1 hx.2.1 hx.2.2.1 hx.2.2.2] using h1
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [Perm.mul_apply, swap_mul_swap_apply_fst hac had, hτb]
    · rw [Perm.mul_apply, swap_mul_swap_apply_snd hbc hbd, hτa]
    · rw [Perm.mul_apply, swap_mul_swap_apply_third had.symm hbd.symm, hτd]
    · rw [Perm.mul_apply, swap_mul_swap_apply_fourth hac.symm hbc.symm, hτc]
  · obtain ⟨g, hg, hgσ⟩ := exists_even_conj_eq hσ π
    refine ⟨g, hg, ?_⟩
    rw [hgσ, ← hτ]
    calc τ = τ * ((swap a b * swap c d) * (swap a b * swap c d)) := by rw [hww, mul_one]
      _ = τ * (swap a b * swap c d) * (swap a b * swap c d) := (mul_assoc _ _ _).symm

end PermFour

section Transfer

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

theorem orderOf_perm_eq {y : G} (hy : y ∈ L) :
    orderOf ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = orderOf y := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]

theorem sign_perm_eq_one {y : G} (hy : y ∈ L) :
    Perm.sign ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = 1 :=
  Perm.mem_alternatingGroup.1 (e ⟨y, hy⟩).2

theorem exists_conj_perm {y : G} (hy : y ∈ L) {g : Perm (Fin n)} (hg : Perm.sign g = 1) :
    ∃ l ∈ L, ∃ hl : l * y * l⁻¹ ∈ L,
      ((e ⟨l * y * l⁻¹, hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        g * ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) * g⁻¹ := by
  set a : L := e.symm ⟨g, Perm.mem_alternatingGroup.2 hg⟩ with ha
  refine ⟨a, a.2, mul_mem (mul_mem a.2 hy) (inv_mem a.2), ?_⟩
  have h1 : (⟨(a : G) * y * (a : G)⁻¹, mul_mem (mul_mem a.2 hy) (inv_mem a.2)⟩ : L) =
      a * ⟨y, hy⟩ * a⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, ha, MulEquiv.apply_symm_apply]
  rfl

theorem commute_of_perm_commute {x y : G} (hx : x ∈ L) (hy : y ∈ L)
    (h : ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
      ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
        ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) : x * y = y * x := by
  have h1 : (⟨x * y, mul_mem hx hy⟩ : L) = ⟨y * x, mul_mem hy hx⟩ := by
    apply e.injective
    apply Subtype.ext
    have e1 : (⟨x * y, mul_mem hx hy⟩ : L) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    have e2 : (⟨y * x, mul_mem hy hx⟩ : L) = ⟨y, hy⟩ * ⟨x, hx⟩ := rfl
    rw [e1, e2, map_mul, map_mul]
    exact h
  exact congrArg Subtype.val h1

theorem mem_centralizer_rootGroup {x : G} (hx : x ∈ L) (S : Finset (Fin n))
    (hfix : ∀ i ∈ S, ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i) :
    x ∈ centralizer (rootGroup e S : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ corr (X := G) e (altSub S) := hh
  obtain ⟨hhL, hhS⟩ := mem_corr.1 hh'
  refine commute_of_perm_commute e hhL hx ?_
  refine Perm.Disjoint.commute (fun i => ?_)
  by_cases hi : i ∈ S
  · exact Or.inr (hfix i hi)
  · exact Or.inl ((mem_altSub.1 hhS).2 i hi)

end Transfer

end FuseConj

open FuseConj

theorem farClass : FarClass := by
  intro G _ L n e y hy y' hy' hy2 hy'2 hn hn'
  have hσ := (orderOf_perm_eq e hy).trans hy2
  have hσ' := (orderOf_perm_eq e hy').trans hy'2
  have hf : Nat.card (Function.fixedPoints
      ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) < 4 := by
    by_contra h
    exact hn ⟨hy, not_lt.1 h⟩
  have hf' : Nat.card (Function.fixedPoints
      ((e ⟨y', hy'⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) < 4 := by
    by_contra h
    exact hn' ⟨hy', not_lt.1 h⟩
  have h1 := natCard_fixedPoints_eq_mod_four hσ (sign_perm_eq_one e hy) hf
  have h2 := natCard_fixedPoints_eq_mod_four hσ' (sign_perm_eq_one e hy') hf'
  obtain ⟨g, hg, hgσ⟩ := exists_even_conj hσ hσ' (h1.trans h2.symm)
  obtain ⟨l, hl, hl', hlσ⟩ := exists_conj_perm e hy hg
  refine ⟨l, hl, ?_⟩
  have h3 : (⟨l * y * l⁻¹, hl'⟩ : L) = ⟨y', hy'⟩ :=
    e.injective (Subtype.ext (hlσ.trans hgσ))
  exact congrArg Subtype.val h3

theorem nearCover (k : ℕ) : NearCover k := by
  intro G _ L n _ e S hS hk y hy hy2 hnear
  obtain ⟨hyL, h4⟩ := hnear
  have hσ := (orderOf_perm_eq e hyL).trans hy2
  obtain ⟨g, hg, hgfix⟩ := exists_even_perm_fixing hσ S (by rw [hS]; omega)
  obtain ⟨l, hl, hl', hlσ⟩ := exists_conj_perm e hyL hg
  refine ⟨l, hl, mem_centralizer_rootGroup e hl' S fun i hi => ?_⟩
  rw [hlσ]
  exact hgfix i hi

theorem rootCover : RootCover := by
  intro G _ L n hn e S hS
  obtain ⟨a, T, haT, rfl, hT⟩ := Finset.card_eq_succ.1 hS
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.1 hT
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haT
  obtain ⟨hab, hac, had⟩ := haT
  have hww := swap_mul_swap_mul_self hac had hbc hbd
  have hws := sign_swap_mul_swap hab hcd
  have hw1 : swap a b * swap c d ≠ 1 := by
    intro h
    have h1 := congrArg (fun f : Perm (Fin n) => f a) h
    simp only [swap_mul_swap_apply_fst hac had, Perm.one_apply] at h1
    exact hab h1.symm
  have hw2 : orderOf (swap a b * swap c d) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  have hSw : ∀ i ∉ ({a, b, c, d} : Finset (Fin n)), (swap a b * swap c d) i = i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact swap_mul_swap_apply_of_ne hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : L, e e₀ = ⟨swap a b * swap c d, Perm.mem_alternatingGroup.2 hws⟩ :=
    ⟨e.symm _, e.apply_symm_apply _⟩
  have he₀perm : ((e ⟨(e₀ : G), e₀.2⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      swap a b * swap c d := congrArg Subtype.val he₀
  have he₀ord : orderOf (e₀ : G) = 2 := by
    rw [← orderOf_perm_eq e e₀.2, he₀perm, hw2]
  have h4 : 4 ≤ Nat.card (Function.fixedPoints (swap a b * swap c d)) := by
    have := le_natCard_fixedPoints ({a, b, c, d} : Finset (Fin n)) hSw
    rw [Fintype.card_fin, hS] at this
    omega
  refine ⟨(e₀ : G), ?_, he₀ord, e₀.2, ?_, ?_⟩
  · show (e₀ : G) ∈ corr (X := G) e (altSub _)
    exact mem_corr.2 ⟨e₀.2, by rw [he₀perm]; exact mem_altSub.2 ⟨hws, hSw⟩⟩
  · exact nearCover 4 G L n (by omega) e _ hS le_rfl (e₀ : G) e₀.2 he₀ord
      ⟨e₀.2, by rw [he₀perm]; exact h4⟩
  · intro y hy hy2
    by_cases hnear : IsNear e y
    · obtain ⟨l, hl, hlc⟩ := nearCover 4 G L n (by omega) e _ hS le_rfl y hy hy2 hnear
      exact ⟨l, hl, Or.inl hlc⟩
    · have hσ := (orderOf_perm_eq e hy).trans hy2
      have hF : Nat.card (Function.fixedPoints
          ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) < 4 := by
        by_contra h
        exact hnear ⟨hy, not_lt.1 h⟩
      obtain ⟨b', hb's, hb'b', hb'ne, hb'fix, g, hg, hgσ⟩ := exists_far_decomp hσ
        (sign_perm_eq_one e hy) hF hab hac had hbc hbd hcd (by rw [Fintype.card_fin]; omega)
      obtain ⟨l, hl, hl', hlσ⟩ := exists_conj_perm e hy hg
      obtain ⟨b₀, hb₀⟩ : ∃ b₀ : L, e b₀ = ⟨b', Perm.mem_alternatingGroup.2 hb's⟩ :=
        ⟨e.symm _, e.apply_symm_apply _⟩
      have hb₀perm : ((e ⟨(b₀ : G), b₀.2⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = b' :=
        congrArg Subtype.val hb₀
      have h5 : l * y * l⁻¹ = (b₀ : G) * e₀ := by
        have h6 : (⟨l * y * l⁻¹, hl'⟩ : L) = b₀ * e₀ := by
          apply e.injective
          apply Subtype.ext
          rw [map_mul]
          exact hlσ.trans (hgσ.trans (by rw [hb₀, he₀]; rfl))
        exact congrArg Subtype.val h6
      refine ⟨l, hl, Or.inr ⟨(b₀ : G), b₀.2, ?_, ?_, ?_, h5⟩⟩
      · refine mem_centralizer_rootGroup e b₀.2 _ fun i hi => ?_
        rw [hb₀perm]
        exact hb'fix i hi
      · rw [← orderOf_perm_eq e b₀.2, hb₀perm]
        exact orderOf_eq_prime (by rw [pow_two]; exact hb'b') hb'ne
      · intro h7
        rw [← h5, conj_eq_one_iff] at h7
        subst h7
        simp at hy2

end CFSG.OddStandard.AltStdSec
