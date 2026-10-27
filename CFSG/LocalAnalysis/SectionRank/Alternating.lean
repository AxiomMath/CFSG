module

public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.SectionRank

open CFSG.Open Equiv

variable {n : ℕ}

theorem threeCycle_apply_of_ne {α : Type*} [DecidableEq α] {a b c x : α} (ha : x ≠ a)
    (hb : x ≠ b) (hc : x ≠ c) : (swap a b * swap a c) x = x := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha hc, swap_apply_of_ne_of_ne ha hb]

abbrev blk (hn : 9 ≤ n) (k j : Fin 3) : Fin n := ⟨3 * k + j, by omega⟩

theorem blk_ne (hn : 9 ≤ n) (k : Fin 3) {i j : Fin 3} (h : i ≠ j) : blk hn k i ≠ blk hn k j := by
  intro he
  apply h
  rw [Fin.ext_iff] at he ⊢
  simp only at he
  omega

theorem blk_ne_blk (hn : 9 ≤ n) {k l : Fin 3} (h : k ≠ l) (i j : Fin 3) :
    blk hn k i ≠ blk hn l j := by
  intro he
  apply h
  rw [Fin.ext_iff] at he ⊢
  simp only at he
  omega

@[expose] def cycPerm (hn : 9 ≤ n) (k : Fin 3) : Perm (Fin n) :=
  swap (blk hn k 0) (blk hn k 1) * swap (blk hn k 0) (blk hn k 2)

theorem isThreeCycle_cycPerm (hn : 9 ≤ n) (k : Fin 3) : (cycPerm hn k).IsThreeCycle :=
  Perm.isThreeCycle_swap_mul_swap_same (blk_ne hn k (by decide)) (blk_ne hn k (by decide))
    (blk_ne hn k (by decide))

@[expose] def cyc (hn : 9 ≤ n) (k : Fin 3) : alternatingGroup (Fin n) :=
  ⟨cycPerm hn k, Perm.mem_alternatingGroup.2 (isThreeCycle_cycPerm hn k).sign⟩

theorem cyc_pow_three (hn : 9 ≤ n) (k : Fin 3) : cyc hn k ^ 3 = 1 := by
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← (isThreeCycle_cycPerm hn k).orderOf]
  exact pow_orderOf_eq_one _

theorem cyc_apply_of_ne (hn : 9 ≤ n) (k : Fin 3) {x : Fin n} (hx : ∀ j, x ≠ blk hn k j) :
    (cyc hn k : Perm (Fin n)) x = x :=
  threeCycle_apply_of_ne (hx 0) (hx 1) (hx 2)

theorem cyc_apply_ne (hn : 9 ≤ n) (k : Fin 3) :
    (cyc hn k : Perm (Fin n)) (blk hn k 0) ≠ blk hn k 0 := by
  change cycPerm hn k (blk hn k 0) ≠ blk hn k 0
  rw [cycPerm, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (blk_ne hn k (by decide))
    (blk_ne hn k (by decide))]
  exact blk_ne hn k (by decide)

theorem cyc_commute (hn : 9 ≤ n) {k l : Fin 3} (hkl : k ≠ l) : Commute (cyc hn k) (cyc hn l) := by
  have hd : Perm.Disjoint (cyc hn k : Perm (Fin n)) (cyc hn l) := by
    intro x
    by_cases hx : ∃ j, x = blk hn k j
    · right
      obtain ⟨j, rfl⟩ := hx
      exact cyc_apply_of_ne hn l fun j' => blk_ne_blk hn hkl j j'
    · left
      push Not at hx
      exact cyc_apply_of_ne hn k hx
  exact Subtype.ext hd.commute.eq

theorem cyc_pow_apply (hn : 9 ≤ n) (k : Fin 3) (m : ℕ) {x : Fin n} (hx : ∀ j, x ≠ blk hn k j) :
    ((cyc hn k ^ m : alternatingGroup (Fin n)) : Perm (Fin n)) x = x := by
  rw [SubgroupClass.coe_pow]
  exact Perm.pow_apply_eq_self_of_apply_eq_self (cyc_apply_of_ne hn k hx) m

theorem three_le_pRank_alternating (hn : 9 ≤ n) :
    3 ≤ pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set G := alternatingGroup (Fin n)
  set F₀ : Unit →* G := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hnot : ∀ {k : Fin 3} {g : G}, (g : Perm (Fin n)) (blk hn k 0) = blk hn k 0 →
      g ≠ cyc hn k := by
    rintro k g hg rfl
    exact cyc_apply_ne hn k hg
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := exists_extend (fun a b => Subsingleton.elim _ _)
    (fun a => Subsingleton.elim _ _) (k := 0) (by simp) F₀ hF₀ (y := cyc hn 0) (cyc_pow_three hn 0)
    (by
      rintro ⟨b, hb⟩
      exact hnot (k := 0) (g := F₀ b) (by simp [F₀]) hb)
    (fun b => by simp [F₀])
  have hF₁ap : ∀ b, (F₁ b : Perm (Fin n)) (blk hn 1 0) = blk hn 1 0 ∧
      (F₁ b : Perm (Fin n)) (blk hn 2 0) = blk hn 2 0 := by
    intro b
    obtain ⟨b', m, hb⟩ := hr₁ b
    rw [hb]
    simp only [F₀, MonoidHom.one_apply, one_mul]
    exact ⟨cyc_pow_apply hn 0 m fun j => blk_ne_blk hn (by decide) 0 j,
      cyc_pow_apply hn 0 m fun j => blk_ne_blk hn (by decide) 0 j⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := exists_extend hc₁ hp₁ hcard₁ F₁ hF₁
    (y := cyc hn 1) (cyc_pow_three hn 1)
    (by
      rintro ⟨b, hb⟩
      exact hnot (k := 1) (g := F₁ b) (hF₁ap b).1 hb)
    (fun b => by
      obtain ⟨b', m, hb⟩ := hr₁ b
      rw [hb]
      simp only [F₀, MonoidHom.one_apply, one_mul]
      exact (cyc_commute hn (by decide)).pow_left m)
  have hF₂ap : ∀ b, (F₂ b : Perm (Fin n)) (blk hn 2 0) = blk hn 2 0 := by
    intro b
    obtain ⟨b', m, hb⟩ := hr₂ b
    rw [hb, Subgroup.coe_mul, Perm.mul_apply,
      cyc_pow_apply hn 1 m fun j => blk_ne_blk hn (by decide) 0 j]
    exact (hF₁ap b').2
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, -⟩ := exists_extend hc₂ hp₂ hcard₂ F₂ hF₂
    (y := cyc hn 2) (cyc_pow_three hn 2)
    (by
      rintro ⟨b, hb⟩
      exact hnot (k := 2) (g := F₂ b) (hF₂ap b) hb)
    (fun b => by
      obtain ⟨b', m, hb⟩ := hr₂ b
      obtain ⟨b'', m', hb'⟩ := hr₁ b'
      rw [hb, hb']
      simp only [F₀, MonoidHom.one_apply, one_mul]
      exact ((cyc_commute hn (by decide)).pow_left m').mul_left
        ((cyc_commute hn (by decide)).pow_left m))
  exact le_pRank_of_injective (by norm_num) hc₃ hp₃ hcard₃ F₃ hF₃ le_top

theorem pRank_alternating_le_two (hn : n ≤ 8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    pRank p (⊤ : Subgroup (alternatingGroup (Fin n))) ≤ 2 := by
  refine pRank_le hp.one_lt fun E _ hE => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card E = p ^ k :=
    IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE.2 _ g.2)⟩
  rw [hk]
  by_contra hlt
  push Not at hlt
  have h3 : p ^ 3 ∣ p ^ k := Nat.pow_dvd_pow p (by
    by_contra h
    push Not at h
    have : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    omega)
  have hdvd : p ^ 3 ∣ Nat.factorial 8 := by
    have h1 : Nat.card E ∣ Nat.card (alternatingGroup (Fin n)) := Subgroup.card_subgroup_dvd_card E
    have h2 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial n := by
      have := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
      rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact h3.trans (hk ▸ h1 |>.trans (h2.trans (Nat.factorial_dvd_factorial hn)))
  have hp3 : p ^ 3 ≤ Nat.factorial 8 := Nat.le_of_dvd (Nat.factorial_pos 8) hdvd
  have hp34 : p ≤ 34 := by
    by_contra h
    push Not at h
    have : 35 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left h 3
    have h8 : Nat.factorial 8 = 40320 := by decide
    omega
  interval_cases p <;> simp_all (config := { decide := true })

end CFSG.SectionRank
