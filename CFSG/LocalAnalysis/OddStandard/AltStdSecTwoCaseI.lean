module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRootOut

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section PermCases

variable {n : ℕ}

theorem swap_mul_swap_comm {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  apply Perm.Disjoint.commute
  intro i
  by_cases hi : i = a ∨ i = b
  · right
    rcases hi with rfl | rfl
    · exact swap_apply_of_ne_of_ne hac had
    · exact swap_apply_of_ne_of_ne hbc hbd
  · push Not at hi
    exact Or.inl (swap_apply_of_ne_of_ne hi.1 hi.2)

theorem apply_mem_of_comm_swap {s : Perm (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hs : swap i j * s = s * swap i j) : s i = i ∨ s i = j := by
  have h1 := congrArg (fun f : Perm (Fin n) => f i) hs
  simp only [Perm.mul_apply, swap_apply_left] at h1
  by_contra hcon
  push Not at hcon
  rw [swap_apply_of_ne_of_ne hcon.1 hcon.2] at h1
  exact hij (s.injective h1)

theorem perm_cases_of_forall_comm {e' s : Perm (Fin n)} (he2 : e' * e' = 1)
    (hs : ∀ π : Perm (Fin n), π * e' = e' * π → π * s = s * π) :
    s = 1 ∨ s = e' ∨ ∃ p q : Fin n, p ≠ q ∧ (∀ i, e' i = i ↔ i = p ∨ i = q) ∧
      (s = swap p q ∨ s = e' * swap p q) := by
  classical
  have hee : ∀ i, e' (e' i) = i := fun i => by
    have := congrArg (fun f : Perm (Fin n) => f i) he2
    simpa [Perm.mul_apply] using this
  have hse : e' * s = s * e' := hs e' rfl
  have hes : ∀ i, e' (s i) = s (e' i) := fun i => by
    have := congrArg (fun f : Perm (Fin n) => f i) hse
    simpa [Perm.mul_apply] using this
  have hswapF : ∀ i j, e' i = i → e' j = j → swap i j * e' = e' * swap i j := by
    intro i j hi hj
    rw [mul_swap_eq_swap_mul, hi, hj]
  have hswapP : ∀ i, swap i (e' i) * e' = e' * swap i (e' i) := by
    intro i
    rw [mul_swap_eq_swap_mul, hee i, swap_comm]
  have hpair : ∀ i, e' i ≠ i → s i = i ∨ s i = e' i := fun i hi =>
    apply_mem_of_comm_swap (Ne.symm hi) (hs _ (hswapP i))
  have hunif : (∀ i, e' i ≠ i → s i = i) ∨ (∀ i, e' i ≠ i → s i = e' i) := by
    by_cases hex : ∃ i₀, e' i₀ ≠ i₀
    · obtain ⟨i₀, hi₀⟩ := hex
      have key : ∀ j, e' j ≠ j → j ≠ i₀ → j ≠ e' i₀ →
          ∃ π : Perm (Fin n), π * e' = e' * π ∧ π i₀ = j ∧ π (e' i₀) = e' j := by
        intro j hj hji hje
        have hej : e' j ≠ i₀ := fun h' => hje (by rw [← h', hee])
        have heji : e' j ≠ e' i₀ := fun h' => hji (e'.injective h')
        refine ⟨swap i₀ j * swap (e' i₀) (e' j), ?_, ?_, ?_⟩
        · have h1 : e' * swap i₀ j = swap (e' i₀) (e' j) * e' := mul_swap_eq_swap_mul e' i₀ j
          have h2 : e' * swap (e' i₀) (e' j) = swap i₀ j * e' := by
            rw [mul_swap_eq_swap_mul, hee, hee]
          have hcomm : swap i₀ j * swap (e' i₀) (e' j) = swap (e' i₀) (e' j) * swap i₀ j :=
            swap_mul_swap_comm hi₀.symm hej.symm hje hj.symm
          calc swap i₀ j * swap (e' i₀) (e' j) * e' =
              swap (e' i₀) (e' j) * swap i₀ j * e' := by rw [hcomm]
            _ = swap (e' i₀) (e' j) * (e' * swap (e' i₀) (e' j)) := by rw [mul_assoc, ← h2]
            _ = (e' * swap i₀ j) * swap (e' i₀) (e' j) := by rw [← mul_assoc, ← h1]
            _ = e' * (swap i₀ j * swap (e' i₀) (e' j)) := by rw [mul_assoc]
        · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi₀.symm hej.symm, swap_apply_left]
        · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hej hj]
      rcases hpair i₀ hi₀ with h1 | h1
      · left
        intro j hj
        by_cases hji : j = i₀
        · rw [hji]; exact h1
        by_cases hje : j = e' i₀
        · rw [hje, ← hes, h1]
        obtain ⟨π, hπ, hπi, -⟩ := key j hj hji hje
        have := congrArg (fun f : Perm (Fin n) => f i₀) (hs π hπ)
        simp only [Perm.mul_apply, h1, hπi] at this
        exact this.symm
      · right
        intro j hj
        by_cases hji : j = i₀
        · rw [hji]; exact h1
        by_cases hje : j = e' i₀
        · rw [hje, ← hes, h1]
        obtain ⟨π, hπ, hπi, hπe⟩ := key j hj hji hje
        have := congrArg (fun f : Perm (Fin n) => f i₀) (hs π hπ)
        simp only [Perm.mul_apply, h1, hπi, hπe] at this
        exact this.symm
    · push Not at hex
      exact Or.inl fun i hi => absurd (hex i) hi
  set F : Finset (Fin n) := fixFin e' with hF
  have hsF : ∀ i ∈ F, s i ∈ F := by
    intro i hi
    rw [mem_fixFin] at hi ⊢
    rw [hes, hi]
  by_cases hF3 : 3 ≤ F.card
  ·
    have hfixF : ∀ i ∈ F, s i = i := by
      intro i hi
      have hcard : 2 ≤ (F.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
      obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 hcard
      rw [Finset.mem_erase] at hj hk
      have hiF : e' i = i := mem_fixFin.1 hi
      rcases apply_mem_of_comm_swap (Ne.symm hj.1)
          (hs _ (hswapF i j hiF (mem_fixFin.1 hj.2))) with h1 | h1
      · exact h1
      rcases apply_mem_of_comm_swap (Ne.symm hk.1)
          (hs _ (hswapF i k hiF (mem_fixFin.1 hk.2))) with h2 | h2
      · exact h2
      exact absurd (h1.symm.trans h2) hjk
    rcases hunif with hu | hu
    · left
      ext i
      by_cases hi : e' i = i
      · exact congrArg Fin.val (hfixF i (mem_fixFin.2 hi))
      · exact congrArg Fin.val (hu i hi)
    · right; left
      ext i
      by_cases hi : e' i = i
      · rw [hfixF i (mem_fixFin.2 hi), hi]
      · rw [hu i hi]
  · by_cases hF2 : F.card = 2
    · obtain ⟨p, q, hpq, hFpq⟩ := Finset.card_eq_two.1 hF2
      have hpF : p ∈ F := by rw [hFpq]; simp
      have hqF : q ∈ F := by rw [hFpq]; simp
      have hiff : ∀ i, e' i = i ↔ i = p ∨ i = q := by
        intro i
        rw [← mem_fixFin, ← hF, hFpq]
        simp
      have hsp := apply_mem_of_comm_swap hpq
        (hs _ (hswapF p q (mem_fixFin.1 hpF) (mem_fixFin.1 hqF)))
      have hsq : s q = q ∨ s q = p := by
        rcases hsp with h1 | h1
        · left
          have := hsF q hqF
          rw [hFpq] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h2 | h2
          · exact absurd (s.injective (h2.trans h1.symm)) (Ne.symm hpq)
          · exact h2
        · right
          have := hsF q hqF
          rw [hFpq] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h2 | h2
          · exact h2
          · exact absurd (s.injective (h2.trans h1.symm)) (Ne.symm hpq)
      have hFact : (s p = p ∧ s q = q) ∨ (s p = q ∧ s q = p) := by
        rcases hsp with h1 | h1 <;> rcases hsq with h2 | h2
        · exact Or.inl ⟨h1, h2⟩
        · exact absurd (s.injective (h1.trans h2.symm)) hpq
        · exact absurd (s.injective (h1.trans h2.symm)) hpq
        · exact Or.inr ⟨h1, h2⟩
      have hother : ∀ i, i ≠ p → i ≠ q → e' i ≠ i := fun i hip hiq h' =>
        ((hiff i).1 h').elim hip hiq
      rcases hFact with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hunif with hu | hu
      · left
        ext i
        by_cases hip : i = p
        · rw [hip, h1]; rfl
        by_cases hiq : i = q
        · rw [hiq, h2]; rfl
        exact congrArg Fin.val (hu i (hother i hip hiq))
      · right; left
        ext i
        by_cases hip : i = p
        · rw [hip, h1, (hiff p).2 (Or.inl rfl)]
        by_cases hiq : i = q
        · rw [hiq, h2, (hiff q).2 (Or.inr rfl)]
        rw [hu i (hother i hip hiq)]
      · right; right
        refine ⟨p, q, hpq, hiff, Or.inl ?_⟩
        ext i
        by_cases hip : i = p
        · rw [hip, h1, swap_apply_left]
        by_cases hiq : i = q
        · rw [hiq, h2, swap_apply_right]
        rw [hu i (hother i hip hiq), swap_apply_of_ne_of_ne hip hiq]
      · right; right
        refine ⟨p, q, hpq, hiff, Or.inr ?_⟩
        ext i
        by_cases hip : i = p
        · rw [hip, h1, Perm.mul_apply, swap_apply_left, (hiff q).2 (Or.inr rfl)]
        by_cases hiq : i = q
        · rw [hiq, h2, Perm.mul_apply, swap_apply_right, (hiff p).2 (Or.inl rfl)]
        rw [hu i (hother i hip hiq), Perm.mul_apply, swap_apply_of_ne_of_ne hip hiq]
    ·
      have hfixF : ∀ i ∈ F, s i = i := by
        intro i hi
        have h1 := hsF i hi
        by_contra hne
        have : 1 < F.card := Finset.one_lt_card.2 ⟨s i, h1, i, hi, hne⟩
        omega
      rcases hunif with hu | hu
      · left
        ext i
        by_cases hi : e' i = i
        · exact congrArg Fin.val (hfixF i (mem_fixFin.2 hi))
        · exact congrArg Fin.val (hu i hi)
      · right; left
        ext i
        by_cases hi : e' i = i
        · rw [hfixF i (mem_fixFin.2 hi), hi]
        · rw [hu i hi]

end PermCases

section CaseI

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem centralizer_le_of_caseI (htri : ExactShapeTrichotomy) (h : Setting G L n)
    (d : Cyc L Q z) (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n)
    (hn12 : n ≠ 12) {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4)
    (hkn : S₀.card + 7 ≤ n)
    (hI : CaseIAt e z S₀) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) :
    centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨hx2, -, hx1⟩ := swap_elt_facts h d T e hx hτ
  have hzx : z ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]; exact (mem_centralizer_singleton_iff.1 hx).symm
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hnear : ∀ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b → b ≠ z →
      5 ≤ (fixFin (permOf h d e hb)).card → (fixFin (permOf h d e hb)).card ≠ 6 → False := by
    intro b hb hzb hbz h5 h6
    obtain ⟨c, hc⟩ := isConj_iff.1 hzb
    exact near_partner_false h d T e hk hkn hI hb hc hbz ⟨h5, h6⟩
  have hfus : ¬ IsConj z (z * x) := by
    intro hc
    have hzxC : z * x ∈ centralizer ({z} : Set G) := mul_mem hzC hx
    have hp : permOf h d e hzxC = permOf h d e hx := by
      rw [permOf_mul h d e hzC hx hzxC, permOf_self h d e hzC, one_mul]
    refine hnear (z * x) hzxC hc ?_ ?_ ?_
    · intro h'
      exact hx1 (mul_eq_left.1 h')
    · rw [hp, card_fixFin_of_isSwap hτ]; omega
    · rw [hp, card_fixFin_of_isSwap hτ]; omega
  rcases twoSec_cases htri h d T e (by omega) hx hτ hfus hzx with h1 | ⟨b, hb, hzb, hbz, hcard⟩ | h1
  · exact h1
  · exfalso
    rcases hcard with h2 | h2 | h2 <;> exact hnear b hb hzb hbz (by omega) (by omega)
  · omega

theorem exists_swap_comm_ne {σ : Perm (Fin n)} (hn : 4 ≤ n) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ τ : Perm (Fin n), τ.IsSwap ∧ τ * σ = σ * τ ∧ τ ≠ σ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Perm.ext hcon)
  have hσσ : σ (σ i) = i := by
    have := congrArg (fun f : Perm (Fin n) => f i) hσ2
    simpa [Perm.mul_apply] using this
  have hcomm : swap i (σ i) * σ = σ * swap i (σ i) := by
    rw [mul_swap_eq_swap_mul, hσσ, swap_comm]
  by_cases hne : swap i (σ i) = σ
  ·
    have hcard : 1 < ((Finset.univ.erase i).erase (σ i)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.1 hcard
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk hl
    refine ⟨swap k l, ⟨k, l, hkl, rfl⟩, ?_, ?_⟩
    · rw [← hne]
      exact swap_mul_swap_comm hk.2 hk.1 hl.2 hl.1
    · intro h'
      rw [← hne] at h'
      have := congrArg (fun f : Perm (Fin n) => f k) h'
      simp only [swap_apply_left, swap_apply_of_ne_of_ne hk.2 hk.1] at this
      exact hkl this.symm
  · exact ⟨swap i (σ i), ⟨i, σ i, hi.symm, rfl⟩, hcomm, hne⟩

theorem false_of_caseI_of_claim (h : Setting G L n) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n)
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hI : CaseIAt e z S₀)
    (hclaim : ∀ {x : G} (hx : x ∈ centralizer ({z} : Set G)), (permOf h d e hx).IsSwap →
      centralizer ({x} : Set G) ≤ centralizer ({z} : Set G)) : False := by
  classical
  have hz2 : z * z = 1 := d.mul_self
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hz1 : z ≠ 1 := fun h1 => by have := d.order; rw [h1, orderOf_one] at this; omega
  have hnear : ∀ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b → b ≠ z →
      7 ≤ (fixFin (permOf h d e hb)).card → False := by
    intro b hb hzb hbz h7
    obtain ⟨c, hc⟩ := isConj_iff.1 hzb
    exact near_partner_false h d T e hk hkn hI hb hc hbz ⟨by omega, by omega⟩
  obtain ⟨g, hne, hcomm, -, -⟩ := exists_partner h d
  set c : G := g⁻¹ with hc
  set a : G := c * z * c⁻¹ with ha
  set a' : G := c⁻¹ * z * c with ha'
  have haeq : a = g⁻¹ * z * g := by rw [ha, hc, inv_inv]
  have haC : a ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff, haeq]; exact hcomm
  have haz : a ≠ z := by rw [haeq]; exact hne
  have ha'C : a' ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff, ha', hc, inv_inv]
    calc g * z * g⁻¹ * z = g * (z * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * z) * g⁻¹ := by rw [hcomm]
      _ = z * (g * z * g⁻¹) := by group
  have ha'z : a' ≠ z := by
    intro h'
    apply hne
    rw [ha', hc, inv_inv] at h'
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [h']
      _ = z := by group
  have ha'2 : a' * a' = 1 := by
    rw [ha']
    calc c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
      _ = 1 := by rw [hz2]; group
  have ha2 : a * a = 1 := by
    rw [ha]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  set σ' := permOf h d e ha'C with hσ'
  have hoC : (1 : G) ∈ centralizer ({z} : Set G) := one_mem _
  have hperm1 : permOf h d e hoC = 1 := by show rho e h.hn 1 = 1; exact map_one _
  have hι1 : (swapIota h d T e 1 : G) = 1 := by rw [map_one]; rfl
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    rcases eq_swapIota_or h d T e ha'C with h2 | h2
    · rw [← hσ', h1, hι1] at h2
      apply hz1
      calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
        _ = 1 := by rw [← ha', h2]; group
    · rw [← hσ', h1, hι1, mul_one] at h2
      exact ha'z h2
  have hσ'2 : σ' * σ' = 1 := by
    rw [hσ', ← permOf_mul h d e ha'C ha'C (mul_mem ha'C ha'C)]
    rw [permOf_congr' ha'2 (mul_mem ha'C ha'C) hoC h d e, hperm1]
  obtain ⟨τt, hτts, hτtc, hτtne⟩ := exists_swap_comm_ne (by omega) hσ'2 hσ'1
  set xt : G := (swapIota h d T e τt : G) with hxt
  have hxtC : xt ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e _
  have hpxt : permOf h d e hxtC = τt := permOf_swapIota h d T e _
  have hxta' : xt * a' = a' * xt :=
    comm_of_permOf_comm h d T.card e hxtC ha'C (by rw [hpxt]; exact hτtc)
  have hxt2 : xt * xt = 1 := by
    have : swapIota h d T e τt * swapIota h d T e τt = 1 := by
      rw [← map_mul]
      obtain ⟨p, q, _, hpq⟩ := hτts
      rw [hpq, swap_mul_self, map_one]
    exact congrArg Subtype.val this
  set ea : G := c * xt * c⁻¹ with hea
  have heaC : ea ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff, hea]
    calc c * xt * c⁻¹ * z = c * (xt * (c⁻¹ * z * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * z * c) * xt) * c⁻¹ := by rw [← ha', hxta']
      _ = z * (c * xt * c⁻¹) := by group
  have hconjle : ∀ w : G, (centralizer ({w} : Set G) ≤ centralizer ({z} : Set G)) →
      centralizer ({c * w * c⁻¹} : Set G) ≤ centralizer ({a} : Set G) := by
    intro w hw y hy
    have h1 : c⁻¹ * y * c ∈ centralizer ({w} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hy ⊢
      calc c⁻¹ * y * c * w = c⁻¹ * (y * (c * w * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * w * c⁻¹) * y) * c := by rw [hy]
        _ = w * (c⁻¹ * y * c) := by group
    have h2 := mem_centralizer_singleton_iff.1 (hw h1)
    rw [mem_centralizer_singleton_iff, ha]
    calc y * (c * z * c⁻¹) = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [h2]
      _ = c * z * c⁻¹ * y := by group
  have hea_le : centralizer ({ea} : Set G) ≤ centralizer ({a} : Set G) :=
    hconjle xt (hclaim hxtC (by rw [hpxt]; exact hτts))
  set s := permOf h d e haC with hs
  set e' := permOf h d e heaC with he'
  have hι_mem : ∀ π₀ : Perm (Fin n), ((swapIota h d T e π₀ : ↥(L ⊔ zpowers u)) : G) ∈
      centralizer ({z} : Set G) := fun π₀ => swapIota_mem_centralizer h d T e π₀
  have hcomm_of : ∀ (w : G) (hw : w ∈ centralizer ({z} : Set G)),
      centralizer ({w} : Set G) ≤ centralizer ({a} : Set G) →
      ∀ π₀ : Perm (Fin n), π₀ * permOf h d e hw = permOf h d e hw * π₀ → π₀ * s = s * π₀ := by
    intro w hw hle π₀ hπ₀
    have h1 : ((swapIota h d T e π₀ : ↥(L ⊔ zpowers u)) : G) * w =
        w * (swapIota h d T e π₀ : G) :=
      comm_of_permOf_comm h d T.card e (hι_mem π₀) hw (by rw [permOf_swapIota]; exact hπ₀)
    have h2 := mem_centralizer_singleton_iff.1
      (hle (mem_centralizer_singleton_iff.2 h1))
    have hm1 := mul_mem (hι_mem π₀) haC
    have hm2 := mul_mem haC (hι_mem π₀)
    have h4 : permOf h d e hm1 = permOf h d e hm2 := permOf_congr' h2 hm1 hm2 h d e
    rw [permOf_mul h d e (hι_mem π₀) haC hm1, permOf_mul h d e haC (hι_mem π₀) hm2,
      permOf_swapIota] at h4
    exact h4
  have hea2 : ea * ea = 1 := by
    rw [hea]
    calc c * xt * c⁻¹ * (c * xt * c⁻¹) = c * (xt * xt) * c⁻¹ := by group
      _ = 1 := by rw [hxt2]; group
  have he'2 : e' * e' = 1 := by
    rw [he', ← permOf_mul h d e heaC heaC (mul_mem heaC heaC),
      permOf_congr' hea2 (mul_mem heaC heaC) hoC h d e, hperm1]
  have hcase := perm_cases_of_forall_comm he'2 (hcomm_of ea heaC hea_le)
  rcases hcase with hs1 | hse | ⟨p, q, hpq, hfix, hs3 | hs4⟩
  ·
    rcases eq_swapIota_or h d T e haC with h1 | h1
    · rw [← hs, hs1, hι1] at h1
      apply hz1
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = 1 := by rw [← ha, h1]; group
    · rw [← hs, hs1, hι1, mul_one] at h1
      exact haz h1
  ·
    have hxtz : xt ≠ z := by
      intro h'
      have := permOf_congr' h' hxtC hzC h d e
      rw [hpxt, permOf_self h d e hzC] at this
      obtain ⟨p, q, hpq, hpqe⟩ := hτts
      rw [this] at hpqe
      have h2 := congrArg (fun f : Perm (Fin n) => f p) hpqe
      simp only [Perm.one_apply, swap_apply_left] at h2
      exact hpq h2
    have hι : (swapIota h d T e s : G) = swapIota h d T e e' := by rw [hse]
    have hcases : a = ea ∨ a = z * ea := by
      rcases eq_swapIota_or h d T e haC with h1 | h1 <;>
        rcases eq_swapIota_or h d T e heaC with h2 | h2
      · left; rw [h1, h2, ← hs, ← he', hι]
      · right; rw [h1, h2, ← hs, ← he', hι, ← mul_assoc, hz2, one_mul]
      · right; rw [h1, h2, ← hs, ← he', hι]
      · left; rw [h1, h2, ← hs, ← he', hι]
    rcases hcases with h1 | h1
    · apply hxtz
      calc xt = c⁻¹ * (c * xt * c⁻¹) * c := by group
        _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [← hea, ← h1]
        _ = z := by group
    ·
      have h2 : xt = a' * z := by
        have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        calc xt = c⁻¹ * (c * xt * c⁻¹) * c := by group
          _ = c⁻¹ * (z⁻¹ * (c * z * c⁻¹)) * c := by rw [← hea, ← ha, h1]; group
          _ = a' * z := by rw [ha', hzinv]; group
      have hm := mul_mem ha'C hzC
      have h3 := permOf_congr' h2 hxtC hm h d e
      rw [hpxt, permOf_mul h d e ha'C hzC hm, permOf_self h d e hzC, mul_one] at h3
      exact hτtne h3
  ·
    have hsw : s.IsSwap := ⟨p, q, hpq, hs3⟩
    exact hnear a haC (isConj_iff.2 ⟨c, ha.symm⟩) haz
      (by rw [← hs, card_fixFin_of_isSwap hsw]; omega)
  ·
    have hep : e' * swap p q = swap p q * e' := by
      rw [mul_swap_eq_swap_mul, (hfix p).2 (Or.inl rfl), (hfix q).2 (Or.inr rfl)]
    set y : G := a * ea with hy
    have hyC : y ∈ centralizer ({z} : Set G) := mul_mem haC heaC
    have hpy : permOf h d e hyC = swap p q := by
      rw [permOf_mul h d e haC heaC hyC, ← hs, ← he', hs4, mul_assoc, ← hep, ← mul_assoc, he'2,
        one_mul]
    have hpqs : (swap p q).IsSwap := ⟨p, q, hpq, rfl⟩
    have hzxt : z * xt ∈ centralizer ({z} : Set G) := mul_mem hzC hxtC
    have hpzxt : permOf h d e hzxt = τt := by
      rw [permOf_mul h d e hzC hxtC hzxt, permOf_self h d e hzC, one_mul, hpxt]
    have hyeq : c * (z * xt) * c⁻¹ = y := by rw [hy, ha, hea]; group
    have hy_le : centralizer ({y} : Set G) ≤ centralizer ({a} : Set G) := by
      have := hconjle (z * xt) (hclaim hzxt (by rw [hpzxt]; exact hτts))
      rwa [hyeq] at this
    have hcase2 := perm_cases_of_forall_comm (e' := swap p q) (swap_mul_self p q)
      (fun π₀ hπ₀ => hcomm_of y hyC hy_le π₀ (by rw [hpy]; exact hπ₀))
    have hfixcard : (fixFin e').card = 2 := by
      have : fixFin e' = {p, q} := by
        ext i
        rw [mem_fixFin, hfix]
        simp
      rw [this, Finset.card_pair hpq]
    rcases hcase2 with h1 | h1 | ⟨p', q', hpq', hfix', -⟩
    ·
      have : e' = swap p q := by
        rw [hs4] at h1
        calc e' = e' * swap p q * swap p q := by rw [mul_assoc, swap_mul_self, mul_one]
          _ = swap p q := by rw [h1, one_mul]
      rw [this, card_fixFin_of_isSwap hpqs] at hfixcard
      omega
    ·
      have : e' = 1 := by
        rw [hs4] at h1
        calc e' = e' * swap p q * swap p q := by rw [mul_assoc, swap_mul_self, mul_one]
          _ = 1 := by rw [h1, swap_mul_self]
      rw [this] at hfixcard
      have : fixFin (1 : Perm (Fin n)) = Finset.univ := by ext i; simp [mem_fixFin]
      rw [this, Finset.card_univ, Fintype.card_fin] at hfixcard
      omega
    ·
      have h2 : (fixFin (swap p q)).card = 2 := by
        have : fixFin (swap p q) = {p', q'} := by
          ext i
          rw [mem_fixFin, hfix']
          simp
        rw [this, Finset.card_pair hpq']
      rw [card_fixFin_of_isSwap hpqs] at h2
      omega

theorem false_of_caseI (htri : ExactShapeTrichotomy) (h : Setting G L n) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) (hn12 : n ≠ 12)
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hI : CaseIAt e z S₀) : False :=
  false_of_caseI_of_claim h d T e (by omega) hk hkn hI
    fun hx hτ => centralizer_le_of_caseI htri h d T e hn hn12 hk hkn hI hx hτ

end CaseI

end CFSG.OddStandard.AltStdSec
