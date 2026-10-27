module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma fin6_symmDiff_pair_same (j a b : Fin 6) (hab : a ≠ b) (haj : a ≠ j)
    (hbj : b ≠ j) :
    symmDiff ({j, a} : Finset (Fin 6)) ({j, b} : Finset (Fin 6)) = {a, b} := by
  revert j a b
  decide

private lemma fin6_symmDiff_pairs (a b c d : Fin 6) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    symmDiff ({a, b} : Finset (Fin 6)) ({c, d} : Finset (Fin 6)) = {a, b, c, d} := by
  revert a b c d
  decide

private lemma symmDiff_eq_sdiff_of_subset {K P : Finset (Fin 6)} (h : P ⊆ K) :
    symmDiff K P = K \ P := by
  rw [symmDiff_eq_sup_sdiff_inf]
  change (K ∪ P) \ (K ∩ P) = K \ P
  rw [Finset.union_eq_left.mpr h, Finset.inter_eq_right.mpr h]

private lemma exists_pair_notMem {X : Finset (Fin 6)} (hX : X.card ≤ 4) :
    ∃ c d : Fin 6, c ≠ d ∧ c ∉ X ∧ d ∉ X := by
  have h2 : 1 < Xᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp h2
  exact ⟨c, d, hcd, Finset.mem_compl.mp hc, Finset.mem_compl.mp hd⟩

private lemma exists_pair_of_mem_card_two {T : Finset (Fin 6)} {j : Fin 6}
    (hcard : T.card = 2) (hj : j ∈ T) : ∃ e : Fin 6, e ≠ j ∧ T = {j, e} := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h
  · subst h; exact ⟨q, Ne.symm hpq, rfl⟩
  · subst h; exact ⟨p, hpq, by rw [Finset.pair_comm]⟩

theorem sec9ci_comb {n : ℕ} (hn : n = 6) (j : Fin n) (𝒮 : Set (Finset (Fin n)))
    (hev : ∀ S ∈ 𝒮, Even S.card) (hsd : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, symmDiff S S' ∈ 𝒮)
    (hcompl : ∀ S ∈ 𝒮, Sᶜ ∈ 𝒮)
    (hperm : ∀ u v w z : Fin n, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      u ≠ j → v ≠ j → w ≠ j → z ≠ j →
      ∀ S ∈ 𝒮, S.map (Equiv.swap u v * Equiv.swap w z).toEmbedding ∈ 𝒮)
    (hne : ∃ S ∈ 𝒮, S ≠ ∅ ∧ S ≠ Finset.univ) :
    ∀ S : Finset (Fin n), Even S.card → S ∈ 𝒮 := by
  subst hn
  obtain ⟨S₀, hS₀, hS₀ne, hS₀neuniv⟩ := hne
  have hpair : ∃ x y : Fin 6, x ≠ y ∧ ({x, y} : Finset (Fin 6)) ∈ 𝒮 := by
    have hcard : S₀.card = 2 ∨ S₀.card = 4 := by
      obtain ⟨k, hk⟩ := hev S₀ hS₀
      have hle : S₀.card ≤ 6 := by simpa using Finset.card_le_univ S₀
      have h0 : S₀.card ≠ 0 := fun h => hS₀ne (Finset.card_eq_zero.mp h)
      have h6 : S₀.card ≠ 6 :=
        fun h => hS₀neuniv (Finset.eq_univ_of_card S₀ (by simpa using h))
      omega
    rcases hcard with h2 | h4
    · obtain ⟨x, y, hxy, hxy_eq⟩ := Finset.card_eq_two.mp h2
      exact ⟨x, y, hxy, hxy_eq ▸ hS₀⟩
    · have hc : S₀ᶜ ∈ 𝒮 := hcompl S₀ hS₀
      have hc2 : S₀ᶜ.card = 2 := by rw [Finset.card_compl, Fintype.card_fin]; omega
      obtain ⟨x, y, hxy, hxy_eq⟩ := Finset.card_eq_two.mp hc2
      exact ⟨x, y, hxy, hxy_eq ▸ hc⟩
  have move : ∀ x y z : Fin 6, x ≠ y → y ≠ j → z ≠ x → z ≠ y → z ≠ j →
      ({x, y} : Finset (Fin 6)) ∈ 𝒮 → ({x, z} : Finset (Fin 6)) ∈ 𝒮 := by
    intro x y z hxy hyj hzx hzy hzj hmem
    have hX : ({x, y, z, j} : Finset (Fin 6)).card ≤ 4 := Finset.card_le_four
    obtain ⟨c, d, hcd, hc, hd⟩ := exists_pair_notMem hX
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
    have hx : (Equiv.swap y z * Equiv.swap c d) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hc.1) (Ne.symm hd.1),
        Equiv.swap_apply_of_ne_of_ne hxy (Ne.symm hzx)]
    have hy : (Equiv.swap y z * Equiv.swap c d) y = z := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hc.2.1) (Ne.symm hd.2.1),
        Equiv.swap_apply_left]
    have hmap : ({x, y} : Finset (Fin 6)).map
        (Equiv.swap y z * Equiv.swap c d).toEmbedding = {x, z} := by
      rw [show ({x, y} : Finset (Fin 6)) = insert x {y} by rfl, Finset.map_insert,
        Finset.map_singleton]
      simp only [Equiv.coe_toEmbedding, hx, hy]
    have hres := hperm y z c d (Ne.symm hzy) (Ne.symm hc.2.1) (Ne.symm hd.2.1)
      (Ne.symm hc.2.2.1) (Ne.symm hd.2.2.1) hcd hyj hzj hc.2.2.2 hd.2.2.2 {x, y} hmem
    rwa [hmap] at hres
  have move' : ∀ x y z : Fin 6, x ≠ y → y ≠ j → z ≠ x → z ≠ j →
      ({x, y} : Finset (Fin 6)) ∈ 𝒮 → ({x, z} : Finset (Fin 6)) ∈ 𝒮 := by
    intro x y z hxy hyj hzx hzj hmem
    by_cases hzy : z = y
    · subst hzy; exact hmem
    · exact move x y z hxy hyj hzx hzy hzj hmem
  obtain ⟨x₀, y₀, hx₀y₀, hP₀⟩ := hpair
  have hallpairs : ∀ a b : Fin 6, a ≠ b → ({a, b} : Finset (Fin 6)) ∈ 𝒮 := by
    by_cases hj : j ∈ ({x₀, y₀} : Finset (Fin 6))
    · have hj' : ∃ y : Fin 6, y ≠ j ∧ ({j, y} : Finset (Fin 6)) ∈ 𝒮 := by
        rw [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hxj | hyj
        · subst hxj
          exact ⟨y₀, hx₀y₀.symm, hP₀⟩
        · subst hyj
          exact ⟨x₀, hx₀y₀, by rwa [Finset.pair_comm]⟩
      obtain ⟨y, hyj, hjy⟩ := hj'
      have hthrough : ∀ z : Fin 6, z ≠ j → ({j, z} : Finset (Fin 6)) ∈ 𝒮 := by
        intro z hzj
        by_cases hzy : z = y
        · subst hzy; exact hjy
        · exact move j y z hyj.symm hyj hzj hzy hzj hjy
      intro a b hab
      by_cases haj : a = j
      · rw [haj] at hab ⊢
        exact hthrough b (Ne.symm hab)
      · by_cases hbj : b = j
        · rw [hbj] at hab ⊢
          simpa [Finset.pair_comm] using hthrough a haj
        · have hres := hsd _ (hthrough a haj) _ (hthrough b hbj)
          rwa [fin6_symmDiff_pair_same j a b hab haj hbj] at hres
    · have hj'' : j ≠ x₀ ∧ j ≠ y₀ := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hj
      have hx₀j : x₀ ≠ j := Ne.symm hj''.1
      have hy₀j : y₀ ≠ j := Ne.symm hj''.2
      have hx₀move : ∀ c : Fin 6, c ≠ j → c ≠ x₀ → c ≠ y₀ →
          ({x₀, c} : Finset (Fin 6)) ∈ 𝒮 :=
        fun c hcj hcx hcy => move' x₀ y₀ c hx₀y₀ hy₀j hcx hcj hP₀
      have hy₀move : ∀ c : Fin 6, c ≠ j → c ≠ x₀ → c ≠ y₀ →
          ({y₀, c} : Finset (Fin 6)) ∈ 𝒮 :=
        fun c hcj hcx hcy =>
          move' y₀ x₀ c hx₀y₀.symm hx₀j hcy hcj (by simpa [Finset.pair_comm] using hP₀)
      have havoid : ∀ a b : Fin 6, a ≠ b → a ≠ j → b ≠ j →
          ({a, b} : Finset (Fin 6)) ∈ 𝒮 := by
        intro a b hab haj hbj
        by_cases haP : a ∈ ({x₀, y₀} : Finset (Fin 6))
        · rw [Finset.mem_insert, Finset.mem_singleton] at haP
          rcases haP with hax | hay
          · rw [hax] at hab haj ⊢
            by_cases hbP : b ∈ ({x₀, y₀} : Finset (Fin 6))
            · rw [Finset.mem_insert, Finset.mem_singleton] at hbP
              rcases hbP with hbx | hby
              · exact absurd hbx.symm hab
              · rw [hby]; exact hP₀
            · rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hbP
              exact hx₀move b hbj hbP.1 hbP.2
          · rw [hay] at hab haj ⊢
            by_cases hbP : b ∈ ({x₀, y₀} : Finset (Fin 6))
            · rw [Finset.mem_insert, Finset.mem_singleton] at hbP
              rcases hbP with hbx | hby
              · rw [hbx]; simpa [Finset.pair_comm] using hP₀
              · exact absurd hby.symm hab
            · rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hbP
              exact hy₀move b hbj hbP.1 hbP.2
        · rw [Finset.mem_insert, Finset.mem_singleton, not_or] at haP
          by_cases hbP : b ∈ ({x₀, y₀} : Finset (Fin 6))
          · rw [Finset.mem_insert, Finset.mem_singleton] at hbP
            rcases hbP with hbx | hby
            · rw [hbx]; simpa [Finset.pair_comm] using hx₀move a haj haP.1 haP.2
            · rw [hby]; simpa [Finset.pair_comm] using hy₀move a haj haP.1 haP.2
          · rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hbP
            have h1 : ({x₀, a} : Finset (Fin 6)) ∈ 𝒮 := hx₀move a haj haP.1 haP.2
            have h1' : ({a, x₀} : Finset (Fin 6)) ∈ 𝒮 := by rwa [Finset.pair_comm] at h1
            exact move' a x₀ b haP.1 hx₀j hab.symm hbj h1'
      have hK : (({x₀, y₀} : Finset (Fin 6))ᶜ) ∈ 𝒮 := hcompl _ hP₀
      have hKcard : (({x₀, y₀} : Finset (Fin 6))ᶜ).card = 4 := by
        rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hx₀y₀]
      have hjK : j ∈ (({x₀, y₀} : Finset (Fin 6))ᶜ) := Finset.mem_compl.mpr hj
      have hcard3 : ((({x₀, y₀} : Finset (Fin 6))ᶜ).erase j).card = 3 := by
        rw [Finset.card_erase_of_mem hjK, hKcard]
      have h1lt : 1 < ((({x₀, y₀} : Finset (Fin 6))ᶜ).erase j).card := by omega
      obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp h1lt
      rw [Finset.mem_erase] at hc hd
      have hsub : ({c, d} : Finset (Fin 6)) ⊆ (({x₀, y₀} : Finset (Fin 6))ᶜ) := by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hc.2
        · exact hd.2
      have hT : symmDiff (({x₀, y₀} : Finset (Fin 6))ᶜ) ({c, d} : Finset (Fin 6)) ∈ 𝒮 :=
        hsd _ hK _ (havoid c d hcd hc.1 hd.1)
      rw [symmDiff_eq_sdiff_of_subset hsub] at hT
      have hTcard : ((({x₀, y₀} : Finset (Fin 6))ᶜ) \ ({c, d} : Finset (Fin 6))).card = 2 := by
        rw [Finset.card_sdiff_of_subset hsub, hKcard, Finset.card_pair hcd]
      have hjT : j ∈ (({x₀, y₀} : Finset (Fin 6))ᶜ) \ ({c, d} : Finset (Fin 6)) := by
        rw [Finset.mem_sdiff]
        refine ⟨hjK, ?_⟩
        rw [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hc.1, Ne.symm hd.1⟩
      obtain ⟨e, hej, heq⟩ := exists_pair_of_mem_card_two hTcard hjT
      have hje : ({j, e} : Finset (Fin 6)) ∈ 𝒮 := heq ▸ hT
      intro a b hab
      by_cases haj : a = j
      · rw [haj] at hab ⊢
        by_cases hbe : b = e
        · rw [hbe]; exact hje
        · exact move' j e b hej.symm hej hab.symm hab.symm hje
      · by_cases hbj : b = j
        · rw [hbj] at hab ⊢
          simpa [Finset.pair_comm] using move' j e a hej.symm hej haj haj hje
        · exact havoid a b hab haj hbj
  intro S hSeven
  have hcases : S.card = 0 ∨ S.card = 2 ∨ S.card = 4 ∨ S.card = 6 := by
    obtain ⟨k, hk⟩ := hSeven
    have hle : S.card ≤ 6 := by simpa using Finset.card_le_univ S
    omega
  have hempty : (∅ : Finset (Fin 6)) ∈ 𝒮 := by
    have hp : ({0, 1} : Finset (Fin 6)) ∈ 𝒮 := hallpairs 0 1 (by decide)
    have hres := hsd _ hp _ hp
    rwa [symmDiff_self] at hres
  rcases hcases with h0 | h2 | h4 | h6
  · rwa [Finset.card_eq_zero.mp h0]
  · obtain ⟨a, b, hab, hSeq⟩ := Finset.card_eq_two.mp h2
    rw [hSeq]
    exact hallpairs a b hab
  · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hSeq⟩ := Finset.card_eq_four.mp h4
    have hres := hsd _ (hallpairs a b hab) _ (hallpairs c d hcd)
    rw [fin6_symmDiff_pairs a b c d hab hac had hbc hbd hcd] at hres
    rwa [← hSeq] at hres
  · rw [Finset.eq_univ_of_card S (by rw [h6, Fintype.card_fin])]
    simpa using hcompl _ hempty

theorem sec9ci_swap_mul_swap {α : Type*} [DecidableEq α] {u v w z : α} (huv : u ≠ v)
    (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    Equiv.swap u v * Equiv.swap w z =
      (Equiv.swap u w * Equiv.swap u v) * (Equiv.swap v z * Equiv.swap v w) := by
  set τ₁ : Equiv.Perm α := Equiv.swap u w * Equiv.swap u v with hτ₁
  set τ₂ : Equiv.Perm α := Equiv.swap v z * Equiv.swap v w with hτ₂
  have hτ₁u : τ₁ u = v := by
    rw [hτ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne huv.symm hvw]
  have hτ₁v : τ₁ v = w := by
    rw [hτ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have hτ₁w : τ₁ w = u := by
    rw [hτ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne huw.symm hvw.symm,
      Equiv.swap_apply_right]
  have hτ₁z : τ₁ z = z := by
    rw [hτ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne huz.symm hvz.symm,
      Equiv.swap_apply_of_ne_of_ne huz.symm hwz.symm]
  have hτ₂v : τ₂ v = w := by
    rw [hτ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hvw.symm hwz]
  have hτ₂w : τ₂ w = z := by
    rw [hτ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have hτ₂z : τ₂ z = v := by
    rw [hτ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hvz.symm hwz.symm,
      Equiv.swap_apply_right]
  have hτ₂u : τ₂ u = u := by
    rw [hτ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne huv huw,
      Equiv.swap_apply_of_ne_of_ne huv huz]
  have hτ₁x : ∀ x : α, x ≠ u → x ≠ v → x ≠ w → x ≠ z → τ₁ x = x := by
    intro x hxu hxv hxw hxz
    rw [hτ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxu hxv,
      Equiv.swap_apply_of_ne_of_ne hxu hxw]
  have hτ₂x : ∀ x : α, x ≠ u → x ≠ v → x ≠ w → x ≠ z → τ₂ x = x := by
    intro x hxu hxv hxw hxz
    rw [hτ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxv hxw,
      Equiv.swap_apply_of_ne_of_ne hxv hxz]
  ext i
  simp only [Equiv.Perm.mul_apply]
  rcases eq_or_ne i u with rfl | hu
  · rw [Equiv.swap_apply_of_ne_of_ne huw huz, Equiv.swap_apply_left, hτ₂u, hτ₁u]
  · rcases eq_or_ne i v with rfl | hv
    · rw [Equiv.swap_apply_of_ne_of_ne hvw hvz, Equiv.swap_apply_right, hτ₂v, hτ₁w]
    · rcases eq_or_ne i w with rfl | hw
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne huz.symm hvz.symm, hτ₂w, hτ₁z]
      · rcases eq_or_ne i z with rfl | hz
        · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne huw.symm hvw.symm, hτ₂z, hτ₁v]
        · rw [Equiv.swap_apply_of_ne_of_ne hw hz, Equiv.swap_apply_of_ne_of_ne hu hv,
            hτ₂x i hu hv hw hz, hτ₁x i hu hv hw hz]

theorem sec9ci_cycle_cube {α : Type*} [DecidableEq α] {u v w : α} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) : (Equiv.swap u w * Equiv.swap u v) * (Equiv.swap u w * Equiv.swap u v) *
      (Equiv.swap u w * Equiv.swap u v) = 1 := by
  set τ : Equiv.Perm α := Equiv.swap u w * Equiv.swap u v with hτ
  have hτu : τ u = v := by
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne huv.symm hvw]
  have hτv : τ v = w := by
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have hτw : τ w = u := by
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne huw.symm hvw.symm,
      Equiv.swap_apply_right]
  have hτx : ∀ x : α, x ≠ u → x ≠ v → x ≠ w → τ x = x := by
    intro x hxu hxv hxw
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxu hxv,
      Equiv.swap_apply_of_ne_of_ne hxu hxw]
  ext i
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rcases eq_or_ne i u with rfl | hu
  · rw [hτu, hτv, hτw]
  · rcases eq_or_ne i v with rfl | hv
    · rw [hτv, hτw, hτu]
    · rcases eq_or_ne i w with rfl | hw
      · rw [hτw, hτu, hτv]
      · rw [hτx i hu hv hw, hτx i hu hv hw, hτx i hu hv hw]

theorem sec9ci_dbl_sq {α : Type*} [DecidableEq α] {u v w z : α} (huv : u ≠ v) (huw : u ≠ w)
    (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    (Equiv.swap u v * Equiv.swap w z) * (Equiv.swap u v * Equiv.swap w z) = 1 := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap u v) (Equiv.swap w z) :=
    Equiv.Perm.disjoint_swap_swap (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true, true_and, or_false, not_or]
      exact ⟨⟨huv, huw, huz⟩, ⟨hvw, hvz⟩, hwz⟩)
  rw [Commute.mul_mul_mul_comm hd.commute.symm (Equiv.swap u v) (Equiv.swap w z),
    Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]

end CFSG.OddStandard.SmallF3.Omega
