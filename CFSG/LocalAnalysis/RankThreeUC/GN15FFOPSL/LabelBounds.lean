module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.LabelBounds.Arith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Finset CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar in
theorem psl_false_of_label_bounds {n f r : ℕ} (hn : 5 ≤ n) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ n) (ε : Fin f → Finset (Fin n)) (h0 : ∀ i, (⟨0, by omega⟩ : Fin n) ∉ ε i)
    (ht : ∃ i, ε i ≠ ∅)
    (hscal : r ∣ ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ))
    {s d : ℕ}
    (hs : f ≤ s * (univ.filter fun i => ε i ≠ ∅).card)
    (hdim : s * d < f * n ^ 2)
    (hd : ∏ i ∈ univ.filter (fun i => ε i ≠ ∅), orbitSize (ε i) ≤ d)
    (hextra : ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) →
      (ε i₀ = {⟨1, by omega⟩, ⟨2, by omega⟩} ∨ ε i₀ = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) →
      n * (n - 1) + n.choose 3 ≤ d)
    (hnat : (univ.filter fun i => ε i ≠ ∅).card = 2 →
      (∀ i, ε i ≠ ∅ → ε i = {⟨1, by omega⟩} ∨ ε i = {⟨n - 1, by omega⟩}) → False)
    (hadj : ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) → ε i₀ = {⟨1, by omega⟩, ⟨n - 1, by omega⟩} → False)
    (hcube : ∀ h6 : n = 6, ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) → ε i₀ = {⟨3, by omega⟩} → False) :
    False := by
  classical
  have hn2 : 2 ≤ n := by omega
  let T : Finset (Fin f) := univ.filter fun i => ε i ≠ ∅
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, by simpa [T] using hi⟩
  have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
  have hsT : f ≤ s * T.card := by simpa [T] using hs
  have hdT : ∏ i ∈ T, orbitSize (ε i) ≤ d := by simpa [T] using hd
  have hlt : d < T.card * n ^ 2 := lt_mul_sq_of_period hsT hdim
  have hpow : n ^ T.card ≤ d :=
    le_trans (pow_card_active_le_prod_orbitSize hn2 ε h0) hdT
  rcases Nat.lt_or_ge T.card 3 with hlt3 | hge3
  · have h1or2 : T.card = 1 ∨ T.card = 2 := by omega
    rcases h1or2 with h1 | h2
    ·
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
      have hempty : ∀ i, i ≠ i₀ → ε i = ∅ := by
        intro i hi
        by_contra hne'
        have hmem : i ∈ T := by simpa [T] using hne'
        rw [hi₀] at hmem
        exact hi (Finset.mem_singleton.mp hmem)
      have hi₀ne : ε i₀ ≠ ∅ := by
        have hmem : i₀ ∈ T := by
          rw [hi₀]
          exact Finset.mem_singleton_self i₀
        simpa [T] using hmem
      have hd1 : orbitSize (ε i₀) ≤ d := by simpa [hi₀] using hdT
      have hlt1 : d < n ^ 2 := by simpa [h1] using hlt
      have hSpos : 0 < (ε i₀).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hi₀ne)
      rcases Nat.lt_or_ge (ε i₀).card 2 with hc1 | hc2
      ·
        have hcard1 : (ε i₀).card = 1 := by omega
        obtain ⟨j, hSj⟩ := Finset.card_eq_one.mp hcard1
        have hj0 : (j : ℕ) ≠ 0 := by
          intro h
          apply h0 i₀
          rw [hSj, Finset.mem_singleton]
          exact Fin.ext h.symm
        have hjpos : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
        have hrdvd : r ∣ (j : ℕ) :=
          prime_dvd_of_scalar_singleton hr hr2 hempty hSj hscal
        have hchoose : n.choose (j : ℕ) < n ^ 2 := by
          have h := hd1
          rw [hSj, orbitSize_singleton] at h
          exact lt_of_le_of_lt h hlt1
        obtain ⟨h6, hj3⟩ :=
          eq_six_three_of_choose_lt_sq hr hr2 hrn hrdvd hjpos j.isLt hchoose
        have hset : ε i₀ = {(⟨3, by omega⟩ : Fin n)} := by
          rw [hSj, Finset.singleton_inj]
          exact Fin.ext hj3
        exact hcube h6 i₀ hempty hset
      ·
        by_cases hex : (ε i₀).card = 2 ∧
            ∃ k, CFSG.LieType.SpecialLinear.ExteriorModel.blocks (ε i₀) k = n - 2
        · obtain ⟨hcard2, hex2⟩ := hex
          have hdisj :=
            (CFSG.LieType.SpecialLinear.ExteriorModel.exists_blocks_eq_sub_two_iff
              (n := n) (S := ε i₀) (by omega : 4 ≤ n) (h0 i₀) hcard2).mp hex2
          rcases hdisj with h12 | h1n | hn12
          · have hlo := hextra i₀ hempty (Or.inl h12)
            have hsq := sq_le_mul_pred_add_choose_three (by omega : 4 ≤ n)
            omega
          · exact hadj i₀ hempty h1n
          · have hlo := hextra i₀ hempty (Or.inr hn12)
            have hsq := sq_le_mul_pred_add_choose_three (by omega : 4 ≤ n)
            omega
        · have hm := sq_le_orbitSize_of_two_le_card hn (h0 i₀) hc2 hex
          omega
    ·
      obtain ⟨i₁, i₂, hne, hTpair⟩ := Finset.card_eq_two.mp h2
      have hi1 : ε i₁ ≠ ∅ := by
        have hmem : i₁ ∈ T := by
          rw [hTpair]
          exact Finset.mem_insert_self i₁ {i₂}
        simpa [T] using hmem
      have hi2 : ε i₂ ≠ ∅ := by
        have hmem : i₂ ∈ T := by
          rw [hTpair]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i₂)
        simpa [T] using hmem
      have hprod : orbitSize (ε i₁) * orbitSize (ε i₂) ≤ d := by
        have h := hdT
        rw [hTpair, Finset.prod_pair hne] at h
        exact h
      have h2n : d < 2 * n ^ 2 := by simpa [h2] using hlt
      by_cases hnat1 : ε i₁ = {(⟨1, by omega⟩ : Fin n)} ∨
          ε i₁ = {(⟨n - 1, by omega⟩ : Fin n)}
      · by_cases hnat2 : ε i₂ = {(⟨1, by omega⟩ : Fin n)} ∨
            ε i₂ = {(⟨n - 1, by omega⟩ : Fin n)}
        ·
          have hnatall : ∀ i, ε i ≠ ∅ →
              ε i = {⟨1, by omega⟩} ∨ ε i = {⟨n - 1, by omega⟩} := by
            intro i hi
            have hmem : i ∈ T := by simpa [T] using hi
            rw [hTpair] at hmem
            rcases Finset.mem_insert.mp hmem with h | h
            · rw [h]; exact hnat1
            · rw [Finset.mem_singleton.mp h]
              exact hnat2
          exact hnat (by simpa [T] using h2) hnatall
        ·
          have hnon2 : n.choose 2 ≤ orbitSize (ε i₂) :=
            choose_two_le_orbitSize_of_nonnatural hn (h0 i₂) hi2 hnat2
          have hn1 : n ≤ orbitSize (ε i₁) := n_le_orbitSize hn2 (h0 i₁) hi1
          have hkey : n * n.choose 2 ≤ orbitSize (ε i₁) * orbitSize (ε i₂) :=
            Nat.mul_le_mul hn1 hnon2
          have hle : 2 * n ^ 2 ≤ d :=
            le_trans (le_trans (two_mul_sq_le_mul_choose_two hn) hkey) hprod
          omega
      ·
        have hnon1 : n.choose 2 ≤ orbitSize (ε i₁) :=
          choose_two_le_orbitSize_of_nonnatural hn (h0 i₁) hi1 hnat1
        have hn2' : n ≤ orbitSize (ε i₂) := n_le_orbitSize hn2 (h0 i₂) hi2
        have hkey : n * n.choose 2 ≤ orbitSize (ε i₁) * orbitSize (ε i₂) := by
          rw [Nat.mul_comm (orbitSize (ε i₁)) (orbitSize (ε i₂))]
          exact Nat.mul_le_mul hn2' hnon1
        have hle : 2 * n ^ 2 ≤ d :=
          le_trans (le_trans (two_mul_sq_le_mul_choose_two hn) hkey) hprod
        omega
  ·
    have hmul : T.card * n ^ 2 < n ^ T.card := mul_sq_lt_pow_of_three_le hn hge3
    omega

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
