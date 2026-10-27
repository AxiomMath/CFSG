module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A8Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv Equiv.Perm Subgroup CFSG.QuasithinUnique

theorem factorization_two_360 : (360 : ℕ).factorization 2 = 3 := by
  have h : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 45)]

theorem card_fixerAlt_zero_one_le : Nat.card (fixerAlt {0, 1}) ≤ 360 := by
  have h := card_fixerAlt_le {0, 1} (by decide)
  have h6 : Fintype.card {x : Fin 8 // x ∉ ({0, 1} : Finset (Fin 8))} = 6 := by decide
  rw [h6] at h
  exact h

theorem card_fixerAlt_zero_one_six_seven_le : Nat.card (fixerAlt {0, 1, 6, 7}) ≤ 12 := by
  have h := card_fixerAlt_le {0, 1, 6, 7} (by decide)
  have h4 : Fintype.card {x : Fin 8 // x ∉ ({0, 1, 6, 7} : Finset (Fin 8))} = 4 := by decide
  rw [h4] at h
  exact h

theorem card_fixerAlt_two_three_four_five_le : Nat.card (fixerAlt {2, 3, 4, 5}) ≤ 12 := by
  have h := card_fixerAlt_le {2, 3, 4, 5} (by decide)
  have h4 : Fintype.card {x : Fin 8 // x ∉ ({2, 3, 4, 5} : Finset (Fin 8))} = 4 := by decide
  rw [h4] at h
  exact h

theorem conj_mem_fixerAlt' {S S' : Finset (Fin 8)} {g h : Perm (Fin 8)}
    (hg : ∀ x ∈ S', g⁻¹ x ∈ S) (hh : h ∈ fixerAlt S) : g * h * g⁻¹ ∈ fixerAlt S' := by
  obtain ⟨hfix, hsign⟩ := mem_fixerAlt.mp hh
  refine mem_fixerAlt.mpr ⟨fun x hx => ?_, by simp [hsign]⟩
  have h1 : g (h (g⁻¹ x)) = x := by
    rw [hfix _ (hg x hx)]
    exact Equiv.apply_symm_apply g x
  exact h1

theorem exists_standard {L U : Subgroup (Perm (Fin 8))} (hL : IsA4Block L U)
    (hLB : L ≤ fixerAlt {0, 1})
    (hU : ∀ x, x ∈ U ↔ ∃ i ∈ ({0, 2, 4, 6} : Finset (Fin 8)), dd i = x) :
    ∃ Λr W : Subgroup (Perm (Fin 8)), Λr ≤ alternatingGroup (Fin 8) ∧ IsA4Block Λr W ∧
      (∀ l ∈ L, ∀ y ∈ Λr, l * y = y * l) ∧
      swap (0 : Fin 8) 1 ∈ normalizer (Λr : Set (Perm (Fin 8))) ∧ swap (0 : Fin 8) 1 ∉ Λr := by
  obtain ⟨c, hcL, hc3, hcN, -, hLc⟩ := hL.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hc01 := (mem_fixerAlt.mp (hLB hcL)).1
  have hc0 : c 0 = 0 := hc01 0 (by simp)
  have hc1 : c 1 = 1 := hc01 1 (by simp)
  have hpres : ∀ x ∈ ({0, 1, 6, 7} : Finset (Fin 8)), c x ∈ ({0, 1, 6, 7} : Finset (Fin 8)) := by
    intro x hx
    rw [← ia_fix]
    intro i hi
    have huU : dd i ∈ U := (hU _).mpr ⟨i, hi, rfl⟩
    have h1 : c⁻¹ * dd i * c ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (U : Set (Perm (Fin 8)))).inv_mem hcN)
        (dd i)).mp huU
      simpa using this
    obtain ⟨j, hj, hjeq⟩ := (hU _).mp h1
    have h2 := (ia_fix x).mpr hx j hj
    rw [hjeq] at h2
    have h3 := congrArg c h2
    simpa [Perm.mul_apply] using h3
  have hmem6 : c 6 = 6 ∨ c 6 = 7 := by
    have h := hpres 6 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h
    · exact absurd (c.injective (h.trans hc0.symm)) (by decide)
    · exact absurd (c.injective (h.trans hc1.symm)) (by decide)
    · exact Or.inl h
    · exact Or.inr h
  have hmem7 : c 7 = 6 ∨ c 7 = 7 := by
    have h := hpres 7 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h
    · exact absurd (c.injective (h.trans hc0.symm)) (by decide)
    · exact absurd (c.injective (h.trans hc1.symm)) (by decide)
    · exact Or.inl h
    · exact Or.inr h
  have hc6 : c 6 = 6 := by
    rcases hmem6 with h | h
    · exact h
    · exfalso
      have h7 : c 7 = 6 := by
        rcases hmem7 with h' | h'
        · exact h'
        · exact absurd (c.injective (h'.trans h.symm)) (by decide)
      have h8 := congrArg (fun p : Perm (Fin 8) => p 6) hc3'
      rw [pow_three'] at h8
      simp [Perm.mul_apply, h, h7] at h8
  have hc7 : c 7 = 7 := by
    rcases hmem7 with h' | h'
    · exact absurd (c.injective (h'.trans hc6.symm)) (by decide)
    · exact h'
  have hcfix : c ∈ fixAll {0, 1, 6, 7} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hUfix : U ≤ fixAll {0, 1, 6, 7} := by
    intro u hu x hx
    obtain ⟨i, hi, rfl⟩ := (hU u).mp hu
    exact (ia_fix x).mpr hx i hi
  have hLfix : L ≤ fixAll {0, 1, 6, 7} := by
    rw [hLc]
    exact sup_le hUfix (Subgroup.zpowers_le.mpr hcfix)
  have hLle : L ≤ fixerAlt {0, 1, 6, 7} := fun l hl =>
    mem_fixerAlt.mpr ⟨hLfix hl, (mem_fixerAlt.mp (hLB hl)).2⟩
  have hLeq : L = fixerAlt {0, 1, 6, 7} :=
    Subgroup.eq_of_le_of_card_ge hLle (by
      rw [hL.card_L]
      exact card_fixerAlt_zero_one_six_seven_le)
  have hleft : L.map (MulAut.conj permPi).toMonoidHom ≤ fixerAlt {2, 3, 4, 5} := by
    rintro _ ⟨l, hl, rfl⟩
    rw [hLeq] at hl
    exact conj_mem_fixerAlt' permPi_inv hl
  have hLπ : IsA4Block (L.map (MulAut.conj permPi).toMonoidHom)
      (U.map (MulAut.conj permPi).toMonoidHom) := hL.map (MulAut.conj permPi)
  have hΛeq : L.map (MulAut.conj permPi).toMonoidHom = fixerAlt {2, 3, 4, 5} :=
    Subgroup.eq_of_le_of_card_ge hleft (by
      rw [hLπ.card_L]
      exact card_fixerAlt_two_three_four_five_le)
  rw [hΛeq] at hLπ
  refine ⟨fixerAlt {2, 3, 4, 5}, U.map (MulAut.conj permPi).toMonoidHom, inf_le_right, hLπ, ?_, ?_,
    ?_⟩
  · intro l hl y hy
    have hl' := (mem_fixerAlt.mp (hLle hl)).1
    have hy' := (mem_fixerAlt.mp hy).1
    have hdis : Perm.Disjoint l y := by
      intro x
      have hx : x ∈ ({0, 1, 6, 7} : Finset (Fin 8)) ∨ x ∈ ({2, 3, 4, 5} : Finset (Fin 8)) := by
        revert x
        decide
      rcases hx with h | h
      · exact Or.inl (hl' x h)
      · exact Or.inr (hy' x h)
    exact hdis.commute
  · exact mem_normalizer_fixerAlt (by decide)
  · intro h
    have := (mem_fixerAlt.mp h).2
    rw [Equiv.Perm.sign_swap (show (0 : Fin 8) ≠ 1 by decide)] at this
    exact absurd this (by decide)

theorem exists_of_conj_standard {L U : Subgroup (Perm (Fin 8))} (hL : IsA4Block L U)
    (hLB : L ≤ fixerAlt {0, 1}) {h : Perm (Fin 8)} (hh : h ∈ fixerAlt {0, 1})
    (hU : ∀ x, x ∈ U.map (MulAut.conj h).toMonoidHom ↔
      ∃ i ∈ ({0, 2, 4, 6} : Finset (Fin 8)), dd i = x) :
    ∃ Λr W : Subgroup (Perm (Fin 8)), Λr ≤ alternatingGroup (Fin 8) ∧ IsA4Block Λr W ∧
      (∀ l ∈ L, ∀ y ∈ Λr, l * y = y * l) ∧
      swap (0 : Fin 8) 1 ∈ normalizer (Λr : Set (Perm (Fin 8))) ∧ swap (0 : Fin 8) 1 ∉ Λr := by
  have hhfix := (mem_fixerAlt.mp hh).1
  have hσ : h * swap (0 : Fin 8) 1 * h⁻¹ = swap 0 1 := by
    rw [← Equiv.swap_apply_apply, hhfix 0 (by simp), hhfix 1 (by simp)]
  have hL' : IsA4Block (L.map (MulAut.conj h).toMonoidHom) (U.map (MulAut.conj h).toMonoidHom) :=
    hL.map (MulAut.conj h)
  have hLB' : L.map (MulAut.conj h).toMonoidHom ≤ fixerAlt {0, 1} := by
    rintro _ ⟨l, hl, rfl⟩
    exact conj_mem_fixerAlt' (S := {0, 1}) (S' := {0, 1}) (fun x hx => by
      obtain rfl | rfl : x = 0 ∨ x = 1 := by simpa using hx
      · simp [Perm.inv_eq_iff_eq.mpr (hhfix 0 (by simp)).symm]
      · simp [Perm.inv_eq_iff_eq.mpr (hhfix 1 (by simp)).symm]) (hLB hl)
  obtain ⟨Λr', W', hΛalt, hΛA4, hcomm, hnorm, hnot⟩ := exists_standard hL' hLB' hU
  have mem_conj : ∀ (X : Subgroup (Perm (Fin 8))) (y : Perm (Fin 8)),
      y ∈ X.map (MulAut.conj h⁻¹).toMonoidHom ↔ h * y * h⁻¹ ∈ X := by
    intro X y
    rw [Subgroup.mem_map_equiv]
    simp
  refine ⟨Λr'.map (MulAut.conj h⁻¹).toMonoidHom, W'.map (MulAut.conj h⁻¹).toMonoidHom, ?_,
    hΛA4.map (MulAut.conj h⁻¹), ?_, ?_, ?_⟩
  · intro y hy
    rw [mem_conj] at hy
    have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
    have := hn.conj_mem _ (hΛalt hy) h⁻¹
    simpa [mul_assoc] using this
  · intro l hl y hy
    rw [mem_conj] at hy
    have hl' : h * l * h⁻¹ ∈ L.map (MulAut.conj h).toMonoidHom := ⟨l, hl, rfl⟩
    have h1 := hcomm _ hl' _ hy
    have e1 : (h * l * h⁻¹) * (h * y * h⁻¹) = h * (l * y) * h⁻¹ := by group
    have e2 : (h * y * h⁻¹) * (h * l * h⁻¹) = h * (y * l) * h⁻¹ := by group
    rw [e1, e2] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conj, mem_conj]
    have e : h * (swap (0 : Fin 8) 1 * y * (swap (0 : Fin 8) 1)⁻¹) * h⁻¹ =
        swap 0 1 * (h * y * h⁻¹) * (swap (0 : Fin 8) 1)⁻¹ := by
      calc _ = (h * swap (0 : Fin 8) 1 * h⁻¹) * (h * y * h⁻¹) * (h * swap (0 : Fin 8) 1 * h⁻¹)⁻¹ := by
              group
        _ = _ := by rw [hσ]
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hnorm (h * y * h⁻¹)
  · intro hmem
    rw [mem_conj, hσ] at hmem
    exact hnot hmem

theorem tabA8_pure {K L₁ L₂ U₁ U₂ D : Subgroup (Perm (Fin 8))}
    (hKC : K ≤ Subgroup.centralizer {swap (0 : Fin 8) 1}) (hKalt : K ≤ alternatingGroup (Fin 8))
    (hKcard : Nat.card K = 360) (hKperf : ⁅K, K⁆ = K)
    (hL₁ : IsA4Block L₁ U₁) (hL₂ : IsA4Block L₂ U₂) (h₁ : L₁ ≤ K) (h₂ : L₂ ≤ K) (hne : U₁ ≠ U₂)
    (hD : D ≤ K) (hD8 : Nat.card D = 8) (hU₁ : U₁ ≤ D) (hU₂ : U₂ ≤ D) :
    ∃ Λ Λr W : Subgroup (Perm (Fin 8)), (Λ = L₁ ∨ Λ = L₂) ∧ Λr ≤ alternatingGroup (Fin 8) ∧
      IsA4Block Λr W ∧ (∀ l ∈ Λ, ∀ y ∈ Λr, l * y = y * l) ∧
      swap (0 : Fin 8) 1 ∈ normalizer (Λr : Set (Perm (Fin 8))) ∧
      swap (0 : Fin 8) 1 ∉ Λr := by
  have hKle : K ≤ fixerAlt {0, 1} := fun k hk =>
    mem_fixerAlt.mpr ⟨le_fixAll_of_perfect hKperf hKC hk, mem_alternatingGroup.mp (hKalt hk)⟩
  have hKeq : K = fixerAlt {0, 1} :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hKcard]; exact card_fixerAlt_zero_one_le)
  have htwo : twoPart K = 8 := by
    rw [twoPart, hKcard, factorization_two_360]
    norm_num
  have hSylD : IsSylowTwoOf D K :=
    isSylowTwoOf_of_card_eq hD (IsPGroup.of_card (n := 3) (by rw [hD8]; norm_num))
      (by rw [hD8, htwo])
  have hD0K : d0 ≤ K := by
    rw [hKeq]
    exact d0_le_fixerAlt
  have hSyl0 : IsSylowTwoOf d0 K :=
    isSylowTwoOf_of_card_eq hD0K (IsPGroup.of_card (n := 3) (by rw [card_d0]; norm_num))
      (by rw [card_d0, htwo])
  obtain ⟨h, hhK, hDh⟩ := hSylD.exists_conj hSyl0
  have hhB : h ∈ fixerAlt {0, 1} := by
    rw [← hKeq]
    exact hhK
  have hcls : ∀ {L U : Subgroup (Perm (Fin 8))}, IsA4Block L U → U ≤ D →
      (∀ x, x ∈ U.map (MulAut.conj h).toMonoidHom ↔ ∃ i ∈ ({0, 2, 4, 6} : Finset (Fin 8)), dd i = x) ∨
        (∀ x, x ∈ U.map (MulAut.conj h).toMonoidHom ↔
          ∃ i ∈ ({0, 2, 5, 7} : Finset (Fin 8)), dd i = x) := by
    intro L U hA hUD
    refine klein_in_d0 (by rw [hDh]; exact Subgroup.map_mono hUD) ?_ ?_
    · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
      exact hA.card_U
    · rintro _ ⟨x, hx, rfl⟩
      have hx2 := hA.sq_U x hx
      show h * x * h⁻¹ * (h * x * h⁻¹) = 1
      calc h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
        _ = 1 := by rw [← pow_two, hx2]; group
  have hL₁B : L₁ ≤ fixerAlt {0, 1} := by
    rw [← hKeq]
    exact h₁
  have hL₂B : L₂ ≤ fixerAlt {0, 1} := by
    rw [← hKeq]
    exact h₂
  rcases hcls hL₁ hU₁ with h1a | h1b
  · obtain ⟨Λr, W, hΛalt, hΛ, hcomm, hnorm, hnot⟩ := exists_of_conj_standard hL₁ hL₁B hhB h1a
    exact ⟨L₁, Λr, W, Or.inl rfl, hΛalt, hΛ, hcomm, hnorm, hnot⟩
  · rcases hcls hL₂ hU₂ with h2a | h2b
    · obtain ⟨Λr, W, hΛalt, hΛ, hcomm, hnorm, hnot⟩ := exists_of_conj_standard hL₂ hL₂B hhB h2a
      exact ⟨L₂, Λr, W, Or.inr rfl, hΛalt, hΛ, hcomm, hnorm, hnot⟩
    · exfalso
      apply hne
      apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
      ext x
      rw [h1b x, h2b x]

end CFSG.QuasithinUnique.DoubleA3
