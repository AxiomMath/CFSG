module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Six1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I269Six

open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4 bar)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.Fischer

abbrev Zs : Subgroup M6 := (CFSG.Open.StatedScalars (Fin 6) F4).subgroupOf (CFSG.Open.StatedSU 6 (2 ^ 1) F4)

theorem mem_Zs {x : M6} : x ∈ Zs ↔
    ∃ c : F4ˣ, (x : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  rw [Zs, Subgroup.mem_subgroupOf, CFSG.Open.StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩

theorem mem_UG_of_M6 (x : M6) : (x : GL (Fin 6) F4) ∈ primeFormUnitary hF4 (idGram F4 6) := by
  have h : (x : GL (Fin 6) F4) ∈ gramSU hF4 (idGram F4 6) := by
    rw [gramSU_idGram_six]; exact x.2
  exact ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_gramSU_iff_unitary hF4).1 h).1

theorem det_M6 (x : M6) : (mM6 x).det = 1 := det_eq_one_of_mem_statedSU' 6 x.2

theorem f4_cube (a : F4) (ha : a ≠ 0) : a ^ 3 = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [F4.card] at h
  norm_num at h
  exact h

theorem f4_add_ne (a b : F4) (h : a ≠ b) : a + b ≠ 0 := by
  intro hab
  apply h
  rw [eq_neg_of_add_eq_zero_left hab, CharTwo.neg_eq]

theorem f4_pair (l a : F4) (h : l ^ 4 * a * a = 1) : a = l := by
  have hl : l ≠ 0 := by rintro rfl; simp at h
  have hl3 := f4_cube l hl
  have h4 : l ^ 4 = l := by rw [show l ^ 4 = l ^ 3 * l by ring, hl3, one_mul]
  rw [h4] at h
  have h2 : a ^ 2 = l ^ 2 := by
    apply mul_left_cancel₀ hl
    calc l * a ^ 2 = l * a * a := by ring
      _ = 1 := h
      _ = l * l ^ 2 := by rw [show l * l ^ 2 = l ^ 3 by ring, hl3]
  have h3 : (a - l) ^ 2 = 0 := by
    have h2' : (2 : F4) = 0 := CharTwo.two_eq_zero
    linear_combination h2 + (l ^ 2 - a * l) * h2'
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
  exact sub_eq_zero.1 this

theorem f4_single (l a : F4) (h : l ^ 5 * a = 1) : a = l := by
  have hl : l ≠ 0 := by rintro rfl; simp at h
  have hl3 := f4_cube l hl
  have h5 : l ^ 5 = l ^ 2 := by rw [show l ^ 5 = l ^ 3 * l ^ 2 by ring, hl3, one_mul]
  rw [h5] at h
  calc a = l ^ 3 * a := by rw [hl3, one_mul]
    _ = l * (l ^ 2 * a) := by ring
    _ = l := by rw [h, mul_one]

theorem f4_four (l : F4) : (4 : ℕ) • l = 0 := by
  rw [nsmul_eq_mul]
  rw [show ((4 : ℕ) : F4) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul, zero_mul]

theorem prod_split_two (g : Fin 6 → F4) (c : F4) (i1 i2 : Fin 6) (hne : i1 ≠ i2)
    (hS : ∀ i, i ≠ i1 → i ≠ i2 → g i = c) : ∏ i, g i = c ^ 4 * g i1 * g i2 := by
  have hi2 : i2 ∈ Finset.univ.erase i1 := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i1),
    ← Finset.mul_prod_erase (Finset.univ.erase i1) g hi2]
  have e3 : ∏ i ∈ (Finset.univ.erase i1).erase i2, g i = c ^ 4 := by
    rw [Finset.prod_congr rfl (g := fun _ => c)]
    · rw [Finset.prod_const]
      congr 1
      rw [Finset.card_erase_of_mem hi2, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
    · intro i hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
      exact hS i hi.2 hi.1
  rw [e3]
  ring

theorem struct_of_diag (d : Fin 6 → F4) (l : F4) (hdet : ∏ i, d i = 1)
    (hns : ∃ i, d i ≠ l) (hrk : (Matrix.diagonal d - Matrix.scalar (Fin 6) l).rank ≤ 2) :
    ∃ i1 i2 : Fin 6, i1 ≠ i2 ∧ (∀ i, i ≠ i1 → i ≠ i2 → d i = l) ∧ d i1 ≠ l ∧ d i2 ≠ l ∧
      d i1 ≠ d i2 := by
  have hcard : Fintype.card {i : Fin 6 // d i = l} +
      (Matrix.diagonal d - Matrix.scalar (Fin 6) l).rank = 6 := card_blk_add_rank d l
  have hSW : (Finset.univ.filter (fun i => ¬ d i = l)).card +
      (Finset.univ.filter (fun i => d i = l)).card = 6 := by
    rw [Finset.filter_not, Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.filter_subset _ _),
      Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_univ (Finset.univ.filter (fun i => d i = l))
    simp only [Fintype.card_fin] at this ⊢
    omega
  have hWle : (Finset.univ.filter (fun i => ¬ d i = l)).card ≤ 2 := by
    have h1 : Fintype.card {i : Fin 6 // d i = l} = (Finset.univ.filter (fun i => d i = l)).card := by
      rw [Fintype.card_subtype]
    omega
  have hWne : (Finset.univ.filter (fun i => ¬ d i = l)).Nonempty := by
    obtain ⟨i, hi⟩ := hns
    exact ⟨i, by simp [hi]⟩
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin 6))
    (fun i => d i = l) d
  have hSprod : ∏ i ∈ Finset.univ.filter (fun i => d i = l), d i =
      l ^ (Finset.univ.filter (fun i => d i = l)).card := by
    rw [Finset.prod_congr rfl (g := fun _ => l) (fun i hi => (Finset.mem_filter.1 hi).2),
      Finset.prod_const]
  rw [hSprod, hdet] at hsplit
  have hW2 : (Finset.univ.filter (fun i => ¬ d i = l)).card = 2 := by
    by_contra hne
    have h1 : (Finset.univ.filter (fun i => ¬ d i = l)).card = 1 := by
      have := Finset.card_pos.2 hWne
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h1
    rw [hj, Finset.prod_singleton] at hsplit
    have hS5 : (Finset.univ.filter (fun i => d i = l)).card = 5 := by omega
    rw [hS5] at hsplit
    have hdj : d j ≠ l := by
      have : j ∈ Finset.univ.filter (fun i => ¬ d i = l) := by rw [hj]; exact Finset.mem_singleton_self j
      simpa using this
    exact hdj (f4_single l (d j) hsplit)
  obtain ⟨i1, i2, hne, hWeq⟩ := Finset.card_eq_two.1 hW2
  have hmem : ∀ i, ¬ d i = l ↔ i = i1 ∨ i = i2 := by
    intro i
    have := congrArg (fun s => i ∈ s) hWeq
    simpa using this
  have hS4 : (Finset.univ.filter (fun i => d i = l)).card = 4 := by omega
  refine ⟨i1, i2, hne, fun i h1 h2 => ?_, (hmem i1).2 (Or.inl rfl), (hmem i2).2 (Or.inr rfl), ?_⟩
  · by_contra hc
    rcases (hmem i).1 hc with h | h
    · exact h1 h
    · exact h2 h
  · intro heq
    have hd2 : d i2 ≠ l := (hmem i2).2 (Or.inr rfl)
    rw [hS4, hWeq, Finset.prod_pair hne, heq] at hsplit
    exact hd2 (f4_pair l (d i2) (by rw [mul_assoc]; exact hsplit))

theorem trace_diag_ne_zero (d : Fin 6 → F4) (l : F4) (i1 i2 : Fin 6) (hne : i1 ≠ i2)
    (hS : ∀ i, i ≠ i1 → i ≠ i2 → d i = l) (h12 : d i1 ≠ d i2) :
    (Matrix.diagonal d).trace ≠ 0 := by
  rw [Matrix.trace_diagonal]
  have hi2 : i2 ∈ Finset.univ.erase i1 := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase Finset.univ d (Finset.mem_univ i1),
    ← Finset.add_sum_erase (Finset.univ.erase i1) d hi2]
  have e3 : ∑ i ∈ (Finset.univ.erase i1).erase i2, d i = ∑ i ∈ (Finset.univ.erase i1).erase i2, l := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
    exact hS i hi.2 hi.1
  have hc : ((Finset.univ.erase i1).erase i2).card = 4 := by
    rw [Finset.card_erase_of_mem hi2, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  rw [e3, Finset.sum_const, hc, f4_four, add_zero]
  exact f4_add_ne _ _ h12

theorem commute_of_conj_smul (A : GL (Fin 6) F4) (B : Matrix (Fin 6) (Fin 6) F4) (c : F4)
    (hB : B.trace ≠ 0)
    (h : (A : Matrix (Fin 6) (Fin 6) F4) * B *
      ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • B) :
    (A : Matrix (Fin 6) (Fin 6) F4) * B = B * (A : Matrix (Fin 6) (Fin 6) F4) := by
  have hinv : ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * (A : Matrix (Fin 6) (Fin 6) F4)
      = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr := congrArg Matrix.trace h
  rw [Matrix.trace_mul_comm, ← mul_assoc, hinv, one_mul, Matrix.trace_smul, smul_eq_mul] at htr
  have hc : c = 1 := by
    have h1 : (c - 1) * B.trace = 0 := by linear_combination -htr
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact sub_eq_zero.1 h2
    · exact absurd h2 hB
  rw [hc, one_smul] at h
  calc (A : Matrix (Fin 6) (Fin 6) F4) * B
      = (A : Matrix (Fin 6) (Fin 6) F4) * B * (((A⁻¹ : GL (Fin 6) F4)) : Matrix (Fin 6) (Fin 6) F4)
        * (A : Matrix (Fin 6) (Fin 6) F4) := by rw [mul_assoc, hinv, mul_one]
    _ = (A : Matrix (Fin 6) (Fin 6) F4) * B * ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
        * (A : Matrix (Fin 6) (Fin 6) F4) := rfl
    _ = B * (A : Matrix (Fin 6) (Fin 6) F4) := by rw [h]

theorem cube_entry (h : Matrix (Fin 6) (Fin 6) F4) (i : Fin 6)
    (hblk : ∀ j, j ≠ i → h i j = 0 ∧ h j i = 0) : (h * h * h) i i = h i i ^ 3 := by
  have hr : ∀ k, (h * h) i k = h i i * h i k := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hj; rw [(hblk j hj).1, zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hr i]; ring
  · intro k _ hk; rw [(hblk k hk).2, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem card_nonzero_pairs : Nat.card {p : F4 × F4 // p.1 ≠ 0 ∧ p.2 ≠ 0} = 9 := by
  have e : {p : F4 × F4 // p.1 ≠ 0 ∧ p.2 ≠ 0} ≃ {x : F4 // x ≠ 0} × {x : F4 // x ≠ 0} :=
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  have h3 : Nat.card {x : F4 // x ≠ 0} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, F4.card]
    simp
  rw [h3]

theorem exists_nonscalar {Ê : Subgroup M6} {d : Fin 6 → F4} {l : F4} {i1 i2 : Fin 6}
    (hne : i1 ≠ i2) (hS : ∀ i, i ≠ i1 → i ≠ i2 → d i = l) (h1 : d i1 ≠ l) (h2 : d i2 ≠ l)
    (h12 : d i1 ≠ d i2) (hblock : ∀ h ∈ Ê, ∀ i j, d i ≠ d j → mM6 h i j = 0)
    (hcard : 9 < Nat.card Ê) :
    ∃ y ∈ Ê, ∀ c : F4, ∃ i j : Fin 6, i ≠ i1 ∧ i ≠ i2 ∧ j ≠ i1 ∧ j ≠ i2 ∧
      mM6 y i j ≠ if i = j then c else 0 := by
  by_contra hcon
  push Not at hcon
  have hd1 : ∀ j, j ≠ i1 → d j ≠ d i1 := by
    intro j hj
    by_cases hj2 : j = i2
    · subst hj2; exact h12.symm
    · rw [hS j hj hj2]; exact fun e => h1 e.symm
  have hd2 : ∀ j, j ≠ i2 → d j ≠ d i2 := by
    intro j hj
    by_cases hj1 : j = i1
    · subst hj1; exact h12
    · rw [hS j hj1 hj]; exact fun e => h2 e.symm
  have hdiag : ∀ h ∈ Ê, ∀ i j, i ≠ j → mM6 h i j = 0 := by
    intro h hh i j hij
    by_cases hd : d i = d j
    · have hi1 : i ≠ i1 := by
        rintro rfl; exact hd1 j (fun e' => hij e'.symm) hd.symm
      have hi2 : i ≠ i2 := by
        rintro rfl; exact hd2 j (fun e' => hij e'.symm) hd.symm
      have hj1 : j ≠ i1 := by
        rintro rfl; exact hd1 i hij hd
      have hj2 : j ≠ i2 := by
        rintro rfl; exact hd2 i hij hd
      obtain ⟨c, hc⟩ := hcon h hh
      rw [hc i j hi1 hi2 hj1 hj2, if_neg hij]
    · exact hblock h hh i j hd
  have hSdiag : ∀ h ∈ Ê, ∀ i, i ≠ i1 → i ≠ i2 → ∀ i0, i0 ≠ i1 → i0 ≠ i2 →
      mM6 h i i = mM6 h i0 i0 := by
    intro h hh i hi1 hi2 i0 hj1 hj2
    obtain ⟨c, hc⟩ := hcon h hh
    simp [hc i i hi1 hi2 hi1 hi2, hc i0 i0 hj1 hj2 hj1 hj2]
  obtain ⟨i0, hi01, hi02⟩ : ∃ i0 : Fin 6, i0 ≠ i1 ∧ i0 ≠ i2 := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset (Fin 6)) ⊆ {i1, i2} := by
      intro i _
      by_cases hi : i = i1
      · simp [hi]
      · simp [hno i hi]
    have h6 := Finset.card_le_card hsub
    have h2 : ({i1, i2} : Finset (Fin 6)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at h6
    omega
  have hdetf : ∀ h ∈ Ê, mM6 h i0 i0 ^ 4 * mM6 h i1 i1 * mM6 h i2 i2 = 1 := by
    intro h hh
    have hdg : mM6 h = Matrix.diagonal (fun i => mM6 h i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.diagonal_apply]
      · rw [hdiag h hh i j hij, Matrix.diagonal_apply_ne _ hij]
    have := det_M6 h
    rw [hdg, Matrix.det_diagonal, prod_split_two _ _ _ _ hne
      (fun i hi1 hi2 => hSdiag h hh i hi1 hi2 i0 hi01 hi02)] at this
    exact this
  have hnz : ∀ h ∈ Ê, mM6 h i0 i0 ≠ 0 ∧ mM6 h i1 i1 ≠ 0 := by
    intro h hh
    have := hdetf h hh
    constructor
    · rintro h0; rw [h0] at this; simp at this
    · rintro h0; rw [h0] at this; simp at this
  let f : Ê → {p : F4 × F4 // p.1 ≠ 0 ∧ p.2 ≠ 0} := fun h =>
    ⟨(mM6 h.1 i0 i0, mM6 h.1 i1 i1), (hnz h.1 h.2).1, (hnz h.1 h.2).2⟩
  have hf : Function.Injective f := by
    intro h k hfk
    have h3 : ((mM6 h.1 i0 i0, mM6 h.1 i1 i1) : F4 × F4) = (mM6 k.1 i0 i0, mM6 k.1 i1 i1) :=
      congrArg Subtype.val hfk
    obtain ⟨hA, hB⟩ := Prod.mk.inj h3
    have e1 := hdetf h.1 h.2
    have e2 := hdetf k.1 k.2
    rw [hA, hB] at e1
    have hu : mM6 k.1 i0 i0 ^ 4 * mM6 k.1 i1 i1 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (hnz k.1 k.2).1) (hnz k.1 k.2).2
    have hC : mM6 h.1 i2 i2 = mM6 k.1 i2 i2 := mul_left_cancel₀ hu (e1.trans e2.symm)
    apply Subtype.ext
    ext i j
    show mM6 h.1 i j = mM6 k.1 i j
    by_cases hij : i = j
    · subst hij
      by_cases hi1 : i = i1
      · subst hi1; exact hB
      by_cases hi2 : i = i2
      · subst hi2; exact hC
      rw [hSdiag h.1 h.2 i hi1 hi2 i0 hi01 hi02, hSdiag k.1 k.2 i hi1 hi2 i0 hi01 hi02, hA]
    · rw [hdiag h.1 h.2 i j hij, hdiag k.1 k.2 i j hij]
  have := Nat.card_le_card_of_injective f hf
  rw [card_nonzero_pairs] at this
  omega

end CFSG.LocalAnalysis.GLTheoremA.I269Six

end
