module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Unit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GU6

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA.SFM12

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

@[expose] def permM (π : Equiv.Perm (Fin 6)) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun r s => if r = π s then 1 else 0

theorem permM_transpose_mul (π : Equiv.Perm (Fin 6)) : (permM (F := F) π)ᵀ * permM π = 1 := by
  ext r s
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [permM, Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (π r)]
  · simp [π.injective.eq_iff]
  · intro b _ hb
    have : ¬ b = π r := hb
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem permM_mul_self (π : Equiv.Perm (Fin 6)) (hπ : ∀ s, π (π s) = s) :
    permM (F := F) π * permM π = 1 := by
  ext r s
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [permM, Matrix.of_apply]
  rw [Finset.sum_eq_single (π s)]
  · simp [hπ]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem permM_map_frob (π : Equiv.Perm (Fin 6)) :
    (permM (F := F) π).map (⇑(iterateFrobenius F 2 2 : F →+* F)) = permM π := by
  ext r s
  simp only [permM, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp [frob_apply4]

theorem det_permM_involution (π : Equiv.Perm (Fin 6)) (hπ : ∀ s, π (π s) = s) :
    (permM (F := F) π).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : (permM (F := F) π).det ^ 2 = 1 := by
    rw [sq, ← Matrix.det_mul, permM_mul_self π hπ, Matrix.det_one]
  have hsub : ((permM (F := F) π).det - 1) ^ 2 = 0 := by
    linear_combination hsq + (1 - (permM (F := F) π).det) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsub)

@[expose] def diagU (t : Fin 6 → F) (ht : ∀ k, t k ≠ 0) : GL (Fin 6) F :=
  Units.mk (Matrix.diagonal t) (Matrix.diagonal fun k => (t k)⁻¹)
    (by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      simp [ht k])
    (by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      simp [ht k])

theorem diagU_val (t : Fin 6 → F) (ht : ∀ k, t k ≠ 0) :
    ((diagU t ht : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = Matrix.diagonal t :=
  rfl

@[expose] def permU (π : Equiv.Perm (Fin 6)) (hπ : ∀ s, π (π s) = s) : GL (Fin 6) F :=
  Units.mk (permM π) (permM π) (permM_mul_self π hπ) (permM_mul_self π hπ)

theorem permU_val (π : Equiv.Perm (Fin 6)) (hπ : ∀ s, π (π s) = s) :
    ((permU (F := F) π hπ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = permM π :=
  rfl

theorem diagU_mem_SU (hF : Nat.card F = (2 ^ 2) ^ 2) {t : Fin 6 → F} (ht : ∀ k, t k ≠ 0)
    (ht5 : ∀ k, t k ^ 5 = 1) (hdet : ∏ k, t k = 1) : diagU t ht ∈ StatedSU 6 (2 ^ 2) F := by
  rw [mem_SU_iff hF]
  refine ⟨?_, ?_⟩
  · rw [diagU_val, Matrix.det_diagonal, hdet]
  · rw [diagU_val, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    simp only [Function.comp, frob_apply4]
    rw [← pow_succ]
    exact ht5 k

theorem permU_mem_SU (hF : Nat.card F = (2 ^ 2) ^ 2) (π : Equiv.Perm (Fin 6))
    (hπ : ∀ s, π (π s) = s) : permU (F := F) π hπ ∈ StatedSU 6 (2 ^ 2) F := by
  rw [mem_SU_iff hF]
  refine ⟨?_, ?_⟩
  · rw [permU_val]
    exact det_permM_involution π hπ
  · rw [permU_val, permM_map_frob]
    exact permM_transpose_mul π

theorem diagU_mem_Ug (hF : Nat.card F = (2 ^ 2) ^ 2) {d : Fin 6 → F} {l0 : F} {t : Fin 6 → F}
    (ht : ∀ k, t k ≠ 0) (ht5 : ∀ k, t k ^ 5 = 1) (hdet : ∏ k, t k = 1)
    (hoff : ∀ k, ¬ d k = l0 → t k = 1) :
    (⟨diagU t ht, diagU_mem_SU hF ht ht5 hdet⟩ : ↥(StatedSU 6 (2 ^ 2) F)) ∈ Ug d l0 := by
  refine ⟨fun m => ?_, ?_⟩
  · show Matrix.diagonal t * eigP d m = eigP d m * Matrix.diagonal t
    unfold eigP
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  · show Matrix.diagonal t * (1 - eigP d l0) = 1 - eigP d l0
    have e : (1 : Matrix (Fin 6) (Fin 6) F) - eigP d l0 =
        Matrix.diagonal (fun k => 1 - if d k = l0 then 1 else 0) := by
      unfold eigP
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    rw [e, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : d k = l0
    · simp [hk]
    · simp [hk, hoff k hk]

theorem permU_mem_Ug (hF : Nat.card F = (2 ^ 2) ^ 2) {d : Fin 6 → F} {l0 : F}
    (π : Equiv.Perm (Fin 6)) (hπ : ∀ s, π (π s) = s) (hd : ∀ s, d (π s) = d s)
    (hmove : ∀ s, π s ≠ s → d s = l0) :
    (⟨permU (F := F) π hπ, permU_mem_SU hF π hπ⟩ : ↥(StatedSU 6 (2 ^ 2) F)) ∈ Ug d l0 := by
  refine ⟨fun m => ?_, ?_⟩
  · show permM π * eigP d m = eigP d m * permM π
    ext r s
    simp only [eigP, permM, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    by_cases h : r = π s
    · subst h
      simp [hd s]
    · simp [h]
  · show permM π * (1 - eigP d l0) = 1 - eigP d l0
    have e : (1 : Matrix (Fin 6) (Fin 6) F) - eigP d l0 =
        Matrix.diagonal (fun k => if d k = l0 then 0 else 1) := by
      unfold eigP
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
      congr 1
      funext k
      by_cases hk : d k = l0 <;> simp [hk]
    rw [e]
    ext r s
    simp only [permM, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.of_apply]
    by_cases hrs : r = s
    · subst hrs
      by_cases hπr : π r = r
      · simp [hπr]
      · have hdr := hmove r hπr
        simp [hdr]
    · by_cases h : r = π s
      · have hs : π s ≠ s := by
          intro h'
          exact hrs (h.trans h')
        have hdr := hmove s hs
        simp [h, hs, hd s, hdr, hrs]
      · simp [h, hrs]

theorem block_card_five [Finite F] (hF : Nat.card F = (2 ^ 2) ^ 2) {d : Fin 6 → F}
    {g : ↥(StatedSU 6 (2 ^ 2) F)} (hgd : (g : GL (Fin 6) F).val = Matrix.diagonal d)
    (hd5 : ∀ k, d k ^ 5 = 1) (hg1 : g ≠ 1) {J : Subgroup ↥(StatedSU 6 (2 ^ 2) F)}
    (hJq : CFSG.Open.IsQuasisimple J)
    (hJC : J ≤ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)))
    (hnorm : ∀ c ∈ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)), ∀ j ∈ J,
      c * j * c⁻¹ ∈ J)
    (h41 : 41 ∣ Nat.card J) : ∃ l0 : F, (Eset d l0).card = 5 ∧ Ug d l0 ≤ J := by
  have hCg : Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)) = Cg d :=
    centralizer_eq_Cg hgd
  rw [hCg] at hJC hnorm
  obtain ⟨l0, hl0⟩ := exists_block hF hJq hJC hnorm
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  have hdet : (g : GL (Fin 6) F).val.det = 1 := ((mem_SU_iff hF (g : GL (Fin 6) F)).1 g.2).1
  have hdetd : ∏ k, d k = 1 := by
    rw [← Matrix.det_diagonal, ← hgd]
    exact hdet
  have hcard_le : (Eset d l0).card ≤ 6 := by
    have := Finset.card_le_univ (Eset d l0)
    simpa using this
  rcases (show (Eset d l0).card ≤ 4 ∨ (Eset d l0).card = 5 ∨ (Eset d l0).card = 6 by omega)
    with h4 | h5 | h6
  · exfalso
    have h1 : 41 ∣ Nat.card ↥(Ug d l0) := h41.trans (Subgroup.card_dvd_of_le hl0)
    exact not_dvd41_card_GL hF16 h4 (h1.trans (card_Ug_dvd_GL d l0))
  · refine ⟨l0, h5, ?_⟩
    have hUgC : Ug d l0 ≤ Cg d := fun x hx => hx.1
    have hUq : CFSG.Open.IsQuasisimple ↥(Ug d l0) := isQuasisimple_Ug d l0 hF (by omega)
    exact quasisimple_le_of_normal hUq hl0 hJq (fun j hj m hm => hnorm j (hUgC hj) m hm)
  · exfalso
    apply hg1
    have hall : ∀ k, d k = l0 := by
      have huniv := Finset.eq_univ_of_card (Eset d l0) (by simpa using h6)
      intro k
      have hk : k ∈ Eset d l0 := by rw [huniv]; exact Finset.mem_univ k
      exact (mem_Eset' d l0 k).1 hk
    have hl6 : l0 ^ 6 = 1 := by
      have : ∏ k, d k = l0 ^ 6 := by
        rw [Finset.prod_congr rfl (fun k _ => hall k), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      rw [← this]
      exact hdetd
    have hl5 : l0 ^ 5 = 1 := by rw [← hall 0]; exact hd5 0
    have hl1 : l0 = 1 := by
      have h : l0 ^ 6 = l0 ^ 5 * l0 := pow_succ l0 5
      rw [hl6, hl5, one_mul] at h
      exact h.symm
    have hd1 : d = fun _ => (1 : F) := funext fun k => by rw [hall k, hl1]
    apply Subtype.ext
    apply Units.ext
    show (g : GL (Fin 6) F).val = 1
    rw [hgd, hd1]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem compl_eq_one {d : Fin 6 → F} {l0 : F} (hW : (Eset d l0).card = 5) (hd5 : ∀ k, d k ^ 5 = 1)
    (hdet : ∏ k, d k = 1) (k : Fin 6) (hk : ¬ d k = l0) : d k = 1 := by
  have hl5 : l0 ^ 5 = 1 := by
    obtain ⟨k1, hk1⟩ := Finset.card_pos.1 (by omega : 0 < (Eset d l0).card)
    have hk1' : d k1 = l0 := (mem_Eset' d l0 k1).1 hk1
    rw [← hk1']
    exact hd5 k1
  have hC : (Eset d l0).card + (Finset.univ.filter fun k : Fin 6 => ¬ d k = l0).card = 6 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 6)))
      (fun k : Fin 6 => d k = l0)
    simpa using this
  have hC1 : (Finset.univ.filter fun k : Fin 6 => ¬ d k = l0).card = 1 := by omega
  obtain ⟨k0, hk0⟩ := Finset.card_eq_one.1 hC1
  have hprod : ∏ k, d k = l0 ^ 5 * d k0 := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin 6))
      (fun k => d k = l0)]
    have e1 : ∏ k ∈ Finset.univ.filter (fun k => d k = l0), d k = l0 ^ 5 := by
      rw [Finset.prod_congr rfl (fun k hk => (mem_Eset' d l0 k).1 hk), Finset.prod_const, hW]
    have e2 : ∏ k ∈ Finset.univ.filter (fun k => ¬ d k = l0), d k = d k0 := by
      rw [hk0, Finset.prod_singleton]
    rw [e1, e2]
  have hd0 : d k0 = 1 := by
    rw [hprod, hl5, one_mul] at hdet
    exact hdet
  have hkC : k ∈ Finset.univ.filter fun k : Fin 6 => ¬ d k = l0 := by simpa using hk
  rw [hk0, Finset.mem_singleton] at hkC
  rw [hkC, hd0]

end CFSG.LocalAnalysis.GLTheoremA.Y10GU6
