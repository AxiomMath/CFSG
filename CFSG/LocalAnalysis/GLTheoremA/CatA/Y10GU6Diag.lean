module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Ug
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GU6

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA.SFM12

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

@[expose] def tt (l0 : F) (i l : Fin 6) : Fin 6 → F :=
  fun k => if k = i then l0 else if k = l then l0⁻¹ else 1

theorem tt_i (l0 : F) (i l : Fin 6) : tt l0 i l i = l0 := by simp [tt]

theorem tt_l (l0 : F) {i l : Fin 6} (hil : i ≠ l) : tt l0 i l l = l0⁻¹ := by
  simp [tt, Ne.symm hil]

theorem tt_other (l0 : F) {i l k : Fin 6} (hki : k ≠ i) (hkl : k ≠ l) : tt l0 i l k = 1 := by
  simp [tt, hki, hkl]

theorem tt_prod (l0 : F) {i l : Fin 6} (hil : i ≠ l) : ∏ k, tt l0 i l k = l0 * l0⁻¹ := by
  rw [Fintype.prod_eq_mul i l hil]
  · rw [tt_i, tt_l l0 hil]
  · intro x hx
    exact tt_other l0 hx.1 hx.2

theorem tt_pow5 {l0 : F} (hl5 : l0 ^ 5 = 1) (i l k : Fin 6) : tt l0 i l k ^ 5 = 1 := by
  unfold tt
  split_ifs
  · exact hl5
  · rw [inv_pow, hl5, inv_one]
  · exact one_pow 5

theorem tt_ne_zero {l0 : F} (hl0 : l0 ≠ 0) (i l k : Fin 6) : tt l0 i l k ≠ 0 := by
  unfold tt
  split_ifs <;> simp [hl0]

theorem card_add_card_compl (d : Fin 6 → F) (l0 : F) :
    (Eset d l0).card + (Finset.univ.filter fun k : Fin 6 => ¬ d k = l0).card = 6 := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 6)))
    (fun k : Fin 6 => d k = l0)
  simpa using this

theorem mem_of_ne_pair {d : Fin 6 → F} {l0 : F} (hW : (Eset d l0).card = 5) {r s : Fin 6}
    (hrs : r ≠ s) : d r = l0 ∨ d s = l0 := by
  by_contra h
  push Not at h
  have hC := card_add_card_compl d l0
  have hsub : ({r, s} : Finset (Fin 6)) ⊆ Finset.univ.filter fun k : Fin 6 => ¬ d k = l0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [h.1]
    · simp [h.2]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_pair hrs] at h1
  omega

theorem exists_avoid {d : Fin 6 → F} {l0 : F} (hW : (Eset d l0).card = 5) (r s : Fin 6) :
    ∃ l, d l = l0 ∧ l ≠ r ∧ l ≠ s := by
  by_contra h
  push Not at h
  have hsub : Eset d l0 ⊆ {r, s} := by
    intro x hx
    have hx' : d x = l0 := (mem_Eset' d l0 x).1 hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc
    push Not at hc
    exact hc.2 (h x hx' hc.1)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_two (a := r) (b := s)
  omega

theorem eq_of_not_mem {d : Fin 6 → F} {l0 : F} (hW : (Eset d l0).card = 5) {r s : Fin 6}
    (hr : ¬ d r = l0) (hs : ¬ d s = l0) : r = s := by
  by_contra hrs
  have hC := card_add_card_compl d l0
  have hsub : ({r, s} : Finset (Fin 6)) ⊆ Finset.univ.filter fun k : Fin 6 => ¬ d k = l0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [hr]
    · simp [hs]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_pair hrs] at h1
  omega

theorem entry_rel {m : Matrix (Fin 6) (Fin 6) F} {φ : F ≃+* F} {t : Fin 6 → F}
    (h : m * (Matrix.diagonal t).map φ = Matrix.diagonal t * m) (r s : Fin 6) :
    m r s * φ (t s) = t r * m r s := by
  rw [Matrix.diagonal_map (map_zero φ)] at h
  have := congrFun (congrFun h r) s
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this

theorem swap_hd {d : Fin 6 → F} {i j : Fin 6} (hdij : d i = d j) (s : Fin 6) :
    d (Equiv.swap i j s) = d s := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1
    exact hdij.symm
  · subst h2
    exact hdij
  · rfl

theorem swap_move {d : Fin 6 → F} {l0 : F} {i j : Fin 6} (hi : d i = l0) (hj : d j = l0)
    (s : Fin 6) (hs : Equiv.swap i j s ≠ s) : d s = l0 := by
  rw [Equiv.swap_apply_def] at hs
  split_ifs at hs with h1 h2
  · subst h1
    exact hi
  · subst h2
    exact hj
  · exact absurd rfl hs

theorem diag_fix [Finite F] (hF : Nat.card F = (2 ^ 2) ^ 2) {d : Fin 6 → F} {l0 : F}
    (hl0 : l0 ≠ 1) (hl5 : l0 ^ 5 = 1) (hW : (Eset d l0).card = 5) (hd5 : ∀ k, d k ^ 5 = 1)
    (hdet : ∏ k, d k = 1) (A : GL (Fin 6) F)
    (hA : ((A : Matrix (Fin 6) (Fin 6) F).map (fun x : F => x ^ 4))ᵀ *
      (A : Matrix (Fin 6) (Fin 6) F) = 1)
    (φ : F ≃+* F)
    (hrel : ∀ x : ↥(StatedSU 6 (2 ^ 2) F), x ∈ Ug d l0 →
      (A : Matrix (Fin 6) (Fin 6) F) * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map φ =
        ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (A : Matrix (Fin 6) (Fin 6) F)) :
    ∃ j : ℕ, ∃ b : F, b ≠ 0 ∧ (A : Matrix (Fin 6) (Fin 6) F) =
      Matrix.scalar (Fin 6) b * Matrix.diagonal (fun k => d k ^ j) ∧ ∀ x, φ x = x := by
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  have hl0z : l0 ≠ 0 := by
    rintro rfl
    norm_num at hl5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set m : Matrix (Fin 6) (Fin 6) F := (A : Matrix (Fin 6) (Fin 6) F) with hm
  have hT : ∀ i l : Fin 6, d i = l0 → d l = l0 → i ≠ l →
      m * (Matrix.diagonal (tt l0 i l)).map φ = Matrix.diagonal (tt l0 i l) * m := by
    intro i l hi hl hil
    have htdet : ∏ k, tt l0 i l k = 1 := by
      rw [tt_prod l0 hil, mul_inv_cancel₀ hl0z]
    have hoff : ∀ k, ¬ d k = l0 → tt l0 i l k = 1 := by
      intro k hk
      apply tt_other l0
      · rintro rfl
        exact hk hi
      · rintro rfl
        exact hk hl
    exact hrel _ (diagU_mem_Ug hF (tt_ne_zero hl0z i l) (tt_pow5 hl5 i l) htdet hoff)
  have hoffdiag : ∀ r s : Fin 6, r ≠ s → m r s = 0 := by
    intro r s hrs
    by_cases hr : d r = l0
    · obtain ⟨l, hl, hlr, hls⟩ := exists_avoid hW r s
      have e := entry_rel (hT r l hr hl (Ne.symm hlr)) r s
      rw [tt_other l0 (Ne.symm hrs) (Ne.symm hls), tt_i, map_one] at e
      have h1 : (1 - l0) * m r s = 0 := by linear_combination e
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (sub_eq_zero.1 h).symm hl0
      · exact h
    · have hs : d s = l0 := (mem_of_ne_pair hW hrs).resolve_left hr
      obtain ⟨l, hl, hls, -⟩ := exists_avoid hW s s
      have hrl : r ≠ l := by
        rintro rfl
        exact hr hl
      have e := entry_rel (hT s l hs hl (Ne.symm hls)) r s
      rw [tt_other l0 hrs hrl, tt_i] at e
      have hφl : φ l0 ≠ 1 := by
        intro h
        apply hl0
        apply φ.injective
        rw [h, map_one]
      have h1 : (φ l0 - 1) * m r s = 0 := by linear_combination e
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (sub_eq_zero.1 h) hφl
      · exact h
  have hdiagpow : ∀ r : Fin 6, m r r ^ 5 = 1 := by
    intro r
    have h := congrFun (congrFun hA r) r
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single r] at h
    · simp only [Matrix.transpose_apply, Matrix.map_apply] at h
      rw [pow_succ]
      exact h
    · intro k _ hk
      simp [Matrix.transpose_apply, Matrix.map_apply, hoffdiag k r hk]
    · intro h'
      exact absurd (Finset.mem_univ r) h'
  have hne0 : ∀ r : Fin 6, m r r ≠ 0 := by
    intro r h0
    have := hdiagpow r
    rw [h0] at this
    norm_num at this
  obtain ⟨r0, hr0⟩ : ∃ r0 : Fin 6, d r0 = l0 := by
    obtain ⟨r0, hr0⟩ := Finset.card_pos.1 (by omega : 0 < (Eset d l0).card)
    exact ⟨r0, (mem_Eset' d l0 r0).1 hr0⟩
  have hφl0 : φ l0 = l0 := by
    obtain ⟨l, hl, hlr, -⟩ := exists_avoid hW r0 r0
    have e := entry_rel (hT r0 l hr0 hl (Ne.symm hlr)) r0 r0
    rw [tt_i] at e
    have e2 : m r0 r0 * φ l0 = m r0 r0 * l0 := by rw [e, mul_comm]
    exact mul_left_cancel₀ (hne0 r0) e2
  have hφid : ∀ x, φ x = x := apply_eq_of_fix_fifth hF16 φ hl5 hl0 hφl0
  have hmapid : ∀ M : Matrix (Fin 6) (Fin 6) F, M.map φ = M := fun M => by
    ext r s
    simp [hφid]
  have hP : ∀ i j : Fin 6, d i = l0 → d j = l0 → i ≠ j →
      m * permM (Equiv.swap i j) = permM (Equiv.swap i j) * m := by
    intro i j hi hj _
    have hd : ∀ s, d (Equiv.swap i j s) = d s := swap_hd (hi.trans hj.symm)
    have hmove : ∀ s, Equiv.swap i j s ≠ s → d s = l0 := swap_move hi hj
    have h := hrel _ (permU_mem_Ug hF (d := d) (l0 := l0) (Equiv.swap i j)
      (fun s => Equiv.swap_apply_self i j s) hd hmove)
    rw [hmapid] at h
    exact h
  have hdiag_eq : ∀ i j : Fin 6, d i = l0 → d j = l0 → i ≠ j → m i i = m j j := by
    intro i j hi hj hij
    have h := congrFun (congrFun (hP i j hi hj hij) i) j
    have key : ∀ k : Fin 6, (i = Equiv.swap i j k) ↔ k = j := by
      intro k
      rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
    simp only [Matrix.mul_apply, permM, Matrix.of_apply, key, Equiv.swap_apply_right,
      Equiv.swap_apply_left, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  obtain ⟨i0, hi0⟩ : ∃ r : Fin 6, d r = l0 := ⟨r0, hr0⟩
  have hWconst : ∀ r, d r = l0 → m r r = m i0 i0 := by
    intro r hr
    by_cases h : r = i0
    · rw [h]
    · exact hdiag_eq r i0 hr hi0 h
  obtain ⟨k0, hk0⟩ : ∃ k, ¬ d k = l0 := by
    by_contra h
    push Not at h
    have hall : Eset d l0 = Finset.univ := by
      ext k
      simp [Eset, h k]
    rw [hall] at hW
    simp at hW
  have hcompl : ∀ r, ¬ d r = l0 → m r r = m k0 k0 := by
    intro r hr
    rw [eq_of_not_mem hW hr hk0]
  have hab5 : (m i0 i0 / m k0 k0) ^ 5 = 1 := by
    rw [div_pow, hdiagpow i0, hdiagpow k0, div_one]
  have hprim : IsPrimitiveRoot l0 5 := by
    have h := IsPrimitiveRoot.orderOf l0
    rw [orderOf_eq_prime hl5 hl0] at h
    exact h
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hab5
  have hb0 : m k0 k0 ≠ 0 := hne0 k0
  have hab : m i0 i0 = m k0 k0 * l0 ^ j := by
    rw [hj]
    field_simp
  refine ⟨j, m k0 k0, hb0, ?_, hφid⟩
  ext r s
  rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  by_cases hrs : r = s
  · subst hrs
    by_cases hr : d r = l0
    · rw [Matrix.diagonal_apply_eq, hWconst r hr, hab, hr]
    · have h1 := compl_eq_one hW hd5 hdet r hr
      rw [Matrix.diagonal_apply_eq, hcompl r hr]
      simp [h1]
  · rw [Matrix.diagonal_apply_ne _ hrs, hoffdiag r s hrs]

end CFSG.LocalAnalysis.GLTheoremA.Y10GU6
