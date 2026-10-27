module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairing

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section PermLemmas

variable {n : ℕ}

theorem dbl_mul_self {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    (swap a b * swap c d) * (swap a b * swap c d) = 1 := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  ext x
  by_cases hx1 : x = a
  · subst hx1
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx2 : x = b
  · subst hx2
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx3 : x = c
  · subst hx3
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx4 : x = d
  · subst hx4
    simp [Perm.mul_apply, swap_apply_def, *]
  simp [Perm.mul_apply, swap_apply_def, *]

theorem dbl_inv {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    (swap a b * swap c d)⁻¹ = swap a b * swap c d :=
  inv_eq_of_mul_eq_one_right (dbl_mul_self hab hac had hbc hbd hcd)

theorem card_support_dbl {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (swap a b * swap c d).support.card = 4 := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  have hset : (swap a b * swap c d).support = {a, b, c, d} := by
    ext x
    rw [Perm.mem_support]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hx1 : x = a
    · subst hx1
      simp [Perm.mul_apply, swap_apply_def, *]
    by_cases hx2 : x = b
    · subst hx2
      simp [Perm.mul_apply, swap_apply_def, *]
    by_cases hx3 : x = c
    · subst hx3
      simp [Perm.mul_apply, swap_apply_def, *]
    by_cases hx4 : x = d
    · subst hx4
      simp [Perm.mul_apply, swap_apply_def, *]
    simp [Perm.mul_apply, swap_apply_def, *]
  rw [hset]
  simp [Finset.card_insert_of_notMem, *]

theorem dbl_mul_apply {σ : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (ha : σ a = b) (hb : σ b = a)
    (hc : σ c = d) (hd : σ d = c) (x : Fin n) :
    (swap a b * swap c d * σ) x = if x = a ∨ x = b ∨ x = c ∨ x = d then x else σ x := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  by_cases hx1 : x = a
  · subst hx1
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx2 : x = b
  · subst hx2
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx3 : x = c
  · subst hx3
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx4 : x = d
  · subst hx4
    simp [Perm.mul_apply, swap_apply_def, *]
  have hσx : σ x ≠ a ∧ σ x ≠ b ∧ σ x ≠ c ∧ σ x ≠ d := by
    refine ⟨fun h => hx2 (σ.injective (h.trans hb.symm)),
      fun h => hx1 (σ.injective (h.trans ha.symm)),
      fun h => hx4 (σ.injective (h.trans hd.symm)),
      fun h => hx3 (σ.injective (h.trans hc.symm))⟩
  simp [Perm.mul_apply, swap_apply_def, hx1, hx2, hx3, hx4, hσx.1, hσx.2.1, hσx.2.2.1,
    hσx.2.2.2]

theorem card_support_dbl_mul {σ : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (ha : σ a = b) (hb : σ b = a)
    (hc : σ c = d) (hd : σ d = c) :
    (swap a b * swap c d * σ).support.card + 4 = σ.support.card := by
  have hset : (swap a b * swap c d * σ).support = σ.support \ {a, b, c, d} := by
    ext x
    rw [Perm.mem_support, Finset.mem_sdiff, Perm.mem_support,
      dbl_mul_apply hab hac had hbc hbd hcd ha hb hc hd x]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hx : x = a ∨ x = b ∨ x = c ∨ x = d
    · simp [hx]
    · simp [hx]
  have hsub : ({a, b, c, d} : Finset (Fin n)) ⊆ σ.support := by
    intro x hx
    rw [Perm.mem_support]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [ha]; exact hab.symm
    · rw [hb]; exact hab
    · rw [hc]; exact hcd.symm
    · rw [hd]; exact hcd
  have hcard : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
    have := hab.symm
    have := hac.symm
    have := had.symm
    have := hbc.symm
    have := hbd.symm
    have := hcd.symm
    simp [Finset.card_insert_of_notMem, *]
  rw [hset, Finset.card_sdiff_of_subset hsub, hcard]
  have := Finset.card_le_card hsub
  omega

theorem exists_dbl_decomp {σ : Perm (Fin n)} (h2 : σ * σ = 1) (hs : sign σ = 1) (h1 : σ ≠ 1) :
    ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c ∧
      (swap a b * swap c d * σ).support.card + 4 = σ.support.card ∧
      (swap a b * swap c d * σ) * (swap a b * swap c d * σ) = 1 ∧
      sign (swap a b * swap c d * σ) = 1 := by
  obtain ⟨a, b, c, d, h12, h1b1, h1b2, h2b1, h2b2, hbb, e1, e2, e3, e4⟩ :=
    exists_swap_pairs (σ := σ) (Perm.mem_alternatingGroup.2 hs) h2 h1
  have hab : a ≠ b := h1b1
  have hac : a ≠ c := h12
  have had : a ≠ d := h1b2
  have hbc : b ≠ c := h2b1.symm
  have hbd : b ≠ d := hbb
  have hcd : c ≠ d := h2b2
  refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, e1, e3, e2, e4,
    card_support_dbl_mul hab hac had hbc hbd hcd e1 e3 e2 e4, ?_, ?_⟩
  · ext x
    have hx := dbl_mul_apply hab hac had hbc hbd hcd e1 e3 e2 e4 x
    have hinv : ∀ y, σ (σ y) = y := fun y => by
      have := congrArg (fun p : Perm (Fin n) => p y) h2
      simpa using this
    by_cases hmem : x = a ∨ x = b ∨ x = c ∨ x = d
    · simp only [Perm.mul_apply, hx, hmem, ite_true, Perm.coe_one, id_eq]
    · have hmem' : ¬ (σ x = a ∨ σ x = b ∨ σ x = c ∨ σ x = d) := by
        rintro (h | h | h | h)
        · exact hmem (Or.inr (Or.inl (σ.injective (h.trans e3.symm))))
        · exact hmem (Or.inl (σ.injective (h.trans e1.symm)))
        · exact hmem (Or.inr (Or.inr (Or.inr (σ.injective (h.trans e4.symm)))))
        · exact hmem (Or.inr (Or.inr (Or.inl (σ.injective (h.trans e2.symm)))))
      have hx' := dbl_mul_apply hab hac had hbc hbd hcd e1 e3 e2 e4 (σ x)
      simp only [Perm.mul_apply, hx, hmem, hmem', ite_false, hx', hinv x, Perm.coe_one, id_eq]
  · rw [Perm.sign_mul, hs, mul_one, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide

end PermLemmas

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.sq_dbl_ne_one (C : CoverSetup n K) (hn : 8 ≤ n) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {x : K}
    (hx : C.ρ x = swap a b * swap c d) : x * x ≠ 1 :=
  C.dblI_sq_ne_one hn (x := x) ⟨by rw [hx]; exact dbl_mul_self hab hac had hbc hbd hcd,
    by rw [hx]; exact card_support_dbl hab hac had hbc hbd hcd⟩

theorem CoverSetup.four_dvd_and_sq_eq_one_iff (C : CoverSetup n K) (hn : 8 ≤ n) :
    ∀ (m : ℕ) (x : K), C.ρ x * C.ρ x = 1 → (C.ρ x).support.card = m →
      4 ∣ m ∧ (x * x = 1 ↔ 8 ∣ m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hx2 hm
    by_cases h1 : C.ρ x = 1
    · have hm0 : m = 0 := by rw [← hm, h1]; simp
      subst hm0
      exact ⟨dvd_zero _, ⟨fun _ => dvd_zero _, fun _ => C.sq_of_mem_center
        ((C.ρ_eq_one_iff).1 h1)⟩⟩
    · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd, hcard, hσ'2, hσ's⟩ :=
        exists_dbl_decomp hx2 (C.sign_ρ x) h1
      set δ : Perm (Fin n) := swap a b * swap c d with hδ
      obtain ⟨xδ, hxδ⟩ := C.exists_ρ_eq (σ := δ) (by
        rw [hδ, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]; decide)
      set y : K := xδ⁻¹ * x with hy
      have hρy : C.ρ y = δ * C.ρ x := by
        rw [hy, map_mul, map_inv, hxδ, hδ, dbl_inv hab hac had hbc hbd hcd]
      have hxy : x = xδ * y := by rw [hy]; group
      have hy2 : C.ρ y * C.ρ y = 1 := by rw [hρy]; exact hσ'2
      have hycard : (C.ρ y).support.card + 4 = m := by rw [hρy, hm.symm]; exact hcard
      obtain ⟨h4y, hyiff⟩ := ih (C.ρ y).support.card (by omega) y hy2 rfl
      have hfix : ∀ z, (z = a ∨ z = b ∨ z = c ∨ z = d) → (δ * C.ρ x) z = z := fun z hz => by
        rw [hδ, dbl_mul_apply hab hac had hbc hbd hcd ha hb hc hd z]
        simp [hz]
      have hcomm : y * xδ = xδ * y := by
        have hind := C.induces_conj y
        rw [hρy] at hind
        have := hind.apply_eq_of_dbl_fixed hab hac had hbc hbd hcd (hfix a (Or.inl rfl))
          (hfix b (Or.inr (Or.inl rfl))) (hfix c (Or.inr (Or.inr (Or.inl rfl))))
          (hfix d (Or.inr (Or.inr (Or.inr rfl)))) hxδ
        simp only [MulAut.conj_apply] at this
        calc y * xδ = (y * xδ * y⁻¹) * y := by group
          _ = xδ * y := by rw [this]
      have hxδ2 : xδ * xδ ≠ 1 := C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hxδ
      have hxδc : xδ * xδ ∈ center K := C.sq_mem_center (by
        rw [hxδ, hδ]; exact dbl_mul_self hab hac had hbc hbd hcd)
      have hyc : y * y ∈ center K := C.sq_mem_center hy2
      have hxx : x * x = (xδ * xδ) * (y * y) := by
        rw [hxy]
        calc xδ * y * (xδ * y) = xδ * (y * xδ) * y := by group
          _ = xδ * (xδ * y) * y := by rw [hcomm]
          _ = (xδ * xδ) * (y * y) := by group
      have hsq : (xδ * xδ) * (xδ * xδ) = 1 := C.sq_of_mem_center hxδc
      have h4 : 4 ∣ m := by omega
      refine ⟨h4, ?_⟩
      constructor
      · intro h
        have : y * y ≠ 1 := by
          intro h1y
          rw [h1y, mul_one] at hxx
          exact hxδ2 (hxx ▸ h)
        have h8 : ¬ 8 ∣ (C.ρ y).support.card := fun h8 => this (hyiff.2 h8)
        omega
      · intro h8
        have h8y : ¬ 8 ∣ (C.ρ y).support.card := by omega
        have hyne : y * y ≠ 1 := fun h1y => h8y (hyiff.1 h1y)
        have : y * y = xδ * xδ := C.center_eq_of_ne_one hyc hxδc hyne hxδ2
        rw [hxx, this]
        exact hsq

theorem CoverSetup.sq_eq_one_iff_dvd (C : CoverSetup n K) (hn : 8 ≤ n) {x : K}
    (hx : C.ρ x * C.ρ x = 1) : x * x = 1 ↔ 8 ∣ (C.ρ x).support.card :=
  ((C.four_dvd_and_sq_eq_one_iff hn _ x hx rfl).2)

end AhatData

theorem sq_eq_one_iff_dvd_of_doubleCover {n : ℕ} (hn : 8 ≤ n) {K : Type} [Group K]
    (hK : IsDoubleCoverOfAlt K n) (π : K →* alternatingGroup (Fin n))
    (hπs : Function.Surjective π) (hπk : π.ker = center K) {x : K}
    (hx : (π x : Perm (Fin n)) * (π x : Perm (Fin n)) = 1) :
    x * x = 1 ↔ 8 ∣ (π x : Perm (Fin n)).support.card :=
  AhatData.CoverSetup.sq_eq_one_iff_dvd (⟨π, hπs, hπk, hK⟩ : AhatData.CoverSetup n K) hn hx

end CFSG.OddStandard.Solomon75
