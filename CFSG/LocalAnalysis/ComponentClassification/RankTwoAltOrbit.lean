module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIITransport

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm

abbrev Pt (m : ℕ) : Type := (Fin m × Fin 2) × Fin 2

@[expose] def aM (m : ℕ) : Perm (Pt m) := prodCongr (Equiv.refl _) (swap 0 1)

@[expose] def bM (m : ℕ) : Perm (Pt m) := prodCongr (prodCongr (Equiv.refl _) (swap 0 1)) (Equiv.refl _)

@[expose] def cM : Perm (Pt 2) := prodCongr (prodCongr (swap 0 1) (Equiv.refl _)) (Equiv.refl _)

variable {α : Type*}

@[expose] def pw (y : Perm α) (s : Fin 2) : Perm α := if s = 0 then 1 else y

theorem pw_one (y : Perm α) : pw y 1 = y := rfl

theorem pw_mul_pw {y : Perm α} (hy : y * y = 1) (s s' : Fin 2) : pw y s * pw y s' = pw y (s + s') := by
  fin_cases s <;> fin_cases s' <;> simp [pw, hy]

theorem pw_comm {y z : Perm α} (hyz : y * z = z * y) (s j : Fin 2) : pw y s * pw z j = pw z j * pw y s := by
  fin_cases s <;> fin_cases j <;> simp [pw, hyz]

@[expose] def orbitMap (ya yb : Perm α) {m : ℕ} (r : Fin m → α) (p : Pt m) : α :=
  (pw ya p.2 * pw yb p.1.2) (r p.1.1)

section

variable {ya yb : Perm α} (ha2 : ya * ya = 1) (hb2 : yb * yb = 1) (hab : ya * yb = yb * ya)
include ha2 hb2 hab

theorem pw_mul_pw_mul (s j s' j' : Fin 2) :
    pw ya s * pw yb j * (pw ya s' * pw yb j') = pw ya (s + s') * pw yb (j + j') := by
  rw [← pw_mul_pw ha2, ← pw_mul_pw hb2]
  have h := pw_comm hab s' j
  calc pw ya s * pw yb j * (pw ya s' * pw yb j')
      = pw ya s * (pw yb j * pw ya s') * pw yb j' := by group
    _ = pw ya s * (pw ya s' * pw yb j) * pw yb j' := by rw [← h]
    _ = pw ya s * pw ya s' * (pw yb j * pw yb j') := by group

theorem pw_mul_pw_mul_self (s j : Fin 2) : pw ya s * pw yb j * (pw ya s * pw yb j) = 1 := by
  rw [pw_mul_pw_mul ha2 hb2 hab]
  fin_cases s <;> fin_cases j <;> rfl

theorem orbitMap_injective {m : ℕ} {r : Fin m → α}
    (hreg : ∀ k (s j : Fin 2), (pw ya s * pw yb j) (r k) = r k → s = 0 ∧ j = 0)
    (horb : ∀ k l (s j : Fin 2), (pw ya s * pw yb j) (r k) = r l → k = l) :
    Function.Injective (orbitMap ya yb r) := by
  rintro ⟨⟨k, j⟩, s⟩ ⟨⟨k', j'⟩, s'⟩ h
  simp only [orbitMap] at h
  have h1 : (pw ya (s' + s) * pw yb (j' + j)) (r k) = r k' := by
    rw [← pw_mul_pw_mul ha2 hb2 hab, Perm.mul_apply, h, ← Perm.mul_apply,
      pw_mul_pw_mul_self ha2 hb2 hab, Perm.one_apply]
  obtain rfl := horb k k' _ _ h1
  obtain ⟨hs, hj⟩ := hreg k _ _ h1
  have hs' : s = s' := by
    fin_cases s <;> fin_cases s' <;> first | rfl | exact absurd hs (by decide)
  have hj' : j = j' := by
    fin_cases j <;> fin_cases j' <;> first | rfl | exact absurd hj (by decide)
  rw [hs', hj']

omit hb2 hab in
theorem orbitMap_aM {m : ℕ} (r : Fin m → α) (p : Pt m) :
    ya (orbitMap ya yb r p) = orbitMap ya yb r (aM m p) := by
  obtain ⟨⟨k, j⟩, s⟩ := p
  have hs : ya * pw ya s = pw ya (swap 0 1 s) := by
    rw [show ya * pw ya s = pw ya 1 * pw ya s from rfl, pw_mul_pw ha2]
    congr 1
    fin_cases s <;> rfl
  simp only [orbitMap, aM, prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [← Perm.mul_apply, ← mul_assoc, hs]

omit ha2 in
theorem orbitMap_bM {m : ℕ} (r : Fin m → α) (p : Pt m) :
    yb (orbitMap ya yb r p) = orbitMap ya yb r (bM m p) := by
  obtain ⟨⟨k, j⟩, s⟩ := p
  have h1 : yb * pw ya s = pw ya s * yb := by
    have := pw_comm hab.symm 1 s
    rwa [pw_one] at this
  have hj : yb * pw yb j = pw yb (swap 0 1 j) := by
    rw [show yb * pw yb j = pw yb 1 * pw yb j from rfl, pw_mul_pw hb2]
    congr 1
    fin_cases j <;> rfl
  simp only [orbitMap, bM, prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [← Perm.mul_apply, ← mul_assoc, h1, mul_assoc, hj]

end

theorem orbitMap_cM {ya yb yc : Perm α} (hc2 : yc * yc = 1) (hac : ya * yc = yc * ya)
    (hbc : yb * yc = yc * yb) {r : Fin 2 → α} (hr : yc (r 0) = r 1) (p : Pt 2) :
    yc (orbitMap ya yb r p) = orbitMap ya yb r (cM p) := by
  obtain ⟨⟨k, j⟩, s⟩ := p
  have hr' : yc (r 1) = r 0 := by rw [← hr, ← Perm.mul_apply, hc2, Perm.one_apply]
  have h1 : yc * pw ya s = pw ya s * yc := by
    have := pw_comm hac s 1
    rw [pw_one] at this
    exact this.symm
  have h2 : yc * pw yb j = pw yb j * yc := by
    have := pw_comm hbc j 1
    rw [pw_one] at this
    exact this.symm
  have hcomm : yc * (pw ya s * pw yb j) = pw ya s * pw yb j * yc := by
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  simp only [orbitMap, cM, prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [← Perm.mul_apply, hcomm, Perm.mul_apply]
  congr 1
  fin_cases k
  · exact hr
  · exact hr'

end CFSG.ComponentClassification.RankTwoAlt
