module

public import Certificates.Data.G23RecogHCharInputs
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HChar

open CFSG.GH74.QTGen4.Recog.G23.HCharData

@[expose] def hcT : Fin 20 → Fin 20 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1],
    ![2, 2, 2, -1, -1, 2, 2, -1, 2, 2, 2, -1, -1, -1, -1, 0, 0, 0, 0, 0],
    ![3, 3, -1, 0, 0, -1, 3, 0, 3, 3, -1, 0, 0, 0, 0, -1, 1, 1, 1, -1],
    ![3, 3, -1, 0, 0, -1, 3, 0, 3, 3, -1, 0, 0, 0, 0, 1, -1, -1, -1, 1],
    ![2, 2, 2, 2, 2, 2, 2, 2, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0],
    ![3, 3, 3, 3, 3, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 1],
    ![3, 3, 3, 3, 3, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, -1],
    ![9, 9, -3, 0, 0, 1, -3, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, -1],
    ![9, 9, -3, 0, 0, 1, -3, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, -1, 1],
    ![6, 6, -2, 0, 0, -2, 6, 0, -3, -3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![6, 6, 6, -3, -3, -2, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 2, -1, -1, 2, 2, -1, -1, -1, -1, -1, -1, 2, 2, 0, 0, 0, 0, 0],
    ![2, 2, 2, -1, -1, 2, 2, -1, -1, -1, -1, 2, 2, -1, -1, 0, 0, 0, 0, 0],
    ![4, -4, 0, -2, 2, 0, 0, 0, -2, 2, 0, 1, -1, 1, -1, 0, 0, -2, 2, 0],
    ![4, -4, 0, -2, 2, 0, 0, 0, -2, 2, 0, 1, -1, 1, -1, 0, 0, 2, -2, 0],
    ![8, -8, 0, -4, 4, 0, 0, 0, 2, -2, 0, -1, 1, -1, 1, 0, 0, 0, 0, 0],
    ![8, -8, 0, 2, -2, 0, 0, 0, -4, 4, 0, -1, 1, -1, 1, 0, 0, 0, 0, 0],
    ![8, -8, 0, 2, -2, 0, 0, 0, 2, -2, 0, -1, 1, 2, -2, 0, 0, 0, 0, 0],
    ![8, -8, 0, 2, -2, 0, 0, 0, 2, -2, 0, 2, -2, -1, 1, 0, 0, 0, 0, 0]]

@[expose] def hcDcl : Fin 15 → Fin 20 := ![1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 19]

@[expose] def hcQ : Fin 15 → Fin 15 → ℤ :=
  ![![-9, 2, 2, 2, 6, -8, -8, -8, 3, 3, 10, -4, 6, -9, 18],
    ![18, 12, 12, 12, -12, 0, 0, 0, 18, -6, -12, 0, 12, 18, 36],
    ![0, 16, -8, -8, 0, -32, 16, 16, 24, 0, 8, -16, 24, 0, 0],
    ![0, 16, -8, -8, 0, 32, -16, -16, 24, 0, 8, 16, 24, 0, 0],
    ![18, 12, 12, 12, 36, 0, 0, 0, -6, 18, -12, 0, 12, 18, 36],
    ![0, 96, -48, -48, 0, 0, 0, 0, -48, 0, 48, 0, -48, 0, 0],
    ![0, -8, -8, -8, -24, 16, -32, 16, 0, 24, 8, -16, 24, 0, 0],
    ![0, -8, -8, -8, -24, -16, 32, -16, 0, 24, 8, 16, 24, 0, 0],
    ![0, -48, -48, -48, 48, 0, 0, 0, 0, -48, 48, 0, -48, 0, 0],
    ![0, -32, -32, 64, 0, -32, -32, -32, 0, 0, 32, 32, 0, 0, 0],
    ![0, -32, -32, 64, 0, 32, 32, 32, 0, 0, 32, -32, 0, 0, 0],
    ![0, -32, 64, -32, 0, -32, -32, 64, 0, 0, 32, 32, 0, 0, 0],
    ![0, -32, 64, -32, 0, 32, 32, -64, 0, 0, 32, -32, 0, 0, 0],
    ![72, 0, 0, 0, 0, 0, 0, 0, -72, -72, 0, 0, 0, -72, 0],
    ![72, 0, 0, 0, 0, 0, 0, 0, 72, 72, 0, 0, 0, -72, 0]]

@[expose] def psiTab (k : Fin 15) (j : Fin 20) : ℤ :=
  ((psiTerms k).map fun p => p.2 * hcT p.1 j).sum

theorem sum_size : ∑ j, hcSize j = 576 := by decide +kernel

theorem row_orth : ∀ m n : Fin 20,
    ∑ j, (hcSize j : ℤ) * hcT m j * hcT n j = if m = n then 576 else 0 := by decide +kernel

theorem col_orth : ∀ j j' : Fin 20,
    (hcSize j : ℤ) * ∑ m, hcT m j * hcT m j' = if j = j' then 576 else 0 := by decide +kernel

theorem eig : ∀ (m : Fin 20) (r : Fin 4) (j : Fin 20),
    hcT m 0 * ∑ k, (hcSize k : ℤ) * hcA r j k * hcT m k =
      hcSize (hcI r) * hcT m (hcI r) * (hcSize j * hcT m j) := by decide +kernel

theorem sep : ∀ m n : Fin 20,
    (∀ r, hcT m (hcI r) * hcT n 0 = hcT n (hcI r) * hcT m 0) → m = n := by decide +kernel

theorem deg_eq : ∀ m : Fin 20, hcT m 0 = (charDegs m : ℤ) := by decide +kernel

theorem deg_pos : ∀ m : Fin 20, 0 < hcT m 0 := by decide +kernel

theorem sum_deg_sq : ∑ m, (hcT m 0) ^ 2 = 576 := by decide +kernel

theorem triv_row : ∀ j, hcT 0 j = 1 := by decide +kernel

theorem row_inj : ∀ m n : Fin 20, (∀ j, hcT m j = hcT n j) → m = n := by decide +kernel

theorem psi_vanish : ∀ (k : Fin 15) (j : Fin 20), hcDfl j = false → psiTab k j = 0 := by
  decide +kernel

theorem psi_gram : ∀ k l : Fin 15,
    ∑ j, (hcSize j : ℤ) * psiTab k j * psiTab l j = 576 * psiGram k l := by decide +kernel

theorem psi_triv : ∀ k : Fin 15,
    ∑ j, (hcSize j : ℤ) * psiTab k j * hcT 0 j = if k = 0 ∨ k = 10 then 576 else 0 := by
  decide +kernel

theorem psi_chi9 : ∀ k : Fin 15, k ≠ 0 →
    ∑ j, (hcSize j : ℤ) * psiTab k j * hcT 8 j = 0 := by decide +kernel

theorem chi9_z : hcT 8 1 = 9 := by decide +kernel

theorem chi20_z : hcT 19 1 = -8 := by decide +kernel

theorem chi9_order4 : ∀ j : Fin 20, hcOrd j = 4 → hcDfl j = true → hcT 8 j = -3 := by
  decide +kernel

theorem sum_chi9 : ∑ j, (if hcDfl j = true then (hcSize j : ℤ) * hcT 8 j else 0) = -171 := by
  decide +kernel

theorem count_invol : ∑ j, (if hcOrd j = 2 ∧ j ≠ 1 then hcSize j else 0) = 90 := by decide +kernel

theorem count_order4 : ∑ j, (if hcOrd j = 4 ∧ hcDfl j = false then hcSize j else 0) = 72 := by
  decide +kernel

theorem count_D : ∑ j, (if hcDfl j = true then hcSize j else 0) = 413 := by decide +kernel

theorem sum_N :
    ∑ j, (if hcDfl j = true then (hcSize j : ℤ) * psiTab 0 j * hcCt j else 0) = 7200 := by
  decide +kernel

theorem span_inv : ∀ l l' : Fin 15,
    ∑ k, hcQ l k * psiTab k (hcDcl l') = if l = l' then 576 else 0 := by decide +kernel

theorem dcl_surj : ∀ j : Fin 20, hcDfl j = true → ∃ l, hcDcl l = j := by decide +kernel

end CFSG.GH74.QTGen4.Recog.G23.P7.HChar
