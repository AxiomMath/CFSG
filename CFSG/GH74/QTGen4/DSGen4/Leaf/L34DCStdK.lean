module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCCert

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open Certificates.L34DC
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open CFSG.QuasithinUnique.Fin257 CFSG.QuasithinUnique.Fin257.L3
open CFSG.GH74.KGroups (GF4)
open CFSG.Quasithin.H13.F431.L3.P3

theorem elt_64 : elt 64 = (0, 0, 0, 1) := by decide +kernel

theorem nfY_xw (x : Elt) (h1 : x.2.1 = 0) (h2 : x.2.2.2 = 0) :
    nfY x = xP (psi x.1) * wP (psi x.2.2.1) := by
  unfold nfY
  rw [h1, h2, map_zero, yP_zero, dd_zero, mul_one, mul_one, wP_mul_xP]

theorem nfY_yw (x : Elt) (h1 : x.1 = 0) (h2 : x.2.2.2 = 0) :
    nfY x = yP (psi x.2.1) * wP (psi x.2.2.1) := by
  unfold nfY
  rw [h1, h2, map_zero, xP_zero, dd_zero, mul_one, mul_one, wP_mul_yP]

theorem dB_val : dB.1 = dd 1 := by
  show nfY (elt 64) = dd 1
  rw [elt_64]
  simp only [nfY, map_zero, wP_zero, xP_zero, yP_zero, one_mul, mul_one]

theorem eB16_val : (eB 16).1 = xP 1 := by
  show nfY (elt 16) = xP 1
  rw [elt_16]
  simp only [nfY, map_zero, map_one, wP_zero, yP_zero, dd_zero, mul_one, one_mul]

theorem eB4_val : (eB 4).1 = yP 1 := by
  show nfY (elt 4) = yP 1
  rw [elt_4]
  simp only [nfY, map_zero, map_one, wP_zero, xP_zero, dd_zero, mul_one, one_mul]

theorem eB_injective : Function.Injective eB := by
  intro i j h
  have h1 : nfY (elt i) = nfY (elt j) := congrArg Subtype.val h
  have h2 : elt i = elt j := nfY_inj h1
  rw [← idx_elt i, ← idx_elt j, h2]

theorem eB_surjective : Function.Surjective eB :=
  fun g => ⟨ιB g, Subtype.ext (nfY_elt_ιB g)⟩

theorem natCard_B0K : Nat.card B0 = 192 := by
  rw [← Nat.card_eq_of_bijective eB ⟨eB_injective, eB_surjective⟩, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem dB_ne_one : dB ≠ 1 := by
  intro h
  have h' : nfY (elt 64) = 1 := congrArg Subtype.val h
  have h'' : elt 64 = one := nfY_inj (by rw [h', nfY_one])
  rw [elt_64] at h''
  exact absurd (congrArg (fun x : Elt => x.2.2.2) h'') (by decide)

theorem dB_pow_three : dB ^ 3 = 1 := by
  have h1 : dB * dB = eB 128 := by
    show eBx (elt 64) * eBx (elt 64) = eBx (elt 128)
    rw [← eBx_mul]
    congr 1
  have h2 : eB 128 * dB = 1 := by
    show eBx (elt 128) * eBx (elt 64) = 1
    rw [← eBx_mul]
    have : mulE (elt 128) (elt 64) = one := by decide +kernel
    rw [this]
    apply Subtype.ext
    exact nfY_one
  rw [pow_three', h1, h2]

theorem orderOf_dB : orderOf dB = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime dB_pow_three dB_ne_one

theorem eB_eq_evalB (i : Fin 192) :
    eB i = evalB (word (wordArr ()) i) gY := by
  apply Subtype.ext
  have h1 := nfY_evalW (gStd ()) gY nfY_gStd (word (wordArr ()) i)
  rw [Certificates.certificate5167.1 i] at h1
  exact h1

theorem B0_words (g : ↥B0) :
    ∃ w : List (Fin 3), g = evalB w gY := by
  refine ⟨word (wordArr ()) (ιB g), ?_⟩
  rw [← eB_eq_evalB]
  exact Subtype.ext (nfY_elt_ιB g).symm

theorem kClass (n : MulAut ↥B0)
    (hd : n dB = dB ∨ n dB = dB⁻¹)
    (hV : ∀ b : ↥B0, b.1 ∈ (V2' : Subgroup YF) → (n b).1 ∈ (V2' : Subgroup YF)) :
    ∃ (ε : Bool) (A B C C' : GF4), A ≠ 0 ∧ B ≠ 0 ∧
      (n dB).1 = (if ε then (dB.1)⁻¹ else dB.1) ∧
      (n (eB 16)).1 = xP (psi A) * wP (psi C) ∧
      (n (eB 4)).1 = yP (psi B) * wP (psi C') := by
  obtain ⟨y, z, h2, h3, hY1, hY2, hY3, hZ1, hZ2, hZ3⟩ := nstab_of_cert n hV
  obtain ⟨ε, h1⟩ : ∃ ε : Bool, (n dB).1 = (if ε then (dB.1)⁻¹ else dB.1) := by
    rcases hd with h | h
    · exact ⟨false, by rw [h]; rfl⟩
    · exact ⟨true, by rw [h, Subgroup.coe_inv]; rfl⟩
  refine ⟨ε, y.1, z.2.1, y.2.2.1, z.2.2.1, hY3, hZ3, h1, ?_, ?_⟩
  · rw [h2, nfY_xw _ hY1 hY2]
  · rw [h3, nfY_yw _ hZ1 hZ2]

end CFSG.GH74.QTGen4.DSGen4.L34
