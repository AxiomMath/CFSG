module

public import CFSG.Monster.B.CTIB.Fusion
public import Certificates.Certificate3113
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.Bin

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def caseBWord : List ℤ := [3, -1, -2, -3, -3, 2, -3, -1, -3]

theorem caseBWord_letters : ∀ l ∈ caseBWord, IsLetter3 l := by decide

theorem beta_caseBWord :
    (βr (wordS' caseBWord)) = Dyadic.wordK Dyadic.caseBWordK :=
  beta_wordS3 caseBWord_letters

theorem caseB_pow_nine :
    ((wordS' caseBWord)⁻¹ * rs 6 * wordS' caseBWord * qS 1 * (wordS' caseBWord)⁻¹ *
        qS 854 * wordS' caseBWord * qS 1 * ((wordS' caseBWord)⁻¹ * rs 6 * wordS' caseBWord) *
        qS 4356) ^ 9 = 1 := by
  obtain ⟨A, C, hA, hC, h9⟩ := Certificates.certificate3113
  have hA' := beta_conj_of (w := wordS' caseBWord) (r := rs 6) (A := A) (by
    rw [beta_caseBWord, beta_rs]
    exact hA)
  have hC' := beta_conj_of (w := wordS' caseBWord) (r := qS 854) (A := C) (by
    rw [beta_caseBWord, beta_qSK]
    exact hC)
  have e : (wordS' caseBWord)⁻¹ * rs 6 * wordS' caseBWord * qS 1 * (wordS' caseBWord)⁻¹ *
      qS 854 * wordS' caseBWord * qS 1 * ((wordS' caseBWord)⁻¹ * rs 6 * wordS' caseBWord) *
      qS 4356 = ((wordS' caseBWord)⁻¹ * rs 6 * wordS' caseBWord) * qS 1 *
      ((wordS' caseBWord)⁻¹ * qS 854 * wordS' caseBWord) * qS 1 *
      ((wordS' caseBWord)⁻¹ * rs 6 * wordS' caseBWord) * qS 4356 := by group
  rw [e]
  refine betaRow_inj CTIB.betaS_explicit.injective ?_
  simp only [map_pow, map_mul, map_one, Units.val_pow_eq_pow_val, Units.val_mul,
    Units.val_one] at hA' hC' ⊢
  rw [← hA', ← hC']
  simp only [beta_qSK]
  exact h9

end CFSG.EvenSmallLie.TwoE6
