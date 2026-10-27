module

public import CFSG.LieType.Chevalley.A2CommutatorCertE8

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem a2CheckAll_G2 : a2CheckAll .G2 = true := by decide +kernel

theorem a2CheckAll_F4 : a2CheckAll .F4 = true := by decide +kernel

theorem a2CheckAll_D4 : a2CheckAll .D4 = true := by decide +kernel

theorem e6_a2CheckRow_0 : a2CheckRow .E6 ⟨0, by decide⟩ = true := by decide +kernel

theorem e6_a2CheckRow_1 : a2CheckRow .E6 ⟨1, by decide⟩ = true := by decide +kernel

theorem e6_a2CheckRow_2 : a2CheckRow .E6 ⟨2, by decide⟩ = true := by decide +kernel

theorem e6_a2CheckRow_3 : a2CheckRow .E6 ⟨3, by decide⟩ = true := by decide +kernel

theorem e6_a2CheckRow_4 : a2CheckRow .E6 ⟨4, by decide⟩ = true := by decide +kernel

theorem e6_a2CheckRow_5 : a2CheckRow .E6 ⟨5, by decide⟩ = true := by decide +kernel

theorem a2CheckAll_E6 : a2CheckAll .E6 = true :=
  a2CheckAll_of_rows fun i => by
    fin_cases i
    exacts [e6_a2CheckRow_0, e6_a2CheckRow_1, e6_a2CheckRow_2, e6_a2CheckRow_3,
      e6_a2CheckRow_4, e6_a2CheckRow_5]

theorem e7_a2CheckRow_0 : a2CheckRow .E7 ⟨0, by decide⟩ = true := by decide +kernel

theorem e7_a2CheckRow_1 : a2CheckRow .E7 ⟨1, by decide⟩ = true := by decide +kernel

theorem e7_a2CheckRow_2 : a2CheckRow .E7 ⟨2, by decide⟩ = true := by decide +kernel

theorem e7_a2CheckRow_3 : a2CheckRow .E7 ⟨3, by decide⟩ = true := by decide +kernel

theorem e7_a2CheckRow_4 : a2CheckRow .E7 ⟨4, by decide⟩ = true := by decide +kernel

theorem e7_a2CheckRow_5 : a2CheckRow .E7 ⟨5, by decide⟩ = true := by decide +kernel

theorem e7_a2CheckRow_6 : a2CheckRow .E7 ⟨6, by decide⟩ = true := by decide +kernel

theorem a2CheckAll_E7 : a2CheckAll .E7 = true :=
  a2CheckAll_of_rows fun i => by
    fin_cases i
    exacts [e7_a2CheckRow_0, e7_a2CheckRow_1, e7_a2CheckRow_2, e7_a2CheckRow_3,
      e7_a2CheckRow_4, e7_a2CheckRow_5, e7_a2CheckRow_6]

theorem a2CheckAll_eq_true : ∀ τ : Tag, a2CheckAll τ = true
  | .G2 => a2CheckAll_G2
  | .F4 => a2CheckAll_F4
  | .D4 => a2CheckAll_D4
  | .E6 => a2CheckAll_E6
  | .E7 => a2CheckAll_E7
  | .E8 => a2CheckAll_E8

theorem simpleRow_eq_true
    : ∀ (τ : Tag) (j : Fin τ.rank), simpleRow τ j = true
  | .G2, j => by
    fin_cases j
    exacts [g2_simpleRow_0, g2_simpleRow_1]
  | .F4, j => by
    fin_cases j
    exacts [f4_simpleRow_0, f4_simpleRow_1, f4_simpleRow_2, f4_simpleRow_3]
  | .D4, j => by
    fin_cases j
    exacts [d4_simpleRow_0, d4_simpleRow_1, d4_simpleRow_2, d4_simpleRow_3]
  | .E6, j => by
    fin_cases j
    exacts [e6_simpleRow_0, e6_simpleRow_1, e6_simpleRow_2, e6_simpleRow_3, e6_simpleRow_4,
      e6_simpleRow_5]
  | .E7, j => by
    fin_cases j
    exacts [e7_simpleRow_0, e7_simpleRow_1, e7_simpleRow_2, e7_simpleRow_3, e7_simpleRow_4,
      e7_simpleRow_5, e7_simpleRow_6]
  | .E8, j => by
    fin_cases j
    exacts [e8_simpleRow_0, e8_simpleRow_1, e8_simpleRow_2, e8_simpleRow_3, e8_simpleRow_4,
      e8_simpleRow_5, e8_simpleRow_6, e8_simpleRow_7]

variable {τ : Tag} {R : Type*} [CommRing R]

theorem brackets_of_cartan
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) :
    infE τ R i * infE τ R j - infE τ R j * infE τ R i =
        (signOf τ j i : R) • entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) ∧
      infF τ R i * infF τ R j - infF τ R j * infF τ R i =
        ((-signOf τ (τ.rootCertificate.image j j) i : ℤ) : R) • entriesOp τ R
          (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) ∧
      infE τ R i * entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) * infE τ R i ∧
      infE τ R j * entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image j i) 1) * infE τ R j ∧
      infF τ R i * entriesOp τ R
          (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) *
          infF τ R i ∧
      infF τ R j * entriesOp τ R
          (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) =
        entriesOp τ R (entries τ (τ.rootCertificate.image (τ.rootCertificate.image j j) i) 1) *
          infF τ R j :=
  brackets_of_a2PairCheck (dataChecks τ) (simpleRow_eq_true τ)
    (a2PairCheck_of_a2CheckAll (a2CheckAll_eq_true τ) hij hji)

end CFSG.LieType.Chevalley.RootOps
