module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFStab
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFMax
public import Certificates.Certificate26720
public import Certificates.Certificate26721
public import Certificates.Certificate26722
public import Certificates.Certificate26723
public import Certificates.Certificate26724
public import Certificates.Certificate26725
public import Certificates.Certificate26726
public import Certificates.Certificate26727
public import Certificates.Certificate26728
public import Certificates.Certificate26729

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.HNSchreier CFSG.ONSchreier.Native

@[expose] noncomputable def hnfBeta (i : Fin 9) : ↥JH := hnfRep hnfRepWords[i.val]!

theorem hnfBeta_zero : hnfBeta 0 = aJ := by
  have h : hnfRepWords[(0 : Fin 9).val]! = [] := rfl
  unfold hnfBeta
  rw [h]
  unfold hnfRep
  rw [wordProd_nil, conjBy_def, one_mul, inv_one, mul_one]

theorem hnfSetup_facts :
    hnfG1 ∈ centralizer ({aJ} : Set ↥JH) ∧ hnfG2 ∈ centralizer ({aJ} : Set ↥JH) ∧
    ∀ i j : Fin 9, i ≠ j →
      Disjoint (conjOrb (centralizer ({aJ} : Set ↥JH)) (hnfBeta i))
        (conjOrb (centralizer ({aJ} : Set ↥JH)) (hnfBeta j)) :=
  Certificates.certificate26720

theorem hnfOrbit1_lower :
    1408 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[1]!)).ncard :=
  Certificates.certificate26721

theorem hnfOrbit2_lower :
    2200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[2]!)).ncard :=
  Certificates.certificate26722

theorem hnfOrbit3_lower :
    5775 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[3]!)).ncard :=
  Certificates.certificate26723

theorem hnfOrbit4_lower :
    35200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[4]!)).ncard :=
  Certificates.certificate26724

theorem hnfOrbit5_lower :
    123200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[5]!)).ncard :=
  Certificates.certificate26725

theorem hnfOrbit6_lower :
    277200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[6]!)).ncard :=
  Certificates.certificate26726

theorem hnfOrbit7_lower :
    354816 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[7]!)).ncard :=
  Certificates.certificate26727

theorem hnfOrbit8_lower :
    739200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[8]!)).ncard :=
  Certificates.certificate26728

theorem hnfStab_card :
    240 ≤ Nat.card ↥(hnfC0 ⊓ centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH)) :=
  Certificates.certificate26729

section Orbits

theorem hnf_orbit_lower (i : Fin 9) : hnfS i ≤ (conjOrb hnfC0 (hnfBeta i)).ncard := by
  have hfin := finite_JH
  fin_cases i
  · show 1 ≤ _
    exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (Set.toFinite _)).2
      ⟨_, mem_conjOrb_self _ _⟩).ne'
  · exact hnfOrbit1_lower
  · exact hnfOrbit2_lower
  · exact hnfOrbit3_lower
  · exact hnfOrbit4_lower
  · exact hnfOrbit5_lower
  · exact hnfOrbit6_lower
  · exact hnfOrbit7_lower
  · exact hnfOrbit8_lower

end Orbits

section Centralizer

theorem hnfC0_le_centralizer : hnfC0 ≤ centralizer ({aJ} : Set ↥JH) := by
  obtain ⟨h1, h2, -⟩ := hnfSetup_facts
  unfold hnfC0
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · rw [hx]
    exact mem_centralizer_singleton_iff.2 rfl
  · rw [hx]; exact h1
  · rw [hx]; exact h2

end Centralizer

section Equality

theorem hnf_card_C0 : 177408000 ≤ Nat.card ↥hnfC0 := by
  have hfin := finite_JH
  have h8 : 739200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[8]!)).ncard := hnf_orbit_lower 8
  have hs := hnfStab_card
  have hmul := ncard_conjOrb_mul hnfC0 (hnfRep hnfRepWords[8]!)
  rw [← hmul]
  calc 177408000 = 739200 * 240 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h8 hs

end Equality

section Data2

theorem hnfC0_eq (hCcard : Nat.card ↥(centralizer ({aJ} : Set ↥JH)) = 177408000) :
    hnfC0 = centralizer ({aJ} : Set ↥JH) := by
  have hfin := finite_JH
  exact Subgroup.eq_of_le_of_card_ge hnfC0_le_centralizer (by rw [hCcard]; exact hnf_card_C0)

theorem hnf_disjoint (_hCcard : Nat.card ↥(centralizer ({aJ} : Set ↥JH)) = 177408000)
    (i j : Fin 9) (hij : i ≠ j) :
    Disjoint (conjOrb (centralizer ({aJ} : Set ↥JH)) (hnfBeta i))
      (conjOrb (centralizer ({aJ} : Set ↥JH)) (hnfBeta j)) :=
  hnfSetup_facts.2.2 i j hij

theorem hnfOrbitData_JH (hCcard : Nat.card ↥(centralizer ({aJ} : Set ↥JH)) = 177408000)
    (hGcard : Nat.card ↥JH = 273030912000000) : HNFOrbitData ↥JH aJ hnfBeta where
  card_C := hCcard
  card_G := hGcard
  beta_zero := hnfBeta_zero
  beta_class := fun i => ⟨wordProd hnfAB hnfRepWords[i.val]!, rfl⟩
  lower := fun i => by
    rw [← hnfC0_eq hCcard]
    exact hnf_orbit_lower i
  disjoint := hnf_disjoint hCcard

end Data2

end CFSG.EvenSporadicStandard.Solomon78
