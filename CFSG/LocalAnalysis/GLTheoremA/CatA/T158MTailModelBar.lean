module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailModelTE6Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailPull
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.T171Sh
open scoped commutatorElement

section Bar

variable {X X' : Type} [Group X] [Finite X] [Group X']

private theorem map_le_normalizer_map (φ : X →* X') {K H : Subgroup X}
    (hH : H ≤ Subgroup.normalizer (K : Set X)) :
    H.map φ ≤ Subgroup.normalizer ((K.map φ : Subgroup X') : Set X') :=
  (Subgroup.map_mono hH).trans (Subgroup.le_normalizer_map φ)

theorem commutator_le_centMod_of_map_le (φ : X →* X') (hker : Nat.Coprime 3 (Nat.card φ.ker))
    {K T B : Subgroup X} (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (h : (⁅T.map φ, B.map φ⁆ : Subgroup X') ≤ Subgroup.centralizer ((K.map φ : Subgroup X') : Set X')) :
    (⁅T, B⁆ : Subgroup X) ≤ centModSubgroup 3 K := by
  refine commutator_le_centMod_of_map φ hker hTN hBN fun z hz l hl => ?_
  have hz' : φ z ∈ (⁅T.map φ, B.map φ⁆ : Subgroup X') := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem φ hz
  exact (Subgroup.mem_centralizer_iff.mp (h hz') (φ l) (Subgroup.mem_map_of_mem φ hl)).symm

end Bar

theorem t158TailModel_bar_U6
    {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X'] (φ : X →* X')
    (hker : Nat.Coprime 3 (Nat.card φ.ker)) {K B T : Subgroup X} {J A : Subgroup X'} {d β : X'} {n : ℕ}
    (hSetup : Setup 3 (K.map φ) J A d β) (hU6 : catalogIs (PSimple 3 (K.map φ)) (S10.isU6n n))
    (hnodd : Odd n) (hAB : A ≤ B.map φ) (hA27 : 3 ^ 3 ≤ Nat.card A)
    (hBA : ∀ b ∈ B.map φ, ∃ a ∈ A, b * a⁻¹ ∈ Subgroup.centralizer ((K.map φ : Subgroup X') : Set X'))
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (h9 : U6Type9) : (⁅T, B⁆ : Subgroup X) ≤ centModSubgroup 3 K :=
  commutator_le_centMod_of_map_le φ hker hTN hBN
    (u6_noAct_core hSetup hU6 hnodd hAB (map_le_normalizer_map φ hBN) hA27 hBA (hT2.map φ)
      (map_le_normalizer_map φ hTN) (map_le_normalizer_map φ hBT) h9)

theorem t158TailModel_bar_TE6
    {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X'] (φ : X →* X')
    (hker : Nat.Coprime 3 (Nat.card φ.ker)) {K B T : Subgroup X} {J A : Subgroup X'} {d β : X'} {n : ℕ}
    (hSetup : Setup 3 (K.map φ) J A d β) (hTE6 : catalogIs (PSimple 3 (K.map φ)) (S10.isTE6n n))
    (hnodd : Odd n) (hAB : A ≤ B.map φ) (hA81 : 3 ^ 4 ≤ Nat.card A)
    (hBA : ∀ b ∈ B.map φ, ∃ a ∈ A, b * a⁻¹ ∈ Subgroup.centralizer ((K.map φ : Subgroup X') : Set X'))
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hX : TwE6BigToralExit) : (⁅T, B⁆ : Subgroup X) ≤ centModSubgroup 3 K :=
  commutator_le_centMod_of_map_le φ hker hTN hBN
    (te6_noAct_core hSetup hTE6 hnodd hAB (map_le_normalizer_map φ hBN) hA81 hBA (hT2.map φ)
      (map_le_normalizer_map φ hTN) (map_le_normalizer_map φ hBT) hX)

end CFSG.LocalAnalysis.GLTheoremA.T158

end
