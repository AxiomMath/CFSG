module

public import CFSG.ClassicalInvolution.Phan.Phan3B3CTData
public import CFSG.ClassicalInvolution.Phan.Phan3B3TwistData
public import CFSG.ClassicalInvolution.Phan.Phan3AModel
public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs
public import CFSG.ClassicalInvolution.Phan.Phan3PermModel

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

structure B3Checks : Prop where
  card : Finite PhanB3Group ∧ Nat.card PhanB3Group ≤ 176904 * 51840
  ker : ∃ N : Subgroup PhanB3Group, N.Normal ∧ Nat.card N ≤ 2 ∧
    (∀ w ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels, wordVal b3CtEltP w ∈ N) ∧
    ∀ i : Fin 8,
      (wordVal b3CtEltP (decodeWord 6 b3PhanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N
  twist : ∀ p ∈ b3BadPairs, Subsingleton (PG 6 (b3TwistRels p.1 p.2))
  sl3 : Finite (PG 4 sl3Rels) ∧ Nat.card (PG 4 sl3Rels) ≤ 5616
  sp4 : Finite (PG 4 sp4Rels) ∧ Nat.card (PG 4 sp4Rels) ≤ 51840

variable (hc : B3Checks)

include hc in
theorem card_phanB3Group_le :
    Finite PhanB3Group ∧ Nat.card PhanB3Group ≤ 176904 * 51840 :=
  hc.card

include hc in
theorem exists_ker_le_ker {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (π : PhanB3Group →* G) (hπ : Function.Surjective π) :
    ∃ N : Subgroup PhanB3Group, N ≤ π.ker ∧
      (∀ w ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels, wordVal b3CtEltP w ∈ N) ∧
      ∀ i : Fin 8,
        (wordVal b3CtEltP (decodeWord 6 b3PhanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N := by
  have := hc.card.1
  obtain ⟨N, hN, hcard, h1, h2⟩ := hc.ker
  exact ⟨N, ker_le_ker_of_card_le_four hnab π hπ N (hcard.trans (by norm_num)), h1, h2⟩

end CFSG.ClassicalInvolution.Phan.Q3G
