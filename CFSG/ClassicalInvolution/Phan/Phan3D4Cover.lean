module

public import Certificates.Certificate270006
public import CFSG.ClassicalInvolution.Phan.Phan3D4CT

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.PhanD4

theorem d4Checks : D4Checks :=
  ⟨Certificates.certificate270006.1, Certificates.certificate270006.2.1,
    Certificates.certificate270006.2.2⟩

theorem exists_ctChain_of_family {G : Type} [Group G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (F : PhanFamilyD4 K9 3 1 G)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (d4Gens6 F)))))
    (hgen : Subgroup.closure (Set.range (d4Gens F)) = ⊤) {K : Type} [Field K]
    (hK : Nat.card K = 3) :
    ∃ U : Fin 4 → Subgroup G,
      (∀ i j : Fin 4, i ≠ j → ¬ Timmesfeld.edgeD 4 i j → ¬ Timmesfeld.edgeD 4 j i →
        ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ i j : Fin 4, Timmesfeld.edgeD 4 i j →
        ∃ W, WeakCT.LinearBlockStandardPair K W (U i) (U j)) ∧ ⨆ k, U k = ⊤ := by
  have hπ : Function.Surjective (d4Hom F h3) := by
    rw [← MonoidHom.range_eq_top, range_d4Hom F h3]
    exact hgen
  have hfin : Finite PhanD4Group := (card_phanD4Group_le d4Checks).1
  have : Finite G := Finite.of_surjective _ hπ
  exact exists_ctChain d4Checks hnab (d4Hom F h3) hπ hK

end CFSG.ClassicalInvolution.Phan.Q3G
