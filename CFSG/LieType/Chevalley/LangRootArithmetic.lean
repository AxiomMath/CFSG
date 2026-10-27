module

public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.LangRootArithmeticG2

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Polynomial

theorem exceptional_Lang_exact_root_arithmetic :
    (Tag.G2.cartan.det = 1 ∧ Tag.F4.cartan.det = 1 ∧ Tag.D4.cartan.det = 4 ∧
      Tag.E6.cartan.det = 3 ∧ Tag.E7.cartan.det = 2 ∧ Tag.E8.cartan.det = 1) ∧
    (∀ (R : Type*) [CommRing R] (τ : Tag) (i : Fin τ.rank) (a b : Label τ),
      ∃ p q : R[X], p.natDegree ≤ (if τ = .G2 then 3 else 2) ∧
        q.natDegree ≤ (if τ = .G2 then 3 else 2) ∧
        ∀ c : R, xOp τ R i c (Finsupp.single b 1) a = p.eval c ∧
          yOp τ R i c (Finsupp.single b 1) a = q.eval c) ∧
    ∀ (L : Type) [Field L], ringChar L = 3 → ∀ M : Module.End L (RootModule Tag.G2 L),
      (Commute M (xOp Tag.G2 L ⟨0, by decide⟩ 1) ∧ Commute M (yOp Tag.G2 L ⟨0, by decide⟩ 1) ∧
          Commute M (xOp Tag.G2 L ⟨1, by decide⟩ 1) ∧
          Commute M (yOp Tag.G2 L ⟨1, by decide⟩ 1)) ↔
        ∃ a : L, M = a • (1 : Module.End L (RootModule Tag.G2 L)) :=
  ⟨⟨det_cartan_G2, det_cartan_F4, det_cartan_D4, det_cartan_E6, det_cartan_E7, det_cartan_E8⟩,
    fun R _ τ i a b => exists_entry_polynomial R τ i a b,
    fun L _ hL M => G2_char_three_commutant L hL M⟩

end CFSG.LieType.Chevalley
