module

public import Certificates.Certificate270007
public import CFSG.ClassicalInvolution.Phan.Phan3B3Bridge
public import CFSG.ClassicalInvolution.Phan.Phan3B3CT

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.Asc77.B3C (SymplecticPhanPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

theorem b3Checks : B3Checks :=
  ⟨Certificates.certificate270007.1, Certificates.certificate270007.2.1,
    Certificates.certificate270007.2.2.1, Certificates.certificate270007.2.2.2.1,
    Certificates.certificate270007.2.2.2.2⟩

theorem exists_b3CtChain_of_phanChain {G : Type} [Group G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {U : Fin 3 → Subgroup G}
    (hcomm : Commutes (U 0) (U 2))
    (h01 : ∃ W, UnitaryBlockStandardPair K9 3 1 W (U 0) (U 1))
    (h12 : ∃ W, SymplecticPhanPair F3F h2F W (U 1) (U 2)) (hgen : ⨆ k, U k = ⊤)
    (hH3 : ∃ w ∈ U 2, Commutes (U 1) (conjSub w (U 1)) ∧
      ¬ 3 ∣ Nat.card (Subgroup.center ↥(U 0 ⊔ U 1 ⊔ conjSub w (U 1))))
    {K : Type} [Field K] (hK : Nat.card K = 3) :
    ∃ V : Fin 3 → Subgroup G, (∀ a ∈ V 0, ∀ b ∈ V 2, a * b = b * a) ∧
      (∃ W, WeakCT.LinearBlockStandardPair K W (V 0) (V 1)) ∧
      (∃ W, SymplecticBlockPair K W (V 1) (V 2)) ∧ ⨆ k, V k = ⊤ := by
  obtain ⟨π, hπ⟩ := exists_surj_b3Hom b3Checks.twist hcomm h01 h12 hgen hH3
  have hfin : Finite PhanB3Group := (card_phanB3Group_le b3Checks).1
  have : Finite G := Finite.of_surjective _ hπ
  exact exists_b3CtChain b3Checks hnab π hπ hK

end CFSG.ClassicalInvolution.Phan.Q3G
