module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HSubKernel
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KNormXInf
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCompNonempty
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KernelFrattini

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem inf_le_kerIn_sup_kSub {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (hOp : relPPrimeCore p H ≤ M) :
    (xSub p M H ⊓ M : Subgroup G) ≤
      CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M (kSub p M H ⊔ (xSub p M H ⊓ M)) := by
  have hK : kSub p M H ≤ Subgroup.normalizer ((xSub p M H ⊓ M) ⊓ M : Set G) := by
    simpa only [inf_assoc, inf_idem] using kSub_le_normalizer_xSub_inf (p := p) (M := M) (H := H) Fact.out hOp
  have hXn : (xSub p M H ⊓ M : Subgroup G) ≤
      Subgroup.normalizer ((xSub p M H ⊓ M) ⊓ M : Set G) := by
    simp only [inf_assoc, inf_idem]
    exact Subgroup.le_normalizer
  have h := inf_le_kerIn_sup (K := kSub p M H) (X := xSub p M H ⊓ M) (M := M) hK hXn
  simpa only [inf_assoc, inf_idem] using h

theorem not_dvd_card_xSub_inf_of_glue {p d : ℕ} [Fact p.Prime] [Fact d.Prime] {M H : Subgroup G}
    (hOp : relPPrimeCore p H ≤ M)
    (hgen : pLayerIn p H ≤ M → H ≤ kSub p M H ⊔ (H ⊓ M)) (hH : ¬ H ≤ M)
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) :
    ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G) := by
  have hKnle : ¬ kSub p M H ≤ M := not_kSub_le_M_of_pLayerIn_le hH hgen
  have hJM : ¬ (kSub p M H ⊔ (xSub p M H ⊓ M)) ≤ M :=
    fun h => hKnle (le_trans le_sup_left h)
  exact not_dvd_card_of_le_kerIn (hstr := hstr)
    (J := kSub p M H ⊔ (xSub p M H ⊓ M)) hJM (inf_le_kerIn_sup_kSub hOp)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
