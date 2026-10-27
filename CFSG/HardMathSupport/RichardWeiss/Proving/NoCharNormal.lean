module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.QuasithinUnique.Setup.Campbell (NoCharNormal)

theorem noCharNormal_of_asc81bHyp {G : Type} [Group G] {X S R₀ Y : Subgroup G}
    (hA : CFSG.AGLEmbedding.Asc81bHyp X S) (hYX : Y ≤ X) (hR₀S : R₀ ≤ S)
    (hchar : (R₀.subgroupOf S).Characteristic)
    (hYS : ¬ Y ≤ Subgroup.normalizer (S : Set G)) :
    NoCharNormal R₀ Y := by
  intro C hCR hC1 hCchar hYC
  apply hYS
  have hCS : (C.subgroupOf S).Characteristic :=
    CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans hR₀S hCR hchar hCchar
  have hle : X ⊓ Subgroup.normalizer (C : Set G) ≤ CFSG.Quasithin.cgsIn X S :=
    le_iSup_of_le C (le_iSup_of_le (hCR.trans hR₀S) (le_iSup_of_le hC1
      (le_iSup_of_le hCS le_rfl)))
  intro y hy
  have h1 : y ∈ X ⊓ Subgroup.normalizer (C : Set G) := ⟨hYX hy, hYC hy⟩
  have h2 := hle h1
  rw [hA.cgs] at h2
  exact (Subgroup.mem_inf.mp h2).2

end CFSG.HardMathSupport.RichardWeiss.Proving

end
