module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo1Nat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenU
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.Co1Patterson CFSG.Blueprint

section Main

theorem uCo1 : UCo1 := by
  intro F X hFD hXD hF hFc hX hFX
  have h := le_ker_of_typeSystem (n := 8) (k := 4) (by norm_num)
    (Subgroup.subtype_injective L₀) nativeTypeSystem
    (F := F.subgroupOf (Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1)))
    (X := X.subgroupOf (Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1)))
    (hF.subgroupOf _) ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFD).toEquiv).trans hFc)
    (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXD).symm)
    (fun f hf => Subgroup.mem_normalizer_iff.2 fun h =>
      Subgroup.mem_normalizer_iff.1 (hFX hf) (h : NativeSporadic.Co1))
  intro x hx
  have hx' := h (show (⟨x, hXD hx⟩ : Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1)) ∈
    X.subgroupOf _ from hx)
  exact (Setting.phiV₀_eq_one_iff nativeSetting _
    (map_Mbar_eq_omega_of_card nativeSetting width_nativeSetting card_Mbar_nativeSetting)
    ⟨x, hXD hx⟩).1 (MonoidHom.mem_ker.1 hx')

end Main

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
