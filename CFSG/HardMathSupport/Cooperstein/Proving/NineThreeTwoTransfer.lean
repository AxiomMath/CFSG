module

public import CFSG.HardMathSupport.Cooperstein.Proving.PCoreTransport
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] {X Y L S : Subgroup G}

theorem pCoreOf_le_self {p : ℕ} {H : Subgroup G} : CFSG.Open.pCoreOf p H ≤ H :=
  CFSG.openPCoreOf_le p H

theorem eq_of_subgroupOf_eq' {A A' B : Subgroup G} (hA : A ≤ B) (hA' : A' ≤ B)
    (h : A.subgroupOf B = A'.subgroupOf B) : A = A' := by
  ext x
  constructor
  · intro hx
    have hxB : x ∈ B := hA hx
    have hmem : (⟨x, hxB⟩ : ↥B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  · intro hx
    have hxB : x ∈ B := hA' hx
    have hmem : (⟨x, hxB⟩ : ↥B) ∈ A'.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx
    rw [← h, Subgroup.mem_subgroupOf] at hmem
    exact hmem

def subgroupOfMapEquiv {Q Q' : Type} [Group Q] [Group Q'] {A B : Subgroup Q} {A' B' : Subgroup Q'}
    (hAB : A ≤ B) (hA'B' : A' ≤ B') (e : ↥B ≃* ↥B')
    (he : (A.subgroupOf B).map e.toMonoidHom = A'.subgroupOf B') : ↥A ≃* ↥A' :=
  (Subgroup.subgroupOfEquivOfLe hAB).symm.trans <|
    (e.subgroupMap (A.subgroupOf B)).trans <|
      (MulEquiv.subgroupCongr he).trans (Subgroup.subgroupOfEquivOfLe hA'B')

theorem barM_pCore_transfer (hLY : L ≤ Y) (hLX : L ≤ X)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) {Z K : Subgroup G}
    (hZ : Z ≤ L) (hK : K ≤ L) (hcl : barM Y Z = CFSG.Open.pCoreOf 2 (barM Y K)) :
    barM X Z = CFSG.Open.pCoreOf 2 (barM X K) := by
  have he := barMEquiv_map_subgroupOf hLY hLX h.symm hK
  have heZ := barMEquiv_map_subgroupOf hLY hLX h.symm hZ
  have hpc := pCoreOf_map_subgroupOf (p := 2) (barMEquiv hLY hLX h.symm) he
    (barM_mono hK) (barM_mono hK)
  have hsub : (barM X Z).subgroupOf (barM X L) =
      (CFSG.Open.pCoreOf 2 (barM X K)).subgroupOf (barM X L) := by
    rw [← heZ, hcl, hpc]
  exact eq_of_subgroupOf_eq' (barM_mono hZ) (pCoreOf_le_self.trans (barM_mono hK)) hsub

end CFSG.HardMathSupport.Cooperstein.Proving

end
