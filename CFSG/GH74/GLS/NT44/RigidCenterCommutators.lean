module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section

set_option autoImplicit false

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace CFSG.GH74.GLS.NT44

private theorem mem_cSec_of_mem_zStar_kz {G : Type} [Group G] [Finite G]
    {fullQ : Type} [Group fullQ] {b y : G}
    (hy : y ∈ zStar (Kz fullQ b)) {M : Subgroup G}
    (hM : IsPCompIn 2 (centralizer ({b} : Set G)) M) : y ∈ cSec M := by
  classical
  have hPle : Kz fullQ b ≤ pLayerOf 2 (centralizer ({b} : Set G)) :=
    sSup_le_sSup fun K hK => hK.1.1.2.2
  by_cases hrig : M ∈ RigidSet fullQ b
  · have hMK : M ≤ Kz fullQ b := le_sSup hrig
    have hyN : y ∈ normalizer (M : Set G) := pLayerOf_le_normalizer hM (hPle hy.1)
    refine ⟨hyN, TwoThin.mem_normalizer_pPrimeCoreOf hyN, fun k hk => ?_⟩
    have h1 : ⁅k, y⁆ ∈ pPrimeCoreOf 2 (Kz fullQ b) := hy.2.2.2 k (hMK hk)
    have h2 : ⁅k, y⁆ ∈ M := by
      have e : ⁅k, y⁆ = k * (y * k⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact M.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hyN k⁻¹).mp (M.inv_mem hk))
    exact Bg.Pu5.inf_pPrimeCoreOf_le hMK ⟨h2, h1⟩
  · have hle : Kz fullQ b ≤ cSec M :=
      sSup_le fun K hK => le_cSec_of_ne hK.1.1.2.2 hM (fun h => hrig (h ▸ hK))
    exact hle hy.1

theorem commutator_mem_of_mem_zStar_kz {G : Type} [Group G] [Finite G]
    {fullQ : Type} [Group fullQ] {b y : G}
    (hy : y ∈ zStar (Kz fullQ b)) :
    ∀ l ∈ pLayerOf 2 (centralizer ({b} : Set G)),
      ⁅l, y⁆ ∈ pPrimeCoreOf 2 (centralizer ({b} : Set G)) :=
  Bg.Pu5.commutator_mem_pPrimeCoreOf_of_forall_mem_cSec
    (fun _ hM => mem_cSec_of_mem_zStar_kz hy hM)

end CFSG.GH74.GLS.NT44

end
