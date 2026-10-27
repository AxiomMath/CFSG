module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Quasi
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.ClassicalInvolution CFSG.Sporadic.Ly CFSG.Sporadic.Schreier

theorem ivk93_ly :
    Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) := by
  obtain ⟨hkey, hq, -, -⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  refine ivk93_empty_of_cfg fun L _ _ hL y _ q L₁ L₂ hc => ?_
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥J := e.trans lyEquivJ
  have hord : orderOf (e' y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hc.ord
  have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hso
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  obtain ⟨c, -, hcz⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' y)
    (Subgroup.mem_top _) hord
  obtain ⟨G, hG, φ, hqG⟩ : ∃ (G : Type) (_ : Group G)
      (φ : ↥(centralizer ({y} : Set L)) ≃* G), CFSG.IsQuasisimple G :=
    ⟨↥LyProof.KJ, inferInstance,
      (GHInv.centralizerEquivConj (J : Subgroup (GL (Fin 111) (ZMod 5))) e' y
        (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5))) (g := (c : GL (Fin 111) (ZMod 5))) c.2
        (by rw [hcz]; simp)).trans
        ((GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans (MulEquiv.subgroupCongr hkey)),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hq⟩
  have hq' : CFSG.IsQuasisimple ↥(centralizer ({y} : Set L)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqG
  exact hc.false_of_quasisimple_centralizer hq'

end CFSG.GH74.GLS.IVK.Proofs2
