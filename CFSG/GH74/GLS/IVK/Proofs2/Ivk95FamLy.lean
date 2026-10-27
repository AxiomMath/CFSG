module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.ClassicalInvolution CFSG.Sporadic.Ly CFSG.Sporadic.Schreier

theorem ivk95x_isQuasisimple_of_open {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    CFSG.IsQuasisimple G :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native G).1 h

theorem ivk95_ly :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) := by
  obtain ⟨hkey, hq, -, hcardK⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  refine ivk95_empty_of_cfg fun L _ _ hL y hy => ?_
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥J := e.trans lyEquivJ
  have hord : orderOf (e' y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hy.ord
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
  obtain ⟨c, -, hc⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' y)
    (Subgroup.mem_top _) hord
  obtain ⟨G, hG, φ, hqG, hcardG⟩ : ∃ (G : Type) (_ : Group G)
      (φ : ↥(centralizer ({y} : Set L)) ≃* G), CFSG.IsQuasisimple G ∧ Nat.card G = 39916800 :=
    ⟨↥LyProof.KJ, inferInstance,
      (GHInv.centralizerEquivConj (J : Subgroup (GL (Fin 111) (ZMod 5))) e' y
        (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5))) (g := (c : GL (Fin 111) (ZMod 5))) c.2
        (by rw [hc]; simp)).trans
        ((GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans (MulEquiv.subgroupCongr hkey)),
      ivk95x_isQuasisimple_of_open hq, hcardK⟩
  have hq' : CFSG.IsQuasisimple ↥(centralizer ({y} : Set L)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqG
  refine hy.false_of_quasisimple_centralizer hq' (fun q hq5 => ?_)
  rw [Nat.card_congr φ.toEquiv, hcardG]
  exact (sl2_card_ne_39916800 q hq5).symm

end CFSG.GH74.GLS.IVK.Proofs2
