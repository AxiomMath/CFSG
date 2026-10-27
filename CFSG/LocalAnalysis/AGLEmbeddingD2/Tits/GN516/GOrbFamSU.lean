module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUBlocks
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLChev
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareUnitary
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.CGT.PushingUpLit.BHS6.Basic
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenGlue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenType
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BaumComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.C126Split2
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate3006
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.SquareUnitary CFSG.LieType.CurtisTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem cartanC_ne_zero_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    CFSG.LieType.Universal.Symplectic.cartanC m i j ≠ 0 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  unfold CFSG.LieType.Universal.Symplectic.cartanC
  rw [Matrix.of_apply, if_neg hij]
  split_ifs with h1 h2 <;> simp_all <;> omega

theorem cartan_ne_zero_iff {n : ℕ} {i j : Fin (n / 2)} (hij : i ≠ j) :
    cartan n i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  unfold cartan
  split_ifs
  · exact cartanC_ne_zero_iff hij
  · rw [Matrix.transpose_apply, cartanC_ne_zero_iff hij.symm, or_comm]

section Block

variable {m : ℕ} {a b : Fin m}

theorem mem_blk_pair (hb : b.val = a.val + 1) (hm : b.val + 1 < m) (q : Fin (m + 1)) :
    q ∈ blkSet ({a, b} : Set (Fin m)) a.castSucc ↔ a.val ≤ q.val ∧ q.val ≤ b.val + 1 := by
  have ha := a.isLt
  have hb' := b.isLt
  rw [mem_blkSet]
  unfold SameBlk
  constructor
  · intro h
    constructor
    · by_contra hq
      have hqm : q.val < m := by have := q.isLt; omega
      have := h ⟨q.val, hqm⟩
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Fin.ext_iff]; omega)
      exact hq (this.mpr le_rfl)
    · by_contra hq
      have := h ⟨b.val + 1, hm⟩
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Fin.ext_iff]; omega)
      exact hq (this.mp (by show a.val ≤ b.val + 1; omega))
  · rintro ⟨h1, h2⟩ j hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Fin.ext_iff] at hj
    simp only [Fin.val_castSucc]
    omega

theorem nodesOf_blk_pair (hb : b.val = a.val + 1) (hm : b.val + 1 < m) :
    nodesOf (blkSet ({a, b} : Set (Fin m)) a.castSucc) = ({a, b} : Set (Fin m)) := by
  ext k
  simp only [nodesOf, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    mem_blk_pair hb hm, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
  omega

theorem last_not_mem_blk_pair (hb : b.val = a.val + 1) (hm : b.val + 1 < m) :
    Fin.last m ∉ blkSet ({a, b} : Set (Fin m)) a.castSucc := by
  rw [mem_blk_pair hb hm, Fin.val_last]
  omega

theorem card_coordsOf_blk_pair (hb : b.val = a.val + 1) (hm : b.val + 1 < m) :
    (coordsOf (blkSet ({a, b} : Set (Fin m)) a.castSucc)).card = 3 := by
  refine Finset.card_eq_three.mpr ⟨a, b, ⟨b.val + 1, hm⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.val_mk] at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.val_mk] at this
    omega
  · ext i
    simp only [mem_coordsOf, mem_blk_pair hb hm, Finset.mem_insert, Finset.mem_singleton,
      Fin.ext_iff, Fin.val_castSucc, Fin.val_mk]
    omega

end Block

section SL3

variable (hF : Nat.card F = (2 ^ f) ^ 2)

theorem exists_sl3_GAu {n : ℕ} (S : Finset (Fin (n / 2))) (hS : S.card = 3) :
    ∃ l : Matrix.SpecialLinearGroup (Fin 3) F →* SU (unitaryInvolution F 2 f) n,
      Function.Injective l ∧ l.range = GAu hF S := by
  let e : Fin 3 ≃ ↥S := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hS)).symm
  let φ : Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup ↥S F :=
    slReindexEquiv e
  let L := levSU (σ := unitaryInvolution F 2 f) (aIdx_injective S) (aIdx_disj S)
    (unitaryInvolution_involutive hF)
  refine ⟨L.comp φ.toMonoidHom, ?_, ?_⟩
  · exact (levSU_injective (aIdx_injective S) (aIdx_disj S) (unitaryInvolution_involutive hF)).comp
      φ.injective
  · apply le_antisymm
    · rintro g ⟨y, rfl⟩
      exact ⟨φ y, rfl⟩
    · rintro g ⟨x, rfl⟩
      exact ⟨φ.symm x, by simp [L]⟩

end SL3

section Edge

variable (hF : Nat.card F = (2 ^ f) ^ 2)

theorem edgeRange_su_of_adj {n : ℕ} {a b : Fin (n / 2)} (hb : b.val = a.val + 1)
    (hm : b.val + 1 < n / 2) :
    ∃ l : Matrix.SpecialLinearGroup (Fin 3) F →* SU (unitaryInvolution F 2 f) n,
      Function.Injective l ∧
        l.range = rankOne (rootDatum hF n).rootGroup a ⊔ rankOne (rootDatum hF n).rootGroup b := by
  have hn : 2 ≤ n := by omega
  have hne : (nodesOf (blkSet ({a, b} : Set (Fin (n / 2))) a.castSucc)).Nonempty :=
    ⟨a, by rw [nodesOf_blk_pair hb hm]; exact Set.mem_insert _ _⟩
  obtain ⟨l, hl, hr⟩ := exists_sl3_GAu hF _ (card_coordsOf_blk_pair hb hm)
  refine ⟨l, hl, ?_⟩
  have hG : GbU hF (blkSet ({a, b} : Set (Fin (n / 2))) a.castSucc) =
      GAu hF (coordsOf (blkSet ({a, b} : Set (Fin (n / 2))) a.castSucc)) := by
    unfold GbU
    rw [if_neg (last_not_mem_blk_pair hb hm)]
  rw [hr, ← hG, GbU_eq (I := ({a, b} : Set (Fin (n / 2)))) (p := a.castSucc) hF hn rfl hne]
  exact (congrArg (leviM (rootDatum hF n)) (nodesOf_blk_pair hb hm)).trans
    (leviM_pair (rootDatum hF n) a b)

theorem edgeLevi_su_of_adj {n : ℕ} {a b : Fin (n / 2)} (hb : b.val = a.val + 1)
    (hm : b.val + 1 < n / 2) : Edge.EdgeLevi (rootDatum hF n) a b := by
  obtain ⟨l, hl, hr⟩ := edgeRange_su_of_adj hF hb hm
  exact EdgeLev.edgeLevi_of_sl3 l hl hr

end Edge

private theorem edgeCond_comm {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}
    {H : Fin D.rank → Subgroup K} {u v : Fin D.rank} (h : Core.EdgeCond D H v u) :
    Core.EdgeCond D H u v := by
  rcases h with h | h | h
  · exact Or.inl (EdgeLev.edgeLevi_symm h)
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

theorem edgeCond_su (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    (H : Fin (rootDatum hF n).rank → Subgroup (SU (unitaryInvolution F 2 f) n))
    (hrank : 3 ≤ (rootDatum hF n).rank) (u v : Fin (rootDatum hF n).rank)
    (hadj : (TauCeti.diagramGraph (rootDatum hF n).cartan).Adj u v) :
    Core.EdgeCond (rootDatum hF n) H u v := by
  have hpath : ∀ i j : Fin (rootDatum hF n).rank, i ≠ j →
      ((rootDatum hF n).cartan i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
    fun i j hij => cartan_ne_zero_iff (n := n) hij
  have key : ∀ x y : Fin (rootDatum hF n).rank, x.val + 1 = y.val →
      Core.EdgeCond (rootDatum hF n) H x y := by
    intro x y hxy
    by_cases hy : y.val + 1 < (rootDatum hF n).rank
    · exact Or.inl (edgeLevi_su_of_adj hF (n := n) hxy.symm hy)
    · have hy' : y.val + 1 = (rootDatum hF n).rank := by have := y.isLt; omega
      have hx' : x.val + 2 = (rootDatum hF n).rank := by omega
      exact Or.inr (Or.inl
        (EdgeLev.degree_ne_of_path hrank (rootDatum hF n).isFiniteType hpath hy' hx').symm)
  have hc := (rootDatum hF n).isFiniteType.diagramGraph_adj_iff.mp hadj
  rcases (cartan_ne_zero_iff (n := n) hc.1).mp hc.2 with h | h
  · exact key u v h
  · exact edgeCond_comm (key v u h)

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
