module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryOvergroup
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAssembly (classical_model_outer_solvable)

theorem unitary_catalog_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hqp : q.p = p) (hd : d.1 = .twistedA 2 q) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdU : IsUnitaryIndex p d := ⟨q, hqp, hd⟩
  have hS := UnitaryModel.statedClassicalModel hdU ⟨MulEquiv.refl _⟩
  obtain ⟨hfin, -, hsimple⟩ := CFSG.LieType.Simplicity.fam_classical_converse _ ⟨_, _, _, _, hS⟩
  refine ⟨hsimple, ?_, classical_model_outer_solvable hS⟩
  obtain ⟨hcard, -⟩ := kFactUnitarySylowStructure _ p d hp2 hdU ⟨MulEquiv.refl _⟩
    (default : Sylow p (TauCeti.CFSGIndex.lie d).Group)
  obtain ⟨q', -, -, hfe, hq'⟩ := hdU.exists_eq
  refine exists_mul_ne_of_sq_dvd_card hp ?_ Nat.card_pos.ne'
  exact (pow_dvd_pow p (by omega)).trans (hcard ▸ card_subgroup_dvd_card _)

theorem threeFourTwoUnitary_inf {p : ℕ} (hp : p.Prime) {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hqp : q.p = p) (hd : d.1 = .twistedA 2 q)
    {Y : Type} [Group Y] [Finite Y] {K Y₀ : Subgroup Y} (R : Sylow p Y) (hK : K.Normal)
    (hKX : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hRY₀ : (R : Subgroup Y) ≤ Y₀)
    (hKY₀ : ¬ K ≤ Y₀) : Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isSolvable_inf_of_forall_sylow_le R (fun T H hTH hH =>
    UnitaryModel.isSolvable_of_unitary_sylow_le ⟨q, hqp, hd⟩ hKX T hTH hH) hRY₀ hKY₀

theorem threeFourTwoUnitary_holds : ThreeFourTwoUnitary := by
  intro p hp hp2 q d hqp hd
  obtain ⟨hX, hnab, hout⟩ := unitary_catalog_facts hp hp2 hqp hd
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R _ _ hK hKX _ _ _ _ _ _ _ hRY₀ hKY₀
  exact Or.inl (threeFourTwoUnitary_inf hp hqp hd R hK hKX hRY₀ hKY₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
