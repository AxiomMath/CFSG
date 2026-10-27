module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.Adapters.Certificate43Check
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneDickson
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAssembly (classical_model_outer_solvable)

theorem linTwo_catalog_facts {p : ℕ} (hp : p.Prime) {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hqp : q.p = p) (hq2 : 2 ≤ q.exponent) (hd : d.1 = .A 1 q) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := q.exponent)
    (d := d) ⟨q, hd, hqp, rfl⟩
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  have hS := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv (MulEquiv.refl _)
  haveI := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hS
  refine ⟨inferInstance, ?_, classical_model_outer_solvable hS⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := Finite.of_equiv _ eP.symm.toEquiv
  have hT := (psl2GF_sylow p q.exponent (by omega) (default : Sylow p (PSL2GF p q.exponent))).2
  refine exists_mul_ne_of_sq_dvd_card hp ?_ Nat.card_pos.ne'
  rw [Nat.card_congr eP.toEquiv]
  exact (pow_dvd_pow p hq2).trans (hT ▸ card_subgroup_dvd_card _)

theorem linTwo_isSolvable_of_sylow_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex} (hqp : q.p = p) (hq2 : 2 ≤ q.exponent)
    (hd : d.1 = .A 1 q) {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) (T : Sylow p L) (H : Subgroup L)
    (hTH : (T : Subgroup L) ≤ H) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := CFSG.Adapters.certificate43_holds
  obtain ⟨e₁⟩ := hL
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := q.exponent)
    (d := d) ⟨q, hd, hqp, rfl⟩
  by_contra hns
  exact hH (eq_top_of_sylow_le_of_equiv_psl2GF hp2 (by omega) (e₁.trans e₂) H T hTH hns)

theorem threeFourTwoLinTwo_inf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hqp : q.p = p) (hq2 : 2 ≤ q.exponent) (hd : d.1 = .A 1 q)
    {Y : Type} [Group Y] [Finite Y] {K Y₀ : Subgroup Y} (R : Sylow p Y) (hK : K.Normal)
    (hKX : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hRY₀ : (R : Subgroup Y) ≤ Y₀)
    (hKY₀ : ¬ K ≤ Y₀) : Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isSolvable_inf_of_forall_sylow_le R
    (fun T H hTH hH => linTwo_isSolvable_of_sylow_le hp hp2 hqp hq2 hd hKX T H hTH hH) hRY₀ hKY₀

theorem threeFourTwoLinTwo_holds : ThreeFourTwoLinTwo := by
  intro p hp hp2 q d hqp hq2 hd
  obtain ⟨hX, hnab, hout⟩ := linTwo_catalog_facts hp hqp hq2 hd
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R _ _ hK hKX _ _ _ _ _ _ _ hRY₀ hKY₀
  exact Or.inl (threeFourTwoLinTwo_inf hp hp2 hqp hq2 hd R hK hKX hRY₀ hKY₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
