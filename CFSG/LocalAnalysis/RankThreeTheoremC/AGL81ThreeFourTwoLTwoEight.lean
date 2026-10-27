module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.Adapters.Certificate43Check
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem threeFourTwoNoneAt_of_sylow_le_isSolvable {p : ℕ} {X : Type*} [Group X] [Finite X]
    (hX : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (hsol : ∀ (T : Sylow p X) (H : Subgroup X), (T : Subgroup X) ≤ H → H ≠ ⊤ →
      Group.IsSolvable H) :
    ThreeFourTwoNoneAt p X := by
  refine threeFourTwoNoneAt_of_model hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp _ hKn e _ _ _ _ _ _ _ hRY₀ hKY₀
  haveI := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine exists_solvable_centralizer_of_isSolvable (hsol (T.mapSurjective he) _ ?_ ?_)
  · rw [Sylow.coe_mapSurjective]
    refine map_mono fun t ht => mem_subgroupOf.mpr (hRY₀ ?_)
    have h : (t : Y) ∈ (R : Subgroup Y) ⊓ K := hT ▸ mem_map_of_mem K.subtype ht
    exact h.1
  · intro htop
    refine hKY₀ fun k hk => ?_
    have h1 : e ⟨k, hk⟩ ∈ (Y₀.subgroupOf K).map e.toMonoidHom := htop ▸ mem_top _
    obtain ⟨k', hk', hkk'⟩ := mem_map.mp h1
    have hk'' : k' = ⟨k, hk⟩ := e.injective hkk'
    rw [hk''] at hk'
    exact mem_subgroupOf.mp hk'

section LTwoEight

variable {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex}

theorem nonempty_mulEquiv_lTwoEight (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) :
    Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* PSL2GF 2 3) :=
  nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := d) ⟨q, hd, hq2, hq3⟩

theorem finite_lTwoEight (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) :
    Finite (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨eP⟩ := nonempty_mulEquiv_lTwoEight hq2 hq3 hd
  exact Finite.of_equiv _ eP.symm.toEquiv

theorem card_lTwoEight (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) :
    Nat.card (TauCeti.CFSGIndex.lie d).Group = 504 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_lTwoEight hq2 hq3 hd
  rw [Nat.card_congr e.toEquiv,
    show PSL2GF 2 3 = Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) from rfl,
    CFSG.Walter.psl2_even_card (f := 3) (by norm_num)]
  norm_num

theorem lTwoEight_catalog_facts (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨eP⟩ := nonempty_mulEquiv_lTwoEight hq2 hq3 hd
  haveI := finite_lTwoEight hq2 hq3 hd
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  have hS := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv (MulEquiv.refl _)
  haveI := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hS
  refine ⟨inferInstance, ?_,
    CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable hS⟩
  have hT := (psl2GF_sylow 2 3 (by norm_num) (default : Sylow 2 (PSL2GF 2 3))).2
  refine nonabelian_of_simple_of_sq_dvd Nat.prime_two ?_
  rw [Nat.card_congr eP.toEquiv]
  exact (pow_dvd_pow 2 (by norm_num : 2 ≤ 3)).trans (hT ▸ card_subgroup_dvd_card _)

theorem lTwoEight_isSolvable_of_ne_top (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q)
    (H : Subgroup (TauCeti.CFSGIndex.lie d).Group) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  haveI := CFSG.Adapters.certificate43_holds
  obtain ⟨e⟩ := nonempty_mulEquiv_lTwoEight hq2 hq3 hd
  have hH' : H.map e.toMonoidHom ≠ ⊤ := fun htop => hH (by
    rw [← comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective H, htop, comap_top])
  haveI := CFSG.SignalizerFunctorTheorem.CatalogBridge.proper_subgroup_solvable_psl2_even
    Nat.prime_three (by decide) (H.map e.toMonoidHom) hH'
  exact Group.isSolvable_of_isSolvable_injective
    (f := (equivMapOfInjective H e.toMonoidHom e.injective).toMonoidHom)
    (equivMapOfInjective H e.toMonoidHom e.injective).injective

theorem threeFourTwoNoneAt_lTwoEight (hq2 : q.p = 2) (hq3 : q.exponent = 3)
    (hd : d.1 = .A 1 q) : ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨hs, hnab, hout⟩ := lTwoEight_catalog_facts hq2 hq3 hd
  haveI := finite_lTwoEight hq2 hq3 hd
  exact threeFourTwoNoneAt_of_sylow_le_isSolvable hs hnab hout fun _ H _ hH =>
    lTwoEight_isSolvable_of_ne_top hq2 hq3 hd H hH

end LTwoEight

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
