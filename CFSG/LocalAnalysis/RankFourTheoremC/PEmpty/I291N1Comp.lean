module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BComp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp mem_cjComp_of_mem)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y} {L : Subgroup Y}

theorem normal_of_unique (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L) : L.Normal := by
  refine ⟨fun c hc g => ?_⟩
  set C : CFSG.LocalCores.ComponentIndex Y := ⟨L, (CFSG.isComponent_iff_open L).2 hL⟩ with hC
  have h1 : (cjComp g C).1 = L :=
    hLu _ ((CFSG.isComponent_iff_open _).1 (cjComp g C).2)
  have h2 := mem_cjComp_of_mem g C hc
  rwa [h1] at h2

theorem isPGroup_center [Fact p.Prime] (hcore : primeComplementCore (G := Y) p = ⊥)
    (hL : IsComponentOf L ⊤) : IsPGroup p (center ↥L) := by
  intro c
  have hmem : ((c : ↥L) : Y) ∈ CFSG.pCore p Y := by
    refine CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.center_comp_le_pCore hcore
      ⟨L, (CFSG.isComponent_iff_open L).2 hL⟩ (c : ↥L).2 (fun g hg => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨g, hg⟩)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := Y) (p := p)) ⟨_, hmem⟩
  refine ⟨k, ?_⟩
  ext
  simpa using congrArg Subtype.val hk

theorem pCore_le_of_sylow [Fact p.Prime] (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) :
    CFSG.pCore p Y ≤ P := by
  have hsup : IsPGroup p ↥(P ⊔ CFSG.pCore p Y) :=
    IsPGroup.to_sup_of_normal_right hP.isPGroup (CFSG.pCore_isPGroup (G := Y) (p := p))
  have h := hP.eq_of_le (le_sup_left : P ≤ P ⊔ CFSG.pCore p Y) le_top hsup
  calc CFSG.pCore p Y ≤ P ⊔ CFSG.pCore p Y := le_sup_right
    _ = P := h

theorem pCore_eq_bot (hcfg : Cfg p P x z) (hL : IsComponentOf L ⊤) (hLn : L.Normal)
    (hZ : center ↥L = ⊥) : CFSG.pCore p Y = ⊥ := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  by_contra hne
  have hle := pCore_le_of_sylow hcfg.sylow
  have hz : z ∈ CFSG.pCore p Y :=
    hcfg.z_mem_of_normal hle
      (fun g _ n hn => (CFSG.pCore_normal (p := p)).conj_mem n hn g) hne
  have hzL : z ∈ L :=
    hcfg.z_mem_comp_of_fixed (C := ⟨L, (CFSG.isComponent_iff_open L).2 hL⟩) (fun g _ => by
      rw [normalizer_eq_top_iff.mpr hLn]
      exact mem_top g)
  have hsub : IsSubnormal (CFSG.pCore p Y) ⊤ :=
    ComponentClassification.Components.chain_of_mathlib_subnormal
      (inferInstance : (CFSG.pCore p Y).Normal).isSubnormal
  haveI : Group.IsNilpotent ↥(CFSG.pCore p Y) :=
    (CFSG.pCore_isPGroup (G := Y) (p := p)).isNilpotent
  haveI : Group.IsSolvable ↥(CFSG.pCore p Y) := inferInstance
  have hcomm := ComponentClassification.Layer.commutes_with_solvable_subnormal
    (CFSG.pCore p Y) hsub
  have hLle : L ≤ ComponentClassification.Layer.subgroup Y :=
    ComponentClassification.Layer.component_le hL
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent (hLle g.2)) z hz).symm
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hcfg.z_ne_one (congrArg Subtype.val hzc)

theorem generalizedFitting_eq [Fact p.Prime] (hcore : primeComplementCore (G := Y) p = ⊥)
    (hpc : CFSG.pCore p Y = ⊥) (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L) : CFSG.generalizedFitting Y = L := by
  rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Y p hcore, hpc, bot_sup_eq,
    CFSG.layer_eq_componentClassification, ComponentClassification.Layer.subgroup.eq_sSup]
  have hset : {K : Subgroup Y | IsComponentOf K ⊤} = {L} :=
    Set.ext fun K => ⟨hLu K, fun h => h ▸ hL⟩
  rw [hset, sSup_singleton]

theorem centralizer_eq_bot [Fact p.Prime] (hcore : primeComplementCore (G := Y) p = ⊥)
    (hpc : CFSG.pCore p Y = ⊥) (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L) (hZ : center ↥L = ⊥) :
    centralizer (L : Set Y) = ⊥ := by
  have hbound := CFSG.centralizer_generalizedFitting_le Y
  rw [generalizedFitting_eq hcore hpc hL hLu] at hbound
  rw [eq_bot_iff]
  intro c hc
  have hcL : c ∈ L := hbound hc
  have hcz : (⟨c, hcL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc g g.2)
  rw [hZ, Subgroup.mem_bot] at hcz
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hcz)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291
