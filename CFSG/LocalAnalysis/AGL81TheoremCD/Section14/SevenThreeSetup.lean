module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteenI
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.LieType.HighestRoot.CentChevalleyToral

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

theorem isPGroup_center_of_isComponent {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {L : Subgroup X} (hLcomp : CFSG.IsComponent L) (hO : CFSG.pPrimeCore p X = ⊥) :
    IsPGroup p (Subgroup.center ↥L) := by
  have hle : (Subgroup.center ↥L).map L.subtype ≤ CFSG.pCore p X :=
    (CFSG.LocalCores.center_component_le_center_layer hLcomp).trans
      (CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot p hO)
  exact ((CFSG.pCore_isPGroup (p := p) (G := X)).to_le hle).of_equiv
    (Subgroup.equivMapOfInjective (Subgroup.center ↥L) L.subtype L.subtype_injective).symm

theorem k34odd_hyps_of_isComponent {X : Type} [Group X] [Finite X] (hKX : CFSG.Open.IsKGroup X)
    {L : Subgroup X} (hLcomp : CFSG.IsComponent L)
    (hO : CFSG.pPrimeCore 3 X = ⊥) (hprankL : CFSG.Open.pRank 3 L = 3) :
    CFSG.Open.IsQuasisimple ↥L ∧ CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) ∧
      Odd (Nat.card (Subgroup.center ↥L)) ∧ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 3 := by
  have hQ : CFSG.Open.IsQuasisimple ↥L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.mp hLcomp.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLcomp.1.2.1
  have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hKX L hLcomp.1.2.2
      (QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  obtain ⟨k, hk⟩ := (isPGroup_center_of_isComponent (p := 3) hLcomp hO).exists_card_eq
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [hk]
    exact Odd.pow (n := k) (by decide : Odd 3)
  refine ⟨hQ, hcat, hodd, ?_⟩
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L]
  exact hprankL

theorem exists_perfect_onto_a9_of_injective {Y Y' : Type} [Group Y] [Group Y']
    (π : Y →* Y') (hπ : Function.Injective π) {I : Subgroup Y} (hI : ⁅I, I⁆ = I)
    (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) :
    ∃ I' : Subgroup Y', ⁅I', I'⁆ = I' ∧ ∃ f' : ↥I' →* alternatingGroup (Fin 9),
      Function.Surjective f' ∧ IsPGroup 2 f'.ker := by
  let I' : Subgroup Y' := I.map π
  have hI' : ⁅I', I'⁆ = I' := by
    change ⁅I.map π, I.map π⁆ = I.map π
    rw [← Subgroup.map_commutator, hI]
  let e : ↥I ≃* ↥I' := I.equivMapOfInjective π hπ
  let f' : ↥I' →* alternatingGroup (Fin 9) := f.comp e.symm.toMonoidHom
  refine ⟨I', hI', f', ?_, ?_⟩
  · exact hf.comp e.symm.surjective
  · have h : f'.ker = f.ker.comap e.symm.toMonoidHom :=
      (MonoidHom.comap_ker f e.symm.toMonoidHom).symm
    rw [h]
    exact IsPGroup.comap_of_injective hker e.symm.toMonoidHom e.symm.injective

theorem exists_perfect_onto_a9_le_component {X : Type} [Group X] [Finite X]
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) (hKX : CFSG.Open.IsKGroup X)
    {L : Subgroup X} (hLcomp : CFSG.IsComponent L) (hFstar : CFSG.generalizedFitting X = L)
    {Hs : Subgroup X} (hHsQuot : Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9))) :
    ∃ I : Subgroup ↥L, ⁅I, I⁆ = I ∧ ∃ f : ↥I →* alternatingGroup (Fin 9),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  classical
  have hLnorm : L.Normal := by
    have h := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
    rwa [hFstar] at h
  have hCL : Subgroup.centralizer (L : Set X) ≤ L := by
    have h := CFSG.centralizer_generalizedFitting_le X
    rwa [hFstar] at h
  obtain ⟨n, hn⟩ := h711 X hKX L hLcomp hLnorm
  have hderiv : derivedSeries X n ≤ L := by
    rw [sup_eq_left.mpr hCL] at hn
    exact hn
  let eHs : ↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9) := hHsQuot.some
  let θ : ↥Hs →* Equiv.Perm (Fin 9) :=
    eHs.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Hs))
  have hθsurj : Function.Surjective θ :=
    eHs.surjective.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Hs))
  have hθker : IsPGroup 2 θ.ker := by
    have h : θ.ker = CFSG.pCore 2 ↥Hs := by
      ext x
      simp [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    rw [h]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥Hs)
  let R : Subgroup ↥Hs := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥Hs
  have hRmap : R.map θ = alternatingGroup (Fin 9) :=
    perfectResidual_map_eq_alternatingGroup (α := Fin 9) (by norm_num) θ hθsurj
  let J : Subgroup X := R.map Hs.subtype
  have hJperf : ⁅J, J⁆ = J := by
    change ⁅R.map Hs.subtype, R.map Hs.subtype⁆ = R.map Hs.subtype
    rw [← Subgroup.map_commutator]
    exact congrArg (Subgroup.map Hs.subtype) (Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := ↥Hs)))
  have hJle : J ≤ derivedSeries X n :=
    CFSG.LieType.HighestRoot.le_derivedSeries_of_isPerfect
      (Subgroup.isPerfect_iff.mpr hJperf) n
  have hJleL : J ≤ L := hJle.trans hderiv
  let I : Subgroup ↥L := J.subgroupOf L
  have hmapI : I.map L.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJleL
  have hIperf : ⁅I, I⁆ = I := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hmapI, hJperf]
  let g : ↥R →* alternatingGroup (Fin 9) :=
    (θ.comp R.subtype).codRestrict _ (fun x => by
      have hx : θ (x : ↥Hs) ∈ R.map θ := Subgroup.mem_map_of_mem θ x.2
      rwa [hRmap] at hx)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : Equiv.Perm (Fin 9)) ∈ R.map θ := by
      rw [hRmap]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hgker : g.ker = θ.ker.comap R.subtype := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    change ((θ.comp R.subtype).codRestrict (alternatingGroup (Fin 9)) _) x = 1 ↔
      θ (x : ↥Hs) = 1
    rw [Subtype.ext_iff]
    rfl
  have hgkerP : IsPGroup 2 g.ker := by
    rw [hgker]
    exact IsPGroup.comap_subtype hθker
  let eI : ↥I ≃* ↥J :=
    (I.equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hmapI)
  let eR : ↥R ≃* ↥J := R.equivMapOfInjective Hs.subtype Hs.subtype_injective
  let e : ↥I ≃* ↥R := eI.trans eR.symm
  let f : ↥I →* alternatingGroup (Fin 9) := g.comp e.toMonoidHom
  have hfsurj : Function.Surjective f := hgsurj.comp e.surjective
  have hfker : IsPGroup 2 f.ker := by
    have h : f.ker = g.ker.comap e.toMonoidHom :=
      (MonoidHom.comap_ker g e.toMonoidHom).symm
    rw [h]
    exact IsPGroup.comap_of_injective hgkerP e.toMonoidHom e.injective
  exact ⟨I, hIperf, f, hfsurj, hfker⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree
