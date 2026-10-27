module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GraphOrbitDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.AdjacentComponent
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin.B2F CFSG.Quasithin.E2
open scoped commutatorElement

theorem natMultiBaumStabGraph_of_graphOrbit (hG : KFactChevGraphOrbit) :
    NatMultiBaumStabGraph := by
  intro X _ _ T hX L hL hch P hPb hRP H₁ M₁ hTH hmap hmin hF hJ hV hnat hall hBL
  obtain ⟨hresJ, I, hFam, hn2⟩ := hnat
  set R : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T)) with hR
  have hRL : R ⊓ L = gnImg T T ⊓ L := by
    ext x
    simp only [hR, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩
  have hTp : IsPGroup 2 ↥(gnImg T T) := hX.sylow.2.1.map _
  have hRp : IsPGroup 2 ↥R := hTp.to_le inf_le_left
  have hSyl : IsSylowTwoOf (R ⊓ L) L := by
    rw [hRL]
    exact Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow hL.2.1
  have hPb' : IsMinOverBorel L (R ⊓ L) P := by rw [hRL]; exact hPb
  have hRP' : ¬ R ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)) := hRP
  set W : Subgroup (X ⧸ gnC T) := pElementSubgroup 2 (conjClosure P R) with hW
  have hWL : W ≤ L :=
    (pElementSubgroup_le _).trans (conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp hh.2 z).mp (hPb.1 hz))
  have hRW : R ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) :=
    (le_normalizer_conjClosure P R).trans (normalizer_le_normalizer_pElementSubgroup 2 _)
  have hT : IsSylowTwoOf T H₁ := B6.isSylowTwoOf_mono hX.sylow hTH le_top
  have hres : gnImg T (twoResidual H₁) ≤ conjClosure W (gnImg T T) := by
    show (twoResidual H₁).map (QuotientGroup.mk' (gnC T)) ≤ _
    rw [E1.map_twoResidual]
    show twoResidual (gnImg T H₁) ≤ _
    rw [hmap]
    exact twoResidual_sup_le_of_pGroup hTp (le_normalizer_conjClosure W _)
  have hWH : W ≤ gnImg T H₁ := by
    rw [hmap]
    exact (le_conjClosure W _).trans le_sup_left
  have hYN : conjClosure W (gnImg T T) ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) :=
    conjClosure_le_normalizer_of_component hL hWL hRW hWL Subgroup.le_normalizer
  rcases hG (X ⧸ gnC T) L R P hL.2.2 hch inf_le_right hRp hSyl hPb' hRP' with
    hsolv | ⟨C, hCW, hWC, hWgen, hcomm⟩ | hQ
  · exfalso
    exact false_of_solvable_component hTH hV hFam hn2 hresJ hWH (hres.trans hYN) hres hsolv
  · intro b hb
    obtain ⟨hbT, hbL⟩ := mem_gnStab.1 (hBL hb)
    refine mem_gnStab.2 ⟨hbT, hbL, ?_⟩
    by_contra hbP
    have hbR : QuotientGroup.mk' (gnC T) b ∈ R := ⟨⟨b, hbT, rfl⟩, hbL⟩
    have hCN : gnImg T (twoResidual H₁) ≤ Subgroup.normalizer (C : Set (X ⧸ gnC T)) :=
      hres.trans (conjClosure_le_normalizer_of_component hL hWL hRW (hCW.trans hWL) hWC)
    have hgen : gnImg T (twoResidual H₁) ≤ conjClosure C (gnImg T T) := by
      refine hres.trans (conjClosure_le fun t ht w hw => ?_)
      have hw' : w ∈ conjClosure C (gnImg T T) :=
        (conjClosure_le (H := R) (Z := C) (K := conjClosure C (gnImg T T))
          fun r hr c hc => Subgroup.subset_closure
          (⟨r, hr.1, c, hc, rfl⟩ :
            ∃ h ∈ gnImg T T, ∃ z ∈ C, h * z * h⁻¹ = r * c * r⁻¹)) (hWgen hw)
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure C (gnImg T T) ht) w).mp hw'
    exact false_of_baum_comm hTH hT hV hFam hn2 (hCW.trans hWH) hCN hgen
      (LieType.BorelTits.pCoreOf_isPGroup 2 W) hb (hcomm _ hbR hbP)
  · exfalso
    obtain ⟨hperf, hsimple, -, hodd, P', hP', hnon⟩ := hQ
    have hNn : (CFSG.pCore 2 ↥(twoResidual W)).Normal := CFSG.pCore_normal
    exact false_of_quasisimple_mod_component hTH hV hFam hn2 hresJ hWH (hres.trans hYN) hres
      (CFSG.pCore 2 ↥(twoResidual W)) CFSG.pCore_isPGroup hperf hsimple hodd P' hP' hnon

theorem natMultiBaumStab_of_graphOrbit (hG : KFactChevGraphOrbit) : NatMultiBaumStab :=
  natMultiBaumStab_of_graph (natMultiBaumStabGraph_of_graphOrbit hG)

end CFSG.AGLEmbeddingD2.Tits.GN516
