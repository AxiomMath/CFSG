module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2D
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2D (isPGroup_mem card_mem)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}

theorem conjSub_eq_of_wSet (hd : TightDatum R S t)
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) (g : Y) : conjSub g W = W := by
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  have := WSet.conj hd.hypOmegaGen.conjInvariant hW g
  rwa [hW1] at this

theorem not_le_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ¬ L ≤ W := by
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hd.hypOmegaGen hW
  rintro _ ⟨g, rfl⟩ hle
  have hK : tightCore R ≤ W := fun x hx => by
    have hx' : x ∈ conjSub g⁻¹ W := by
      rw [mem_conjSub_iff, inv_inv]
      exact hle (conj_mem_conjSub hx)
    rwa [conjSub_eq_of_wSet hd hW1 g⁻¹] at hx'
  obtain ⟨e⟩ : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := hc.1
  have hmem : ∀ q, ((e.symm q : R) : Y) ∈ tightCore R := fun q =>
    hd.sylow_core.1 ⟨e.symm q, (e.symm q).2, rfl⟩
  apply (show (QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0 ≠ .xa 0 * .a 1 by decide)
  have h' : e.symm (.a 1) * e.symm (.xa 0) = e.symm (.xa 0) * e.symm (.a 1) :=
    Subtype.ext (Subtype.ext (hWab _ (hK (hmem _)) _ (hK (hmem _))))
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h'

theorem mem_DSet_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      L ∈ DSet (CoreAssembly.conjClass (tightCore R)) W ∧ IsSylow2In L L := by
  intro L hL
  have hLsyl : IsSylow2In L L :=
    ⟨le_rfl, isPGroup_mem hd hc hO2 L hL, fun V hVL _ hLV => le_antisymm hVL hLV⟩
  exact ⟨⟨mem_RSet_of_isSylow2In hL hLsyl,
    fun x _ => mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_wSet hd hW1 x)⟩, hLsyl⟩

theorem exists_rep_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      ∃ ρ : Rep (CoreAssembly.conjClass (tightCore R)) W, ρ.K = L := by
  intro L hL
  obtain ⟨r, hrL, hrW⟩ := Set.not_subset.mp (not_le_of_wSet hd hc hW1 L hL)
  obtain ⟨hLD, hLsyl⟩ := mem_DSet_of_wSet hd hc hO2 hW1 L hL
  exact ⟨⟨L, L, r, hL, hLD, hLsyl, hrL, hrW⟩, rfl⟩

theorem uniqueInvolution_mem_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ u : Y, IsUniqueInvolution L u → u ∈ W := by
  intro L hL u hu
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  obtain ⟨hLD, hLsyl⟩ := mem_DSet_of_wSet hd hc hO2 hW1 L hL
  exact (Q3CL.Thompson.uniqueInvolution_mem_W hd.hypOmegaGen hW hL hLD hLsyl hu).2

theorem mem_omegaStarNbr_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) :
    ∀ K ∈ CoreAssembly.conjClass (tightCore R), ∀ J ∈ CoreAssembly.conjClass (tightCore R),
      K ≠ J → J ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) K := by
  intro K hK J hJ hne
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  obtain ⟨ρ, rfl⟩ := exists_rep_of_wSet hd hc hO2 hW1 K hK
  obtain ⟨σ, rfl⟩ := exists_rep_of_wSet hd hc hO2 hW1 J hJ
  exact Q3T6.Mu.muTab_omegaStar hd.partIHypG hW ρ σ hne

theorem dstarConnected_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) :
    T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) := by
  intro K hK J hJ
  by_cases h : K = J
  · subst h
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨hJ, Or.inl (mem_omegaStarNbr_of_wSet hd hc hO2 hW1 K hK J hJ h)⟩

theorem not_dbarConnected_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W})
    (hnc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))) :
    ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W := by
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  intro hDb
  apply hnc
  intro K hK J hJ
  by_contra hKJ
  refine Q3T6.Mu.not_dbarConnected_of_shape hd.partIHypG hW hK (fun h => hKJ ?_) hDb
  have hJs : J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    dstarConnected_of_wSet hd hc hO2 hW1 K hK J hJ
  rw [← h] at hJs
  exact hJs

theorem subsingleton_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W})
    (hZ : MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ L' ∈ CoreAssembly.conjClass (tightCore R),
      L = L' := by
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  have c := Q3CL.T8.ctxOf hd.partIHypG hW
  intro L hL L' hL'
  obtain ⟨ρ, rfl⟩ := exists_rep_of_wSet hd hc hO2 hW1 L hL
  obtain ⟨σ, rfl⟩ := exists_rep_of_wSet hd hc hO2 hW1 L' hL'
  obtain ⟨φ⟩ := hZ
  have h1 : φ (T8.repElt ρ) ≠ 1 := fun h =>
    muDelta_ne_one hW (T8.repElt_mem ρ) (φ.injective (by rw [h, map_one]))
  have h1' : φ (T8.repElt σ) ≠ 1 := fun h =>
    muDelta_ne_one hW (T8.repElt_mem σ) (φ.injective (by rw [h, map_one]))
  exact (repElt_eq_iff_gen c ρ σ).mp (φ.injective (z2_eq_of_ne_one _ _ h1 h1'))

end CFSG.ClassicalInvolution.Q3.TL4.SecIdE2
