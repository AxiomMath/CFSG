module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4U
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Y

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance.Bootstrap (rankTwoSpan le_rankTwoSpan_of_le_centralizer)
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K' : Subgroup Y} {u x y x' : Y}

theorem oddCoreOf_layerY_le_rankTwoSpan_e4 (hL : TightLargeHypR r n Y R S t)
    (hF : E4FrameAt R t J K' u x y x') :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤
      rankTwoSpan (Subgroup.closure ({t, u, x * y * x'} : Set Y)) := by
  have hΩ := hL.datum.hypOmegaGen
  have hA := hF.isElemAbelian hL
  have h8 := hF.natCard hL
  have hAt : Subgroup.closure ({t, u, x * y * x'} : Set Y) ≤
      Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hF.comm_tu.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hF.comm_ts.symm
  have hnorm : Subgroup.closure ({t, u, x * y * x'} : Set Y) ≤ Subgroup.normalizer
      (oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) : Set Y) := by
    intro a ha
    rw [mem_normalizer_iff_conjSub_eq, ← Thompson.oddCoreOf_conjSub_eq,
      layerY_conjSub_eq hΩ.conjInvariant (hAt ha)]
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two _ _ hA (by rw [h8]; norm_num) hnorm
    (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

@[expose] def TightE4LinkGenR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      LinkE4 R t → ¬ TriNbrAll R t → ∀ (J K' : Subgroup Y) (u x y x' : Y),
        E4FrameAt R t J K' u x y x' →
          linkLayer R t ≤ rankTwoSpan (Subgroup.closure ({t, u, x * y * x'} : Set Y))

theorem tightE4GenR_of (hgen : TightE4LinkGenR 3 n) : TightE4GenR 3 n := by
  intro Y _ _ R S t hL hc hcase hA J hJ J' hJ'
  have h := TightLargeHypR.typeRFam hL
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
  obtain ⟨K', x, y, x', hF⟩ := exists_e4FrameAt hL hcase hA hJ hu
  obtain ⟨gb, hgb⟩ := hcase.1 _ (subgroupOf_mem_linkRestrict (t := t) hJ) _
    (subgroupOf_mem_linkRestrict (t := t) hJ')
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hJ)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hJ')] at h1
  obtain ⟨g₁, hg₁⟩ := linkLayerHom'_surjective hL gb
  have hg₁Y := linkLayer_le_layerY hL g₁.2
  have hg₁C : (g₁ : Y) ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer g₁.2
  have h2 : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub (g₁ : Y) J) =
      secImg (CoreAssembly.conjClass (tightCore R)) t J' := by
    have e : QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨g₁, hg₁Y⟩ =
          (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t) := by
      rw [← hg₁]
      rfl
    have h3 := conjSub_secImg (Ω := CoreAssembly.conjClass (tightCore R)) (x := t)
      ⟨(g₁ : Y), hg₁Y⟩ J
    rw [e, h1] at h3
    exact h3.symm
  have hJg := conjSub_mem_omegaNbr_core hL hJ hg₁C
  obtain ⟨ν, hν, hJeq⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hJg)
    (xMem_of_mem_omegaNbr_core hL hJ') h2
  refine Relation.ReflTransGen.single ⟨u, x * y * x', ⟨K', x, y, x', hF, rfl⟩, (ν : Y) * g₁,
    Subgroup.mul_mem _ (layerY_le_centralizer ν.2) hg₁C,
    Subgroup.mul_mem _ (oddCoreOf_layerY_le_rankTwoSpan_e4 hL hF ⟨ν, hν, rfl⟩)
      (hgen Y R S t hL hc hcase hA J K' u x y x' hF g₁.2), ?_⟩
  rw [hJeq, ← conjSub_mul]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
