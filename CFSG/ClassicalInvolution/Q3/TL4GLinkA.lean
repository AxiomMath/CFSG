module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLay
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Balance.Bootstrap
  (rankTwoSpan le_rankTwoSpan_of_le_centralizer card_closure_pair_eq_four)

namespace GLinkA

theorem centralizer_inf_le_rankTwoSpan {G : Type} [Group G] [Finite G] {B : Subgroup G}
    {t c : G} (ht : t * t = 1) (hc : c * c = 1) (ht1 : t ≠ 1) (hc1 : c ≠ 1) (hne : t ≠ c)
    (htc : t * c = c * t) (hle : Subgroup.closure ({t, c} : Set G) ≤ B) :
    Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ≤ rankTwoSpan B := by
  refine le_rankTwoSpan_of_le_centralizer
    ⟨hle, by rw [card_closure_pair_eq_four ht hc ht1 hc1 hne htc]; norm_num⟩ ?_
  intro y hy
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hy.1).symm

theorem closure_pair_le_of_mem {G : Type} [Group G] {t u v c : G}
    (hc : c ∈ Subgroup.closure ({t, u, v} : Set G)) :
    Subgroup.closure ({t, c} : Set G) ≤ Subgroup.closure ({t, u, v} : Set G) := by
  rw [Subgroup.closure_le]
  rintro w (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · exact hc

end GLinkA

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem GLinkA.layerY_le_rankTwoSpan_of_not_dConnected (h4 : Thm4RBelow r n)
    (hG : TightSecLinkGenR r n) (hL : TightLargeHypR r n Y R S t) {J K' : Subgroup Y}
    (hJK : GAdj R t J K') {u v : Y} (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution K' v)
    (hnc : ¬ DConnected (coreLinkFam R t)) :
    layerY (CoreAssembly.conjClass (tightCore R)) t ≤
      rankTwoSpan (Subgroup.closure ({t, u, v} : Set Y)) ⊓ Subgroup.centralizer ({t} : Set Y) := by
  obtain ⟨hJ, hK'K, hK'J, u₀, v₀, hu₀, hv₀, hne⟩ := id hJK
  have e1 : u = u₀ := hu.eq hu₀
  have e2 : v = v₀ := hv.eq hv₀
  subst e1
  subst e2
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  have h := TightLargeHypR.typeRFam hL
  have hnt := noTwins_of_large hL
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hXJ := xMem_of_mem_omegaNbr_core hL hJ
  have hXK' := xMem_of_mem_omegaNbr_core hL hK'K
  have huv : u * v = v * u := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hu hK'J hv
  have htu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htv : t * v = v * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hK'K hv
  have huv' : u ≠ v := fun e => hK'J.2.1 (hnt _ hJ.1 K' ⟨hK'K.1, u, hu, e ▸ hv⟩)
  have htu' : t ≠ u := fun e => hJ.2.1 (hnt _ hK J ⟨hJ.1, t, ht, e ▸ hu⟩)
  have htv' : t ≠ v := fun e => hK'K.2.1 (hnt _ hK K' ⟨hK'K.1, t, ht, e ▸ hv⟩)
  have hKK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hK'K.1 hK'K
  have hJK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hK'K.1 hK'J
  obtain ⟨P, hP, -, hPt, hPu⟩ :=
    exists_isSylow2In_member_le_centralizer hL hK'K.1 hv hKK' hJK' ht hu htu' htu
  have hnbr : secImg (CoreAssembly.conjClass (tightCore R)) t K' ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J) :=
    secImg_mem_omegaNbr hXJ hXK' hP hPt (hPu.trans (h.tight J hJ.1 u hu))
      (secImg_ne h hXJ hXK' hu hv huv huv')
  have hcls := AlphaFr.conjClass_secImg_eq hL hJ
    (fun Mb hMb => AlphaFr.exists_conj_of_not_dConnected h4 hL hnc ⟨J, hJ, rfl⟩ hMb)
  have hK'c : secImg (CoreAssembly.conjClass (tightCore R)) t K' ∈
      CoreAssembly.conjClass (secImg (CoreAssembly.conjClass (tightCore R)) t J) := by
    rw [hcls]
    exact ⟨K', hK'K, rfl⟩
  have hdisc : ¬ DConnected
      (CoreAssembly.conjClass (secImg (CoreAssembly.conjClass (tightCore R)) t J)) := by
    rw [hcls]
    exact hnc
  have hgen := hG _ (AlphaFr.natCard_secQuot_lt_of_large hL) _ (h.secFam (x := t))
    secQuot_oddCore_eq_bot omegaGen_secFam (aEmpty_secFam h) _ (secImg_mem hXJ) _ hnbr hK'c
    hdisc _ _ (isUniqueInvolution_secImg h hXJ hu) (isUniqueInvolution_secImg h hXK' hv)
  have hmem : ∀ w ∈ ({t, u, v} : Set Y), w ∈ Subgroup.closure ({t, u, v} : Set Y) :=
    fun w hw => Subgroup.subset_closure hw
  have huvt : t ≠ u * v := by
    intro e
    apply hne
    calc v = u * (u * v) := by rw [← mul_assoc, hu.sq, one_mul]
      _ = u * t := by rw [← e]
      _ = t * u := htu.symm
  have huv1 : u * v ≠ 1 := fun e => huv' (by
    calc u = u * (v * v) := by rw [hv.sq, mul_one]
      _ = (u * v) * v := by group
      _ = v := by rw [e, one_mul])
  have huv2 : (u * v) * (u * v) = 1 := by
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu.sq, hv.sq, one_mul]
  have htuv : t * (u * v) = (u * v) * t := by
    calc t * (u * v) = (t * u) * v := by group
      _ = u * (t * v) := by rw [htu, mul_assoc]
      _ = (u * v) * t := by rw [htv, mul_assoc]
  refine AlphaFr.layerY_le_of_linkGen hΩ.conjInvariant ?_
    (mem_layerY_of_isUniqueInvolution h hXJ hu) (mem_layerY_of_isUniqueInvolution h hXK' hv)
    hu.sq hv.sq huv ?_ ?_ ?_ hgen
  · exact le_inf (oddCoreOf_layerY_le_rankTwoSpan hL hJK hu hv)
      ((oddCoreOf_le_self _).trans layerY_le_centralizer)
  · exact le_inf (GLinkA.centralizer_inf_le_rankTwoSpan ht.sq hu.sq ht.ne_one hu.ne_one htu' htu
      (GLinkA.closure_pair_le_of_mem (hmem u (by simp)))) inf_le_right
  · exact le_inf (GLinkA.centralizer_inf_le_rankTwoSpan ht.sq hv.sq ht.ne_one hv.ne_one htv' htv
      (GLinkA.closure_pair_le_of_mem (hmem v (by simp)))) inf_le_right
  · exact le_inf (GLinkA.centralizer_inf_le_rankTwoSpan ht.sq huv2 ht.ne_one huv1 huvt htuv
      (GLinkA.closure_pair_le_of_mem (Subgroup.mul_mem _ (hmem u (by simp))
        (hmem v (by simp))))) inf_le_right

theorem tightGraphLinkAR_of (h4 : Thm4RBelow r n) (hG : TightSecLinkGenR r n) :
    TightGraphLinkAR r n := by
  intro Y _ _ R S t hL _ hA hnc J hJ J' hJ'
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
  obtain ⟨K', hK'K, hK'J, v, hv, hne⟩ := hA J hJ u hu
  have hJK : GAdj R t J K' := ⟨hJ, hK'K, hK'J, u, v, hu, hv, hne⟩
  have hY := GLinkA.layerY_le_rankTwoSpan_of_not_dConnected h4 hG hL hJK hu hv hnc
  obtain ⟨gb, hgb⟩ := AlphaFr.exists_conj_of_not_dConnected h4 hL hnc ⟨J, hJ, rfl⟩ ⟨J', hJ', rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have hgY := Subgroup.mem_inf.mp (hY g.2)
  have hgJ : conjSub (g : Y) J ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    conjSub_mem_omegaNbr_core hL hJ (layerY_le_centralizer g.2)
  have heq : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub (g : Y) J) =
      secImg (CoreAssembly.conjClass (tightCore R)) t J' := by
    rw [← conjSub_secImg]
    exact hgb
  have hstep : GLinkStep R t J (conjSub (g : Y) J) :=
    Or.inr ⟨K', hJK, u, v, hu, hv, (g : Y), hgY.2, hgY.1, rfl⟩
  exact (Relation.ReflTransGen.single hstep).trans
    (reflTransGen_gLinkStep_of_secImg_eq hL hA hgJ hJ' heq)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
