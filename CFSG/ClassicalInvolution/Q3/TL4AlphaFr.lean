module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrProp
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrDefs
public import CFSG.ClassicalInvolution.Q3.TL4Conn278AN
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLay

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

namespace AlphaFr

theorem inf_centralizer_le_normalizer {G : Type} [Group G] {c z : G} {α₀ : Subgroup G}
    (h : alphaOf (Subgroup.closure ({c, z} : Set G)) = α₀) :
    Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (α₀ : Set G) := by
  intro y hy
  apply T8T.centralizer_le_normalizer_of_alphaOf_eq h
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hy.1).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem layerY_le_normalizer_of_not_dConnected (hH : TightHyp51TriR r n)
    (h4 : Thm4RBelow r n) (hG : TightSecLinkGenR r n) (hL : TightLargeHypR r n Y Rd Sd z)
    {A B : Subgroup Y} {a b : Y}
    (hA : A ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hAB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) A)
    (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b)
    (hind : b ∉ Subgroup.closure ({z, a} : Set Y)) (hnc : ¬ DConnected (coreLinkFam Rd z)) :
    layerY (CoreAssembly.conjClass (tightCore Rd)) z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({a, z} : Set Y)) : Set Y) := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hz := hd.isUniqueInvolution_core
  have h := TightLargeHypR.typeRFam hL
  have hnt := noTwins_of_large hL
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) :=
    CoreAssembly.mem_conjClass_self _
  have hXA := xMem_of_mem_omegaNbr_core hL hA
  have hXB := xMem_of_mem_omegaNbr_core hL hB
  have hab : a * b = b * a := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ha hAB hb
  have hza : z * a = a * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hA ha
  have hzb : z * b = b * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hB hb
  have hane : a ≠ b := fun e => hAB.2.1 (hnt _ hA.1 B ⟨hB.1, a, ha, e ▸ hb⟩)
  have hza' : z ≠ a := fun e => hA.2.1 (hnt _ hK A ⟨hA.1, z, hz, e ▸ ha⟩)
  have hKB := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hB.1 hB
  have hAB' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hA.1 hB.1 hAB
  obtain ⟨P, hP, -, hPz, hPa⟩ :=
    exists_isSylow2In_member_le_centralizer hL hB.1 hb hKB hAB' hz ha hza' hza
  have hnbr : secImg (CoreAssembly.conjClass (tightCore Rd)) z B ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) z)
        (secImg (CoreAssembly.conjClass (tightCore Rd)) z A) :=
    secImg_mem_omegaNbr hXA hXB hP hPz (hPa.trans (h.tight A hA.1 a ha))
      (secImg_ne h hXA hXB ha hb hab hane)
  have hcls := conjClass_secImg_eq hL hA
    (fun Mb hMb => exists_conj_of_not_dConnected h4 hL hnc ⟨A, hA, rfl⟩ hMb)
  have hBc : secImg (CoreAssembly.conjClass (tightCore Rd)) z B ∈
      CoreAssembly.conjClass (secImg (CoreAssembly.conjClass (tightCore Rd)) z A) := by
    rw [hcls]
    exact ⟨B, hB, rfl⟩
  have hdisc : ¬ DConnected
      (CoreAssembly.conjClass (secImg (CoreAssembly.conjClass (tightCore Rd)) z A)) := by
    rw [hcls]
    exact hnc
  have hgen := hG _ (natCard_secQuot_lt_of_large hL) _ (h.secFam (x := z))
    secQuot_oddCore_eq_bot omegaGen_secFam (aEmpty_secFam h) _ (secImg_mem hXA) _ hnbr hBc
    hdisc _ _ (isUniqueInvolution_secImg h hXA ha) (isUniqueInvolution_secImg h hXB hb)
  obtain ⟨hbal, -⟩ := alpha_of_triangle hH hL hA hB hAB ha hb hind
  have hab1 : a * b ≠ 1 := fun e => hane (by
    rw [eq_inv_of_mul_eq_one_right e, inv_eq_of_mul_eq_one_right ha.sq])
  have habz : a * b ≠ z := fun e => hind (by
    have hb' : b = a * z := by
      calc b = a * (a * b) := by rw [← mul_assoc, ha.sq, one_mul]
        _ = a * z := by rw [e]
    rw [hb']
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha.sq, hb.sq, one_mul]
  have habzc : (a * b) * z = z * (a * b) := by
    calc a * b * z = a * (z * b) := by rw [mul_assoc, hzb]
      _ = z * (a * b) := by rw [← mul_assoc, ← hza, mul_assoc]
  have hle : Subgroup.closure ({a * b, z} : Set Y) ≤ Subgroup.closure ({z, a, b} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  have hαab := hbal _ hle
    (T7A.isElemAbelian2_closure_pair hab2 hz.sq hab1 hz.ne_one habz habzc)
  exact layerY_le_of_linkGen hΩ.conjInvariant
    (oddCoreOf_layerY_le_normalizer hH hL hA hB hAB ha hb hind)
    (mem_layerY_of_isUniqueInvolution h hXA ha) (mem_layerY_of_isUniqueInvolution h hXB hb)
    ha.sq hb.sq hab (inf_centralizer_le_normalizer rfl)
    (inf_centralizer_le_normalizer (alphaOf_eq_of_link_edge hH hL hA hB hAB ha hb))
    (inf_centralizer_le_normalizer hαab) hgen

end Cit3

end AlphaFr

section Cit3


variable {r n : ℕ}

theorem tightAlphaFrameR_of (hH : TightHyp51TriR r n) (h4 : Thm4RBelow r n)
    (hG : TightSecLinkGenR r n) : TightAlphaFrameR r n := by
  intro Y _ _ Rd Sd z hL _ hfr J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2
  obtain ⟨A, B, a, b, hA, hB, hAB, ha, hb, hind⟩ := AlphaFr.exists_base_triangle hL hfr
  have key : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({u, z} : Set Y)) =
        alphaOf (Subgroup.closure ({a, z} : Set Y)) := by
    by_cases hconn : DConnected (coreLinkFam Rd z)
    · exact AlphaFr.alphaOf_eq_of_linkConn hH hL hA ha
        (AlphaFr.oddCoreOf_layerY_le_normalizer hH hL hA hB hAB ha hb hind) hconn
    · intro J hJ u hu
      exact AlphaFr.alphaOf_eq_of_layerY_le hL hA ha
        (AlphaFr.layerY_le_normalizer_of_not_dConnected hH h4 hG hL hA hB hAB ha hb hind hconn)
        hJ hu (AlphaFr.exists_conj_of_not_dConnected h4 hL hconn ⟨A, hA, rfl⟩ ⟨J, hJ, rfl⟩)
  rw [key J₁ hJ₁ t₁ h1, key J₂ hJ₂ t₂ h2]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
