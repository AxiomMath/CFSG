module

public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscB1
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

namespace LinkDisc

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem omegaNbr_coreLinkFam_of_secFam (hL : TightLargeHypR r n Y R S t) {J M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
      omegaNbr (coreLinkFam R t) (secImg (CoreAssembly.conjClass (tightCore R)) t J) := by
  have hΦ := (TightLargeHypR.typeRFam hL).secFam (x := t)
  obtain ⟨-, hne, T, hT, hTM, hTN⟩ := h
  have hTs := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ.hyp
    (secImg_mem (xMem_of_mem_omegaNbr_core hL hM)) hT hTM
  exact ⟨⟨M, hM, rfl⟩, hne, T, mem_RSet_of_isSylow2In ⟨M, hM, rfl⟩ hTs, hTM, hTN⟩

theorem secImg_eq_or_nbr_of_linkConn (hL : TightLargeHypR r n Y R S t)
    (hall : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J)
    (hconn : DConnected (linkFam R t)) {J L : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hL' : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    secImg (CoreAssembly.conjClass (tightCore R)) t L =
        secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
      secImg (CoreAssembly.conjClass (tightCore R)) t L ∈
        omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
          (secImg (CoreAssembly.conjClass (tightCore R)) t J) := by
  have hΦ := ((TightLargeHypR.typeRFam hL).secFam (x := t)).hyp
  have key : ∀ b, Relation.ReflTransGen
      (fun Mb Nb => Nb ∈ linkFam R t ∧ dAdj (linkFam R t) Mb Nb)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) b →
      b ∈ linkFam R t ∧
        ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          (secImg (CoreAssembly.conjClass (tightCore R)) t M).subgroupOf (linkGrp R t) = b →
            secImg (CoreAssembly.conjClass (tightCore R)) t M =
                secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
              secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
                omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
                  (secImg (CoreAssembly.conjClass (tightCore R)) t J) := by
    intro b hb
    induction hb with
    | refl =>
      exact ⟨subgroupOf_mem_linkRestrict hJ, fun M hM hMb =>
        Or.inl (secImg_eq_of_subgroupOf_eq hM hJ hMb)⟩
    | @tail b c _ hbc ih =>
      obtain ⟨⟨_, ⟨M₁, hM₁, rfl⟩, -, rfl⟩, hP⟩ := ih
      obtain ⟨hc, hadj⟩ := hbc
      refine ⟨hc, fun M hM hMc => ?_⟩
      subst hMc
      have hnbr : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
          omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
            (secImg (CoreAssembly.conjClass (tightCore R)) t M₁) := by
        rcases hadj with h1 | h2
        · exact omegaNbr_secFam_of_link hL hM₁ hM h1
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM))
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM₁))
            (omegaNbr_secFam_of_link hL hM hM₁ h2)
      rcases hP M₁ hM₁ rfl with e | hM₁J
      · rw [e] at hnbr
        exact Or.inr hnbr
      · have hJM₁ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ
          (secImg_mem (xMem_of_mem_omegaNbr_core hL hJ))
          (secImg_mem (xMem_of_mem_omegaNbr_core hL hM₁)) hM₁J
        exact Or.inl (eq_of_mem_omegaNbr_coreLinkFam_of_noGNbr hL hM₁ (hall M₁ hM₁)
          (omegaNbr_coreLinkFam_of_secFam hL hM hnbr)
          (omegaNbr_coreLinkFam_of_secFam hL hJ hJM₁))
  exact (key _ (hconn _ (subgroupOf_mem_linkRestrict hJ) _
    (subgroupOf_mem_linkRestrict hL'))).2 L hL' rfl

@[expose] def TightLinkEdgeNoTriR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t →
      (∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J →
          ¬ ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
            secImg (CoreAssembly.conjClass (tightCore R)) t L =
                secImg (CoreAssembly.conjClass (tightCore R)) t J ∨
              secImg (CoreAssembly.conjClass (tightCore R)) t L =
                secImg (CoreAssembly.conjClass (tightCore R)) t M

theorem tightLinkDiscNoTriR_of (hB2 : TightLinkEdgeNoTriR r n) : TightLinkDiscNoTriR r n := by
  intro Y _ _ R S t hL hc hT hα hall hconn
  obtain ⟨J, hJ, -⟩ := id hα
  by_cases hone : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      secImg (CoreAssembly.conjClass (tightCore R)) t L =
        secImg (CoreAssembly.conjClass (tightCore R)) t J
  · exact false_of_secImg_eq hL hJ hone
  push Not at hone
  obtain ⟨M₀, hM₀, hne⟩ := hone
  have hnbr := (secImg_eq_or_nbr_of_linkConn hL hall hconn hJ hM₀).resolve_left hne
  obtain ⟨ν, hν, hM₀ν⟩ := exists_conj_omegaNbr_of_secImg (TightLargeHypR.typeRFam hL)
    (xMem_of_mem_omegaNbr_core hL hJ) (xMem_of_mem_omegaNbr_core hL hM₀) hnbr
  have hJν := conjSub_mem_omegaNbr_core hL hJ (layerY_le_centralizer ν.2)
  have hJν' := secImg_conj_of_mem hν J
  refine hB2 Y R S t hL hc hT hα hall _ hJν M₀ hM₀ hM₀ν fun L hL' => ?_
  rcases secImg_eq_or_nbr_of_linkConn hL hall hconn hJ hL' with e | hLJ
  · exact Or.inl (by rw [hJν', e])
  · exact Or.inr (eq_of_mem_omegaNbr_coreLinkFam_of_noGNbr hL hJ (hall J hJ)
      (omegaNbr_coreLinkFam_of_secFam hL hL' hLJ) (omegaNbr_coreLinkFam_of_secFam hL hM₀ hnbr))

end Cit3

end LinkDisc

end CFSG.ClassicalInvolution.Q3.TL4
