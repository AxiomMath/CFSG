module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicSmall

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section U42RootB

variable {D : Type} [Group D] {α : MulAut D} {S : Subgroup D}

theorem IsU42Root.isComponentOf (h : IsU42Root α S) :
    CFSG.Assembly.IsComponentOf S (α.toMonoidHom.eqLocus (MonoidHom.id D)) :=
  (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.2.1).2
    h.isComponent

end U42RootB

theorem ru_u42Free :
    SporadicU42Free .Ru :=
  sporadicU42Free_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    u42_fails_not_three_dvd u42_fails_not_three_dvd (fun _ _ _ ⟨e⟩ t ht =>
      compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd ru_centralizerIn_comps
        (e.trans CFSG.Sporadic.RuSchreier.ruEquivP) t ht)
    (outer_comps_of_forall_inner (s := .Ru) (mem_inner_of_mulEquiv
      CFSG.Sporadic.RuSchreier.ruEquivP CFSG.Sporadic.RuSchreier.mulAut_inner) _)

theorem mcl_u42Free :
    SporadicU42Free .McL := by
  have hUi : ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Nonempty (Y ⧸ center Y ≃* mclX) := by
    rintro Y _ hY hnab hcard ⟨θ⟩
    refine u42_fails_card_quotient_center_mem (N := {20160}) (by norm_num) Y hY hnab hcard ?_
    rw [Set.mem_singleton_iff]
    exact (Nat.card_congr θ.toEquiv).trans CFSG.Sporadic.SmallOddCore.card_mclX
  exact sporadicU42Free_of_comps (isoInvariant_quotient_center_equiv mclX)
    (isoInvariant_card_quotient_center _) hUi
    (u42_fails_card_quotient_center_mem (N := {7920}) (by norm_num))
    (fun G _ _ ⟨e⟩ t ht => mcl_inner_comps e t ht)
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => mcl_outer_comps e β (mul_self_eq_one_of_orderOf_eq_two hβ2) hβ)

theorem hs_u42Free :
    SporadicU42Free .HS := by
  intro D _ _ hD hs α S h
  obtain ⟨e⟩ := hs
  by_cases hα : α ∈ inner D
  · obtain ⟨t, ht, hαt⟩ :=
      exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD) h.1 hα
    have hcomp : CFSG.Assembly.IsComponentOf S (centralizer ({t} : Set D)) := by
      have := h.isComponentOf
      rwa [← hαt, eqLocus_conj] at this
    obtain ⟨-, -, h360⟩ :=
      CFSG.Sporadic.SmallOddCore.cti_hs_involution_local_components_simple_order_360 ⟨e⟩ ht hcomp
    rw [h.2.2.2.2.2] at h360
    norm_num at h360
  · obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
      CFSG.Sporadic.SmallOddCore.hs_involution_centralizers
    obtain ⟨r, hr, hcard, hout⟩ := autModel_exists_row CFSG.Sporadic.SmallOddCore.hs_autModel
      CFSG.Sporadic.SmallOddCore.hsRows (fun r => CFSG.Sporadic.SmallOddCore.tp 3850 r.rep)
      CFSG.Sporadic.SmallOddCore.ClassRow.centOrder CFSG.Sporadic.SmallOddCore.ClassRow.outer
      hcover (fun r hr => ⟨(hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩)
      (e.trans CFSG.Sporadic.Schreier.hsPermEquiv) α h.1
    have hmem := List.mem_map_of_mem (f := fun r : CFSG.Sporadic.SmallOddCore.ClassRow =>
      (r.outer, r.classSize, r.centOrder)) hr
    rw [hmap] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨ho, -, -⟩ | ⟨ho, -, -⟩ | ⟨-, -, hc⟩ | ⟨-, -, hc⟩
    · exact absurd (hout.2 hα) (by rw [ho]; simp)
    · exact absurd (hout.2 hα) (by rw [ho]; simp)
    · rw [hc] at hcard
      have hdvd := h.card_dvd_eqLocus
      rw [hcard] at hdvd
      norm_num at hdvd
    · rw [hc] at hcard
      have hdvd := h.card_dvd_eqLocus
      rw [hcard] at hdvd
      norm_num at hdvd

theorem he_u42Free :
    SporadicU42Free .He := by
  intro D _ _ hD hs α S h
  obtain ⟨e⟩ := hs
  by_cases hα : α ∈ inner D
  · obtain ⟨t, ht, hαt⟩ :=
      exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD) h.1 hα
    have hcomp : CFSG.Assembly.IsComponentOf S (centralizer ({t} : Set D)) := by
      have := h.isComponentOf
      rwa [← hαt, eqLocus_conj] at this
    have h20160 :=
      CFSG.Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order ⟨e⟩ ht
        hcomp
    exact u42_fails_card_quotient_center_mem (N := {20160}) (by norm_num) _ h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2 (Set.mem_singleton_iff.2 h20160)
  · set θ : D ≃* CFSG.Sporadic.HeldB.heP := e.trans CFSG.Sporadic.HeldB.heEquivP
    have hγ2 : orderOf (MulAut.congr θ α) = 2 := (orderOf_congr θ α).trans h.1
    have hγout : MulAut.congr θ α ∉
        (MulAut.conj : CFSG.Sporadic.HeldB.heP →* MulAut CFSG.Sporadic.HeldB.heP).range :=
      fun hb => hα ((congr_mem_inner_iff θ α).1 hb)
    obtain ⟨x, hx, hxP, hx2⟩ := CFSG.Sporadic.HeldB.exists_heConjR_eq
      CFSG.Sporadic.HeldB.ctbh_full_automorphism_permutation_model.1 _ hγ2 hγout
    obtain ⟨g, hg, hxg⟩ := CFSG.Sporadic.HeldB.exists_conj_heAutU x.2 hxP hx2
    have hfix : (MulAut.congr θ α).toMonoidHom.eqLocus (MonoidHom.id CFSG.Sporadic.HeldB.heP) =
        CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
          (CFSG.Sporadic.HeldB.heConjR x) := by
      rw [hx]
      ext y
      rfl
    have hcard : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) = 15120 := by
      rw [card_eqLocus_congr θ α, hfix,
        Nat.card_congr (CFSG.Sporadic.HeldB.fixedSubgroupEquivOfConj x hg _ hxg).toEquiv,
        CFSG.Sporadic.HeldB.card_heP_centralizer_heAutU]
    have hdvd := h.card_dvd_eqLocus
    rw [hcard] at hdvd
    norm_num at hdvd

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
