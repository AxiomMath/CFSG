module

public import CFSG.LocalAnalysis.EvenSporadicStandard.LyStd.NoHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.SwapHom

public section

namespace CFSG.EvenSporadicStandard.LyStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB CFSG.EvenSporadicStandard.McLStd

theorem noSwappedPair_ly :
    NoSwappedPair .Ly := by
  intro G _ _ L h hL t u ht ht2 hu hu2 hsw
  have htu : t ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht u hu).symm
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  obtain ⟨hCt, -, hcomm⟩ := h.centralizer_eq_prod_ly hL ht ht2
  have hzp : zpowers t ≤ centralizer ({u} : Set G) := zpowers_le.2 htu
  have hC : centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) ≤
      zpowers t ⊔ (centralizer ({u} : Set G) ⊓ L) := by
    rintro x ⟨hxt, hxu⟩
    rw [hCt] at hxt
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcomm hxt
    have hau : a ∈ centralizer ({u} : Set G) := by
      have := Subgroup.mul_mem _ hxu (Subgroup.inv_mem _ (hzp hb))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hau, ha⟩) (Subgroup.mem_sup_left hb)
  obtain ⟨φ, hφ⟩ := exists_hom_of_swappedPair ht2 htu hLt hC hsw
  exact ly_no_hom h hL ht ht2 hu hu2 φ htu hφ

theorem stdHasIntrinsicAn_ly_of_container
    (hct : ContainerIsDoubleCover .Ly) : StdHasIntrinsicAn .Ly :=
  stdHasIntrinsicAn_ly_of_residuals noSwappedPair_ly hct

theorem ly_not_standard_of_container
    (hS : Solomon2AnInput) (hct : ContainerIsDoubleCover .Ly)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) :
    ¬ IsSporadic L .Ly :=
  ly_not_standard hS (stdHasIntrinsicAn_ly_of_container hct) h

end CFSG.EvenSporadicStandard.LyStd
