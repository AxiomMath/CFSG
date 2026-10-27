module

public import CFSG.GF2Type.Smith1980Orth.ReductionSix
public import CFSG.GF2Type.SmithTypeE.E7.Defs
public import CFSG.GF2Type.SmithTypeE.E7.Omega
public import CFSG.GF2Type.SmithTypeE.Parts

public section

namespace CFSG.GF2Type.SmithTypeE

open Matrix Module CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.EvenSource CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.Bridge CFSG.GroupTheory.WeirSylow

theorem nonempty_mulEquiv_omegaPlus_six_of_six
    (hOrth6 : GF2Type.Smith1980Orth.Smith1980OrthogonalSixStatement)
    {M : Type} [Group M] [Finite M] [IsSimpleGroup M] (t : M) (ht2 : orderOf t = 2)
    (hext : IsExtraspecialPGroup 2 (generalizedFitting (Subgroup.centralizer ({t} : Set M))))
    (hcard : Nat.card (generalizedFitting (Subgroup.centralizer ({t} : Set M))) = 2 ^ 17)
    (hquot : timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({t} : Set M)))
      (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) :
    Nonempty (M ≃* timmesfeldOmegaPlus 6) := by
  have hnonab := exists_noncomm_of_fstar_centralizer t hcard
  set C := Subgroup.centralizer ({t} : Set M) with hC
  let e : generalizedFitting ↥C ≃* inSubgroup generalizedFitting C :=
    (generalizedFitting ↥C).equivMapOfInjective C.subtype C.subtype_injective
  have hext' : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting C) :=
    (timmesfeldIsExtraspecial_iff _).mp ((timmesfeldIsExtraspecial_congr e).mp
      ((timmesfeldIsExtraspecial_iff _).mpr hext))
  have hcard' : Nat.card (inSubgroup generalizedFitting C) = 2 ^ (1 + 2 * 8) :=
    (Nat.card_congr e.symm.toEquiv).trans hcard
  obtain ⟨q, hnd, hplus, ⟨eΩ⟩⟩ := exists_form_omegaPlus_four
  have hmain := hOrth6 M hnonab t ht2 hext' 8 hcard' (by norm_num) (by decide)
    (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4) hquot q hnd
    (Or.inl ⟨MulEquiv.prodCongr (MulEquiv.refl _) eΩ⟩)
  have hL : LieModel M .POmegaPlus 6 2 1 := hmain.1 hplus
  exact nonempty_mulEquiv_timmesfeldOmegaPlus_of_lieModel 6 (by norm_num) hL

theorem partC_of_smithE7Input_six
    (hOrth6 : GF2Type.Smith1980Orth.Smith1980OrthogonalSixStatement)
    (h : SmithE7Input) : PartC := by
  intro G _ _ _ hnonab z hz hext hcard Mbar _ hMbar hMs ⟨t, ht2, htext, htcard, htquot⟩
  have hfin : Finite Mbar := by
    obtain ⟨φ, hφ, -⟩ := hMbar
    exact Finite.of_surjective φ hφ
  haveI : IsSimpleGroup Mbar := hMs
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = 16 := width_ofFStar hz hext' hcard'
  obtain ⟨e⟩ := nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  obtain ⟨eΩ⟩ := nonempty_mulEquiv_omegaPlus_six_of_six hOrth6 t ht2 htext htcard htquot
  have hE := h G (Setting.ofFStar z hz hext') hw ⟨e.trans eΩ⟩
  exact Or.inr (Or.inl ⟨rfl, by decide, hE⟩)

end CFSG.GF2Type.SmithTypeE
