module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_4_21_core : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ q ∈ blockU L, ∀ g : G, g⁻¹ * q * g ∈ T → g⁻¹ * q * g ∈ thompsonJ S

theorem lemma2_4_21 (h8 : Lemma2_4_8) (h16 : Lemma2_4_16) (h19 : Lemma2_4_19)
    (hcore : Lemma2_4_21_core) : Lemma2_4_21 := by
  intro G _ _ T M H S L D n hcfg
  obtain ⟨-, ⟨-, hUQ⟩, ⟨-, -, h3⟩, -, -, -, h7, -⟩ := h8 G T M H S L D n hcfg
  have hcore' := hcore G T M H S L D n hcfg
  obtain ⟨x, hxT, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have h19' := h19 G T M H S L D n hcfg (lin2Z L (thompsonJ S)) rfl
  have hZU : lin2Z L (thompsonJ S) ≤ blockU L := by
    refine (lin2Z_le_centerOf h16 hcfg rfl).trans ?_
    rw [← (h3 x hxT hxS).2.1]
    exact inf_le_left
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine h19'.le.trans (iSup₂_le fun g hg => fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := mem_conjR_iff'.1 hy
    exact Subgroup.subset_closure ⟨hg hy, z, hUQ ▸ hZU hz, g, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyT, a, ha, g, rfl⟩
    exact hcore' a (hUQ ▸ ha) g hyT
  · intro i hi hi2 g hg
    have hE := isElemAbelian_zpowers_of_sq_eq_one hi2
    have hEle : Subgroup.zpowers i ≤ thompsonJ S := Subgroup.zpowers_le.2 hi
    rcases (h7 x hxT hxS).2.2 _ hEle hE with hiU | hiUx
    · exact hcore' i (hiU (Subgroup.mem_zpowers i)) g hg
    · have hj : x * i * x⁻¹ ∈ blockU L := mem_conjR.1 (hiUx (Subgroup.mem_zpowers i))
      have e : (x * g)⁻¹ * (x * i * x⁻¹) * (x * g) = g⁻¹ * i * g := by group
      have := hcore' _ hj (x * g) (by rw [e]; exact hg)
      rwa [e] at this

end CFSG.QuasithinUnique.Lin2
