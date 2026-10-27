module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Rank
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Lie

public section

namespace CFSG.ComponentClassification.GSThmB.X11

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem admissible_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (h : Blueprint.LieModel X t n p f) : StatedLieAdmissible t n p f :=
  (GH74.statedClassicalModel_of_lieModel hn h).1

theorem recognition_of_rows
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    (h3 : CF81X11CharThree) (hU52 : CF81X11U52) (hON : CF81X11ON)
    (hAlt : ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), KConf G N → ∀ n : ℕ, 7 ≤ n →
      ¬ Nonempty (↥N ≃* alternatingGroup (Fin n)))
    (hJ3 : ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), KConf G N →
      ¬ Blueprint.NativeSporadic.IsSporadic ↥N .J3)
    (hSuz : ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), KConf G N →
      ¬ Blueprint.NativeSporadic.IsSporadic ↥N .Suz) : Recognition := by
  intro G _ _ N hc hres
  have hk := hc.kConf
  have h3' := h3 G N hc
  obtain ⟨hJ1, hJ2, hM12, hHS, hHe⟩ := hk.not_sporadic
  obtain ⟨h1, h2, h3'', h4, h5, h6⟩ := hk.not_charTwo hO
  have hp3 : ∀ {t : StatedLieTag} {n p f : ℕ}, n ≠ 0 → p.Prime → p ≠ 2 →
      Blueprint.LieModel ↥N t n p f → p = 3 := fun hn hp hp2 hm =>
    hk.eq_three hGLS hO hp hp2 (admissible_of_lieModel hn hm) hm
  rcases hres with ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨p, f, hp, hp2, hf, hm⟩ | ⟨m, -, hm⟩ | hm | hm |
      hm | hm | hm | hm | hm | ⟨n, hn, hA⟩ | hm | hm | hm | hm | hm | hm | hm | hm
  · exact (hk.not_psl_two hp hp2 hf hm).elim
  · rcases hm with hm | hm | hm | hm | hm | hm | hm
    · exact (hk.not_psl_two hp hp2 (by omega) hm).elim
    · exact (hk.not_psl_three hp hp2 hm).elim
    · exact (hk.not_psu_three hp hp2 hm).elim
    · obtain rfl := hp3 (by norm_num) hp hp2 hm
      obtain rfl := (h3' f).1 (Or.inl hm)
      exact Or.inl hm
    · obtain rfl := hp3 (by norm_num) hp hp2 hm
      obtain rfl := (h3' f).1 (Or.inr (Or.inl hm))
      exact Or.inr (Or.inl hm)
    · obtain rfl := hp3 (by norm_num) hp hp2 hm
      obtain rfl := (h3' f).1 (Or.inr (Or.inr hm))
      exact (hk.not_psp_four_three hm).elim
    · obtain rfl := hp3 (by norm_num) hp hp2 hm
      exact ((h3' f).2 hm).elim
  · exact (hk.not_ree _ hm).elim
  · exact (h1 hm).elim
  · exact (h2 hm).elim
  · exact (h3'' hm).elim
  · exact (h4 hm).elim
  · exact (h5 hm).elim
  · exact (hk.not_u52 hU52 hm).elim
  · exact (h6 hm).elim
  · exact (hAlt G N hk n hn hA).elim
  · exact (hJ1 hm).elim
  · exact (hJ2 hm).elim
  · exact (hJ3 G N hk hm).elim
  · exact (hM12 hm).elim
  · exact (hHS hm).elim
  · exact (hHe hm).elim
  · exact (hk.not_on hON hm).elim
  · exact (hSuz G N hk hm).elim

end CFSG.ComponentClassification.GSThmB.X11
