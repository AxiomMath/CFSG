module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertA5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertL32
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
import CFSG.Adapters.StatedPSLTwoSeven

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127

theorem overgroups_alt_six
    : Overgroups ↥(alternatingGroup (Fin 6)) :=
  Overgroups.of_sylow _ Even6.isSylow_D fun Y hY hne => (Even6.overgroups Y hY).resolve_left hne

theorem overgroups_alt_eight
    : Overgroups ↥(alternatingGroup (Fin 8)) :=
  Overgroups.of_sylow _ Even8.isSylow_D fun Y hY hne => (Even8.overgroups Y hY).resolve_left hne

theorem overgroups_alt
    {S : Type} [Group S] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) : Overgroups S := by
  rcases hn with rfl | rfl | rfl
  · exact Overgroups.of_mulEquiv e.symm CertA5.overgroups
  · exact Overgroups.of_mulEquiv e.symm overgroups_alt_six
  · exact Overgroups.of_mulEquiv e.symm overgroups_alt_eight

theorem overgroups_model_five
    {S : Type} [Group S] (h : StatedClassicalModel S .PSL 2 5 1) :
    Overgroups S := by
  obtain ⟨e⟩ := Setup.Family.alternating_five_of_model_five h
  exact overgroups_alt (Or.inl rfl) e

theorem overgroups_model_nine
    {S : Type} [Group S] (h : StatedClassicalModel S .PSL 2 3 2) :
    Overgroups S := by
  obtain ⟨e⟩ := Setup.Family.alternating_six_of_model_nine h
  exact overgroups_alt (Or.inr (Or.inl rfl)) e

theorem nonempty_equiv_sl_three_two_of_model_seven {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 7 1) :
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven h

theorem overgroups_model_seven
    {S : Type} [Group S] (h : StatedClassicalModel S .PSL 2 7 1) :
    Overgroups S := by
  obtain ⟨e⟩ := nonempty_equiv_sl_three_two_of_model_seven h
  exact Overgroups.of_mulEquiv e.symm CertL32.overgroups_sl

theorem overgroups_psl_three_two
    {S : Type} [Group S] (h : StatedClassicalModel S .PSL 3 2 1) :
    Overgroups S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : S ≃* StatedProj (StatedSL 3 K) := e
  exact Overgroups.of_mulEquiv
    (e'.trans (Setup.Family.statedProjSL_equiv_of_card_two 3 K (by simpa using hK))).symm
    CertL32.overgroups_sl

theorem overgroups_psl_four_two
    {S : Type} [Group S] (h : StatedClassicalModel S .PSL 4 2 1) :
    Overgroups S := by
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff S).mp
    (Or.inl ⟨by decide, h⟩)
  exact overgroups_alt (Or.inr (Or.inr rfl)) e

theorem overgroups_psu_three_three
    {S : Type} [Group S] (h : StatedClassicalModel S .PSU 3 3 1) :
    Overgroups S :=
  CertU33.overgroups_of_lieModel (Or.inl ⟨by decide, h⟩)

end CFSG.QuasithinUnique.Bridge.Over
