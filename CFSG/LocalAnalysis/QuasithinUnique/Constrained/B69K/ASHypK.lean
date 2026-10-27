module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Pair
public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs
public import CFSG.Quasithin.Background.B69E22Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace B69K

variable {V : Type} [CommGroup V] [Finite V]

theorem asHyp_of_compHypK {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (K T' M' : Subgroup Y),
      E2P.ASHyp K T' M' ∧ Nonempty (↥L ⧸ Subgroup.center ↥L ≃* ↥K) := by
  obtain ⟨-, hmp, -, -, -, -, hL, -⟩ := hH
  haveI : Finite (MulAut V) := inferInstanceAs (Finite (V ≃* V))
  obtain ⟨Y, _, _, K, T', M', hAS, π, hπ⟩ :=
    exists_asHyp_of_component hmp.subgroupOf (B69.isComponentOf_subgroupOf hL)
  have e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  haveI := hAS.simple
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  obtain ⟨e⟩ := B69.equiv_of_central_quotients hL.2.2 (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _) (π.comp e0.symm.toMonoidHom) (hπ.comp e0.symm.surjective)
  exact ⟨Y, inferInstance, inferInstance, K, T', M', hAS, ⟨e⟩⟩

theorem not_char2Exc (hExc : E2P.E22Char2ExcFam) {X T M A L : Subgroup (MulAut V)}
    (hH : B69.CompHypK X T M A L) :
    ¬ ((∃ f : ℕ, 2 ≤ f ∧ IsG2 2 f (↥L ⧸ Subgroup.center ↥L)) ∨
      (∃ f : ℕ, 1 ≤ f ∧ Is3D4 2 f (↥L ⧸ Subgroup.center ↥L)) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ Is2F4 f (↥L ⧸ Subgroup.center ↥L)) ∨
      IsTits (↥L ⧸ Subgroup.center ↥L)) := by
  intro h
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e⟩⟩ := asHyp_of_compHypK hH
  refine hExc Y K T' M' hAS ?_
  rcases h with ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, ho, hf, h⟩ | h
  · exact Or.inl ⟨f, hf, IsG2.of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨f, hf, Is3D4.of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, ho, hf, Is2F4.of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (IsTits.of_mulEquiv e h)))

theorem not_lnTwo (hLn : E2P.E22LnTwoFam) {X T M A L : Subgroup (MulAut V)}
    (hH : B69.CompHypK X T M A L) {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ IsPSL n 2 1 (↥L ⧸ Subgroup.center ↥L) := by
  intro h
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e⟩⟩ := asHyp_of_compHypK hH
  exact hLn Y K T' M' hAS n hn (IsPSL.of_mulEquiv e h)

theorem not_alt_seven (hAlt : E2P.E22AltFam) {X T M A L : Subgroup (MulAut V)}
    (hH : B69.CompHypK X T M A L) : ¬ IsAlt 7 (↥L ⧸ Subgroup.center ↥L) := by
  intro h
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e⟩⟩ := asHyp_of_compHypK hH
  exact (hAlt Y K T' M' hAS).2.2.1 (IsAlt.of_mulEquiv e h)

theorem not_alt_eight (hAlt : E2P.E22AltFam) {X T M A L : Subgroup (MulAut V)}
    (hH : B69.CompHypK X T M A L) : ¬ IsAlt 8 (↥L ⧸ Subgroup.center ↥L) := by
  intro h
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e⟩⟩ := asHyp_of_compHypK hH
  exact (hAlt Y K T' M' hAS).2.2.2 (IsAlt.of_mulEquiv e h)

theorem false_of_parabolicPair {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L)
    {C : Type} [Group C] [Finite C] (e : ↥L ⧸ Subgroup.center ↥L ≃* C) {U : Subgroup C}
    (hU : IsSylowTwoOf U ⊤) (hP : ParabolicPair U) : False := by
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e'⟩⟩ := asHyp_of_compHypK hH
  obtain ⟨P₀, P₁, hU₀, hU₁, h₀, h₁, hgen, hinv⟩ := hP
  exact hAS.false_of_invPair (e'.symm.trans e) hU hU₀ hU₁ h₀ h₁ hgen hinv

end B69K

end CFSG.Quasithin
