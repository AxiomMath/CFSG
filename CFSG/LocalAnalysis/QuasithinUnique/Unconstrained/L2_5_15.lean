module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15OuterD
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Inner

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

theorem false_of_isL33OrM11 (hK : K33LocalFacts) (hL : L33AutFacts) (hM : M11OutTrivial)
    {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
    (N : Notation25 hs) {t zK : G} (h : Lv2513 N t zK) (hiso : IsL33OrM11 ↥N.K) : False := by
  have F : K33Facts N.K := hK G N.K hiso
  have hKt := centralizer_t_le_normalizer_K N h F
  by_cases hin : ∀ s ∈ N.S, Ch1.InducesInner s N.K
  · exact false_of_inner N h F hKt hin
  · push Not at hin
    rcases hiso with hL33 | he
    · have L := hL G N.K hL33
      obtain ⟨x', hx'P, hx'S, hx'2, hx'c⟩ := exists_xprime N h F hKt
      have hSC := SC_eq_zpowers_of_outer N h F L hKt hin hx'P hx'S hx'2 hx'c
      exact false_of_outer_stage2 N h F L hKt hx'P hx'S hx'c hSC
    · obtain ⟨s, hs', hso⟩ := hin
      have hsN : s ∈ Subgroup.normalizer (N.K : Set G) :=
        N.S_le_normalizer_K (H_le_normalizer_K N h F) hs'
      obtain ⟨y, hy, hact⟩ := hM G N.K he s⁻¹ (Subgroup.inv_mem _ hsN)
      apply hso
      refine ⟨y⁻¹, N.K.inv_mem hy, fun x hx => ?_⟩
      have := hact x hx
      simpa using this

end CFSG.QuasithinUnique.Unc25K1

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem lemma2515 (hK : K33LocalFacts) (hL : L33AutFacts) (hM : M11OutTrivial) : Lemma2515 := by
  intro G _ _ T M hs N t zK h
  refine ⟨fun ⟨e⟩ => ?_, fun hL33 => ?_⟩
  · exact Unc25K1.false_of_isL33OrM11 hK hL hM N h (Or.inr ⟨e⟩)
  · exact Unc25K1.false_of_isL33OrM11 hK hL hM N h (Or.inl hL33)

end CFSG.QuasithinUnique
