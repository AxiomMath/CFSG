module

public import CFSG.Fischer.Classification.PartII.O2Mono

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E) (h2 : ∀ a ∈ E, (twinClass E a).ncard = 2)
include hμ hP h2

theorem eq_of_isTwin_of_two {a b : H} (ha : a ∈ E) (haμ : a ∉ μ) (h : IsTwin E a b)
    (hbμ : b ∉ μ) : b = a := by
  have := Pair.finite hP
  have hsne : sec E μ a ≠ a := hμ.sec_ne haμ ha
  have hsub : ({a, sec E μ a} : Set H) ⊆ twinClass E a := by
    intro x hx
    rcases hx with rfl | rfl
    · exact self_mem_twinClass ha
    · exact hμ.isTwin_sec ha
  have heq : ({a, sec E μ a} : Set H) = twinClass E a :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [h2 a ha, Set.ncard_pair hsne.symm])
      (Set.toFinite _)
  have hb : b ∈ ({a, sec E μ a} : Set H) := by
    rw [heq]
    exact h
  rcases hb with rfl | rfl
  · rfl
  · exact absurd (hμ.sec_mem ha) hbμ

theorem mul_mul_mem_of_two {a b : H} (ha : a ∈ E) (haμ : a ∉ μ) (hb : b ∈ E) (hbμ : b ∉ μ)
    (hab : a * b ≠ b * a) : a * b * a ∈ μ := by
  have hm := hμ.mate_spec hP ha haμ hb hab
  have he : mate E μ a b = b := hμ.eq_of_isTwin_of_two hP h2 hb hbμ hm.1 hm.2.1
  rw [← he]
  exact hm.2.2

theorem commute_of_two {f g k : H} (hf : f ∈ E) (hg : g ∈ E) (hk : k ∈ E)
    (hfg : f * g ≠ g * f) (hgk : g * k ≠ k * g) (hfk : f * k ≠ k * f) :
    k * (f * g * f) = f * g * f * k := by
  have := Pair.finite hP
  by_contra hc
  obtain ⟨f₀, hf₀, hf₀μ⟩ : ∃ f₀, IsTwin E f f₀ ∧ f₀ ∉ μ := by
    by_cases hfμ : f ∈ μ
    · obtain ⟨x, hx, hxf⟩ := Set.exists_ne_of_one_lt_ncard (by rw [h2 f hf]; norm_num) f
      exact ⟨x, hx, fun hxμ => hxf (hμ.eq_of_isTwin f hfμ x hxμ hx).symm⟩
    · exact ⟨f, isTwin_refl hf, hfμ⟩
  have hf₀E := hf₀.2.1
  have hf₀g : f₀ * g ≠ g * f₀ := not_commute_of_isTwin hf₀ hg hfg
  have hf₀k : f₀ * k ≠ k * f₀ := not_commute_of_isTwin hf₀ hk hfk
  have hc₀ : k * (f₀ * g * f₀) ≠ f₀ * g * f₀ * k :=
    not_commute_of_isTwin' (Pair.isTwin_mul_mul hP hf₀ hg hfg) hk hc
  have hne := hμ.mate_mate_mate_ne_of_affine hP hf₀E hf₀μ hg hk hf₀g hgk hf₀k hc₀
  have hf'E := hμ.mate_mem hP hf₀E hf₀μ hg hf₀g
  have hf'μ := hμ.mate_notMem hP hf₀E hf₀μ hg hf₀g
  have hf'k : mate E μ f₀ g * k ≠ k * mate E μ f₀ g :=
    not_commute_of_isTwin (hμ.isTwin_mate hP hf₀E hf₀μ hg hf₀g) hk hgk
  have hf''E := hμ.mate_mem hP hf'E hf'μ hk hf'k
  have hf''μ := hμ.mate_notMem hP hf'E hf'μ hk hf'k
  have hf''f : mate E μ (mate E μ f₀ g) k * f₀ ≠ f₀ * mate E μ (mate E μ f₀ g) k :=
    not_commute_of_isTwin (hμ.isTwin_mate hP hf'E hf'μ hk hf'k) hf₀E fun e => hf₀k e.symm
  have hm := hμ.mate_spec hP hf''E hf''μ hf₀E hf''f
  exact hne (hμ.eq_of_isTwin_of_two hP h2 hf₀E hf₀μ hm.1 hm.2.1)

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
