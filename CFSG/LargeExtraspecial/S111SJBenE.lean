module

public import CFSG.LargeExtraspecial.S111SJBenC
public import CFSG.LargeExtraspecial.S111SJBenD
public import CFSG.CGT.Timmesfeld75.BenderInputsBasic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender

namespace LayerCfg

variable {X : Type} [Group X] {E O L : Subgroup X} {w : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : X →* (V ≃ₗ[ZMod 2] V)} {a : V}

theorem false_of_bender [Finite X] [FiniteDimensional (ZMod 2) V]
    [E.Normal] [O.Normal] (C : LayerCfg E O L w ρ a) (h6 : 6 ≤ w) {f i e : ℕ}
    (hB : BenderType (E ⧸ center E) f i e) : False := by
  obtain ⟨hw2, hw1⟩ := C.width_le hB
  have h2 := hB.two_le
  have h6' : 2 * i * f ≠ 6 := by
    intro h
    have hi1 : i = 1 := by
      rcases Nat.lt_or_ge i 2 with hi | hi
      · omega
      · nlinarith
    have hi3 : i ≠ 3 := by omega
    have := hw1 hi3
    subst hi1
    omega
  have hD' := two_mul_le_finrank_of_benderType (ρ.comp E.subtype)
    (C.rho_inj.comp Subtype.val_injective) hB h6'
  rw [C.finrank_eq] at hD'
  rcases hB.cases' with ⟨hi, he, -⟩ | ⟨hi, -, -⟩ | ⟨hi, -, -⟩
  · subst hi
    subst he
    by_cases hall : ∀ l ∈ L.map (barAct E), ∃ q, l = MulAut.conj q
    · by_cases hO : O = ⊥
      · exact C.false_of_inner_of_O_eq_bot hB hall hO
      · exact C.false_of_inner_of_O_ne_bot h6 hB hall hO
    · push Not at hall
      obtain ⟨l, hl, hl'⟩ := hall
      refine C.false_of_field h6 hB hl fun ⟨g, hg⟩ => hl' g ?_
      ext x
      rw [hg, MulAut.conj_apply]
  · subst hi
    have := hw1 (by norm_num)
    omega
  · subst hi
    omega

theorem false_of_goldschmidtSimpleType
    [Finite X] [FiniteDimensional (ZMod 2) V] [E.Normal] [O.Normal]
    (C : LayerCfg E O L w ρ a) (h6 : 6 ≤ w) (hG : goldschmidtSimpleType (E ⧸ center E)) :
    False := by
  have hBen : ∀ _ : CFSG.BenderSuzuki.IsBenderGroup (E ⧸ center E), False := fun hB => by
    obtain ⟨n, i, e, h⟩ := isBenderGroup_iff_exists_benderType.mp hB
    exact C.false_of_bender h6 h
  rcases hG with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | h
  · exact hBen (.isPSL2 f (by omega) e)
  · exact hBen (CFSG.CGT.Timmesfeld75.isBenderGroup_of_mulEquiv_sz hn e)
  · exact hBen (CFSG.ComponentClassification.Asc76X.isBenderGroup_of_mulEquiv_psu3 hf e)
  · exact C.false_of_nonBender h6 h

end LayerCfg

end CFSG.LargeExtraspecial.S11
