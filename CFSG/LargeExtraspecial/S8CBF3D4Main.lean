module

public import CFSG.LargeExtraspecial.S8CBF3D4A5
public import CFSG.LargeExtraspecial.S8CBF3D4Red

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem corBA5Residual :
    CorBA5Residual := by
  intro X _ _ t hto _ _ _ ⟨f, hL⟩ R N hNR hRU hRt hRn hperf hNn htN hsimple h60 hN
  have hnc := exists_mul_ne_of_section_nonabelian hRU (exists_mul_ne_of_card_sixty h60)
  have htU : t ∈ normalClosure ({t} : Set X) := subset_normalClosure (Set.mem_singleton t)
  obtain ⟨hcfg, hcard⟩ :=
    a5Config_quotient_center htU hto hnc hNR hRU hRt hRn hperf h60 htN hN
  have hce : ChevalleyExceptionalModel (↥(normalClosure ({t} : Set X)) ⧸
      center ↥(normalClosure ({t} : Set X))) .trialityD4 2 f := by
    rcases hL with ⟨hcl, -⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact hce
    · exact absurd hree (by decide)
    · exact absurd hsz (by decide)
  obtain ⟨⟨-, hf, -⟩, hU⟩ := hce
  obtain ⟨K, _, _, _, σ, hσ, -, hKc, hkc, ⟨e⟩⟩ := TrialityCover.triality_model hf hU
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK : 8 ≤ Nat.card K := by
    rw [hKc]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h2f 3
  have hσ1 : ∃ c, σ c ≠ c := by
    by_contra hc
    push Not at hc
    have h1 : Nat.card (trialityFixedField K σ.toRingHom) = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun c => hc c)
    rw [hkc, hKc] at h1
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  let φ := (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hC : (⊤ : Subgroup _).map φ = graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    ext x
    refine ⟨fun ⟨y, _, hy⟩ => by rw [← hy]; exact (e y).2,
      fun hx => ⟨e.symm ⟨x, hx⟩, mem_top _, ?_⟩⟩
    change ((e (e.symm ⟨x, hx⟩) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = x
    rw [MulEquiv.apply_symm_apply]
  have hlt := card_lt_of_a5Config σ hσ hσ1 hK (hcfg.of_injective φ hφ hC)
  rwa [card_map_of_injective hφ, hcard] at hlt

end CFSG.LargeExtraspecial.S8
