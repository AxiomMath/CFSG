module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseStar
public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseOut

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem autOn_inf_autOn_eq_bot (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (h0 : S ⊓ L ≤ pCoreOf 2 X) :
    autOn S (blockV S L) ⊓ autOn L (blockV S L) = ⊥ := by
  have hPV := sup_le_normalizer_blockV S L
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨hyS, hyL⟩ := hy
  obtain ⟨a, haS, rfl⟩ := (Setup.mem_autOn_iff_rho hPV le_sup_right).mp hyS
  obtain ⟨l, hlL, hla⟩ := (Setup.mem_autOn_iff_rho hPV le_sup_left).mp hyL
  rw [Subgroup.mem_bot]
  have hal : ((l⁻¹ * a : ↥(L ⊔ S)) : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
    rw [← Setup.rho_eq_one_iff hPV, map_mul, map_inv, hla, inv_mul_cancel]
  have hmem : (a : G) ∈ L ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) := by
    have e : (a : G) = (l : G) * ((l⁻¹ * a : ↥(L ⊔ S)) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hlL ⟨(l⁻¹ * a : ↥(L ⊔ S)).2, hal⟩
  exact ((Setup.rho_eq_one_iff hPV a).mpr
    (inf_sup_centralizer_le hA hL hSL h0 haS hmem).2)

section Bound


theorem sstar_out_bound
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hc : IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)))
    (h0 : S ⊓ L ≤ pCoreOf 2 X) :
    (∀ a ∈ autOn S (blockV S L), ∀ b ∈ autOn S (blockV S L), a * b = b * a) ∧
    ∀ E : Subgroup (MulAut ↥(blockV S L)), E ≤ autOn S (blockV S L) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4 := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hq := isQuasisimple_autOn hA hL hSL
  have hFit := quasithinGenFitting_autOn_sup hA hL hSL
  have hcent : autOn (L ⊔ S) (blockV S L) ⊓ Subgroup.centralizer
      (autOn L (blockV S L) : Set (MulAut ↥(blockV S L))) ≤ autOn L (blockV S L) := by
    have := CFSG.Quasithin.centralizer_quasithinGenFitting_le (autOn (L ⊔ S) (blockV S L))
    rwa [hFit] at this
  have hnorm : autOn (L ⊔ S) (blockV S L) ≤
      Subgroup.normalizer (autOn L (blockV S L) : Set (MulAut ↥(blockV S L))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have hn := CFSG.Quasithin.InternalSec.autOn_normal_of (U := blockV S L)
      (sup_le Subgroup.le_normalizer hSL)
    refine ⟨fun hk => hn x hx k hk, fun hk => ?_⟩
    have := hn x⁻¹ (Subgroup.inv_mem _ hx) _ hk
    have e : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
    rwa [e] at this
  obtain ⟨e⟩ := nonempty_autOnCenterQuotientEquiv hA hL hSL
  have hout : OutTwoRank (↥(autOn L (blockV S L)) ⧸ Subgroup.center ↥(autOn L (blockV S L))) :=
    OutTwoRank.of_mulEquiv e.symm (outTwoRank_of_isClassicalTwoOrG2 hc)
  have hS2 : IsPGroup 2 (autOn S (blockV S L)) := by
    have hPV := sup_le_normalizer_blockV S L
    have h2 : IsPGroup 2 S := hA.twoRadical.isPGroup
    rintro ⟨φ, hφ⟩
    obtain ⟨p, hpS, rfl⟩ := (Setup.mem_autOn_iff_rho hPV le_sup_right).mp hφ
    obtain ⟨n, hn⟩ := h2 ⟨(p : G), hpS⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : (p : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hp1 : p ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn')
    show Setup.rho (blockV S L) (L ⊔ S) hPV p ^ 2 ^ n = 1
    rw [← map_pow, hp1, map_one]
  exact out_bound (autOn (L ⊔ S) (blockV S L)) (autOn L (blockV S L)) (autOn S (blockV S L))
    (Subgroup.isPerfect_iff.mp hq.1)
    (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le le_sup_left) hnorm hcent
    (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le le_sup_right) hS2
    (autOn_inf_autOn_eq_bot hA hL hSL h0) hout

end Bound

end CFSG.HardMathSupport.Cooperstein.StructureLie
