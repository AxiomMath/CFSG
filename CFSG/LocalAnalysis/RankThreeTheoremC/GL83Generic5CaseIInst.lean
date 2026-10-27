module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_caseI (hG : Gen5Global G) (hI : GL83Generic5CaseI)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (Sch : KFactCatalogSchreier)
    (KA : KFactSignalizerTrivial) (hExcl : NoExcludedSection3 G)
    (hl : Gen5Local G p P M x) {v : G} (hv1 : v ≠ 1)
    (hvZ : v ∈ centralizer ((gen5L x : Subgroup G) : Set G)) (_hvp : ¬ p ∣ orderOf v)
    (hSyl : IsSylowOf p (gen5U (P : Subgroup G) x) (centralizer ({v} : Set G)))
    {W : Subgroup G} (hW2 : IsPGroup 2 W) (hWN : W ≤ centralizer ({v} : Set G))
    (hUW : gen5U (P : Subgroup G) x ≤ normalizer (W : Set G)) :
    W ≤ rankThreePrimeCore p (centralizer ({v} : Set G)) := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  have hp5 := gen5_five_le hG hl
  set N : Subgroup G := centralizer ({v} : Set G) with hN
  set O : Subgroup N := primeComplementCore (G := N) p with hO
  have hLN : gen5L x ≤ N := fun l hl =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hvZ l hl)
  have hUL := gen5_sylow hG hl
  have hUN : gen5U (P : Subgroup G) x ≤ N := hUL.le.trans hLN
  have hOM : O ≤ (N ⊓ M).subgroupOf N :=
    primeComplementCore_le_subgroupOf_inf_of_coprime hp hUN fun _ hX hXN =>
      gen5_coprime_le hG hl hX hXN
  have hNtop : N ≠ ⊤ := centralizer_singleton_ne_top hG.setting.simple hG.setting.nonab hv1
  obtain ⟨e⟩ := gen5_psl hG hl
  obtain ⟨-, ⟨eL⟩, hUL'⟩ := map_mk_layer hp5 hLN e hUL (gen5_U_elemAbelian hG hl).2
  exact le_rankThreePrimeCore_of_map_mk_eq_bot hWN (hI K1 Sch KA hp5
    (primeComplementCore_quotient_eq_bot p)
    ((catalogSimpleSections_of_isKProper hG.setting.kProper N hNtop).quotient O)
    (noExcludedSection3_quotient hExcl N O) eL hUL' (isSylowOf_top_map_mk hSyl)
    (map_mk_inf_ne_top hOM fun h => gen5_not_le hG hl (hLN.trans h))
    (fun _ hDU hD1 => normalizer_le_map_mk_inf hp hOM hUN hUL.isPGroup
      (fun _ hD hD1 => gen5_normalizer_le hG hl hD hD1) hDU hD1)
    (not_map_mk_le_map_mk_inf hOM hLN (gen5_not_le hG hl))
    (coprime_card_map_of_isPGroup_two (W := W.subgroupOf N) hp (by omega) _
      hW2.comap_subtype)
    (map_subgroupOf_le_normalizer_map hUW _))

end CFSG.LocalAnalysis.RankThreeTheoremC
