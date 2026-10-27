module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_caseII (hG : Gen5Global G) (hII : GL83Generic5CaseII)
    (Sch : KFactCatalogSchreier) (KB : KFactWeakClosure) (KC : KFactInnerAction)
    (hl : Gen5Local G p P M x) {v : G} (hv1 : v ≠ 1)
    (hvZ : v ∈ centralizer ((gen5L x : Subgroup G) : Set G)) (_hvp : ¬ p ∣ orderOf v)
    (hvx : v * x = x * v)
    {W : Subgroup G} (hW2 : IsPGroup 2 W) (hWN : W ≤ centralizer ({v} : Set G))
    (hUW : gen5U (P : Subgroup G) x ≤ normalizer (W : Set G)) :
    ∀ w ∈ W, ∀ l ∈ gen5L x, w⁻¹ * (l⁻¹ * w * l) ∈
      rankThreePrimeCore p (centralizer ({v} : Set G)) := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  have hp5 := gen5_five_le hG hl
  set N : Subgroup G := centralizer ({v} : Set G) with hN
  set O : Subgroup N := primeComplementCore (G := N) p with hO
  have hLN : gen5L x ≤ N := fun l hl =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hvZ l hl)
  have hxN : x ∈ N := mem_centralizer_singleton_iff.mpr hvx.symm
  have hNtop : N ≠ ⊤ := centralizer_singleton_ne_top hG.setting.simple hG.setting.nonab hv1
  obtain ⟨e⟩ := gen5_psl hG hl
  obtain ⟨-, ⟨eL⟩, hUL'⟩ :=
    map_mk_layer hp5 hLN e (gen5_sylow hG hl) (gen5_U_elemAbelian hG hl).2
  obtain ⟨-, hx1, hxp, -, -⟩ := hl.generic.2.1
  have hxo : orderOf (⟨x, hxN⟩ : N) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxp hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxN⟩) = p :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime p) hxo
  have hab := isMulCommutative_sylow_quotient (N := N) fun _ hQ => (gen5_pgroup hG hl hQ).1
  refine commutator_mem_rankThreePrimeCore hWN hLN (hII Sch KB KC hp5
    (primeComplementCore_quotient_eq_bot p)
    ((catalogSimpleSections_of_isKProper hG.setting.kProper N hNtop).quotient O) eL hUL'
    (pRank_top_quotient_le hp fun _ hQ => (gen5_pgroup hG hl hQ).2) hab
    (show QuotientGroup.mk' O ⟨x, hxN⟩ ≠ 1 from fun h => by
      rw [h, orderOf_one] at hxo'
      exact hp.one_lt.ne hxo')
    (by simpa only [hxo'] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxN⟩))
    (mk_mem_centralizer_map (gen5_Z hG hl).1)
    (centralizer_mk_le_normalizer_map hp hxo (gen5_centralizer_le_normalizer x))
    (perfect_le_map_mk hp hxo fun _ hJ hJp => gen5_perfect_le hG hl Sch hJ hJp)
    (weaklyClosed_map_mk hxo hab (gen5_weakly_closed hG hl))
    (coprime_card_map_of_isPGroup_two (W := W.subgroupOf N) hp (by omega) _
      hW2.comap_subtype)
    (map_subgroupOf_le_normalizer_map hUW _))

end CFSG.LocalAnalysis.RankThreeTheoremC
