module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

omit [Finite G] in
theorem coprime_card_map_subgroupOf {Y : Type*} [Group Y] {N W : Subgroup G} (hWN : W ≤ N)
    (hW : Nat.Coprime p (Nat.card W)) (f : N →* Y) :
    Nat.Coprime p (Nat.card ((W.subgroupOf N).map f)) :=
  Nat.Coprime.coprime_dvd_right ((card_map_dvd _ f).trans
    (dvd_of_eq (Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv))) hW

theorem gen5_caseI_N (hG : Gen5Global G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : KFactCatalogSchreier) (KA : KFactSignalizerTrivial) (hExcl : NoExcludedSection3 G)
    (hl : Gen5Local G p P M x) {N : Subgroup G} (hNtop : N ≠ ⊤) (hLN : gen5L x ≤ N)
    (hSyl : IsSylowOf p (gen5U (P : Subgroup G) x) N)
    {W : Subgroup G} (hWp : Nat.Coprime p (Nat.card W)) (hWN : W ≤ N)
    (hUW : gen5U (P : Subgroup G) x ≤ normalizer (W : Set G)) :
    W ≤ rankThreePrimeCore p N := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  have hp5 := gen5_five_le hG hl
  set O : Subgroup N := primeComplementCore (G := N) p
  have hUL := gen5_sylow hG hl
  have hUN : gen5U (P : Subgroup G) x ≤ N := hUL.le.trans hLN
  have hOM : O ≤ (N ⊓ M).subgroupOf N :=
    primeComplementCore_le_subgroupOf_inf_of_coprime hp hUN fun _ hX hXN =>
      gen5_coprime_le hG hl hX hXN
  obtain ⟨e⟩ := gen5_psl hG hl
  obtain ⟨-, ⟨eL⟩, hUL'⟩ := map_mk_layer hp5 hLN e hUL (gen5_U_elemAbelian hG hl).2
  exact le_rankThreePrimeCore_of_map_mk_eq_bot hWN (gl83Generic5CaseI_holds K1 Sch KA hp5
    (primeComplementCore_quotient_eq_bot p)
    ((catalogSimpleSections_of_isKProper hG.setting.kProper N hNtop).quotient O)
    (noExcludedSection3_quotient hExcl N O) eL hUL' (isSylowOf_top_map_mk hSyl)
    (map_mk_inf_ne_top hOM fun h => gen5_not_le hG hl (hLN.trans h))
    (fun _ hDU hD1 => normalizer_le_map_mk_inf hp hOM hUN hUL.isPGroup
      (fun _ hD hD1 => gen5_normalizer_le hG hl hD hD1) hDU hD1)
    (not_map_mk_le_map_mk_inf hOM hLN (gen5_not_le hG hl))
    (coprime_card_map_subgroupOf hWN hWp _) (map_subgroupOf_le_normalizer_map hUW _))

theorem gen5_caseIIHyp [Fact p.Prime] (hG : Gen5Global G) (Sch : KFactCatalogSchreier)
    (hl : Gen5Local G p P M x) {N : Subgroup G} (hNtop : N ≠ ⊤) (hLN : gen5L x ≤ N)
    (hxN : x ∈ N) :
    GL83Generic5CaseIIHyp p
      (((gen5L x).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
      (((gen5U (P : Subgroup G) x).subgroupOf N).map
        (QuotientGroup.mk' (primeComplementCore (G := N) p)))
      (QuotientGroup.mk' (primeComplementCore (G := N) p) ⟨x, hxN⟩) := by
  have hp := gen5_prime hl
  have hp5 := gen5_five_le hG hl
  set O : Subgroup N := primeComplementCore (G := N) p
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
  exact ⟨hp5, primeComplementCore_quotient_eq_bot p,
    (catalogSimpleSections_of_isKProper hG.setting.kProper N hNtop).quotient O, ⟨eL⟩, hUL',
    pRank_top_quotient_le hp fun _ hQ => (gen5_pgroup hG hl hQ).2, hab,
    fun h => by
      rw [h, orderOf_one] at hxo'
      exact hp.one_lt.ne hxo',
    by simpa only [hxo'] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxN⟩),
    mk_mem_centralizer_map (gen5_Z hG hl).1,
    centralizer_mk_le_normalizer_map hp hxo (gen5_centralizer_le_normalizer x),
    perfect_le_map_mk hp hxo fun _ hJ hJp => gen5_perfect_le hG hl Sch hJ hJp,
    weaklyClosed_map_mk hxo hab (gen5_weakly_closed hG hl)⟩

theorem gen5_caseII_N (hG : Gen5Global G) (Sch : KFactCatalogSchreier) (hK : GL83Generic5KFacts)
    (hl : Gen5Local G p P M x) {N : Subgroup G} (hNtop : N ≠ ⊤) (hLN : gen5L x ≤ N) (hxN : x ∈ N)
    {W : Subgroup G} (hWp : Nat.Coprime p (Nat.card W)) (hWN : W ≤ N)
    (hUW : gen5U (P : Subgroup G) x ≤ normalizer (W : Set G)) :
    ∀ w ∈ W, ∀ l ∈ gen5L x, w⁻¹ * (l⁻¹ * w * l) ∈ rankThreePrimeCore p N := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have h := gen5_caseIIHyp hG Sch hl hNtop hLN hxN
  obtain ⟨eL⟩ := h.equiv
  exact commutator_mem_rankThreePrimeCore hWN hLN (gl83Generic5CaseII_holds Sch hK.weakClosure
    hK.innerAction h.five_le h.core_eq_bot h.catalog eL h.sylow h.pRank_le h.abelian h.ne_one
    h.pow_eq_one h.mem_centralizer h.centralizer_le h.perfect_le h.weakClosed
    (coprime_card_map_subgroupOf hWN hWp _) (map_subgroupOf_le_normalizer_map hUW _))

end CFSG.LocalAnalysis.RankThreeTheoremC
