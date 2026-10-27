module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Rank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySylow
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo SmallRankCover smallRankS smallRankR
  smallRankD smallRankIsQ8D8 Lemma628Concl KFactZAction628 sr628_exists_mem_normalizer_not_mem
  sr628_centralizer_le_normalizer_oddCore sr628_card_sup_and_solvable
  sr628_exists_invariant_pGroup_not_le sr628_isNilpotent_fitting sr628_exists_pGroup
  sr628_centralizer_le_normalizer_zpowers smallRankInvolutionRankLE_of_localRank)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T : Subgroup G}

theorem s628_exists_invariant (c : S62Config p P M x z T) (hcov : SmallRankCover p M x) :
    ∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ ∃ F₁ : Subgroup G, IsPGroup f F₁ ∧
      smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (F₁ : Set G) ∧ ¬ F₁ ≤ M := by
  have hp : p.Prime := c.prime
  have hp2 : p ≠ 2 := c.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := smallRankD p x with hD
  set O : Subgroup G := rankThreePrimeCore 2 D with hO
  have hDspec : D ≤ C ∧ C ≤ normalizer (D : Set G) ∧ Nat.Coprime p (Nat.card D) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p C
  have hOspec : O ≤ D ∧ D ≤ normalizer (O : Set G) ∧ Nat.Coprime 2 (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  have hCO : C ≤ normalizer (O : Set G) := sr628_centralizer_le_normalizer_oddCore p x
  have hOM : ¬ O ≤ M := fun hOM => c.point.not_le (hcov.trans (sup_le inf_le_left hOM))
  have hSC : smallRankS x T ≤ C := inf_le_right
  have hBC : zpowers x ⊔ zpowers z ≤ C := c.B_le_centralizer
  have hAO : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (O : Set G) :=
    (sup_le hSC hBC).trans hCO
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := P.isPGroup'.to_le c.B_le_P
  obtain ⟨hcardA, hAsolv⟩ :=
    sr628_card_sup_and_solvable hp hp2 c.S_isPGroup hBp c.B_le_normalizer_S
  have hcop : Nat.Coprime (Nat.card ↥(smallRankS x T ⊔ (zpowers x ⊔ zpowers z)))
      (Nat.card O) := by
    rw [hcardA]
    obtain ⟨a, ha⟩ := c.S_isPGroup.exists_card_eq
    obtain ⟨b, hb⟩ := hBp.exists_card_eq
    rw [ha, hb]
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left a hOspec.2.2)
      (Nat.Coprime.pow_left b (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le hOspec.1) hDspec.2.2))
  have hOsolv : Group.IsSolvable ↥O :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1 hOspec.2.2)
  obtain ⟨f, hfp, F₁, hF₁O, hF₁p, hAF₁, hF₁M⟩ :=
    sr628_exists_invariant_pGroup_not_le hAO hcop hOM
  have : Fact f.Prime := ⟨hfp⟩
  have hF₁ne : F₁ ≠ ⊥ := fun h => hF₁M (h ▸ bot_le)
  have hfdvd : f ∣ Nat.card F₁ :=
    hF₁p.card_eq_or_dvd.resolve_left fun h1 => hF₁ne (Subgroup.eq_bot_of_card_eq _ h1)
  have hfO : f ∣ Nat.card O := hfdvd.trans (Subgroup.card_dvd_of_le hF₁O)
  have hf2 : f ≠ 2 := fun h =>
    absurd (Nat.Coprime.eq_one_of_dvd hOspec.2.2 (h ▸ hfO)) (by norm_num)
  have hfD : f ∣ Nat.card D := hfO.trans (Subgroup.card_dvd_of_le hOspec.1)
  have hfp' : f ≠ p := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDspec.2.2 (h ▸ hfD))
  exact ⟨f, hfp, hf2, hfp', F₁, hF₁p, hAF₁, hF₁M⟩

theorem s628_kfact_conclusion (hK : KFactZAction628) (c : S62Config p P M x z T) {f : ℕ}
    (hfp : f.Prime) (hf2 : f ≠ 2) (hfp' : f ≠ p) {F₁ : Subgroup G} (hF₁ : IsPGroup f F₁)
    (hAF₁ : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (F₁ : Set G))
    (hF₁M : ¬ F₁ ≤ M) :
    (p = 3 ∨ p = 5) ∧ (p = 3 → Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) ∧
      (p = 5 → smallRankIsQ8D8 (smallRankR x z T)) := by
  have : Fact f.Prime := ⟨hfp⟩
  have hSM : smallRankS x T ≤ M := c.S_le_M
  have hBM : zpowers x ⊔ zpowers z ≤ M := c.B_le_M
  have hAM : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (M : Set G) :=
    (sup_le hSM hBM).trans le_normalizer
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = F₁ ⊓ M := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, X = F₁ ⊓ normalizer (N : Set G) := ⟨_, rfl⟩
  have hNF : N ≤ F₁ := by rw [hN]; exact inf_le_left
  have hNM : N ≤ M := by rw [hN]; exact inf_le_right
  have hmemN : ∀ g : G, g ∈ F₁ → g ∈ M → g ∈ N := fun g h1 h2 => by
    rw [hN]; exact ⟨h1, h2⟩
  have hXF : X ≤ F₁ := by rw [hX]; exact inf_le_left
  have hXnorm : X ≤ normalizer (N : Set G) := by rw [hX]; exact inf_le_right
  have hNX : N ≤ X := by rw [hX]; exact le_inf hNF le_normalizer
  have hNnorm : (N.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr hXnorm
  have hXN : ¬ X ≤ N := by
    have hlt : N < F₁ := lt_of_le_of_ne hNF fun h => hF₁M (h ▸ hNM)
    obtain ⟨y, hyF, hyN, hyn⟩ := sr628_exists_mem_normalizer_not_mem hF₁ hlt
    refine fun hXN => hyn (hXN ?_)
    rw [hX]
    exact ⟨hyF, hyN⟩
  have hXM : ¬ X ≤ M := fun h => hXN fun g hg => hmemN g (hXF hg) (h hg)
  have hXp : IsPGroup f X := hF₁.to_le hXF
  have hAN : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (N : Set G) := by
    rw [hN]
    exact (le_inf hAF₁ hAM).trans inf_normalizer_le_normalizer_inf
  have hAX : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (X : Set G) := by
    rw [hX]
    exact (le_inf hAF₁ (hAN.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hSzA : smallRankS x T ⊔ zpowers z ≤ smallRankS x T ⊔ (zpowers x ⊔ zpowers z) :=
    sup_le_sup_left le_sup_right _
  have hH2 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → X ⊓ centralizer (S₀ : Set G) ≤ N := by
    intro S₀ hS₀S hS₀ne hzS₀ g hg
    obtain ⟨hgX, hgc⟩ := Subgroup.mem_inf.mp hg
    exact hmemN g (hXF hgX) (c.normalizer_le hS₀S hS₀ne hzS₀ (centralizer_le_normalizer _ hgc))
  have hzA : z ∈ smallRankS x T ⊔ (zpowers x ⊔ zpowers z) :=
    mem_sup_right (mem_sup_right (mem_zpowers z))
  have hX2 : 2 ≤ CFSG.Open.pRank f X :=
    s62_two_le_pRank_of_commutator c hfp hf2 hXp (hAX hzA) (le_sup_left.trans hAX)
      fun S₀ h1 h2 h3 hXC => hXN fun g hg => hH2 S₀ h1 h2 h3 ⟨hg, hXC hg⟩
  have hrank3 : rankThreeLocalRank f G ≤ 3 :=
    s62_localRank_le_three c.situation c.prop614 hfp hf2 hXp hX2 hXM c.S_isPGroup c.S_le_M
      c.S_ne_bot c.B_le_normalizer_S hAX
  refine hK G p f c.prime hfp c.ne_two hf2 hfp' (smallRankS x T) X N z c.S_isPGroup hXp hNX
    hNnorm hXN c.central.pow_eq_one c.central.ne_one c.z_le_normalizer_S (hSzA.trans hAX)
    (hSzA.trans hAN) c.R_ne_bot hH2 ?_ (smallRankInvolutionRankLE_of_localRank hfp _ X hrank3)
    fun hp3 => absurd hp3 (by have := c.situation.p_ge; omega)
  intro g hg
  obtain ⟨hgX, hgc⟩ := Subgroup.mem_inf.mp hg
  exact hmemN g (hXF hgX) (c.centralizer_le_M hgc)

theorem s628_fitting_inf_eq_bot (h65 : S62Prop65) (c : S62Config p P M x z T)
    (hcov : SmallRankCover p M x) (h1 : p = 3 ∨ p = 5)
    (h5 : p = 5 → smallRankIsQ8D8 (smallRankR x z T)) :
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M = ⊥ := by
  have hp : p.Prime := c.prime
  have hp5 : p = 5 := h1.resolve_left (by have := c.situation.p_ge; omega)
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := smallRankD p x with hD
  set O : Subgroup G := rankThreePrimeCore 2 D with hO
  set F : Subgroup G := CFSG.fittingSubgroupOf O with hF
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥(F ⊓ M) ≠ 1 from fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hgo : orderOf (g : G) = q := by rw [Subgroup.orderOf_coe]; exact hg
  have hgF : (g : G) ∈ F := g.2.1
  have hgM : (g : G) ∈ M := g.2.2
  have hDspec : D ≤ C ∧ C ≤ normalizer (D : Set G) ∧ Nat.Coprime p (Nat.card D) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p C
  have hOspec : O ≤ D ∧ D ≤ normalizer (O : Set G) ∧ Nat.Coprime 2 (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  have hCO : C ≤ normalizer (O : Set G) := sr628_centralizer_le_normalizer_oddCore p x
  have hOF : normalizer (O : Set G) ≤ normalizer (F : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.fittingSubgroup O)
  have : Group.IsNilpotent F := sr628_isNilpotent_fitting O
  obtain ⟨Q₀, hQ₀p, hQ₀F, hgQ₀, hFQ₀⟩ := sr628_exists_pGroup hgF hgo
  have hCQ₀ : C ≤ normalizer (Q₀ : Set G) := hCO.trans (hOF.trans hFQ₀)
  have hFO : F ≤ O := Subgroup.map_subtype_le _
  have hqO : q ∣ Nat.card O := hgo ▸ Subgroup.orderOf_dvd_natCard O (hFO hgF)
  have hq2 : q ≠ 2 := fun h =>
    absurd (Nat.Coprime.eq_one_of_dvd hOspec.2.2 (h ▸ hqO)) (by norm_num)
  have hqD : q ∣ Nat.card D := hqO.trans (Subgroup.card_dvd_of_le hOspec.1)
  have hqp : q ≠ p := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDspec.2.2 (h ▸ hqD))
  have hQ₀D : Q₀ ≤ D := hQ₀F.trans (hFO.trans hOspec.1)
  have hnormQ₀ : (Q₀.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQ₀D).mpr (hDspec.1.trans hCQ₀)
  have hQ₀Q : Q₀ ≤ pCoreOf q D := CFSG.LieType.BorelTits.le_pCoreOf q hQ₀D hnormQ₀ hQ₀p
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hgo
    exact hq.one_lt.ne hgo
  have hQ₁ne : pCoreOf q D ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (g : G) ∈ pCoreOf q D ⊓ M := ⟨hQ₀Q hgQ₀, hgM⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hg1 hmem
  have hQp : IsPGroup q (pCoreOf q D) := CFSG.LieType.BorelTits.pCoreOf_isPGroup q D
  have hCQ : C ≤ normalizer (pCoreOf q D : Set G) :=
    hDspec.2.1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q D)
  have hBQ₁ : zpowers x ⊔ zpowers z ≤ normalizer ((pCoreOf q D ⊓ M : Subgroup G) : Set G) :=
    fun b hb => inf_normalizer_le_normalizer_inf ⟨hCQ (c.B_le_centralizer hb),
      le_normalizer (c.B_le_M hb)⟩
  obtain ⟨k, hk⟩ := (hQp.to_le (inf_le_left : pCoreOf q D ⊓ M ≤ pCoreOf q D)).exists_card_eq
  have hcopQ₁ : Nat.Coprime p (Nat.card (pCoreOf q D ⊓ M : Subgroup G)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp hq).mpr hqp.symm)
  have hoddQ₁ : Odd (Nat.card (pCoreOf q D ⊓ M : Subgroup G)) := by
    rw [hk]
    exact (hq.eq_two_or_odd'.resolve_left hq2).pow
  have hN₁ : normalizer ((pCoreOf q D ⊓ M : Subgroup G) : Set G) ≤ M :=
    h65 G p P M x z c.situation c.point c.central c.prop614 T c.sylowTwo hcov hp5 (h5 hp5) _
      hQ₁ne inf_le_right hBQ₁ hcopQ₁ hoddQ₁
  have hQM : pCoreOf q D ≤ M := by
    by_contra hQM
    have hlt : pCoreOf q D ⊓ M < pCoreOf q D :=
      lt_of_le_of_ne inf_le_left fun heq => hQM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyQ, hyN, hyY⟩ := sr628_exists_mem_normalizer_not_mem hQp hlt
    exact hyY ⟨hyQ, hN₁ hyN⟩
  rw [inf_eq_left.mpr hQM] at hN₁
  exact c.point.not_le (hCQ.trans hN₁)

theorem stepL628_of_kfacts (hK : KFactZAction628) (h65 : S62Prop65) : StepL628 := by
  intro G _ _ p P M x z hS hx hz h614 T hT hcov
  have c : S62Config p P M x z T := ⟨hS, hx, hz, h614, hT⟩
  obtain ⟨f, hfp, hf2, hfp', F₁, hF₁, hAF₁, hF₁M⟩ := s628_exists_invariant c hcov
  obtain ⟨h1, h3, h5⟩ := s628_kfact_conclusion hK c hfp hf2 hfp' hF₁ hAF₁ hF₁M
  exact ⟨h1, h3, h5, s628_fitting_inf_eq_bot h65 c hcov h1 h5⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
