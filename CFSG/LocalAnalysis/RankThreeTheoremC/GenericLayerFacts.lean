module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseLayer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPGroup_two_of_le_centralizer (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {W L E : Subgroup G} (hW2 : IsPGroup 2 W) (hWne : W ≠ ⊥) (hLW : L ≤ centralizer (W : Set G))
    (hEM : E ≤ M) (hEW : E ≤ normalizer (W : Set G)) (hE3 : 3 ≤ CFSG.Open.pRank p E) : L ≤ M := by
  have hprime := sigmaA_prime p hp
  have hH : IsTwoLocal (normalizer (W : Set G)) := ⟨W, hWne, hW2, rfl⟩
  have hrank : 3 ≤ CFSG.Open.pRank p (normalizer (W : Set G) ⊓ M) :=
    hE3.trans (pRank_mono p hprime.one_lt (le_inf hEW hEM))
  exact (hLW.trans (centralizer_le_normalizer _)).trans
    (le_of_three_le_pRank_inf hD1 hp hM hH hrank)

omit [Finite G] in
theorem le_normalizer_inf {A B E : Subgroup G} (hA : E ≤ normalizer (A : Set G))
    (hB : E ≤ normalizer (B : Set G)) : E ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  have hA' := Subgroup.mem_normalizer_iff.mp (hA hg)
  have hB' := Subgroup.mem_normalizer_iff.mp (hB hg)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA' h, hB' h]

theorem pCoreOf_two_inf_centralizer_layer_eq_bot (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hx : IsGenericPoint p P M x)
    (hLM : ¬ rankThreeLayer (centralizer ({x} : Set G)) ≤ M) :
    pCoreOf 2 M ⊓ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) :
      Set G) = ⊥ := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨-, -, -, hrk⟩ := hx
  by_contra hne
  refine hLM (le_of_isPGroup_two_of_le_centralizer hD1 hp hM
    (L := rankThreeLayer (centralizer ({x} : Set G)))
    (E := (P : Subgroup G) ⊓ centralizer ({x} : Set G))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_inf_left) hne
    (Subgroup.le_centralizer_iff.mp inf_le_right) (inf_le_left.trans hPM) ?_ hrk.ge)
  refine le_normalizer_inf ((inf_le_left.trans hPM).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) ?_
  exact inf_le_right.trans ((le_normalizer_rankThreeLayer _).trans
    (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup _))

theorem layer_data_of_isGenericPoint {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G}
    {x : G} (hx : IsGenericPoint p P M x) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    x ∉ rankThreeLayer (centralizer ({x} : Set G)) ∧
      2 ≤ CFSG.Open.pRank p (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
        rankThreeLayer (centralizer ({x} : Set G))) := by
  obtain ⟨-, ⟨-, hx1, -, -, -⟩, hsyl, -⟩ := hx
  refine ⟨fun h => hx1 (eq_one_of_commute_of_mulEquiv_psl_two e h fun h' hh' =>
    mem_centralizer_singleton_iff.mp (rankThreeLayer_le _ hh')), ?_⟩
  exact hm.trans (le_pRank_inf_of_mulEquiv_psl hsyl (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _) (by omega) e)

theorem not_two_dvd_card_inf_centralizer_layer (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x)
    (hLM : ¬ rankThreeLayer (centralizer ({x} : Set G)) ≤ M) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    ¬ 2 ∣ Nat.card ↥(centralizer ({x} : Set G) ⊓
      centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G)) := by
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hxL, hpos⟩ := layer_data_of_isGenericPoint hx hm e
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := id hx
  intro heven
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set L : Subgroup G := rankThreeLayer C with hL
  obtain ⟨W, hW⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (C ⊓ centralizer (L : Set G))
  have hWne : W ≠ ⊥ := by
    intro hW1
    have hcard := hW.card_eq
    rw [hW1, card_bot] at hcard
    have hpos2 : 0 < (Nat.card ↥(C ⊓ centralizer (L : Set G))).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' heven
    exact (Nat.one_lt_two_pow hpos2.ne').ne' hcard.symm
  obtain ⟨E, hEP, hEL, hE, hEc⟩ := exists_isElemAbelian_le_sup_zpowers
    (P := (P : Subgroup G) ⊓ C) (C := C) (L := L) (rankThreeLayer_le _)
    ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hxp
    (fun c hc => mem_centralizer_singleton_iff.mp hc) hxL (by omega)
  have hLW : L ≤ centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.mp (hW.le.trans inf_le_right)
  have hxW : x ∈ centralizer (W : Set G) :=
    mem_centralizer_iff.mpr fun w hw => mem_centralizer_singleton_iff.mp (hW.le hw).1
  exact hLM (le_of_isPGroup_two_of_le_centralizer hD1 hp hM hW.isPGroup hWne hLW
    ((hEP.trans inf_le_left).trans hPM)
    ((hEL.trans (sup_le hLW (zpowers_le.mpr hxW))).trans (centralizer_le_normalizer _))
    (by have := le_pRank_of_elemAbelian_card (le_refl E) hE hEc; omega))

theorem pRank_top_le_three (hS : Setting G) {p : ℕ} [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3 := by
  obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, P.isPGroup',
      by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  exact (pRank_le_of_isSylowOf hsyl).trans hP3.le

theorem isCyclic_of_isPGroup_of_le_centralizer_layer (hS : Setting G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hx : IsGenericPoint p P M x) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) {Q : Subgroup G}
    (hQp : IsPGroup p Q)
    (hQ : Q ≤ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G)) :
    IsCyclic Q := by
  obtain ⟨-, hpos⟩ := layer_data_of_isGenericPoint hx hm e
  obtain ⟨E, hEA, hE, hEc⟩ := pRank_attained p (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
    rankThreeLayer (centralizer ({x} : Set G))) (by omega)
  exact isCyclic_of_le_centralizer (sigmaA_odd p hp)
    (fun l hl hc => eq_one_of_commute_of_mulEquiv_psl_two e hl hc) (pRank_top_le_three hS hp hM)
    le_top hQ hQp (hEA.trans inf_le_right) le_top hE hpos hEc

theorem centralizer_layer_le (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hx : IsGenericPoint p P M x) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G) ≤ M := by
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨-, hpos⟩ := layer_data_of_isGenericPoint hx hm e
  have hS1p : IsPGroup p ↥(((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
      rankThreeLayer (centralizer ({x} : Set G))) :=
    P.isPGroup'.to_inf_left.to_inf_left
  have hN := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hS1p
    ((inf_le_left.trans inf_le_left).trans hPM) hpos
  exact (Subgroup.centralizer_le inf_le_right).trans
    ((centralizer_le_normalizer _).trans hN)

theorem generic_layer_facts (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) {p : ℕ}
    [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    ¬ rankThreeLayer (centralizer ({x} : Set G)) ≤ M ∧
      centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G) ≤ M ∧
      pCoreOf 2 M ⊓ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) :
        Set G) = ⊥ ∧
      ¬ 2 ∣ Nat.card ↥(centralizer ({x} : Set G) ⊓
        centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G)) ∧
      ∀ Q : Subgroup G, IsPGroup p Q →
        Q ≤ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G) →
        IsCyclic Q := by
  obtain ⟨-, ⟨-, -, -, -, hxCM⟩, hsyl, -⟩ := id hx
  have hLM : ¬ rankThreeLayer (centralizer ({x} : Set G)) ≤ M :=
    not_rankThreeLayer_le_of_mulEquiv_psl hS hU0 hp hM hxCM hsyl hm e
  exact ⟨hLM, centralizer_layer_le hS hU0 hp hM hx hm e,
    pCoreOf_two_inf_centralizer_layer_eq_bot hS hD1 hp hM hx hLM,
    not_two_dvd_card_inf_centralizer_layer hS hD1 hp hM hx hLM hm e,
    fun _ hQp hQ => isCyclic_of_isPGroup_of_le_centralizer_layer hS hp hM hx hm e hQp hQ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
