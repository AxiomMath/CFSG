module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.CharCore
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

structure D2Escape {G : Type*} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M A H R : Subgroup G) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  sylow_le : (P : Subgroup G) ≤ M
  core_le : GLBCore p 2 (P : Subgroup G) ≤ M
  maxTwoLocal_M : GLBIsMaxTwoLocal M
  maxTwoLocal_H : GLBIsMaxTwoLocal H
  elem : IsElemAbelian p A
  card_A : Nat.card A = p ^ 2
  core_A : GLBCore p 1 A ≤ M
  A_le : A ≤ R
  le_H : R ≤ H
  le_M : R ≤ M
  isSylow : ∃ T : Sylow p H, (T : Subgroup H).map H.subtype = R
  pRank_eq : pRank p R = 2
  not_le : ¬ H ≤ M

variable {G : Type*} [Group G]

theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem normalizer_map_conj (g : G) (Y : Subgroup G) :
    Subgroup.normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (Y : Set G)).map (MulAut.conj g).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq Y (MulAut.conj g)).symm

theorem centralizer_singleton_le_normalizer_zpowers (t : G) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  have hcent : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have htx : t * x = x * t := Subgroup.mem_centralizer_iff.mp hx t (by simp)
    exact ((show Commute x t from htx.symm).zpow_right n).symm
  exact hcent.trans (Subgroup.centralizer_le_normalizer _)

variable [Finite G]

theorem le_pRank_of_isElemAbelian {p k : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) : k ≤ pRank p E :=
  CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hcard

theorem one_le_pRank_of_isElemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥) : 1 ≤ pRank p E := by
  have : Fact p.Prime := ⟨hp⟩
  have hpE : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpE
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Subgroup.eq_bot_of_card_eq E (by simpa using hk)) hE1
    · exact hpos
  exact hk1.trans (le_pRank_of_isElemAbelian hp hE hk)

theorem normalizer_le_of_core {p : ℕ} (hp : p.Prime) (P : Sylow p G) {M Y : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hcore : GLBCore p 2 (P : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hY : IsPGroup p Y) (hrank : 2 ≤ pRank p Y) : Subgroup.normalizer (Y : Set G) ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le p P hPM hYM hY
  have hrank' : 2 ≤ pRank p (Y.map (MulAut.conj (m : G)).toMonoidHom) := by
    rw [pRank_map_of_injective p hp _ (MulAut.conj (m : G)).injective]
    exact hrank
  have hN := (normalizer_le_glbCore p 2 hm hrank').trans hcore
  rw [normalizer_map_conj] at hN
  exact CFSG.AGLEmbedding.le_of_map_conj_le m.2 hN

theorem le_of_normalizer_inf_le {p : ℕ} [Fact p.Prime] {S M : Subgroup G} (hS : IsPGroup p S)
    (hN : S ⊓ Subgroup.normalizer ((S ⊓ M : Subgroup G) : Set G) ≤ M) : S ≤ M := by
  let : Group.IsNilpotent S := hS.isNilpotent
  have hnormalizer :
      Subgroup.normalizer ((S ⊓ M).subgroupOf S : Set S) = (S ⊓ M).subgroupOf S := by
    apply le_antisymm _ Subgroup.le_normalizer
    rw [← Subgroup.subgroupOf_normalizer_eq inf_le_left]
    intro x hx
    exact ⟨x.property, hN ⟨x.property, hx⟩⟩
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := S))) ((S ⊓ M).subgroupOf S) hnormalizer
  exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right

namespace D2Escape

variable {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem isPGroup (h : D2Escape p P M A H R) : IsPGroup p R := by
  obtain ⟨T, rfl⟩ := h.isSylow
  exact T.isPGroup'.map H.subtype

theorem A_le_M (h : D2Escape p P M A H R) : A ≤ M := h.A_le.trans h.le_M

theorem A_le_H (h : D2Escape p P M A H R) : A ≤ H := h.A_le.trans h.le_H

theorem two_le_pRank_A (h : D2Escape p P M A H R) : 2 ≤ pRank p A :=
  le_pRank_of_isElemAbelian h.prime h.elem h.card_A

theorem normalizer_le_of_le_M (h : D2Escape p P M A H R) {Y : Subgroup G} (hYM : Y ≤ M)
    (hY : IsPGroup p Y) (hrank : 2 ≤ pRank p Y) : Subgroup.normalizer (Y : Set G) ≤ M :=
  normalizer_le_of_core h.prime P h.sylow_le h.core_le hYM hY hrank

theorem normalizer_R_le (h : D2Escape p P M A H R) : Subgroup.normalizer (R : Set G) ≤ M :=
  h.normalizer_le_of_le_M h.le_M h.isPGroup h.pRank_eq.ge

theorem normalizer_le_of_le_A (h : D2Escape p P M A H R) {Y : Subgroup G} (hYA : Y ≤ A)
    (hY : Y ≠ ⊥) : Subgroup.normalizer (Y : Set G) ≤ M :=
  (normalizer_le_glbCore p 1 hYA
    (one_le_pRank_of_isElemAbelian h.prime (isElemAbelian_of_le h.elem hYA) hY)).trans h.core_A

theorem centralizer_le (h : D2Escape p P M A H R) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ M := by
  refine (centralizer_singleton_le_normalizer_zpowers a).trans
    (h.normalizer_le_of_le_A ((Subgroup.zpowers_le).mpr ha) ?_)
  rwa [Ne, Subgroup.zpowers_eq_bot]

theorem signalizer_le (h : D2Escape p P M A H R) {S : Subgroup G}
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hS : p.Coprime (Nat.card S)) : S ≤ M :=
  (rank_two_signalizer_le_gamma_one p h.prime A A S le_rfl h.two_le_pRank_A hAS hS).trans
    h.core_A

theorem primeCore_le (h : D2Escape p P M A H R) : GLBPrimeCore p H ≤ M :=
  h.signalizer_le (h.A_le_H.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H))
    (CFSG.AGLEmbedding.glbPrimeCore_coprime p H)

theorem twoCore_le (h : D2Escape p P M A H R) : pCoreOf 2 H ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H)
  refine h.signalizer_le (h.A_le_H.trans (subgroup_normalizes_pCoreOf 2 H)) ?_
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes h.prime Nat.prime_two).mpr h.ne_two)

theorem inf_lt_left (h : D2Escape p P M A H R) : H ⊓ M < H :=
  lt_of_le_of_ne inf_le_left fun heq => h.not_le (inf_eq_left.mp heq)

theorem inf_lt_right (h : D2Escape p P M A H R) : H ⊓ M < M := by
  refine lt_of_le_of_ne inf_le_right fun heq => h.not_le ?_
  have hMH : M ≤ H := heq ▸ inf_le_left
  exact (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

theorem cgsIn_eq (h : D2Escape p P M A H R) :
    CFSG.Quasithin.cgsIn M (pCoreOf 2 H) = M ⊓ H :=
  CFSG.AGLEmbedding.maxTwoLocal_cgsIn_eq_inf h.maxTwoLocal_H M

end D2Escape

end CFSG.AGLEmbeddingD2
