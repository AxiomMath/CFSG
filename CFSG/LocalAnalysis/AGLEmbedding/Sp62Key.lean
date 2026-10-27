module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCommutator
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Orbit
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Perfect

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_map_conj_inv {Y : Type*} [Group Y] (A : Subgroup Y) (g : Y) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro hx
    exact ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] in
theorem barM_perfect {M V : Subgroup G} (hVM : V ≤ M) (hVV : ⁅V, V⁆ = V) :
    ⁅barM M V, barM M V⁆ = barM M V := by
  refine le_antisymm ((commutator_barM_le M V).trans (by rw [hVV])) ?_
  conv_lhs => rw [← hVV]
  refine barM_le_of_le_preimage ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  refine (mem_preM (M.mul_mem (M.mul_mem (M.mul_mem (hVM hx) (hVM hy)) (M.inv_mem (hVM hx)))
    (M.inv_mem (hVM hy)))).mpr ?_
  have e : (⟨x * y * x⁻¹ * y⁻¹,
      M.mul_mem (M.mul_mem (M.mul_mem (hVM hx) (hVM hy)) (M.inv_mem (hVM hx)))
      (M.inv_mem (hVM hy))⟩ : M) = ⁅(⟨x, hVM hx⟩ : M), ⟨y, hVM hy⟩⁆ := by
    ext
    simp [commutatorElement_def]
  rw [e, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy))

omit [Finite G] in
theorem le_pCoreOf_of_perfect {M V : Subgroup G} (hVM : V ≤ M) (hVV : ⁅V, V⁆ = V)
    {A B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hVA : barM M V ≤ A) (hVB : barM M V ≤ B)
    (hAB : ⁅A, B⁆ = ⊥) : V ≤ pCoreOf 2 M := by
  have hbot : barM M V = ⊥ := by
    rw [← barM_perfect hVM hVV, eq_bot_iff, ← hAB]
    exact Subgroup.commutator_mono hVA hVB
  intro v hv
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hVM hv⟩ ∈ barM M V :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact coe_mem_pCoreOf_two_of_mk_eq_one _ hmem

end Perfect

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Key

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V : Subgroup G}

theorem D1Sp62Data.barM_le (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {X : Subgroup G} (hX : X ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) :
    barM M X ≤ blockParabolic M (pCoreOf 2 H) L :=
  (Subgroup.map_mono (Subgroup.comap_mono hX)).trans
    (h.surv.ph3.barM_Pi_le' h84 h86 hD2 hb hL fun _ hk => h.barM_conj_eq hB3 hL hk)

omit [Finite G] in
theorem blockParabolic_le_barM' (M S L : Subgroup G) : blockParabolic M S L ≤ barM M L :=
  Subgroup.map_mono (Subgroup.comap_mono inf_le_right)

theorem D1Sp62Data.false_of_ne (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {L' : Subgroup G} (hL' : IsTwoPrimeComponent M L') (hVE : V ≤ blockClosure M (H ⊓ M) L')
    (hne : barM M L' ≠ barM M L) : False := by
  have h3 := h.surv.ph3
  obtain ⟨hVV, hVK, hVN, -⟩ := h.piece
  have hVM : V ≤ M := hVK.trans inf_le_right
  set Lb := barM M L with hLb
  have hLc : IsComponentOf Lb ⊤ := hL.component
  have hVL : barM M V ≤ Lb :=
    (h.barM_le h84 h86 hD2 hB3 hb hL (h.le_Pi hB3 hL)).trans (blockParabolic_le_barM' _ _ _)
  have hEC : barM M (blockClosure M (H ⊓ M) L') ≤
      Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine barM_le_of_le_preimage (sup_le ?_ (iSup_le fun k => iSup_le fun hk => ?_))
    · intro q hq
      refine (mem_preM ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M) hq)).mpr ?_
      rw [(mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq]
      exact Subgroup.one_mem _
    · have hLk := hL'.map_conj hk.2
      refine le_preM hLk.le ?_
      have hne' : barM M (L'.map (MulAut.conj k).toMonoidHom) ≠ Lb := by
        intro heq
        apply hne
        have hk' : k⁻¹ ∈ H ⊓ M := (H ⊓ M).inv_mem hk
        rw [← map_conj_map_conj_inv L' k, barM_map_conj hk'.2, heq, hLb, ← barM_map_conj hk'.2]
        exact h.barM_conj_eq hB3 hL hk'
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLk.component hLc hne')
  have hVC : barM M V ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.map_mono (Subgroup.comap_mono hVE)).trans hEC
  exact hVN ((le_pCoreOf_of_perfect hVM hVV hVC hVL
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl)).trans
    h3.twoCore_M_le_glbPrimeCore)

theorem D1Sp62Data.barM_eq (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {L' : Subgroup G} (hL' : IsWeakSBlock M (pCoreOf 2 H) L') : barM M L' = barM M L := by
  by_contra hne
  exact h.false_of_ne h84 h86 hD2 hB3 hb hL hL'.toIsTwoPrimeComponent
    ((h.le_Pi hB3 hL').trans inf_le_right) hne

end Key

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Normal

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V : Subgroup G}

theorem D1Sp62Data.barM_map_conj_eq (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {m : G} (hm : m ∈ M) : barM M (L.map (MulAut.conj m).toMonoidHom) = barM M L := by
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set L' := L.map (MulAut.conj m).toMonoidHom with hL'def
  have hL' := hL.toIsTwoPrimeComponent.map_conj hm
  by_contra hne
  by_cases hS : L' ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)
  · obtain ⟨-, y, hyL, hy3, ⟨l, -, hyl⟩, -⟩ := h3.mem_Pi' hB3 hL
    set y' := m * y * m⁻¹ with hy'
    have hy'L : y' ∈ L' := ⟨y, hyL, by simp [hy', MulAut.conj_apply]⟩
    have hy'K : y' ∈ H ⊓ M := hKeq ▸ ⟨hL'.le hy'L, hS hy'L⟩
    have hy'E : y' ∈ blockClosure M (H ⊓ M) L' :=
      Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
        (Subgroup.mem_iSup_of_mem (H ⊓ M).one_mem ⟨y', hy'L, by simp⟩))
    have hN : H ⊓ M ≤ Subgroup.normalizer
        (((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L' : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hy3' : IsPGroup 3 (Subgroup.zpowers y') := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
      have hya : y ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
      exact isPGroup_zpowers_of_pow_prime_pow_eq_one (by rw [hy', conj_pow, hya]; group)
    have hy1 : y' ≠ 1 := by
      intro h1
      apply hyl
      have hy1 : y = 1 := by
        have := congrArg (fun x => m⁻¹ * x * m) h1
        simpa [hy', mul_assoc] using this
      rw [hy1]
      simp
    have hVE : V ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L' :=
      (h.dichotomy _ inf_le_left hN).resolve_left fun hPiN =>
        not_mem_glbPrimeCore_of_three hy3' hy1 (hPiN ⟨hy'K, hy'E⟩)
    exact h.false_of_ne h84 h86 hD2 hB3 hb hL hL' (hVE.trans inf_le_right) hne
  · exact h.false_of_ne h84 h86 hD2 hB3 hb hL hL'
      ((h.le_Pi hB3 ⟨hL', hS⟩).trans inf_le_right) hne

theorem D1Sp62Data.barM_normal (h : D1Sp62Data P M H R V) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (barM M L).Normal := by
  constructor
  intro n hn g
  obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) g
  have heq := h.barM_map_conj_eq h84 h86 hD2 hB3 hb hL hm
  rw [barM_map_conj hm] at heq
  rw [← heq]
  exact ⟨n, hn, by simp [MulAut.conj_apply]⟩

end Normal

end CFSG.AGLEmbedding
