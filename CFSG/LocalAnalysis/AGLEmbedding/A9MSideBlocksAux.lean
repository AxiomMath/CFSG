module

public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Blocks

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.not_injective_blocks {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hrank : Open.pRank 3 (H ⊓ M) ≤ 3) (hB3 : StmtBlockThree)
    (L : Fin 4 → Subgroup G) (hL : ∀ i, IsWeakSBlock M (pCoreOf 2 H) (L i)) :
    ¬ Function.Injective L := by
  intro hinj
  have h1 := h.toD1Escape.toTwoLocalPair.card_le_pRank_three_of_blocks (fun _ hL' => hB3 h hL') L
    hL hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  omega

theorem D1PhaseThree.eq_or_eq_or_eq_of_isWeakSBlock {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hrank : Open.pRank 3 (H ⊓ M) ≤ 3) (hB3 : StmtBlockThree)
    {L₀ L₁ L₂ L : Subgroup G} (h₀ : IsWeakSBlock M (pCoreOf 2 H) L₀)
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (h01 : L₀ ≠ L₁) (h02 : L₀ ≠ L₂) (h12 : L₁ ≠ L₂) :
    L = L₀ ∨ L = L₁ ∨ L = L₂ := by
  by_contra hne
  push Not at hne
  obtain ⟨hn0, hn1, hn2⟩ := hne
  refine h.not_injective_blocks hrank hB3 ![L₀, L₁, L₂, L] (fun i => ?_) ?_
  · fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

omit [Finite G] in
theorem mem_normalizer_blockCentralizer {M L : Subgroup G} {t : G} (htM : t ∈ M)
    (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    t ∈ Subgroup.normalizer (blockCentralizer M L : Set G) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Cb := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hL' : L.map (MulAut.conj t).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
  have hLbar : (barM M L).map (MulAut.conj (mk ⟨t, htM⟩)).toMonoidHom = barM M L := by
    rw [← barM_map_conj htM, hL']
  have hNC : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have htN : mk ⟨t, htM⟩ ∈ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hNC (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLbar)
  have key : ∀ (g : M), mk g ∈ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ∀ c ∈ blockCentralizer M L, (g : G) * c * (g : G)⁻¹ ∈ blockCentralizer M L := by
    rintro g hg _ ⟨m, hm, rfl⟩
    refine ⟨g * m * g⁻¹, ?_, by simp⟩
    show mk (g * m * g⁻¹) ∈ Cb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key ⟨t, htM⟩ htN c, fun hc => ?_⟩
  have h1 := key (⟨t, htM⟩)⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ htN) _ hc
  simpa [mul_assoc] using h1

theorem blockClosure_le_sup_blockCentralizer {M K L : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) : blockClosure M K L ≤ L ⊔ blockCentralizer M L := by
  refine sup_le (fun q hq => Subgroup.mem_sup_right ?_) (iSup₂_le fun k hk => ?_)
  · have hqM : q ∈ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hq
    refine (mem_blockCentralizer_iff ⟨q, hqM⟩).mpr ?_
    rw [(mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq]
    exact Subgroup.one_mem _
  · have hLk := hL.map_conj (hKM hk)
    by_cases he : barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L
    · rw [hLk.eq_of_barM_eq hL he]
      exact le_sup_left
    · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLk.component
        hL.component he
      have hC := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
      intro x hx
      have hxM : x ∈ M := hLk.le hx
      exact Subgroup.mem_sup_right ((mem_blockCentralizer_iff ⟨x, hxM⟩).mpr
        (hC (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))))

theorem barM_blockClosure_le_centralizer {M K L : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) {C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hC : IsComponentOf C ⊤) (hne : ∀ k ∈ K, barM M (L.map (MulAut.conj k).toMonoidHom) ≠ C) :
    barM M (blockClosure M K L) ≤ Subgroup.centralizer (C : Set _) := by
  refine barM_le_of_le_preimage (blockClosure_le_preimage hKM hL fun k hk => ?_)
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    (hL.map_conj (hKM hk)).component hC (hne k hk)
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc

theorem blockClosure_le_normalizer {M K L L' : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) (hL' : IsTwoPrimeComponent M L') :
    blockClosure M K L ≤ Subgroup.normalizer (L' : Set G) := by
  have hpre := blockClosure_le_preimage hKM hL
    (T := Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M))) fun k hk y hy => by
      by_cases he : barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L'
      · rw [he] at hy
        exact Subgroup.le_normalizer hy
      · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
          (hL.map_conj (hKM hk)).component hL'.component he
        exact Subgroup.centralizer_le_normalizer _
          ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hy)
  exact hL'.le_normalizer (barM_le_of_le_preimage hpre) (hpre.trans (Subgroup.map_subtype_le _))

omit [Finite G] in
theorem conj_mem_blockCentralizer {M L : Subgroup G} {g w : G} (hgM : g ∈ M)
    (hw : w ∈ blockCentralizer M (L.map (MulAut.conj g⁻¹).toMonoidHom)) :
    g * w * g⁻¹ ∈ blockCentralizer M L := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  obtain ⟨⟨w, hwM⟩, hw', rfl⟩ := hw
  have hm : mk ⟨w, hwM⟩ ∈ Subgroup.centralizer
      ((barM M L).map (MulAut.conj (mk ⟨g⁻¹, M.inv_mem hgM⟩)).toMonoidHom : Set _) := by
    rw [← barM_map_conj (M.inv_mem hgM)]
    exact hw'
  refine (mem_blockCentralizer_iff (⟨g, hgM⟩ * ⟨w, hwM⟩ * (⟨g, hgM⟩)⁻¹)).mpr ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : (mk ⟨g, hgM⟩)⁻¹ * y * mk ⟨g, hgM⟩ ∈ (barM M L).map
      (MulAut.conj (mk ⟨g⁻¹, M.inv_mem hgM⟩)).toMonoidHom := by
    refine ⟨y, hy, ?_⟩
    have e : (⟨g⁻¹, M.inv_mem hgM⟩ : M) = (⟨g, hgM⟩ : M)⁻¹ := rfl
    simp only [MulEquiv.coe_toMonoidHom, e, map_inv]
    rw [MulAut.conj_inv_apply]
  have hc := Subgroup.mem_centralizer_iff.mp hm _ hy'
  rw [map_mul, map_mul, map_inv]
  calc y * (mk ⟨g, hgM⟩ * mk ⟨w, hwM⟩ * (mk ⟨g, hgM⟩)⁻¹)
      = mk ⟨g, hgM⟩ * (((mk ⟨g, hgM⟩)⁻¹ * y * mk ⟨g, hgM⟩) * mk ⟨w, hwM⟩) *
          (mk ⟨g, hgM⟩)⁻¹ := by group
    _ = mk ⟨g, hgM⟩ * (mk ⟨w, hwM⟩ * ((mk ⟨g, hgM⟩)⁻¹ * y * mk ⟨g, hgM⟩)) *
          (mk ⟨g, hgM⟩)⁻¹ := by rw [hc]
    _ = mk ⟨g, hgM⟩ * mk ⟨w, hwM⟩ * (mk ⟨g, hgM⟩)⁻¹ * y := by group

end Blocks

section Survivor

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G}

theorem D1SurvivorData.le_normalizer_block (h : D1SurvivorData 3 P M H R X)
    (hB3 : StmtBlockThree) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    X ≤ Subgroup.normalizer (L : Set G) :=
  (h.le_blockClosure rfl hL (hB3 h.ph3 hL)).trans
    (blockClosure_le_normalizer inf_le_right hL.toIsTwoPrimeComponent hL.toIsTwoPrimeComponent)

theorem D1SurvivorData.le_sup_blockCentralizer (h : D1SurvivorData 3 P M H R X)
    (hB3 : StmtBlockThree) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    X ≤ L ⊔ blockCentralizer M L :=
  (h.le_blockClosure rfl hL (hB3 h.ph3 hL)).trans
    (blockClosure_le_sup_blockCentralizer inf_le_right hL.toIsTwoPrimeComponent)

theorem D1SurvivorData.eq_bot_of_forall_centralizer (h : D1SurvivorData 3 P M H R X)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {A : Subgroup G} (hAX : A ≤ X)
    (hAC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : A = ⊥ := by
  have hAR : A ≤ R := hAX.trans h.le_R
  have hA3 : IsPGroup 3 A := h.ph3.isPGroup_R.to_le hAR
  have hle := h.ph3.barM_le_pCore_of_forall_centralizer h84 hD2 hB3 rfl hAR
    (fun Y hY hYn => (h.normal_dichotomy Y hY hYn).imp id hAX.trans) hAC
  rw [hO] at hle
  have hAQ : A ⊓ pCoreOf 2 M = ⊥ := inf_eq_bot_of_isPGroup Nat.prime_three hA3 (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num))
  rw [eq_bot_iff]
  intro a ha
  have haM : a ∈ M := h.ph3.le_M (hAR ha)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩ = 1 :=
    Subgroup.mem_bot.mp (hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)))
  have hmem : a ∈ A ⊓ pCoreOf 2 M := ⟨ha, coe_mem_pCoreOf_two_of_mk_eq_one _ h1⟩
  rwa [hAQ] at hmem

theorem D1SurvivorData.eq_one_of_forall_mem (h : D1SurvivorData 3 P M H R X)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {x : G} (hx : x ∈ X)
    (hxC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → x ∈ blockCentralizer M L) :
    x = 1 := by
  have hC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M (Subgroup.zpowers x) ≤ Subgroup.centralizer (barM M L : Set _) := by
    rintro L hL _ ⟨⟨a, haM⟩, ha, rfl⟩
    exact (mem_blockCentralizer_iff ⟨a, haM⟩).mp
      ((Subgroup.zpowers_le).mpr (hxC L hL) (Subgroup.mem_subgroupOf.mp ha))
  have hbot := h.eq_bot_of_forall_centralizer h84 hD2 hB3 hO ((Subgroup.zpowers_le).mpr hx) hC
  have hmem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  rwa [hbot, Subgroup.mem_bot] at hmem

theorem D1SurvivorData.faithful (h : D1SurvivorData 3 P M H R X) (hZ : centerOf R ≤ X)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {r : G} (hr : r ∈ R)
    (hrC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → r ∈ blockCentralizer M L) :
    r = 1 := by
  have h3 := h.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hRM : R ≤ M := h3.le_M
  set W : Subgroup G := R ⊓ ⨅ (L : Subgroup G) (_ : IsWeakSBlock M (pCoreOf 2 H) L),
    blockCentralizer M L with hWdef
  have hmemW : ∀ w, w ∈ W ↔ w ∈ R ∧ ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      w ∈ blockCentralizer M L := by
    intro w
    simp only [hWdef, Subgroup.mem_inf, Subgroup.mem_iInf]
  have key : ∀ g ∈ R, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    rw [hmemW] at hw ⊢
    refine ⟨R.mul_mem (R.mul_mem hg hw.1) (R.inv_mem hg), fun L hL => ?_⟩
    have hgK : g⁻¹ ∈ H ⊓ M := h3.le_inf (R.inv_mem hg)
    exact conj_mem_blockCentralizer (hRM hg) (hw.2 _ (hL.map_conj hgK.2 (hKeq ▸ hgK).2))
  have hWn : R ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun w => ⟨key g hg w, fun hw => by
      simpa [mul_assoc] using key g⁻¹ (R.inv_mem hg) _ hw⟩
  by_contra hr1
  have hWR : W ≤ R := inf_le_left
  have : Group.IsNilpotent ↥R := h3.isPGroup_R.isNilpotent
  have hWn' : (W.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hWn
  have hW1 : W.subgroupOf R ≠ ⊥ := by
    intro hbot
    have hmem : (⟨r, hr⟩ : R) ∈ W.subgroupOf R :=
      Subgroup.mem_subgroupOf.mpr ((hmemW r).mpr ⟨hr, hrC⟩)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hr1 (congrArg Subtype.val hmem)
  obtain ⟨⟨y, hyW, hyZ⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hW1)
  have hyX : (y : G) ∈ X := hZ ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨g, hg⟩)⟩
  exact hy1 (Subtype.ext (Subtype.ext (h.eq_one_of_forall_mem h84 hD2 hB3 hO hyX
    ((hmemW _).mp (Subgroup.mem_subgroupOf.mp hyW)).2)))

theorem D1SurvivorData.exists_map_conj_eq (h : D1SurvivorData 3 P M H R X)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L L' : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hL' : IsWeakSBlock M (pCoreOf 2 H) L') :
    ∃ k ∈ H ⊓ M, L.map (MulAut.conj k).toMonoidHom = L' := by
  by_contra hne
  push Not at hne
  have hKM : H ⊓ M ≤ M := inf_le_right
  have hXL := h.le_blockClosure rfl hL (hB3 h.ph3 hL)
  have hXL' := h.le_blockClosure rfl hL' (hB3 h.ph3 hL')
  refine h.ne_bot (h.eq_bot_of_forall_centralizer h84 hD2 hB3 hO le_rfl fun L'' hL'' => ?_)
  by_cases hex : ∃ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L''
  · obtain ⟨k, hk, he⟩ := hex
    refine (barM_mono hXL').trans (barM_blockClosure_le_centralizer hKM
      hL'.toIsTwoPrimeComponent hL''.component fun k' hk' he' => ?_)
    have e1 : L'.map (MulAut.conj k').toMonoidHom = L.map (MulAut.conj k).toMonoidHom :=
      (hL'.toIsTwoPrimeComponent.map_conj (hKM hk')).eq_of_barM_eq
        (hL.toIsTwoPrimeComponent.map_conj (hKM hk)) (he'.trans he.symm)
    refine hne (k'⁻¹ * k) ((H ⊓ M).mul_mem ((H ⊓ M).inv_mem hk') hk) ?_
    rw [map_conj_mul_eq, ← e1, ← map_conj_mul_eq, inv_mul_cancel]
    ext g
    simp
  · push Not at hex
    exact (barM_mono hXL).trans (barM_blockClosure_le_centralizer hKM
      hL.toIsTwoPrimeComponent hL''.component hex)

end Survivor

end CFSG.AGLEmbedding
