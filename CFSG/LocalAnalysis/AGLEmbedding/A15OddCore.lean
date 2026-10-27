module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Defs
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section A15

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G} {c : Fin 3 → G}
  {σ τ : G}

theorem D1A15Data.pCore_five_eq_bot (h : D1A15Data P M H R c σ τ) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) : CFSG.pCore 5 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ := by
  have h3 := h.surv.ph3
  by_contra hO
  apply h3.pCorePreimage_not_le hO
  refine h.pcore _ (h3.pCorePreimage_le_inf h84 hD2)
    (inf_le_right.trans (le_normalizer_pCorePreimage 5 M)) ?_
  rintro _ ⟨m, hm, rfl⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 5) (G := ↥M ⧸ CFSG.pCore 2 ↥M)
    ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hm⟩
  refine ⟨k, ?_⟩
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m ^ 5 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  simpa using h3.twoCore_M_le_glbPrimeCore (coe_mem_pCoreOf_two_of_mk_eq_one _ hk')

theorem D1A15Data.le_centralizer_or_inf_eq_bot (h : D1A15Data P M H R c σ τ)
    (T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) [T.Normal] :
    barM M R ≤ Subgroup.centralizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      R ⊓ ((Subgroup.centralizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥ := by
  have h3 := h.surv.ph3
  set Cb := Subgroup.centralizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have : Cb.Normal := Subgroup.normal_centralizer
  set C : Subgroup G := (Cb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype with hC
  have hCM : M ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (normal_preimage_subgroupOf Cb)
  have hYn : H ⊓ M ≤ Subgroup.normalizer (((H ⊓ M) ⊓ C : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (inf_le_right.trans hCM)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rcases h.surv.normal_dichotomy _ inf_le_left hYn with hN | hRC
  · right
    have hRN : R ⊓ GLBPrimeCore 5 H = ⊥ :=
      inf_eq_bot_of_isPGroup (by norm_num) h3.isPGroup_R (glbPrimeCore_coprime 5 H)
    rw [eq_bot_iff, ← hRN]
    exact fun x hx => ⟨hx.1, hN ⟨h3.le_inf hx.1, hx.2⟩⟩
  · left
    rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
    obtain ⟨m, hm, hmr⟩ := (hRC.trans inf_le_right) (Subgroup.mem_subgroupOf.mp hr)
    rwa [show m = ⟨r, hrM⟩ from Subtype.ext hmr] at hm

theorem D1A15Data.isElemAbelian_barM (h : D1A15Data P M H R c σ τ) :
    IsElemAbelian 5 (barM M R) :=
  isElemAbelian_barM_of_isElemAbelian h.elem

theorem D1A15Data.card_barM (h : D1A15Data P M H R c σ τ) : Nat.card (barM M R) = 5 ^ 3 := by
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have hRM : R ≤ M := h.surv.ph3.le_M
  have hO2 : (5 : ℕ).Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hRsub : IsPGroup 5 (R.subgroupOf M) := by
    intro z
    have hz : ((z : M) : G) ^ 5 = 1 := h.elem.2 _ (Subgroup.mem_subgroupOf.mp z.2)
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hz))⟩
  rw [barM, card_map_mk_of_isPGroup (by norm_num) _ hO2 hRsub,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, h.card_R]

theorem D1A15Data.closure_barM (h : D1A15Data P M H R c σ τ) :
    Subgroup.closure (Set.range fun i => QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      ⟨c i, h.surv.ph3.le_M (h.c_mem i)⟩) = barM M R := by
  have hR : R.subgroupOf M =
      Subgroup.closure (Set.range fun i => (⟨c i, h.surv.ph3.le_M (h.c_mem i)⟩ : M)) := by
    refine Subgroup.map_injective M.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le h.surv.ph3.le_M, MonoidHom.map_closure,
      ← Set.range_comp]
    exact h.closure_eq.symm
  rw [barM, hR, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem D1A15Data.le_centralizer_pCore (h : D1A15Data P M H R c σ τ) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hs5 : s ≠ 5) :
    barM M R ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
  have h3 := h.surv.ph3
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  refine (h.le_centralizer_or_inf_eq_bot Sg).resolve_right fun hRC => ?_
  have hfaith : barM M R ⊓ Subgroup.centralizer (Sg : Set _) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨⟨r, hrM⟩, hr, rfl⟩, hrC⟩
    have hr1 : r ∈ R ⊓ ((Subgroup.centralizer (Sg : Set _)).comap mk).map M.subtype :=
      ⟨Subgroup.mem_subgroupOf.mp hr, ⟨r, hrM⟩, hrC, rfl⟩
    rw [hRC, Subgroup.mem_bot] at hr1
    have h1 : (⟨r, hrM⟩ : M) = 1 := Subtype.ext hr1
    rw [h1, map_one]
    exact Subgroup.one_mem _
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hσ : ∀ i : Fin 3, mk ⟨σ, h.σ_mem.2⟩ * mk ⟨c i, h3.le_M (h.c_mem i)⟩ *
      (mk ⟨σ, h.σ_mem.2⟩)⁻¹ = mk ⟨c (i + 1), h3.le_M (h.c_mem (i + 1))⟩ := fun i => by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext (h.σ_conj i))
  have hτ : mk ⟨τ, h.τ_mem.2⟩ * mk ⟨c 0, h3.le_M (h.c_mem 0)⟩ * (mk ⟨τ, h.τ_mem.2⟩)⁻¹ =
        mk ⟨c 0, h3.le_M (h.c_mem 0)⟩ ^ 2 ∧
      mk ⟨τ, h.τ_mem.2⟩ * mk ⟨c 1, h3.le_M (h.c_mem 1)⟩ * (mk ⟨τ, h.τ_mem.2⟩)⁻¹ =
        mk ⟨c 1, h3.le_M (h.c_mem 1)⟩ ∧
      mk ⟨τ, h.τ_mem.2⟩ * mk ⟨c 2, h3.le_M (h.c_mem 2)⟩ * (mk ⟨τ, h.τ_mem.2⟩)⁻¹ =
        mk ⟨c 2, h3.le_M (h.c_mem 2)⟩ ^ 2 := by
    simp only [← map_inv, ← map_mul, ← map_pow]
    refine ⟨congrArg mk (Subtype.ext ?_), congrArg mk (Subtype.ext ?_),
      congrArg mk (Subtype.ext ?_)⟩
    · simpa using h.τ_conj.1
    · simpa using h.τ_conj.2.1
    · simpa using h.τ_conj.2.2
  have h4 : 4 ≤ Open.pRank s Sg :=
    four_le_pRank_of_monomial hs hs2 hs5 (fun i => mk ⟨c i, h3.le_M (h.c_mem i)⟩)
      CFSG.pCore_isPGroup h.isElemAbelian_barM h.closure_barM h.card_barM (le_top.trans hSgN)
      (hSgN (Subgroup.mem_top _)) hσ (hSgN (Subgroup.mem_top _)) hτ hfaith
  set Sh : Subgroup G := (Sg.comap mk).map M.subtype with hSh
  have h4' : 4 ≤ Open.pRank s Sh := by
    have h1 := pRank_barM_le hs hs2 M Sh (Subgroup.map_subtype_le _)
    rw [barM_preimage] at h1
    exact h4.trans h1
  have hShK : Sh ≤ H ⊓ M := h3.preimage_le_inf (h3.le_barM_inf_of_le_centralizer
    ((pCore_le_pPrimeCore_two hs hs2).trans (h3.oddCore_le_centralizer h84 hD2)))
  have hShn : H ⊓ M ≤ Subgroup.normalizer (Sh : Set G) :=
    inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf Sg))
  have hShN : Sh ≤ GLBPrimeCore 5 H := by
    refine (h.surv.normal_dichotomy Sh hShK hShn).resolve_right fun hRSh => ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := s) (G := ↥M ⧸ CFSG.pCore 2 ↥M))
    have hdvd := Subgroup.card_dvd_of_le (barM_le_of_le_preimage hRSh)
    rw [h.card_barM, hk] at hdvd
    have h5 : 5 ∣ s ^ k := (dvd_pow_self 5 (by norm_num)).trans hdvd
    exact hs5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hs).mp
      ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5)).symm
  exact h3.false_of_preimage_le hs hs2
    (mem_glbBetaFour_of_le_pRank hs hs2 h3.maxTwoLocal_M.1 (Subgroup.map_subtype_le _) h4')
    CFSG.pCore_isPGroup ((by norm_num : 3 ≤ 4).trans h4') (glbPrimeCore_le 5 H)
    (le_normalizer_glbPrimeCore 5 H) h3.primeCore_le hShN

theorem D1A15Data.eq_one_of_forall_mem_centralizer (h : D1A15Data P M H R c σ τ)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) {r : G} (hr : r ∈ R)
    (hc : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, h.surv.ph3.le_M hr⟩ ∈
        Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : r = 1 := by
  have h3 := h.surv.ph3
  have hrM : r ∈ M := h3.le_M hr
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set A := Subgroup.zpowers (mk ⟨r, hrM⟩) with hA
  have hr5 : (⟨r, hrM⟩ : M) ^ 5 = 1 := Subtype.ext (by simpa using h.elem.2 r hr)
  have hAp : IsPGroup 5 A :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, ← map_pow, hr5, map_one])
  have hAle : A ≤ CFSG.pCore 5 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_pCore_of_le_centralizer_components hAp (fun Lb hLb => ?_) fun l hl => ?_
    · exact (Subgroup.zpowers_le).mpr (hc Lb hLb)
    · by_cases hl2 : l = 2
      · rw [hl2, pCore_quotient_pCore_eq_bot']
        exact Subgroup.le_centralizer_iff.mp bot_le
      by_cases hl5 : l = 5
      · rw [hl5, h.pCore_five_eq_bot h84 hD2]
        exact Subgroup.le_centralizer_iff.mp bot_le
      refine (Subgroup.zpowers_le).mpr ?_
      exact h.le_centralizer_pCore h84 hD2 hl hl2 hl5
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr))
  rw [h.pCore_five_eq_bot h84 hD2, le_bot_iff, hA, Subgroup.zpowers_eq_bot] at hAle
  have hrQ : r ∈ pCoreOf 2 M := by simpa using coe_mem_pCoreOf_two_of_mk_eq_one _ hAle
  have hRQ : R ⊓ pCoreOf 2 M = ⊥ := inf_eq_bot_of_isPGroup (by norm_num) h3.isPGroup_R (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num))
  have hmem : r ∈ R ⊓ pCoreOf 2 M := ⟨hr, hrQ⟩
  rwa [hRQ, Subgroup.mem_bot] at hmem

end A15

end CFSG.AGLEmbedding
