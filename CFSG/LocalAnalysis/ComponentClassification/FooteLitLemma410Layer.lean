module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitLift
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Sylow

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isPComponent_oddResidualIn_inf_centralizer {a x : G} {K : Subgroup G}
    (hK : IsTwoComponentAt a K) (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hnc : ∃ u v : K ⧸ pPrimeCore 2 K, u * v ≠ v * u) (hx2 : x ^ 2 = 1)
    (hxK : x ∈ coreActionKernel K) :
    oddResidualIn (K ⊓ centralizer ({x} : Set G)) ⊔ oddCoreIn K = K ∧
      IsPComponent 2 ((oddResidualIn (K ⊓ centralizer ({x} : Set G))).subgroupOf
        (K ⊓ centralizer ({x} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K ⊓ centralizer ({x} : Set G) with hY
  set K₀ := oddResidualIn Y with hK₀
  have hK₀Y : K₀ ≤ Y := oddResidualIn_le Y
  have hK₀K : K₀ ≤ K := hK₀Y.trans inf_le_left
  have hle := le_oddResidualIn_sup_oddCoreIn hK (isPGroup_two_zpowers_of_sq_eq_one hx2)
    (zpowers_le.mpr hxK)
  rw [centralizer_zpowers_eq] at hle
  have hsup : K₀ ⊔ oddCoreIn K = K := le_antisymm (sup_le hK₀K (map_subtype_le _)) hle
  refine ⟨hsup, ?_⟩
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₀ Y hK₀Y]
  refine ⟨?_, ?_, ?_⟩
  ·
    have hn : (K₀.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hK₀Y).mpr
      fun y hy => mem_normalizer_oddResidualIn (le_normalizer hy)
    exact hn.isSubnormal
  ·
    rw [eq_top_iff]
    have hgen : closure (((↑) : ↥K₀ → G) ⁻¹' {g : G | g ∈ Y ∧ ∃ k : ℕ, orderOf g = 2 ^ k}) =
        ⊤ := Subgroup.closure_closure_coe_preimage
    rw [← hgen, closure_le]
    rintro y ⟨-, k, hk⟩
    have hyp : IsPGroup 2 (zpowers y) := IsPGroup.of_card (n := k) (by
      rw [Nat.card_zpowers, ← hk, Subgroup.orderOf_coe])
    exact CatalogueBPrimeJoin.pSubgroup_le_residual 2 _ hyp (mem_zpowers y)
  ·
    obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hK₀K hsup
    have : IsSimpleGroup (K₀ ⧸ pPrimeCore 2 K₀) := e.isSimpleGroup
    obtain ⟨u, v, huv⟩ := hnc
    refine isQuasisimple_of_isSimpleGroup' ⟨e.symm u, e.symm v, fun h1 => huv ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, h1]

theorem Foote410Config.le_conjugate_of_mem_coreActionKernel
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G}
    (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G} (hc : Foote410Config M g E Q t)
    (htK : t ∉ footeK L t) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hxK : x ∈ coreActionKernel (footeK L t)) :
    oddResidualIn (footeK L t ⊓ centralizer ({x} : Set G)) ≤ conjugate M g ∧
      Q ⊓ footeK L t ≤ oddResidualIn (footeK L t ⊓ centralizer ({x} : Set G)) ∧
      oddResidualIn (footeK L t ⊓ centralizer ({x} : Set G)) ⊔ oddCoreIn (footeK L t) =
        footeK L t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht2, htC, hCt⟩ := hc.ht
  obtain ⟨-, -, hBs, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨hKB, -, -, hKpc, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  have hBen : Open.fusionIsBenderGroup (footeK L t ⧸ pPrimeCore 2 (footeK L t)) := by
    rcases htype with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact h1
    · exact absurd h1 htK
  set K := footeK L t with hK
  set M' := conjugate M g with hM'def
  have hM' : IsFooteM L M' := isFooteM_conjugate h hM g
  have hKt : K ≤ centralizer ({t} : Set G) := hKB.trans hBs
  have hKtc : IsTwoComponentAt t K := ⟨ht2, hKt, hKpc⟩
  have hsK : IsSimpleGroup (K ⧸ pPrimeCore 2 K) :=
    (AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hBen).simple
  obtain ⟨hsup, hK₀pc⟩ := isPComponent_oddResidualIn_inf_centralizer hKtc hsK
    (exists_mul_ne_of_fusionIsBenderGroup hBen) (hc.hE2 x hxE) hxK
  set K₀ := oddResidualIn (K ⊓ centralizer ({x} : Set G)) with hK₀
  obtain ⟨hK₀tx, hK₀pc'⟩ := TBLit.isPComponent_inf_centralizer hKt hKpc (oddResidualIn_le _)
    hK₀pc
  have htx : t ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hc.hEQ x hxE t hc.htQ).symm
  rw [inf_comm (centralizer ({t} : Set G))] at hK₀tx hK₀pc'
  obtain ⟨B, hBx, hBpc, hK₀B, -⟩ := foote_lemma_2_1_iv_subgroup htx ht2 hK₀tx hK₀pc'
  have hx2 : orderOf x = 2 := orderOf_eq_prime (hc.hE2 x hxE) hx1
  have hxC' : x ∈ coreActionKernel M' := hc.hEC hxE
  obtain ⟨-, -, hFmax, hFF⟩ := foote_lemma_4_5_i h hM' hx2 hxC'
  set F := footeF L x with hF
  have hFx : IsTwoComponentAt x F := hFmax.1
  have hEx : E ≤ centralizer ({x} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr (commute_of_sq_eq_one hc.hE2 he hxE)
  obtain ⟨hFM', hFsup⟩ := footeF_le_of_card_eight h hM' hx2 hxC' hc.hE2 hc.hE8
    (le_inf hc.hEC hEx)
  have hxN : centralizer ({x} : Set G) ≤ normalizer (F : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hFx hFF
  have htF : conjugate F t = F := conjugate_eq_of_mem_normalizer (hxN htx)
  have hQx : Q ≤ centralizer ({x} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.mpr (hc.hEQ x hxE q hq).symm
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hc.hQ8]; norm_num)
  have hVK₀ : Q ⊓ K ≤ K₀ := by
    intro v hv
    refine mem_oddResidualIn (mem_inf.mpr ⟨(mem_inf.mp hv).2, hQx (mem_inf.mp hv).1⟩) ?_
    obtain ⟨n, hn⟩ := hQp ⟨v, (mem_inf.mp hv).1⟩
    have h1 : orderOf v ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hn
      simpa using this)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨i, hi⟩
  refine ⟨?_, hVK₀, hsup⟩
  by_cases hBF : B = F
  · rw [hBF, htF, sup_idem] at hK₀B
    exact hK₀B.trans hFM'
  exfalso
  have hBF' : B ≤ coreActionKernel F :=
    GSThmB.B5a.le_coreActionKernel_of_ne hFx.2.1 hBx hFx.2.2 hBpc (Ne.symm hBF)
  have hBtx : conjugate B t ≤ centralizer ({x} : Set G) := conjugate_le_of_mem hBx htx
  have hBtpc : IsPComponent 2 ((conjugate B t).subgroupOf (centralizer ({x} : Set G))) :=
    isPComponent_conjugate_subgroupOf htx hBpc
  have hBtF : conjugate B t ≠ F := by
    intro h1
    apply hBF
    have h2 : conjugate (conjugate B t) t⁻¹ = conjugate F t⁻¹ := by rw [h1]
    rw [conjugate_conjugate_inv, conjugate_eq_of_mem_normalizer (hxN (inv_mem htx))] at h2
    exact h2
  have hBtF' : conjugate B t ≤ coreActionKernel F :=
    GSThmB.B5a.le_coreActionKernel_of_ne hFx.2.1 hBtx hFx.2.2 hBtpc (Ne.symm hBtF)
  have hVC' : Q ⊓ K ≤ coreActionKernel M' := fun v hv =>
    mem_coreActionKernel_of_sup hFM' hFsup (hc.hQN (mem_inf.mp hv).1)
      ((hK₀B.trans (sup_le hBF' hBtF')) (hVK₀ hv))
  have hVbot := hc.eq_bot (hQp.to_le inf_le_left)
    (le_inf (inf_le_left.trans hc.hQC) hVC')
  have hV4 := hc.card_inf_footeK h h47 hST hAsc h2An hM htK
  rw [hVbot, card_bot] at hV4
  omega

end CFSG.ComponentClassification.FooteLit
