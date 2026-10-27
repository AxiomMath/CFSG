module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitComponentReduction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

@[expose] def FooteSolomonFamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ A ∈ footeFamilyOf L, A ∈ solomonKStar G

variable {G : Type} [Group G] [Finite G]

theorem succ_le_open_pRank_of_commute {p : ℕ} (hp : p.Prime) {E H : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) {r : ℕ} (hEcard : Nat.card E = p ^ r) {b : G}
    (hbc : ∀ e ∈ E, Commute e b) (hbp : b ^ p = 1) (hbE : b ∉ E) (hEH : E ≤ H)
    (hbH : b ∈ H) : r + 1 ≤ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := fun h => hbE (h ▸ one_mem E)
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcomm : ∀ (e : E) (c : zpowers b), Commute (E.subtype e) ((zpowers b).subtype c) := by
    rintro e ⟨c, k, rfl⟩
    exact (hbc e e.2).zpow_right k
  let f : E × zpowers b →* G := MonoidHom.noncommCoprod E.subtype (zpowers b).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨e, c⟩ hx
    have hx' : (e : G) * c = 1 := hx
    have hcE : (c : G) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hx']
      exact inv_mem e.2
    have hc1 : c = 1 := by
      by_contra hc
      have htop := zpowers_eq_top_of_prime_card (G := zpowers b)
        (by rw [Nat.card_zpowers, hbord]) hc
      have hbmem : (⟨b, mem_zpowers b⟩ : zpowers b) ∈ zpowers c := htop ▸ mem_top _
      obtain ⟨m, hm⟩ := hbmem
      apply hbE
      have : (c : G) ^ m = b := congrArg Subtype.val hm
      rw [← this]
      exact zpow_mem hcE m
    rw [hc1, OneMemClass.coe_one, mul_one] at hx'
    have he1 : e = 1 := Subtype.ext hx'
    rw [he1, hc1]
    rfl
  have hEc := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E × zpowers b) ?_ ?_ ?_ f hf ?_
  · rintro ⟨e₁, c₁⟩ ⟨e₂, c₂⟩
    refine Prod.ext (mul_comm' e₁ e₂) ?_
    obtain ⟨c₁, k₁, rfl⟩ := c₁
    obtain ⟨c₂, k₂, rfl⟩ := c₂
    exact Subtype.ext (Commute.zpow_zpow_self b k₁ k₂).eq
  · rintro ⟨e, c⟩
    refine Prod.ext (Subtype.ext (hE.2 e e.2)) ?_
    obtain ⟨c, k, rfl⟩ := c
    apply Subtype.ext
    change (b ^ k) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  · rw [Nat.card_prod, hEcard, Nat.card_zpowers, hbord, pow_succ]
  · rintro _ ⟨⟨e, c⟩, rfl⟩
    obtain ⟨c, k, rfl⟩ := c
    exact H.mul_mem (hEH e.2) (zpow_mem hbH k)

theorem coreActionKernel_top_eq_bot [IsSimpleGroup G] (hna : ∃ g h : G, g * h ≠ h * g)
    {x : G} (hx : orderOf x = 2) : coreActionKernel (⊤ : Subgroup G) = ⊥ := by
  have : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hx' : orderOf (⟨x, mem_top x⟩ : ↥(⊤ : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hx
  have hO : pPrimeCore 2 ↥(⊤ : Subgroup G) = ⊥ := pPrimeCore_two_eq_bot_of_isSimpleGroup hx'
  have hZ : center G = ⊥ := center_eq_bot_of_isSimpleGroup hna
  rw [eq_bot_iff]
  intro g hg
  have hgZ : g ∈ center G := by
    rw [mem_center_iff]
    intro y
    have h1 := hg.2 y (mem_top y)
    rw [hO, Subgroup.map_bot, mem_bot] at h1
    calc y * g = g * y * (y⁻¹ * g⁻¹ * y * g) := by group
      _ = g * y := by rw [h1, mul_one]
  rw [hZ] at hgZ
  exact hgZ

theorem eq_top_of_isTwoComponentIn_top [IsSimpleGroup G] (hna : ∃ g h : G, g * h ≠ h * g)
    {J : Subgroup G} (hJ : IsTwoComponentIn J ⊤) : J = ⊤ := by
  have hJ' : IsPComponent 2 J := isPComponent_subgroupOf_top_iff'.mp hJ.2
  have hsub : J.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := id hJ'
    exact h
  have hGq := LocalCores.isQuasisimple_of_isSimpleGroup hna
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hGq.1 hsub with h | h
  · exact h
  · exfalso
    rw [center_eq_bot_of_isSimpleGroup hna, le_bot_iff] at h
    exact ne_bot_of_isPComponent hJ' h

theorem solomonKStarOf_top_eq_bot [IsSimpleGroup G] (hna : ∃ g h : G, g * h ≠ h * g)
    {x : G} (hx : orderOf x = 2) : solomonKStarOf (⊤ : Subgroup G) = ⊥ := by
  apply le_antisymm _ bot_le
  refine iSup₂_le fun J hJ => ?_
  exfalso
  obtain ⟨hJ2, ⟨⟨-, T, hT, -, hTC, -⟩, -⟩, -⟩ := hJ
  rw [eq_top_of_isTwoComponentIn_top hna hJ2, coreActionKernel_top_eq_bot hna hx,
    le_bot_iff] at hTC
  exact hT hTC

theorem oddCoreIn_le_of_isTwoComponentIn {J N : Subgroup G} (hJ : IsTwoComponentIn J N) :
    oddCoreIn J ≤ oddCoreIn N := by
  have hsub : (J.subgroupOf N).IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := id hJ.2
    exact h
  have h1 := map_mono (f := N.subtype) (Walter.map_pPrimeCore_le_of_isSubnormal hsub)
  have h2 := GSThmB.B5a.map_oddCoreIn_subgroupOf N J
  rw [inf_of_le_right hJ.1] at h2
  rw [h2] at h1
  exact h1

theorem commutator_le_oddCoreIn_of_ne {J₁ J₂ N : Subgroup G} (h₁ : IsTwoComponentIn J₁ N)
    (h₂ : IsTwoComponentIn J₂ N) (hne : J₁ ≠ J₂) : ⁅J₁, J₂⁆ ≤ oddCoreIn N := by
  have hle : J₂ ≤ coreActionKernel J₁ :=
    GSThmB.B5a.le_coreActionKernel_of_ne h₁.1 h₂.1 h₁.2 h₂.2 hne
  refine (commutator_le.mpr fun y hy x hx => ?_).trans (oddCoreIn_le_of_isTwoComponentIn h₁)
  have h := (hle (inv_mem hx)).2 _ (inv_mem hy)
  rwa [inv_inv, inv_inv, ← commutatorElement_def] at h

omit [Finite G] in
theorem mem_oddTwoCoreIn_of_central {N : Subgroup G} {a : G} (haN : a ∈ N)
    (hcent : ∀ n ∈ N, n * a = a * n) (ha : orderOf a = 2) : a ∈ oddTwoCoreIn N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a' : N := ⟨a, haN⟩ with ha'
  refine ⟨a', ?_, rfl⟩
  rw [SetLike.mem_coe, mem_comap]
  set q := QuotientGroup.mk' (pPrimeCore 2 ↥N) a' with hq
  have hqc : ∀ g, g * q = q * g := by
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [hq, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcent g' g'.2)
  have hnorm : (zpowers q).Normal := ⟨fun x hx g => by
    rw [show g * x * g⁻¹ = x by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      rw [show g * q ^ k = q ^ k * g from ((Commute.zpow_right (show Commute g q from hqc g) k)).eq]
      group]
    exact hx⟩
  have hdvd : orderOf q ∣ 2 := by
    rw [hq, ← ha, ← Subgroup.orderOf_mk a haN]
    exact orderOf_map_dvd _ _
  have hdvd' : orderOf q ∣ 2 ^ 1 := by rwa [pow_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  have hp : IsPGroup 2 (zpowers q) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  exact le_sSup (show zpowers q ∈ {H : Subgroup _ | H.Normal ∧ IsPGroup 2 H} from ⟨hnorm, hp⟩)
    (mem_zpowers q)

omit [Finite G] in
theorem le_twoLayerIn_of_isTwoComponentIn {J N : Subgroup G} (hJ : IsTwoComponentIn J N) :
    J ≤ twoLayerIn N := by
  rw [← map_subgroupOf_eq_of_le hJ.1]
  exact map_mono (le_sSup hJ.2)

theorem foote_theorem_3_3_of_local
    (hSol : ∀ N : Subgroup G, IsKBalanced N → solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G))
    (hM3 : FooteSolomonFamilyInput)
    (hβ : ∀ B : Subgroup G, (∃ b : G, IsTwoComponentAt b B) → FooteFamilyType B →
      Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2)
    {t : G} {L : Subgroup G} (hmin : FooteMinimal G) (hce : FooteCounterexample G t L)
    [IsSimpleGroup G] (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) {a : G}
    {K M : Subgroup G} (hK : IsTwoComponentAt a K) (hM : IsTwoComponentAt a M)
    (hKF : K ∈ footeFamilyOf L) (hMF : M ∈ footeFamilyOf L) : K = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hS := hM3 G t L hmin hce ‹_› hrank2
  have ha := hK.1
  set N := centralizer ({a} : Set G) with hN
  have hna : ∃ g h : G, g * h ≠ h * g := by
    obtain ⟨⟨-, -, ⟨-, hLt, hLpc⟩, -, -, -⟩, -⟩ := hce
    obtain ⟨u, v, huv⟩ :=
      exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hLt hLpc)
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨u', v', fun h => huv ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      show u' * v' = v' * u' from Subtype.ext h]
  have hKN : IsTwoComponentIn K N := ⟨hK.2.1, hK.2.2⟩
  have hMN : IsTwoComponentIn M N := ⟨hM.2.1, hM.2.2⟩
  have hLfam : FooteFamilyType L := hce.1.2.2.2.2.1
  obtain ⟨-, ⟨eML⟩⟩ := id hMF
  have hMfam : FooteFamilyType M := footeFamilyType_of_equiv eML hLfam
  have hMq := isQuasisimple_quotient_of_isPComponent hM.2.1 hM.2.2
  have hZM : center (M ⧸ pPrimeCore 2 M) = ⊥ := by
    by_contra hZ
    have h1 := pRank_le_one_of_center_ne_bot hMq hMfam (hβ M ⟨a, hM⟩ hMfam) hZ
    rw [hrank2 M hMF] at h1
    omega
  have haM : a ∉ M := fun haM => center_ne_bot_of_mem_coreActionKernel haM ha
    (GSLit.mem_coreActionKernel_of_le_centralizer hM.2.1) hZM
  have haN : a ∈ N := mem_centralizer_singleton_iff.mpr rfl
  have hcent : ∀ n ∈ N, n * a = a * n := fun n hn => mem_centralizer_singleton_iff.mp hn
  have haO : a ∈ oddTwoCoreIn N := mem_oddTwoCoreIn_of_central haN hcent ha
  set S : Set (Subgroup G) := {J | IsTwoComponentIn J N ∧ J ∈ solomonKStar G} with hSdef
  have hSfin : S.Finite := Set.toFinite S
  set s := hSfin.toFinset with hs
  have hKs : K ∈ s := hSfin.mem_toFinset.mpr ⟨hKN, hS K hKF⟩
  have hMs : M ∈ s := hSfin.mem_toFinset.mpr ⟨hMN, hS M hMF⟩
  have hr : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨K, hKs, M, hMs, hne⟩
  set e := s.equivFin.symm with he
  set Kf : Fin s.card → Subgroup G := fun i => ((e i : s) : Subgroup G) with hKf
  have hKfS : ∀ i, Kf i ∈ S := fun i => hSfin.mem_toFinset.mp (e i).2
  have hbal : IsKBalanced N := by
    refine ⟨s.card, Kf, fun i j hij => e.injective (Subtype.ext hij), fun J => ⟨fun hJ => ?_,
      ?_⟩, hr, fun i j hij => ?_, ?_, ?_⟩
    · refine ⟨e.symm ⟨J, hSfin.mem_toFinset.mpr hJ⟩, ?_⟩
      simp only [hKf, Equiv.apply_symm_apply]
    · rintro ⟨i, rfl⟩
      exact hKfS i
    · exact commutator_le_oddCoreIn_of_ne (hKfS i).1 (hKfS j).1
        (fun h => hij (e.injective (Subtype.ext h)))
    ·
      refine ⟨e.symm ⟨K, hKs⟩, ?_⟩
      have hKi : Kf (e.symm ⟨K, hKs⟩) = K := by simp only [hKf, Equiv.apply_symm_apply]
      rw [hKi]
      set X := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K with hX
      have hrM : CFSG.Open.pRank 2 M = 2 := by
        have h := hrank2 M hMF
        rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h
      obtain ⟨E, hEM, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two M
      rw [hrM] at hEcard
      have hMK : M ≤ coreActionKernel K :=
        GSThmB.B5a.le_coreActionKernel_of_ne hK.2.1 hM.2.1 hK.2.2 hM.2.2 hne
      have hEX : E ≤ X := le_inf
        (hEM.trans ((le_twoLayerIn_of_isTwoComponentIn hMN).trans le_sup_right))
        (hEM.trans hMK)
      have haX : a ∈ X :=
        mem_inf.mpr ⟨mem_sup_left haO, GSLit.mem_coreActionKernel_of_le_centralizer hK.2.1⟩
      have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
      have h3 := succ_le_open_pRank_of_commute Nat.prime_two hE hEcard
        (fun x hx => hcent x (hM.2.1 (hEM hx))) ha2 (fun h => haM (hEM h)) hEX haX
      rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
      exact h3
    ·
      right; left
      have hKN' : solomonKStarOf N ≤ N := iSup₂_le fun J hJ => hJ.1.1
      have haY : a ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N) :=
        mem_inf.mpr ⟨mem_sup_left haO, GSLit.mem_coreActionKernel_of_le_centralizer hKN'⟩
      exact FooteLit.one_le_pRank_of_orderOf_eq_two (g := ⟨a, haY⟩)
        (by rw [Subgroup.orderOf_mk]; exact ha)
  have hle := hSol N hbal
  rw [solomonKStarOf_top_eq_bot hna ha] at hle
  have hKle : K ≤ solomonKStarOf N := le_iSup₂_of_le K ⟨hKN, hS K hKF⟩ le_rfl
  apply ne_bot_of_isPComponent hK.2.2
  rw [le_bot_iff.mp (hKle.trans hle)]
  exact Subgroup.bot_subgroupOf _

theorem foote_theorem_3_3 (hSol : SolomonThm13Input) (hM3 : FooteSolomonFamilyInput)
    (hβ : ∀ B : Subgroup G, (∃ b : G, IsTwoComponentAt b B) → FooteFamilyType B →
      Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2)
    {t : G} {L : Subgroup G} (hmin : FooteMinimal G) (hce : FooteCounterexample G t L)
    [IsSimpleGroup G] (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) {a : G}
    {K M : Subgroup G} (hK : IsTwoComponentAt a K) (hM : IsTwoComponentAt a M)
    (hKF : K ∈ footeFamilyOf L) (hMF : M ∈ footeFamilyOf L) : K = M :=
  foote_theorem_3_3_of_local (hSol G) hM3 hβ hmin hce hrank2 hK hM hKF hMF

end CFSG.ComponentClassification.FooteLit
