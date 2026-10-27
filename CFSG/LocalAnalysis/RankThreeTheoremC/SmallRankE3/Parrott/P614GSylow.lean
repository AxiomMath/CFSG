module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GBender
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.AGLEmbedding
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem subnormal_cases (c : Ctx M B H S K z) : ∀ {A L : Subgroup G}, IsSubnormal A L → L = K →
    A ≤ K ∧ (A ≤ pCoreOf 2 H ∨
      ∀ q : Kbar K, ∃ a : ↥K, (a : G) ∈ A ∧ (QuotientGroup.mk a : Kbar K) = q) := by
  intro A L h
  induction h with
  | refl L₀ =>
    intro hL
    subst hL
    refine ⟨le_rfl, Or.inr fun q => ?_⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨k, k.2, rfl⟩
  | @step A' M' L' hAM hn _ ih =>
    intro hL
    obtain ⟨hM'K, hM'⟩ := ih hL
    refine ⟨hAM.trans hM'K, ?_⟩
    rcases hM' with hM'O | hM'top
    · exact Or.inl (hAM.trans hM'O)
    · have hAK : A' ≤ K := hAM.trans hM'K
      set Abar : Subgroup (Kbar K) :=
        (A'.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) with hAbar
      have hAn : Abar.Normal := by
        refine ⟨fun x hx q => ?_⟩
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨m, hmM, rfl⟩ := hM'top q
        have hma : (m : G) * a * (m : G)⁻¹ ∈ A' := by
          have := hn.conj_mem ⟨a, hAM (mem_subgroupOf.mp ha)⟩ (mem_subgroupOf.mpr ha) ⟨m, hmM⟩
          simpa [mem_subgroupOf] using this
        refine ⟨m * a * m⁻¹, mem_subgroupOf.mpr hma, ?_⟩
        simp
      have := c.isSimpleGroup
      rcases hAn.eq_bot_or_eq_top with h | h
      · left
        intro a ha
        have h1 : (QuotientGroup.mk ⟨a, hAK ha⟩ : Kbar K) ∈ Abar :=
          ⟨⟨a, hAK ha⟩, mem_subgroupOf.mpr ha, rfl⟩
        rw [h, mem_bot] at h1
        exact (c.mk_eq_one_iff _).1 h1
      · right
        intro q
        obtain ⟨a, ha, rfl⟩ : q ∈ Abar := h ▸ mem_top q
        exact ⟨a, mem_subgroupOf.mp ha, rfl⟩

theorem nonempty_equiv_of_onto (c : Ctx M B H S K z) {Y : Subgroup G} (hYK : Y ≤ K)
    (hY : ∀ q : Kbar K, ∃ a : ↥K, (a : G) ∈ Y ∧ (QuotientGroup.mk a : Kbar K) = q)
    {X : Type*} [Group X] (α : ↥Y →* X) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥Y) : Nonempty (Kbar K ≃* X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : ↥Y →* Kbar K :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp (Subgroup.inclusion hYK)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨a, haY, rfl⟩ := hY q
    exact ⟨⟨a, haY⟩, rfl⟩
  have hψker : ∀ y : ↥Y, y ∈ ψ.ker ↔ (y : G) ∈ pCoreOf 2 H := fun y => by
    rw [MonoidHom.mem_ker]
    exact c.mk_eq_one_iff (Subgroup.inclusion hYK y)
  have hkereq : ψ.ker = α.ker := by
    rw [hker]
    apply le_antisymm
    · refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 _ inferInstance ?_
      have h2 : IsPGroup 2 ((pCoreOf 2 H).comap Y.subtype) := c.isPGroup_core.comap_subtype
      have heq : ψ.ker = (pCoreOf 2 H).comap Y.subtype := by
        ext y
        rw [hψker]
        rfl
      rw [heq]
      exact h2
    ·
      have hn : ((CFSG.pCore 2 ↥Y).map ψ).Normal :=
        (CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2).map ψ hψ
      have := c.isSimpleGroup
      rcases hn.eq_bot_or_eq_top with h | h
      · intro y hy
        have : ψ y ∈ (CFSG.pCore 2 ↥Y).map ψ := mem_map_of_mem _ hy
        rw [h, mem_bot] at this
        exact this
      · exfalso
        have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥Y).map ψ) :=
          (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).map ψ
        rw [h] at h2
        obtain ⟨k, hk⟩ := h2 ⟨c.zbar, mem_top _⟩
        have hk' : c.zbar ^ 2 ^ k = 1 := congrArg Subtype.val hk
        have hd := orderOf_dvd_of_pow_eq_one hk'
        rw [c.orderOf_zbar] at hd
        exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))⟩

theorem cgsIn_le_M (c : Ctx M B H S K z) : cgsIn (K ⊔ S) S ≤ M :=
  iSup_le fun C => iSup_le fun hCS => iSup_le fun hC => iSup_le fun hchC =>
    inf_le_right.trans (c.char_le C hCS hC hchC)

theorem S_le_normalizer_KO (c : Ctx M B H S K z) :
    S ≤ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := fun _ hs =>
  inf_normalizer_le_normalizer_sup _ _
    ⟨c.comp.normal (c.S_le hs), c.H_le_normalizer_core (c.S_le hs)⟩

theorem index_S_eq (c : Ctx M B H S K z) :
    (S.subgroupOf (K ⊔ S)).index = ((kRad H S K).subgroupOf (K ⊔ pCoreOf 2 H)).index := by
  have h := index_sup_eq_index_inf c.S_le_normalizer_KO
  have e1 : K ⊔ pCoreOf 2 H ⊔ S = K ⊔ S := by
    rw [sup_assoc, sup_eq_right.mpr c.core_le]
  have e2 : (K ⊔ pCoreOf 2 H) ⊓ S = kRad H S K := by
    rw [kRad, inf_comm]
  rw [e1, e2] at h
  exact h

theorem false_of_sylow (c : Ctx M B H S K z) (hTI : KFactBenderTI) (hGen : KFactBenderGen)
    (hCGT : AschbacherLocalCGTBlock) (hR : pCoreOf 2 H < kRad H S K)
    (hsyl : ¬ 2 ∣ ((kRad H S K).subgroupOf (K ⊔ pCoreOf 2 H)).index) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : S ≤ normalizer (K : Set G) := c.S_le.trans c.comp.normal
  have hXH : K ⊔ S ≤ H := sup_le c.K_le c.S_le
  have hSX : IsSylowTwoOf S (K ⊔ S) := ⟨le_sup_right, c.isPGroup_S, by rwa [c.index_S_eq]⟩
  have hOX : pCoreOf 2 H ≤ pCoreOf 2 (K ⊔ S) :=
    normal_pGroup_le_pCoreOf 2 _ _ (c.core_le.trans le_sup_right)
      ((normal_subgroupOf_iff_le_normalizer (c.core_le.trans le_sup_right)).mpr
        (hXH.trans c.H_le_normalizer_core)) c.isPGroup_core
  have hchar : CharTwo (K ⊔ S) := fun x hx =>
    hOX (c.charTwo ⟨hXH hx.1, centralizer_le hOX hx.2⟩)
  have hne : cgsIn (K ⊔ S) S ≠ K ⊔ S := fun h =>
    c.K_not_le (le_sup_left.trans (h.symm.le.trans c.cgsIn_le_M))
  obtain ⟨Y, hYX, hYsub, hYX', hYC⟩ := hCGT G (K ⊔ S) S (c.kGroup _ hXH) hchar hSX hne
  have hYK : Y ≤ K := le_of_le_sup_of_isShort2 c.isPGroup_S hSK hYX hYX'.1.1
  have hYsubK : IsSubnormal Y K := by
    have h := isSubnormal_inf_of_normal hYsub le_sup_left
      (normal_subgroupOf_sup_of_le_normalizer_left hSK)
    rwa [inf_eq_left.mpr hYK] at h
  rcases (c.subnormal_cases hYsubK rfl).2 with hYO | hYtop
  · exact hYC ((le_inf hYX ((hYO.trans c.core_le).trans le_normalizer)).trans
      (inf_normalizer_le_cgsIn c.S_ne_bot))
  · rcases hYX'.2 with ⟨n, -, F, hF, hFt, hcard, α, hα, hαker, -⟩ | ⟨n, hn, α, hα, hαker, -⟩
    · obtain ⟨e⟩ := c.nonempty_equiv_of_onto hYK hYtop α hα hαker
      have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
      exact c.false_of_bender hTI hGen hR (c.bender_of_sl2 hF' e)
    · obtain ⟨e⟩ := c.nonempty_equiv_of_onto hYK hYtop α hα hαker
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := by omega
        subst hn1
        refine c.false_of_card_lt e ?_
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      · rcases Nat.eq_or_lt_of_le hn2 with hn2' | hn3
        · subst hn2'
          exact c.false_of_bender hTI hGen hR (c.bender_of_alt5 e)
        · exact c.false_of_alt (by omega) e

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
