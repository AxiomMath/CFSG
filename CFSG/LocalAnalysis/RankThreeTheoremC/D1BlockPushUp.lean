module

public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_le_normalizer {X : Type*} [Group X] {A N : Subgroup X}
    (hAN : A ≤ Subgroup.normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) = Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem index_sup_eq_index_inf {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    (T.subgroupOf (L ⊔ T)).index = ((L ⊓ T).subgroupOf L).index := by
  have hprod := card_sup_mul_card_inf_of_le_normalizer hTL
  rw [sup_comm, inf_comm] at hprod
  have h1 : Nat.card T * (T.subgroupOf (L ⊔ T)).index = Nat.card (L ⊔ T : Subgroup G) := by
    rw [← Subgroup.card_mul_index (T.subgroupOf (L ⊔ T)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
  have h2 : Nat.card (L ⊓ T : Subgroup G) * ((L ⊓ T).subgroupOf L).index = Nat.card L := by
    rw [← Subgroup.card_mul_index ((L ⊓ T).subgroupOf L),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hT : 0 < Nat.card T := Nat.card_pos
  have hLT : 0 < Nat.card (L ⊓ T : Subgroup G) := Nat.card_pos
  rw [← h1, ← h2] at hprod
  have : Nat.card T * Nat.card (L ⊓ T : Subgroup G) * (T.subgroupOf (L ⊔ T)).index =
      Nat.card T * Nat.card (L ⊓ T : Subgroup G) * ((L ⊓ T).subgroupOf L).index := by
    linarith [hprod]
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hT hLT) this

theorem not_two_dvd_index_sup_of_inf {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hsyl : ¬ 2 ∣ ((L ⊓ T).subgroupOf L).index) :
    ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index := by
  rwa [index_sup_eq_index_inf hTL]

omit [Finite G] in
theorem isSubnormal_inf_of_normal {A B N : Subgroup G} (h : IsSubnormal A B) (hNB : N ≤ B)
    (hN : (N.subgroupOf B).Normal) : IsSubnormal (A ⊓ N) N := by
  induction h with
  | refl A =>
    rw [inf_eq_right.mpr hNB]
    exact IsSubnormal.refl _
  | step hAM hn _ ih =>
    refine IsSubnormal.step (inf_le_inf_right N hAM) ?_ (ih hNB hN)
    rw [Subgroup.normal_subgroupOf_iff hAM] at hn
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N hAM)]
    intro x g hx hg
    exact ⟨hn x g hx.1 hg.1, N.mul_mem (N.mul_mem hg.2 hx.2) (N.inv_mem hg.2)⟩

theorem normal_subgroupOf_sup_of_le_normalizer_left {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : (L.subgroupOf (L ⊔ T)).Normal := by
  have h := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTL
  rwa [sup_comm] at h

omit [Finite G] in
theorem mul_pow_mul_inv_pow_mem {L : Subgroup G} {l t : G} (hl : l ∈ L)
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) : (l * t) ^ n * (t ^ n)⁻¹ ∈ L := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htn : t ^ n ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ ht n
    have hconj : t ^ n * l * (t ^ n)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htn l).mp hl
    have e : (l * t) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
        ((l * t) ^ n * (t ^ n)⁻¹) * (t ^ n * l * (t ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact L.mul_mem ih hconj

theorem le_of_le_sup_of_isShort2 {L T Y : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hYD : Y ≤ L ⊔ T)
    (hY : ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → N = ⊤) : Y ≤ L := by
  have hLn : (L.subgroupOf (L ⊔ T)).Normal := normal_subgroupOf_sup_of_le_normalizer_left hTL
  have hpow : ∀ y ∈ L ⊔ T, ∃ k : ℕ, y ^ 2 ^ k ∈ L := by
    intro y hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L T hTL] at hy
    obtain ⟨l, hl, t, ht, rfl⟩ := hy
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have h := mul_pow_mul_inv_pow_mem hl (hTL ht) (2 ^ k)
    rwa [htk, inv_one, mul_one] at h
  set N : Subgroup Y := L.subgroupOf Y with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn y => ?_⟩
    have hyD : (y : G) ∈ L ⊔ T := hYD y.2
    have hn' : (n : G) ∈ L := hn
    have h := hLn.conj_mem ⟨n, (le_sup_left : L ≤ L ⊔ T) hn'⟩ hn' ⟨y, hyD⟩
    simpa [hN, Subgroup.mem_subgroupOf] using h
  have h2 : IsPGroup 2 (Y ⧸ N) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hpow y (hYD y.2)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa [hN, Subgroup.mem_subgroupOf] using hk
  have hNtop := hY N h2
  intro y hy
  have : (⟨y, hy⟩ : Y) ∈ N := hNtop ▸ Subgroup.mem_top _
  simpa [hN, Subgroup.mem_subgroupOf] using this

theorem le_of_normal_block_of_local (hglob : AGLGlobal G) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : NoXBlockFor G) {M H L T : Subgroup G} (hM : GLBIsMaxTwoLocal M) (hHM : ¬ H ≤ M)
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) (hTM : T ≤ M) (hT2 : IsPGroup 2 T)
    (hQT : pCoreOf 2 M ≤ T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hsyl : ¬ 2 ∣ ((L ⊓ T).subgroupOf L).index)
    (hloc : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H) :
    L ≤ H := by
  set D := L ⊔ T with hD
  have hDM : D ≤ M := sup_le hLM hTM
  have hTD : ¬ 2 ∣ (T.subgroupOf D).index := not_two_dvd_index_sup_of_inf hTL hsyl
  have hLnD : (L.subgroupOf D).Normal := normal_subgroupOf_sup_of_le_normalizer_left hTL
  have hDtop : D ≠ ⊤ := fun htop => hHM ((top_le_iff.mp (htop ▸ hDM) : M = ⊤) ▸ le_top)
  have hK : Open.IsKGroup ↥D :=
    isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hglob.kProper D hDtop)
  have hQD : pCoreOf 2 M ≤ D := hQT.trans le_sup_right
  have hQcore : pCoreOf 2 M ≤ pCoreOf 2 D :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQD
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr
        (hDM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  have hcharM : CharTwo M := hglob.charTwo M hM.1
  have hchar : CharTwo D := fun x hx =>
    hQcore (hcharM ⟨hDM hx.1, Subgroup.centralizer_le hQcore hx.2⟩)
  have hcgs : cgsIn D T = D := by
    by_contra hne
    obtain ⟨Y, hYD, hYsub, hYX, -⟩ := hCGT G D T hK hchar ⟨le_sup_right, hT2, hTD⟩ hne
    have hYL : Y ≤ L := le_of_le_sup_of_isShort2 hT2 hTL hYD hYX.1.1
    have hYsubL : IsSubnormal Y L := by
      have h := isSubnormal_inf_of_normal hYsub le_sup_left hLnD
      rwa [inf_eq_left.mpr hYL] at h
    exact hD2 M Y hM (hYL.trans hLM) (isSubnormal_of_isSubnormal_of_normal hYsubL hLM hLn) hYX
  calc L ≤ D := le_sup_left
    _ = cgsIn D T := hcgs.symm
    _ ≤ H := iSup_le fun C => iSup_le fun hCT => iSup_le fun hC => iSup_le fun hchC =>
        inf_le_right.trans (hloc C hCT hC hchC)

end CFSG.LocalAnalysis.RankThreeTheoremC
