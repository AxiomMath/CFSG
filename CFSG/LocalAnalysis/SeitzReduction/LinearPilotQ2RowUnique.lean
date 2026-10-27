module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphEnd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped commutatorElement

section Pieces

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  (e : L ≃* LinearFlag.projectiveSL n K)

@[expose] noncomputable def complPieceCore (I : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (blockSL (K := K) Iᶜ))

theorem commutator_complPieceCore [Finite G] (I : Finset (Fin n)) :
    ⁅complPieceCore e I, complPieceCore e I⁆ = complPieceCore e I :=
  F4Pilot.commutator_centralizerPerfectCore _

theorem le_normalizer_complPieceCore [Finite G] {t : G} (ht : t ∈ centralizer (L : Set G))
    (I : Finset (Fin n)) : t ∈ normalizer (complPieceCore e I : Set G) :=
  F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem le_complPieceCore [Finite G] {I : Finset (Fin n)} {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ centralizer (modelToG e (blockSL (K := K) Iᶜ) : Set G)) :
    P ≤ complPieceCore e I :=
  F4Pilot.le_centralizerPerfectCore hP hPC

end Pieces

section Commute

variable {n : ℕ} {K F : Type*} [Field K] [Field F]

theorem projMap_blockSL_compl_le_centralizer (ι : K →+* F) (I : Finset (Fin n)) :
    (blockSL (K := K) Iᶜ).map (projMap n ι) ≤
      centralizer (blockSL (K := F) I : Set (LinearFlag.projectiveSL n F)) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.1 hx
  rw [mem_centralizer_iff]
  rintro _ ⟨B, hB, rfl⟩
  rw [projMap_proj, ← map_mul, ← map_mul]
  exact congrArg (LinearFlag.proj n F)
    (commute_blockSpecialLinear_of_disjoint disjoint_compl_right hB
      (map_ringHom_mem_blockSpecialLinear ι hA)).eq

end Commute

section Generation

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_iSup_centralizerPerfectCore_of_le (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K]
    [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (C : Fin m → Subgroup (LinearFlag.projectiveSL (m + 1) K))
    (hC : ∀ i : Fin m, (C i).map (projMap (m + 1) ι) ≤
      centralizer (blockSL (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1))) :
        Set (LinearFlag.projectiveSL (m + 1) F)))
    {M : Subgroup G} [Group.IsPerfect M]
    (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL (m + 1) F) (hLM : L ≤ M)
    (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ i : Fin m, centralizerPerfectCore (modelToG e (C i)) := by
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨ψ, hψL, -⟩ := exists_mulEquiv_globalNormal_center hn ι hσ1 hσσ hfix e ψ₀ hLM
    (by rw [← ht]; exact pow_orderOf_eq_one t) htM
    (perfectCore_inf_centralizer_eq_of_standardSetting hset hOut hn e hLM htC ht)
  set π : M →* LinearFlag.projectiveSL (m + 1) F :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ
  have hπs : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = center M := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπL : ∀ x : L, π (inclusion hLM x) = projMap (m + 1) ι (e x) := fun x => hψL x
  have hF4 : 4 ≤ Nat.card F := by
    have : CharP K 2 := ι.charP ι.injective 2
    obtain ⟨f, hf, hK⟩ := exists_natCard_eq_two_pow_of_charP K
    rw [natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix, hK, ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set I : Fin m → Finset (Fin (m + 1)) := fun i => {i.castSucc, i.succ} with hI
  set B : Fin m → Subgroup M := fun i => (blockSL (K := F) (I i)).comap π with hB
  set D : Fin m → Subgroup M := fun i => perfectCore (B i) with hD
  have hDB : ∀ i, D i ≤ B i := fun i => CFSG.Quasithin.perfectCore_le _
  have hDpiece : ∀ i, (D i).map M.subtype ≤ centralizerPerfectCore (modelToG e (C i)) := by
    intro i
    have hperf : ⁅(D i).map M.subtype, (D i).map M.subtype⁆ = (D i).map M.subtype := by
      rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    refine F4Pilot.le_centralizerPerfectCore hperf
      (le_centralizer_of_commutator_le_center (M := M) (map_subtype_le _) hperf ?_)
    rw [Subgroup.commutator_le]
    rintro _ ⟨c, hc, rfl⟩ y hy
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hy
    set j : M := inclusion hLM (e.symm x) with hj
    have hcB : π c ∈ blockSL (K := F) (I i) := hDB i hc
    have hjT : π j ∈ centralizer (blockSL (K := F) (I i) :
        Set (LinearFlag.projectiveSL (m + 1) F)) := by
      rw [hj, hπL, MulEquiv.apply_symm_apply]
      exact hC i (mem_map_of_mem _ hx)
    have hcomm : π ⁅c, j⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.1 hjT _ hcB)
    have hZ : ⁅c, j⁆ ∈ center M := by
      rw [← hπker]
      exact hcomm
    exact ⟨⁅c, j⁆, hZ, rfl⟩
  have hgen : (⨆ i, D i) = ⊤ := by
    refine eq_top_of_sup_center_eq_top_of_perfect ?_
    rw [← hπker, ← Subgroup.comap_map_eq, Subgroup.map_iSup]
    have hi : ∀ i, (D i).map π = blockSL (K := F) (I i) := by
      intro i
      rw [hD, CFSG.Quasithin.map_perfectCore, hB, Subgroup.map_comap_eq_self_of_surjective hπs,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (commutator_blockSL_eq_of_card_two (card_nodePair i) hF4)]
    simp_rw [hi]
    rw [hI, iSup_blockSL_pair_eq_top F m, Subgroup.comap_top]
  intro g hg
  have hmem : (⟨g, hg⟩ : M) ∈ ⨆ i, D i := hgen ▸ mem_top _
  have h2 : g ∈ (⨆ i, D i).map M.subtype := ⟨⟨g, hg⟩, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  exact (iSup_mono hDpiece) h2

theorem le_iSup_complPieceCore_of_le (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K]
    [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {M : Subgroup G} [Group.IsPerfect M]
    (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL (m + 1) F) (hLM : L ≤ M)
    (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ i : Fin m, complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) :=
  le_iSup_centralizerPerfectCore_of_le hset hOut hm ι hσ1 hσσ hfix e htC ht
    (fun i => blockSL (K := K) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))ᶜ)
    (fun _ => projMap_blockSL_compl_le_centralizer ι _) ψ₀ hLM htM

theorem conjugate_eq_of_le_compl (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K]
    [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    [Group.IsPerfect G₀] (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F) (g : G)
    (htg : t ∈ normalizer (CFSG.conjugate G₀ g : Set G)) (hLg : L ≤ CFSG.conjugate G₀ g) :
    CFSG.conjugate G₀ g = G₀ := by
  have : Group.IsPerfect (CFSG.conjugate G₀ g) :=
    Group.IsPerfect.ofSurjective (f := (conjugateEquiv G₀ g).toMonoidHom)
      (conjugateEquiv G₀ g).surjective
  have hle := le_iSup_complPieceCore_of_le hset hOut hm ι hσ1 hσσ hfix e htC ht
    (M := CFSG.conjugate G₀ g) ((conjugateQuotientCenterEquiv G₀ g).symm.trans ψ) hLg htg
  rw [← hG₀] at hle
  exact Subgroup.eq_of_le_of_card_ge hle (Nat.card_congr (conjugateEquiv G₀ g).toEquiv).le

end Generation

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem unique_compl (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L)) {m : ℕ}
    (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K] [Field F] [Finite F] [CharP F 2]
    (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hq : CFSG.IsQuasisimple G₀) (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  have : Group.IsPerfect G₀ := hq.1
  exact F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
    conjugate_eq_of_le_compl hset hOut hm ι hσ1 hσσ hfix e (mem_centralizer_of_inf_eq_zpowers hKt)
      ht hG₀ ψ h htM (le_of_mem_normalizer_of_fieldCoreTypeDet hset hOut e ht hKt
        (fieldCoreTypeDet_of_card hm ι hσ1 hσσ hfix)
        ((conjugateQuotientCenterEquiv G₀ h).symm.trans ψ) htM)

theorem false_of_globalField_compl (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K]
    [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)) (hq : CFSG.IsQuasisimple G₀)
    (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀))) :
    False := by
  have := hset.simple
  have hZL : center L = ⊥ := by
    rw [← map_center_eq e.symm, CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot
      (by omega), Subgroup.map_bot]
  exact false_of_simple_globalField hset.nonab hset.standard hZL (by omega) hσ1 hσσ ht hKt hLG₀
    htG₀ ψ hψt (unique_compl hset hOut hm ι hσ1 hσσ hfix e ht hKt hG₀ hq ψ)

theorem false_of_globalField_compl_of_seitzSetting (hset : SeitzSetting G L) {m f : ℕ}
    (hm : 2 ≤ m) {K : Type} [Field K] [Finite K] (hKc : Nat.card K = 2 ^ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)) (hq : CFSG.IsQuasisimple G₀)
    (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀))) :
    False := by
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  exact false_of_globalField_compl hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) hm ι hσ1 hσσ hfix e ht hKt hG₀ hLG₀ htG₀ hq ψ hψt

end Global

end CFSG.SeitzReduction.LinearPilot
