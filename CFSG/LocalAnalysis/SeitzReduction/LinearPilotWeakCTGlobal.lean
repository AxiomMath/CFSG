module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImagesConj
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalQuotient
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped MatrixGroups

section Join

variable {G : Type*} [Group G] {L : Subgroup G}

theorem modelToG_iSup {n : ℕ} {K : Type*} [Field K] (e : L ≃* LinearFlag.projectiveSL n K)
    {ι' : Sort*} (A : ι' → Subgroup (LinearFlag.projectiveSL n K)) :
    modelToG e (⨆ i, A i) = ⨆ i, modelToG e (A i) := by
  simp only [modelToG, Subgroup.map_iSup]

theorem le_iSup_pieceCore_pair {m : ℕ} {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) :
    L ≤ ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
  refine (modelToG_top e).symm.le.trans ?_
  rw [← iSup_blockSL_pair_eq_top K m, modelToG_iSup]
  exact iSup_mono fun i => modelToG_blockSL_le_pieceCore_of_two_le e (card_nodePair i).ge hK

theorem mem_normalizer_iSup_family {M : Type*} [Group M] {ι' : Sort*} {H : ι' → Subgroup M}
    {g : M} (hg : ∀ i, g ∈ normalizer (H i : Set M)) :
    g ∈ normalizer ((⨆ i, H i : Subgroup M) : Set M) := by
  have hmap : ∀ i, (H i).map (MulAut.conj g).toMonoidHom = H i := fun i => by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 (hg i) x).1 hx
    · intro hy
      refine ⟨g⁻¹ * y * g, (mem_normalizer_iff.1 (hg i) _).2 ?_, ?_⟩
      · rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hsup : (⨆ i, H i).map (MulAut.conj g).toMonoidHom = ⨆ i, H i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hmap
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hsup]
    exact ⟨x, hx, rfl⟩
  · rw [← hsup] at hx
    obtain ⟨x', hx', hxx'⟩ := hx
    have : x' = x := by
      change g * x' * g⁻¹ = g * x * g⁻¹ at hxx'
      simpa using hxx'
    exact this ▸ hx'

theorem mem_normalizer_iSup_pieceCore_pair {m : ℕ} {K : Type*} [Field K]
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer ((⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) :
      Subgroup G) : Set G) :=
  mem_normalizer_iSup_family fun _ => le_normalizer_pieceCore e ht _

end Join

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_globalField_of_fieldNeighbourCover (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {F : Type} [Field F] [Finite F]
    (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (hcov : FieldNeighbourCover e t ι σ 3)
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      (∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap (m + 1) ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀)) := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  have hK4 : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  obtain ⟨κ, hκ⟩ := exists_ne_one_of_three_le_card (α := K) (by omega)
  obtain ⟨ψ, hsurj, hker, himg, hqs, hmodel⟩ :=
    exists_weakCT_of_fieldNeighbourCover hm hF (by omega) hκ hcov hcomm hG₀
  have hLG₀ : L ≤ G₀ := by
    rw [hG₀]
    exact le_iSup_pieceCore_pair hK4 e
  have htG₀ : t ∈ normalizer (G₀ : Set G) := by
    rw [hG₀]
    exact mem_normalizer_iSup_pieceCore_pair e htC
  obtain ⟨F', _, _, hF', ⟨ψ₁⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have : Fintype F' := Fintype.ofFinite F'
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF', hF]
  let ψ₀ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F := ψ₁.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcardF))
  obtain ⟨ψ', hψ'L, hψ't⟩ := exists_mulEquiv_globalNormal_center (by omega) ι hσ1 hσσ hfix e ψ₀
    hLG₀ (by rw [← ht]; exact pow_orderOf_eq_one t) htG₀
    (perfectCore_inf_centralizer_eq_of_standardSetting hset hOut (by omega) e hLG₀ htC ht)
  exact ⟨hLG₀, htG₀, hqs, hmodel, ⟨ψ, hsurj, hker, himg⟩, ψ', hψ'L, hψ't⟩

theorem exists_globalField_rootTorus (hset : CFSG.SeitzReduction.SeitzSetting G L) {m f : ℕ}
    (hm : 5 ≤ m) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin (m + 1)))ᶜ)))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      (∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap (m + 1) ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀)) := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  have hK4 : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  obtain ⟨κ, hκ⟩ := exists_ne_one_of_three_le_card (α := K) (by omega)
  have hcov : FieldNeighbourCover e t ι σ 4 := fieldNeighbourCover_rootTorus hparam (by omega)
  exact exists_globalField_of_fieldNeighbourCover hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) (by omega) hKc hf e htC ht ι hσ1 hσσ hfix
    (hcov.mono (by norm_num))
    (fun i j hij => pieceCore_le_centralizer_of_fieldNeighbourCover hcov
      (disjoint_nodePair_of_lt i j hij) (card_nodePair i).ge (card_nodePair j).ge
      (card_union_nodePair_le i j) hκ
      (four_le_of_card_eq_two_pow_two_mul hF (by omega))) hG₀

theorem exists_globalField_rootTorus_of_comm (hset : CFSG.SeitzReduction.SeitzSetting G L)
    {m f : ℕ} (hm : 4 ≤ m) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin (m + 1)))ᶜ)))
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      (∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap (m + 1) ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀)) := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  exact exists_globalField_of_fieldNeighbourCover hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) (by omega) hKc hf e htC ht ι hσ1 hσσ hfix
    (fieldNeighbourCover_rootTorus hparam (by omega)) hcomm hG₀

theorem exists_globalField_levTorus_of_comm (hset : CFSG.SeitzReduction.SeitzSetting G L)
    {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ a : Fin (m + 1),
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      (∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap (m + 1) ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀)) := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  exact exists_globalField_of_fieldNeighbourCover hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) hm hKc hf e htC ht ι hσ1 hσσ hfix
    (fieldNeighbourCover_levTorus hparam (by omega)) hcomm hG₀

theorem exists_globalField_rootTorus_of_one (hset : CFSG.SeitzReduction.SeitzSetting G L)
    {m f : ℕ} (hm : 5 ≤ m) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {a b : Fin (m + 1)} (hab : a ≠ b)
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
      (({a, b} : Finset (Fin (m + 1)))ᶜ)))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      (∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap (m + 1) ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀)) :=
  exists_globalField_rootTorus hset hm hKc hf e htC ht ι hσ1 hσσ hfix
    (fun _ _ hab' => nonempty_fieldNeighbourParam_rootTorus_of_nonempty htC
      (fun c => (hfix (ι c)).2 ⟨c, rfl⟩) hab hP hab') hG₀

theorem exists_globalField_rootTorus_five (hset : CFSG.SeitzReduction.SeitzSetting G L) {f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {a b : Fin 5} (hab : a ≠ b)
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
      (({a, b} : Finset (Fin 5))ᶜ)))
    (h02 : pieceCore e ({0, 1} : Finset (Fin 5)) ≤
      centralizer (pieceCore e ({2, 3} : Finset (Fin 5)) : Set G))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin 4, pieceCore e ({i.castSucc, i.succ} : Finset (Fin 5))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        5 2 (2 * f) ∧
      (∃ ψ : SL(5, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(5, F) ∧
        ∀ i : Fin 4,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin 5))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin 5))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL 5 F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap 5 ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut 5 F σ (ψ (x : G₀ ⧸ center G₀)) :=
  exists_globalField_rootTorus_of_comm hset (m := 4) le_rfl hKc hf e htC ht ι hσ1 hσσ hfix
    (fun _ _ hab' => nonempty_fieldNeighbourParam_rootTorus_of_nonempty htC
      (fun c => (hfix (ι c)).2 ⟨c, rfl⟩) hab hP hab')
    (forall_pieceCore_nodePair_le_centralizer e (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) h02) hG₀

theorem exists_globalField_levTorus_four (hset : CFSG.SeitzReduction.SeitzSetting G L) {f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {a : Fin 4}
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    (h02 : pieceCore e ({0, 1} : Finset (Fin 4)) ≤
      centralizer (pieceCore e ({2, 3} : Finset (Fin 4)) : Set G))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin 3, pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        4 2 (2 * f) ∧
      (∃ ψ : SL(4, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F) ∧
        ∀ i : Fin 3,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin 4))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL 4 F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap 4 ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut 4 F σ (ψ (x : G₀ ⧸ center G₀)) :=
  exists_globalField_levTorus_of_comm hset (m := 3) le_rfl hKc hf e htC ht ι hσ1 hσσ hfix
    (fun _ => nonempty_fieldNeighbourParam_levTorus_of_nonempty htC
      (fun c => (hfix (ι c)).2 ⟨c, rfl⟩) hP _)
    (forall_pieceCore_nodePair_le_centralizer e (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) h02) hG₀

end Global

end CFSG.SeitzReduction.LinearPilot
