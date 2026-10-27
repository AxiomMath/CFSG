module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandardSetting
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_mulEquiv_fieldKind_two_of_equiv (hset : SeitzSetting G L) {n : ℕ}
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hZ : center (((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)))}
    (hDK : ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL (n - 2) 2 (2 * 1))
    (eN : ({a, b}ᶜ : Finset (Fin n)) ≃ Fin (n - 2)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
      ∃ (ι : K →+* F) (σ : F ≃+* F), σ ≠ 1 ∧ σ * σ = 1 ∧
        (∀ x : F, σ x = x ↔ x ∈ Set.range ι) ∧
      ∃ ψ : Kc ≃* LinearFlag.projectiveSL (n - 2) F,
        (∀ (x : SpecialLinearGroup (Fin (n - 2)) K)
          (hx : ((e.symm (LinearFlag.proj n K (blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN x)) :
            L) : G) ∈ centralizer (modelToG e X₀ : Set G))
          (hk : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨_, hx⟩ ∈ Kc),
          ψ ⟨_, hk⟩ = LinearFlag.proj (n - 2) F (SpecialLinearGroup.map ι x)) ∧
        ∀ k : Kc, ψ (Kc.normalizerMonoidHom ⟨_, hsN⟩ k) =
          LinearFlag.fieldAut (n - 2) F σ (ψ k) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : Finite K := finite_of_card_eq_two_pow hK1
  obtain ⟨F, _, _, hF, ⟨ψ₀⟩⟩ := exists_projectiveSL_equiv_of_lieModel_PSL hmodel
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : CharP F 2 := SeitzQ2.charTwo_of_natCard_eq_two_pow hF
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := exists_subfield_involution (le_refl 1) hK1 hF
  set Db := ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
    (centralizer (modelToG e X₀ : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) with hDbdef
  set s := QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ with hsdef
  have hNab : Disjoint ({a, b}ᶜ : Finset (Fin n)) ({a, b} : Finset (Fin n)) := disjoint_compl_left
  have hDC : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) ≤
      centralizer (modelToG e X₀ : Set G) :=
    modelToG_le_centralizer e ((blockSL_le_centralizer_blockSL_of_disjoint hNab).trans
      (centralizer_le hX₀))
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_torusQ1_of_seitzSetting hset hK1 e hn
    htC ht hab hX₀ hX₀c rfl htX rfl
  have hOut := isSolvable_outer_of_mulEquiv (by omega) ψ₀
  have hs : orderOf s = 2 := orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hDs : Db ≤ centralizer ({s} : Set _) := hcomp.1
  have hsD : s ∈ centralizer (Db : Set _) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hDs hd)
  have hsC : s ∉ centralizer (Kc : Set _) := by
    intro h
    apply hτ
    have h1 : (⟨s, hsN⟩ : normalizer (Kc : Set _)) ∈ Kc.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact h
    exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
  have hmemC : ∀ x : SpecialLinearGroup (Fin (n - 2)) K,
      ((e.symm (LinearFlag.proj n K (blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN x)) : L) : G) ∈
        centralizer (modelToG e X₀ : Set G) :=
    fun x => hDC (symm_mem_modelToG e
      (proj_mem_blockSL (blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN x).2))
  let φ₀ : SpecialLinearGroup (Fin (n - 2)) K →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj n K).comp
      ((blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin n))).subtype.comp
        (blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN).toMonoidHom)))
  let φ : SpecialLinearGroup (Fin (n - 2)) K →*
      centralizer (modelToG e X₀ : Set G) ⧸ oddCore (centralizer (modelToG e X₀ : Set G)) :=
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))).comp
      (φ₀.codRestrict (centralizer (modelToG e X₀ : Set G)) hmemC)
  have hφ : φ.range = Db := by
    ext k
    constructor
    · rintro ⟨x, rfl⟩
      rw [hDbdef]
      exact Subgroup.mem_map.2 ⟨⟨_, hmemC x⟩, mem_subgroupOf.2
        (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN x).2)),
        rfl⟩
    · intro hk
      rw [hDbdef] at hk
      obtain ⟨y, hy, rfl⟩ := hk
      obtain ⟨z, hz, hzy⟩ := (mem_modelToG e).1 (mem_subgroupOf.1 hy)
      obtain ⟨A, hA, rfl⟩ := mem_blockSL.1 hz
      refine ⟨(blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN).symm ⟨A, hA⟩, ?_⟩
      apply congrArg (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))
      apply Subtype.ext
      show φ₀ ((blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN).symm ⟨A, hA⟩) = (y : G)
      simp only [φ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        Subgroup.coe_subtype]
      exact hzy
  have hne : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨ε, hεinj, hεrange, hεapp⟩ := SymplecticPilot.exists_projectiveSL_embedding_of_hom
    (Kc := Kc) (by omega) φ (hφ ▸ hne) (hφ ▸ hZ) (hφ ▸ hDK)
  have hθ : Kc.normalizerMonoidHom ⟨s, hsN⟩ * Kc.normalizerMonoidHom ⟨s, hsN⟩ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN (by rw [← hs]; exact pow_orderOf_eq_one s)
  have hDc : IsComponent (Db.subgroupOf (centralizer ({s} : Set _))) :=
    (isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK
  have hD'c : IsComponent ((Db.subgroupOf Kc).subgroupOf
      (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) :=
    F4Pilot.isComponent_subgroupOf_subgroupOf
      (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
  have hεθ : ε.range ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
    rw [hεrange, hφ, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  obtain ⟨ψ, hψε, hψτ⟩ := exists_mulEquiv_projMap_eq_of_isComponent (n := n - 2) (by omega)
    (f := 1) le_rfl hK1 ι hσ1 hσσ hfix ψ₀ hθ ε hεinj hεθ (by rw [hεrange, hφ]; exact hD'c)
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF4, ι, σ, hσ1, hσσ, hfix, ψ,
    fun x hx hk => ?_, hψτ⟩
  have h1 : (⟨_, hk⟩ : Kc) = ε (LinearFlag.proj (n - 2) K x) := Subtype.ext (by rw [hεapp]; rfl)
  rw [h1, hψε, projMap_proj]

theorem exists_mulEquiv_fieldKind_two (hset : SeitzSetting G L) {n : ℕ}
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hZ : center (((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)))}
    (hDK : ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL (n - 2) 2 (2 * 1)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
      ∃ (ι : K →+* F) (σ : F ≃+* F), σ ≠ 1 ∧ σ * σ = 1 ∧
        (∀ x : F, σ x = x ↔ x ∈ Set.range ι) ∧
      ∃ (eN : ({a, b}ᶜ : Finset (Fin n)) ≃ Fin (n - 2))
        (ψ : Kc ≃* LinearFlag.projectiveSL (n - 2) F),
        (∀ (x : SpecialLinearGroup (Fin (n - 2)) K)
          (hx : ((e.symm (LinearFlag.proj n K (blockSLEquiv ({a, b}ᶜ : Finset (Fin n)) eN x)) :
            L) : G) ∈ centralizer (modelToG e X₀ : Set G))
          (hk : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨_, hx⟩ ∈ Kc),
          ψ ⟨_, hk⟩ = LinearFlag.proj (n - 2) F (SpecialLinearGroup.map ι x)) ∧
        ∀ k : Kc, ψ (Kc.normalizerMonoidHom ⟨_, hsN⟩ k) =
          LinearFlag.fieldAut (n - 2) F σ (ψ k) := by
  have hNcard : ({a, b}ᶜ : Finset (Fin n)).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  let eN : ({a, b}ᶜ : Finset (Fin n)) ≃ Fin (n - 2) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hNcard])
  obtain ⟨F, i1, i2, i3, hF4, ι, σ, hσ1, hσσ, hfix, ψ, hψD, hψτ⟩ :=
    exists_mulEquiv_fieldKind_two_of_equiv hset hK e hn htC ht hab hX₀ hX₀c htX hZ hDK hsN hτ
      hmodel eN
  exact ⟨F, i1, i2, i3, hF4, ι, σ, hσ1, hσσ, hfix, eN, ψ, hψD, hψτ⟩

end CFSG.SeitzReduction.LinearPilot
