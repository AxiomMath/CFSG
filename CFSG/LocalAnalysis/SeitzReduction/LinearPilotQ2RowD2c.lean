module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowParam
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2BLift
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamCore
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandardSetting
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Component

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem nonempty_fieldNeighbourParam_of_component_two [Finite G] [Finite F] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ι : K →+* F) (σ : F ≃+* F)
    {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm5 : 5 ≤ m)
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (htX : t ∈ centralizer (X : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hcore : perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G)))) = Kc) (hB : HasBLift Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (ψ : Kc ≃* LinearFlag.projectiveSL m F)
    (hψD : ∀ (x : SpecialLinearGroup (Fin m) K)
      (hx : ((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G) ∈
        centralizer (X : Set G))
      (hk : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨_, hx⟩ ∈ Kc),
      ψ ⟨_, hk⟩ = LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (hψt : ∀ k : Kc, ψ (Kc.normalizerMonoidHom ⟨_, hsN⟩ k) = LinearFlag.fieldAut m F σ (ψ k)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) := by
  obtain ⟨q, hq, hqker, hqapp⟩ :=
    exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have ht : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ htX)
  refine nonempty_fieldNeighbourParam_of_proj_two hK e t ι σ eN hm5
    (ψ.toMonoidHom.comp q) (ψ.surjective.comp hq) ?_ hD ?_ ht ?_
  ·
    intro y hy
    apply hqker
    have h1 : ψ (q y) = ψ 1 := by
      rw [map_one]
      exact hy
    exact ψ.injective h1
  ·
    intro x
    have hx := hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))
    have hxH := F4Pilot.centralizerPerfectCore_le_centralizer _ hx
    have hk : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨_, hxH⟩ ∈ Kc := by
      rw [← hqapp ⟨_, hx⟩]
      exact (q ⟨_, hx⟩).2
    have hq' : q ⟨_, hx⟩ = ⟨_, hk⟩ := Subtype.ext (hqapp _)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hq']
    exact hψD x hxH hk
  ·
    intro y
    have hqt : q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
        Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y) := by
      apply Subtype.ext
      have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y :
          centralizerPerfectCore X) : G),
            F4Pilot.centralizerPerfectCore_le_centralizer _
              ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y).2⟩ :
              centralizer (X : Set G)) =
          ⟨t, htX⟩ * ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer _ y.2⟩ *
            ⟨t, htX⟩⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rfl
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp, e1, map_mul, map_mul,
        map_inv]
    show ψ (q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y)) =
      LinearFlag.fieldAut m F σ (ψ (q y))
    rw [hqt, hψt]

end Component

section FieldKind

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_fieldNeighbourParam_of_fieldKind_two (hset : SeitzSetting G L) {n : ℕ}
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 7 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hZ : center (((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)))} (hKcomp : IsComponent Kc)
    (hDK : ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL (n - 2) 2 (2 * 1)) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e X₀) ({a, b}ᶜ : Finset (Fin n))) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : Finite K := finite_of_card_eq_two_pow hK1
  have hNcard : ({a, b}ᶜ : Finset (Fin n)).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  let eN : ({a, b}ᶜ : Finset (Fin n)) ≃ Fin (n - 2) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hNcard])
  set Db := ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
    (centralizer (modelToG e X₀ : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) with hDbdef
  set s := QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ with hsdef
  have hF : Nat.card F = 2 ^ (2 * 1) := natCard_eq_two_pow_of_fixedField hK1 ι hσ1 hσσ hfix
  have hNab : Disjoint ({a, b}ᶜ : Finset (Fin n)) ({a, b} : Finset (Fin n)) := disjoint_compl_left
  have hDC : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) ≤
      centralizer (modelToG e X₀ : Set G) :=
    modelToG_le_centralizer e ((blockSL_le_centralizer_blockSL_of_disjoint hNab).trans
      (centralizer_le hX₀))
  have hD : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) ≤
      centralizerPerfectCore (modelToG e X₀) :=
    F4Pilot.le_centralizerPerfectCore
      (modelToG_perfect e (commutator_blockSL_eq_of_three_le (by omega))) hDC
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_torusQ1_of_seitzSetting hset hK1 e (by omega)
    htC ht hab hX₀ hX₀c rfl htX rfl
  obtain ⟨F', _, _, hF', ⟨ψ'⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have : Fintype F' := Fintype.ofFinite F'
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF', hF]
  let ψ₀ : Kc ≃* LinearFlag.projectiveSL (n - 2) F := ψ'.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcardF))
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
  have hcore := perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKcomp hDK hs hsD hsN hsC hsyl hOut
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
  obtain ⟨htX', -, -, hBl⟩ := hasBLift_neighbour_linear_two hset hK e (by omega) htC ht hab hX₀ hX₀c
    rfl rfl
  have hB : HasBLift Kc := (hBl Kc hKcomp hsN hsC).1
  refine nonempty_fieldNeighbourParam_of_component_two hK e ι σ eN (by omega) hD htX hcore hB hsN
    ψ ?_ hψτ
  intro x hx hk
  have h1 : (⟨_, hk⟩ : Kc) = ε (LinearFlag.proj (n - 2) K x) := Subtype.ext (by rw [hεapp]; rfl)
  rw [h1, hψε, projMap_proj]

end FieldKind

end CFSG.SeitzReduction.LinearPilot
