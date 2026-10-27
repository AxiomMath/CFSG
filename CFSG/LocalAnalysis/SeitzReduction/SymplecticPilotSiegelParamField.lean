module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelHR8
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open scoped MatrixGroups

section OfSL

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

theorem coe_siegelLeviEquiv_apply (A : SL(n, F)) :
    ((siegelLeviEquiv A : siegelLevi F n) : StatedSp n F) = leviEmbedSL F n A :=
  rfl

@[expose] noncomputable def SiegelFieldParam.ofSL (Φ : SL(n, F) →* G)
    (hrange : Φ.range = siegelCore e) (hker : Φ.ker ≤ center SL(n, F))
    (hN1 : ∀ x : SL(n, K), Φ (SpecialLinearGroup.map ι x) = ((e.symm (leviEmbedSL K n x) : L) : G))
    (hN2 : ∀ (c : Fin n → Kˣ) (x : SL(n, F)),
      Φ (slConjugation n F (TauCeti.diagGL (liftParam ι c)) x) =
        ((e.symm (diagSp K n c) : L) : G) * Φ x * ((e.symm (diagSp K n c) : L) : G)⁻¹)
    (hN3 : ∀ x : SL(n, F), t * Φ x * t⁻¹ = Φ (SpecialLinearGroup.map σ.toRingHom x)) :
    SiegelFieldParam e t ι σ where
  Φ := Φ.comp siegelLeviEquiv.symm.toMonoidHom
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, hrange]
  ker_le := by
    intro x hx
    have hx' : siegelLeviEquiv.symm x ∈ center SL(n, F) := hker hx
    rw [mem_center_iff] at hx' ⊢
    intro g
    have h := congrArg siegelLeviEquiv (hx' (siegelLeviEquiv.symm g))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  N1 := by
    intro x hx
    obtain ⟨A, rfl⟩ := hx
    have h : (⟨spFieldMap n ι (leviEmbedSL K n A), spFieldMap_mem_siegelLevi ι ⟨A, rfl⟩⟩ :
        siegelLevi F n) = siegelLeviEquiv (SpecialLinearGroup.map ι A) :=
      Subtype.ext (spFieldMap_leviEmbedSL ι A)
    rw [h, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hN1]
  N2 := by
    intro c _ x
    obtain ⟨A, rfl⟩ := siegelLeviEquiv.surjective x
    have h : conjDiagSub ι diagSp_mem_normalizer_siegelLevi c (siegelLeviEquiv A) =
        siegelLeviEquiv (slConjugation n F (TauCeti.diagGL (liftParam ι c)) A) :=
      Subtype.ext (by
        rw [coe_conjDiagSub_apply, coe_siegelLeviEquiv_apply, coe_siegelLeviEquiv_apply,
          diagSp_mul_leviEmbedSL_mul_inv])
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, hN2]
  N3 := by
    intro x
    obtain ⟨A, rfl⟩ := siegelLeviEquiv.surjective x
    have h : fieldSiegel σ (siegelLeviEquiv A) =
        siegelLeviEquiv (SpecialLinearGroup.map σ.toRingHom A) :=
      Subtype.ext (by
        rw [coe_fieldSiegel_apply, coe_siegelLeviEquiv_apply, coe_siegelLeviEquiv_apply,
          spFieldMap_leviEmbedSL])
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, hN3]

end OfSL

section Embed

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

theorem symm_leviEmbedSL_mem_centralizer (x : SL(n, K)) :
    ((e.symm (leviEmbedSL K n x) : L) : G) ∈
      centralizer (modelToG e (siegelTorus K n) : Set G) :=
  LinearPilot.map_symm_le_centralizer_map_symm e
    (siegelLevi_le_siegelLeviGL.trans siegelLeviGL_le_centralizer_siegelTorus)
    (symm_mem_modelToG e ⟨x, rfl⟩)

@[expose] noncomputable def siegelBlockHom :
    SL(n, K) →* centralizer (modelToG e (siegelTorus K n) : Set G) :=
  MonoidHom.codRestrict (L.subtype.comp (e.symm.toMonoidHom.comp (leviEmbedSL K n))) _
    (symm_leviEmbedSL_mem_centralizer e)

@[expose] noncomputable def siegelBarHom :
    SL(n, K) →* centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
      oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)) :=
  (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))).comp
    (siegelBlockHom e)

theorem range_siegelBlockHom :
    (siegelBlockHom e).range = (modelToG e (siegelLevi K n)).subgroupOf
      (centralizer (modelToG e (siegelTorus K n) : Set G)) := by
  ext ⟨g, hg⟩
  rw [mem_subgroupOf, MonoidHom.mem_range]
  change (∃ x, siegelBlockHom e x = ⟨g, hg⟩) ↔ g ∈ modelToG e (siegelLevi K n)
  constructor
  · rintro ⟨x, hx⟩
    have hx' : ((e.symm (leviEmbedSL K n x) : L) : G) = g := congrArg Subtype.val hx
    rw [← hx']
    exact symm_mem_modelToG e ⟨x, rfl⟩
  · intro h
    obtain ⟨y, ⟨x, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 h
    exact ⟨x, Subtype.ext rfl⟩

theorem range_siegelBarHom :
    (siegelBarHom e).range = ((modelToG e (siegelLevi K n)).subgroupOf
      (centralizer (modelToG e (siegelTorus K n) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))) := by
  rw [siegelBarHom, MonoidHom.range_comp, range_siegelBlockHom]

end Embed

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ}

theorem nonempty_siegelFieldParam_of_fieldRow (e : L ≃* StatedSp n K) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K n) : Set G))
    (hcomp : CFSG.Open.IsComponentOf
      (((modelToG e (siegelLevi K n)).subgroupOf
        (centralizer (modelToG e (siegelTorus K n) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))))
      (centralizer ({(QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (siegelTorus K n) : Set G)))) ⟨t, htX⟩} :
          Set (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
            oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
        oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))), IsPGroup 2 U →
      U ≤ centralizer ((((modelToG e (siegelLevi K n)).subgroupOf
        (centralizer (modelToG e (siegelTorus K n) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))))) :
            Set (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
              oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))) → Nat.card U ≤ 2)
    (hZ : center (((modelToG e (siegelLevi K n)).subgroupOf
        (centralizer (modelToG e (siegelTorus K n) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
      oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))} (hKcomp : IsComponent Kc)
    (hDK : ((modelToG e (siegelLevi K n)).subgroupOf
        (centralizer (modelToG e (siegelTorus K n) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))
        ⟨t, htX⟩ ∈ normalizer (Kc : Set (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
          oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL n 2 (2 * f)) (hB : HasBLift Kc) :
    Nonempty (SiegelFieldParam e t ι σ) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  set Db := ((modelToG e (siegelLevi K n)).subgroupOf
    (centralizer (modelToG e (siegelTorus K n) : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))))
    with hDbdef
  set s := QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))
    ⟨t, htX⟩ with hsdef
  have hF : Nat.card F = 2 ^ (2 * f) :=
    LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have hF5 : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ (2 * 2) := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨F', _, _, hF', ⟨ψ'⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have : Fintype F' := Fintype.ofFinite F'
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF', hF]
  let ψ₀ : Kc ≃* LinearFlag.projectiveSL n F := ψ'.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcardF))
  have hOut := LinearPilot.isSolvable_outer_of_mulEquiv hn ψ₀
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
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKcomp hDK hs hsD hsN hsC hsyl hOut
  have hne : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨ε, hεinj, hεrange, hεapp⟩ := exists_projectiveSL_embedding_of_hom (Kc := Kc) hn
    (siegelBarHom e) (by rw [range_siegelBarHom]; exact hne)
    (by rw [range_siegelBarHom]; exact hZ) (by rw [range_siegelBarHom]; exact hDK)
  rw [range_siegelBarHom] at hεrange
  have hθ : Kc.normalizerMonoidHom ⟨s, hsN⟩ * Kc.normalizerMonoidHom ⟨s, hsN⟩ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN (by rw [← hs]; exact pow_orderOf_eq_one s)
  have hDc : IsComponent (Db.subgroupOf (centralizer ({s} : Set _))) :=
    (isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK
  have hD'c : IsComponent ((Db.subgroupOf Kc).subgroupOf
      (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) :=
    F4Pilot.isComponent_subgroupOf_subgroupOf
      (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
  have hεθ : ε.range ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
    rw [hεrange, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  obtain ⟨ψ, hψε, hψτ⟩ := LinearPilot.exists_mulEquiv_projMap_eq_of_isComponent hn (by omega)
    hKc ι hσ1 hσσ hfix ψ₀ hθ ε hεinj hεθ (by rw [hεrange]; exact hD'c)
  obtain ⟨q, hq, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hδE : ∀ x : SL(n, K), (L.subtype.comp (e.symm.toMonoidHom.comp (leviEmbedSL K n))) x ∈
      centralizerPerfectCore (modelToG e (siegelTorus K n)) :=
    fun x => modelToG_siegelLevi_le_siegelCore e hK4 (by omega) (symm_mem_modelToG e ⟨x, rfl⟩)
  have ht' : t ∈ normalizer (centralizerPerfectCore (modelToG e (siegelTorus K n)) : Set G) :=
    le_normalizer_siegelCore e htL
  have hσι : ∀ c, σ (ι c) = ι c := fun c => (hfix _).2 ⟨c, rfl⟩
  have hσ2 : σ * σ = 1 := hσσ
  obtain ⟨Φ, hrange, hker, hN1, hN2, hN3⟩ := exists_slParam_of_proj (G := G) hn hF5 ι hσ2 hfix
    (E := centralizerPerfectCore (modelToG e (siegelTorus K n)))
    (F4Pilot.commutator_centralizerPerfectCore _) (ψ.toMonoidHom.comp q)
    (ψ.surjective.comp hq)
    (by
      intro y hy
      apply hqker
      have h1 : ψ (q y) = ψ 1 := by
        rw [map_one]
        exact hy
      exact ψ.injective h1)
    (L.subtype.comp (e.symm.toMonoidHom.comp (leviEmbedSL K n))) hδE
    (by
      intro x
      have hqx : q ⟨_, hδE x⟩ = ε (LinearFlag.proj n K x) := by
        apply Subtype.ext
        rw [hqapp, hεapp]
        rfl
      show ψ (q ⟨_, hδE x⟩) = _
      rw [hqx, hψε, LinearPilot.projMap_proj])
    ht'
    (by
      intro y
      have hqt : q ((centralizerPerfectCore (modelToG e (siegelTorus K n))).normalizerMonoidHom
          ⟨t, ht'⟩ y) = Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y) := by
        apply Subtype.ext
        have e1 : (⟨(((centralizerPerfectCore (modelToG e (siegelTorus K n))).normalizerMonoidHom
            ⟨t, ht'⟩ y : centralizerPerfectCore (modelToG e (siegelTorus K n))) : G),
            F4Pilot.centralizerPerfectCore_le_centralizer _
              ((centralizerPerfectCore (modelToG e (siegelTorus K n))).normalizerMonoidHom
                ⟨t, ht'⟩ y).2⟩ :
              centralizer (modelToG e (siegelTorus K n) : Set G)) =
            ⟨t, htX⟩ * ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer _ y.2⟩ *
              ⟨t, htX⟩⁻¹ := by
          apply Subtype.ext
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
          rfl
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp, e1, map_mul, map_mul,
          map_inv]
      show ψ (q ((centralizerPerfectCore (modelToG e (siegelTorus K n))).normalizerMonoidHom
        ⟨t, ht'⟩ y)) = LinearFlag.fieldAut n F σ (ψ (q y))
      rw [hqt, hψτ])
    (fun c => ((e.symm (diagSp K n c) : L) : G)) (fun c => diagSp_mem_normalizer_siegelCore e c)
    (by
      intro c x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype]
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
        ← map_mul, diagSp_mul_leviEmbedSL_mul_inv])
    (by
      intro c
      have hc : c ^ Nat.card Kˣ = 1 := funext fun i => pow_card_eq_one'
      rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, hc, map_one, map_one]
      rfl)
  exact ⟨SiegelFieldParam.ofSL Φ hrange hker hN1 hN2 hN3⟩

end FieldRow

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

@[expose] def SiegelSwapRow (e : L ≃* StatedSp n K) (t : G) : Prop :=
  ∃ htX : t ∈ centralizer (modelToG e (siegelTorus K n) : Set G),
    ∃ Kc : Subgroup (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
      oddCore (centralizer (modelToG e (siegelTorus K n) : Set G))),
      IsComponent Kc ∧
      ((modelToG e (siegelLevi K n)).subgroupOf
          (centralizer (modelToG e (siegelTorus K n) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K n) : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (siegelTorus K n) : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (siegelTorus K n) : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      center Kc = ⊥ ∧
      Nonempty (Kc ≃* ((modelToG e (siegelLevi K n)).subgroupOf
          (centralizer (modelToG e (siegelTorus K n) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))))

theorem siegel_normal_or_fieldParam_or_swap {f : ℕ}
    (hcat : LinearPilot.SLmCatalogueClausesAt n) (hdet : LinearPilot.SLmEvenTypeDetAt n)
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    (t ∈ centralizer (modelToG e (siegelTorus K n) : Set G) ∧
        (((modelToG e (siegelLevi K n)).subgroupOf
          (centralizer (modelToG e (siegelTorus K n) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (siegelTorus K n) : Set G))))).Normal) ∨
      Nonempty (SiegelFieldParam e t ι σ) ∨ SiegelSwapRow e t := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨htX, hnorm | ⟨⟨Kc, hKcomp, hDKK, ⟨-, hDK, -, hsN, hτ, -, hmodel, -⟩ | hswap⟩, hZ⟩⟩ :=
    siegel_normal_or_overgroup_field (X := modelToG e (siegelTorus K n))
      (D := modelToG e (siegelLevi K n)) hcat hdet hset hKc hf hn e htC ht rfl rfl
  · exact Or.inl ⟨htX, hnorm⟩
  · right; left
    obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_siegelTorus_of_seitzSetting
      (X := modelToG e (siegelTorus K n)) (D := modelToG e (siegelLevi K n)) hset hKc hq hn e
      htC ht rfl htX rfl
    have hsC : QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (siegelTorus K n) : Set G))) ⟨t, htX⟩ ∉
          centralizer (Kc : Set (centralizer (modelToG e (siegelTorus K n) : Set G) ⧸
            oddCore (centralizer (modelToG e (siegelTorus K n) : Set G)))) := by
      intro h
      apply hτ
      have h1 : (⟨_, hsN⟩ : normalizer (Kc : Set _)) ∈ Kc.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact h
      exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
    obtain ⟨-, -, hBl⟩ := bLift_neighbour_siegelTorus_of_seitzSetting
      (X := modelToG e (siegelTorus K n)) (D := modelToG e (siegelLevi K n)) hset hKc hq hn e
      htC ht rfl htX rfl
    have hB : HasBLift Kc := hBl Kc (Subgroup.isPerfect_iff.mp hKcomp.1.1) hsN
      (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKcomp.1 hsN hsC)
    exact nonempty_siegelFieldParam_of_fieldRow e hKc hf hn htC ht ι hσ1 hσσ hfix htX hcomp hsyl
      hZ hKcomp hDK.le hsN hτ hmodel hB
  · exact Or.inr (Or.inr ⟨htX, Kc, hKcomp, hDKK, hswap⟩)

end Seitz

end CFSG.SeitzReduction.SymplecticPilot
