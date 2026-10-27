module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandardSetting
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2BLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamCore
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

section Schur

theorem exists_section_specialLinear_four_of_card_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin 4) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) :
    ∃ s : SpecialLinearGroup (Fin 4) F →* E, ∀ g, π (s g) = g :=
  CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating (m := 3)
    (by norm_num)
    (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by norm_num) (by omega)
      (by omega) (by omega)) hπ hcen

theorem exists_surjective_lift_four_of_card_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {E : Type*} [Group E] [Group.IsPerfect E]
    {p : E →* LinearFlag.projectiveSL 4 F} (hp : Function.Surjective p)
    (hpker : p.ker ≤ center E) :
    ∃ Φ : SpecialLinearGroup (Fin 4) F →* E, (∀ x, p (Φ x) = LinearFlag.proj 4 F x) ∧
      Function.Surjective Φ ∧ Φ.ker ≤ center (SpecialLinearGroup (Fin 4) F) := by
  obtain ⟨s, hs⟩ := exists_section_specialLinear_four_of_card_four hF
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := LinearFlag.proj 4 F) hp)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center hpker)
  let Φ : SpecialLinearGroup (Fin 4) F →* E :=
    ((MonoidHom.snd _ E).comp
      (CFSG.LieType.Steinberg.pullback (LinearFlag.proj 4 F) p).subtype).comp s
  have hΦ : ∀ x, p (Φ x) = LinearFlag.proj 4 F x := fun x => by
    have hmem := CFSG.LieType.Steinberg.mem_pullback.1 (s x).2
    have h1 : ((s x : CFSG.LieType.Steinberg.pullback (LinearFlag.proj 4 F) p) :
        SpecialLinearGroup (Fin 4) F × E).1 = x := hs x
    change p ((s x : CFSG.LieType.Steinberg.pullback (LinearFlag.proj 4 F) p) :
      SpecialLinearGroup (Fin 4) F × E).2 = _
    rw [← hmem, h1]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · have hdecomp : ∀ y : E, ∃ x, y * (Φ x)⁻¹ ∈ center E := fun y => by
      obtain ⟨x, hx⟩ := LinearFlag.proj_surjective 4 F (p y)
      exact ⟨x, hpker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ, hx, mul_inv_cancel])⟩
    have hcomm : commutator E ≤ Φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro y _ z _
      obtain ⟨x, hx⟩ := hdecomp y
      obtain ⟨x', hx'⟩ := hdecomp z
      have e : ⁅y, z⁆ = ⁅Φ x, Φ x'⁆ := by
        have h := CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hx hx' (Φ x)
          (Φ x')
        rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
      rw [e, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro y
    exact hcomm (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top y)
  · intro x hx
    have h1 : LinearFlag.proj 4 F x = 1 := by rw [← hΦ, MonoidHom.mem_ker.1 hx, map_one]
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.scalars_eq_center] at h1
    exact h1

end Schur

section FromProj

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem nonempty_fieldNeighbourParam_of_proj_of_lift [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F) (σ : F ≃+* F)
    {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm : 3 ≤ m)
    (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m F)
    (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hlift : ∃ Φ₀ : SpecialLinearGroup (Fin m) F →* centralizerPerfectCore X,
      (∀ x, p (Φ₀ x) = LinearFlag.proj m F x) ∧ Function.Surjective Φ₀ ∧
        Φ₀.ker ≤ center (SpecialLinearGroup (Fin m) F))
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : SpecialLinearGroup (Fin m) K,
      p ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (h3 : ∀ y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
      LinearFlag.fieldAut m F σ (p y))
    (hg : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G))
    (h2 : ∀ c y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg c⟩ y) =
      LinearFlag.conjAut m F (unitDiagGL (torusBlockUnits ι eN c)) (p y)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) := by
  set E := centralizerPerfectCore X with hE
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  obtain ⟨Φ₀, hΦ₀, hsurj, hker⟩ := hlift
  let ψ₁ : SpecialLinearGroup (Fin m) K →* E :=
    MonoidHom.codRestrict (L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj n K).comp
      ((blockSpecialLinear (K := K) N).subtype.comp (blockSLEquiv N eN).toMonoidHom)))) E
      (fun x => hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2)))
  have hN1 : Φ₀.comp (SpecialLinearGroup.map ι) = ψ₁ :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, hΦ₀]
      exact (h1 x).symm
  have hN3 : (E.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (SpecialLinearGroup.map σ.toRingHom) :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h3, hΦ₀, hΦ₀,
        LinearFlag.fieldAut_proj]
  have hN2 : ∀ c, (E.normalizerMonoidHom ⟨_, hg c⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m F
        (unitDiagGL (torusBlockUnits ι eN c))).toMonoidHom := fun c =>
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, h2, hΦ₀, hΦ₀, LinearFlag.conjAut_proj]
  let Φ : blockSpecialLinear (K := F) N →* G :=
    E.subtype.comp (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom)
  have hΦ : ∀ x', Φ (blockSLEquiv N eN x') = (Φ₀ x' : G) := fun x' => by
    change ((Φ₀ ((blockSLEquiv N eN).symm (blockSLEquiv N eN x')) : E) : G) = _
    rw [MulEquiv.symm_apply_apply]
  refine ⟨⟨Φ, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hs : Function.Surjective (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom) := fun y => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨blockSLEquiv N eN x, by simp⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs, ← MonoidHom.range_eq_map,
      range_subtype]
  ·
    intro x hx
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    have hx' : Φ₀ x' = 1 := by
      apply Subtype.ext
      rw [← hΦ]
      exact hx
    have hz := hker hx'
    rw [mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := (blockSLEquiv N eN).surjective y
    rw [← map_mul, ← map_mul, hz y']
  ·
    intro x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    have hx : (⟨SpecialLinearGroup.map ι (blockSLEquiv N eN x' : SpecialLinearGroup (Fin n) K),
        map_ringHom_mem_blockSpecialLinear ι (blockSLEquiv N eN x').2⟩ :
          blockSpecialLinear (K := F) N) = blockSLEquiv N eN (SpecialLinearGroup.map ι x') :=
      Subtype.ext (blockSLEquiv_map ι N eN x').symm
    rw [hx, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) K →* E => (φ x' : G)) hN1
    exact this
  ·
    intro c x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [conjDiag_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) F →* E => (φ x' : G)) (hN2 c)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this.symm
  ·
    intro x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [mapBlock_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) F →* E => (φ x' : G)) hN3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this

end FromProj

section Four

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem nonempty_fieldNeighbourParam_of_proj_two_four [Finite G] [Finite F] (hK : Nat.card K = 2)
    (hF : Nat.card F = 4) (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F)
    (σ : F ≃+* F) {X : Subgroup G} {N : Finset (Fin n)} (eN : N ≃ Fin 4)
    (p : centralizerPerfectCore X →* LinearFlag.projectiveSL 4 F)
    (hp : Function.Surjective p) (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : SpecialLinearGroup (Fin 4) K,
      p ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        LinearFlag.proj 4 F (SpecialLinearGroup.map ι x))
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (h3 : ∀ y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
      LinearFlag.fieldAut 4 F σ (p y)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) := by
  have : Group.IsPerfect (centralizerPerfectCore X) :=
    Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have := subsingleton_units_of_natCard_eq_two hK
  have hc1 : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c = 1 :=
    fun c => Subsingleton.elim _ _
  have hg1 : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) = 1 := fun c => by
    rw [hc1 c, map_one, map_one, map_one, L.coe_one]
  have hg : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G) := fun c => by
    rw [hg1 c]
    exact one_mem _
  refine nonempty_fieldNeighbourParam_of_proj_of_lift e t ι σ eN (by norm_num) p hpker
    (exists_surjective_lift_four_of_card_four hF hp hpker) hD h1 ht h3 hg fun c y => ?_
  have hunits : torusBlockUnits ι eN c = 1 := by
    rw [hc1 c]
    funext a
    simp [torusBlockUnits]
  have hy : (centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg c⟩ y = y := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hg1 c, one_mul, inv_one, mul_one]
  rw [hy, hunits, unitDiagGL_one, map_one, MulAut.one_apply]

theorem nonempty_fieldNeighbourParam_of_component_two_four [Finite G] [Finite F]
    (hK : Nat.card K = 2) (hF : Nat.card F = 4) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ι : K →+* F) (σ : F ≃+* F) {X : Subgroup G} {N : Finset (Fin n)} (eN : N ≃ Fin 4)
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (htX : t ∈ centralizer (X : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hcore : perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G)))) = Kc) (hB : HasBLift Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (ψ : Kc ≃* LinearFlag.projectiveSL 4 F)
    (hψD : ∀ (x : SpecialLinearGroup (Fin 4) K)
      (hx : ((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G) ∈
        centralizer (X : Set G))
      (hk : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨_, hx⟩ ∈ Kc),
      ψ ⟨_, hk⟩ = LinearFlag.proj 4 F (SpecialLinearGroup.map ι x))
    (hψt : ∀ k : Kc, ψ (Kc.normalizerMonoidHom ⟨_, hsN⟩ k) = LinearFlag.fieldAut 4 F σ (ψ k)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) := by
  obtain ⟨q, hq, hqker, hqapp⟩ :=
    exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have ht : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ htX)
  refine nonempty_fieldNeighbourParam_of_proj_two_four hK hF e t ι σ eN
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
      LinearFlag.fieldAut 4 F σ (ψ (q y))
    rw [hqt, hψt]

end Four

section FieldKind

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_fieldNeighbourParam_of_fieldKind_two_six (hset : SeitzSetting G L) {n : ℕ}
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : n = 6) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
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
  subst hn
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : Finite K := finite_of_card_eq_two_pow hK1
  have hNcard : ({a, b}ᶜ : Finset (Fin 6)).card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  let eN : ({a, b}ᶜ : Finset (Fin 6)) ≃ Fin 4 :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hNcard])
  set Db := ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 6)))).subgroupOf
    (centralizer (modelToG e X₀ : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) with hDbdef
  set s := QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ with hsdef
  have hF : Nat.card F = 2 ^ (2 * 1) := natCard_eq_two_pow_of_fixedField hK1 ι hσ1 hσσ hfix
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have hNab : Disjoint ({a, b}ᶜ : Finset (Fin 6)) ({a, b} : Finset (Fin 6)) := disjoint_compl_left
  have hDC : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 6))) ≤
      centralizer (modelToG e X₀ : Set G) :=
    modelToG_le_centralizer e ((blockSL_le_centralizer_blockSL_of_disjoint hNab).trans
      (centralizer_le hX₀))
  have hD : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 6))) ≤
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
  let ψ₀ : Kc ≃* LinearFlag.projectiveSL 4 F := ψ'.trans
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
  have hmemC : ∀ x : SpecialLinearGroup (Fin 4) K,
      ((e.symm (LinearFlag.proj 6 K (blockSLEquiv ({a, b}ᶜ : Finset (Fin 6)) eN x)) : L) : G) ∈
        centralizer (modelToG e X₀ : Set G) :=
    fun x => hDC (symm_mem_modelToG e
      (proj_mem_blockSL (blockSLEquiv ({a, b}ᶜ : Finset (Fin 6)) eN x).2))
  let φ₀ : SpecialLinearGroup (Fin 4) K →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj 6 K).comp
      ((blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin 6))).subtype.comp
        (blockSLEquiv ({a, b}ᶜ : Finset (Fin 6)) eN).toMonoidHom)))
  let φ : SpecialLinearGroup (Fin 4) K →*
      centralizer (modelToG e X₀ : Set G) ⧸ oddCore (centralizer (modelToG e X₀ : Set G)) :=
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))).comp
      (φ₀.codRestrict (centralizer (modelToG e X₀ : Set G)) hmemC)
  have hφ : φ.range = Db := by
    ext k
    constructor
    · rintro ⟨x, rfl⟩
      rw [hDbdef]
      exact Subgroup.mem_map.2 ⟨⟨_, hmemC x⟩, mem_subgroupOf.2
        (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv ({a, b}ᶜ : Finset (Fin 6)) eN x).2)),
        rfl⟩
    · intro hk
      rw [hDbdef] at hk
      obtain ⟨y, hy, rfl⟩ := hk
      obtain ⟨z, hz, hzy⟩ := (mem_modelToG e).1 (mem_subgroupOf.1 hy)
      obtain ⟨A, hA, rfl⟩ := mem_blockSL.1 hz
      refine ⟨(blockSLEquiv ({a, b}ᶜ : Finset (Fin 6)) eN).symm ⟨A, hA⟩, ?_⟩
      apply congrArg (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))
      apply Subtype.ext
      show φ₀ ((blockSLEquiv ({a, b}ᶜ : Finset (Fin 6)) eN).symm ⟨A, hA⟩) = (y : G)
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
  obtain ⟨ψ, hψε, hψτ⟩ := exists_mulEquiv_projMap_eq_of_isComponent (n := 4) (by omega)
    (f := 1) le_rfl hK1 ι hσ1 hσσ hfix ψ₀ hθ ε hεinj hεθ (by rw [hεrange, hφ]; exact hD'c)
  obtain ⟨htX', -, -, hBl⟩ := hasBLift_neighbour_linear_two hset hK e (by omega) htC ht hab hX₀ hX₀c
    rfl rfl
  have hB : HasBLift Kc := (hBl Kc hKcomp hsN hsC).1
  refine nonempty_fieldNeighbourParam_of_component_two_four hK hF4 e ι σ eN hD htX hcore hB hsN
    ψ ?_ hψτ
  intro x hx hk
  have h1 : (⟨_, hk⟩ : Kc) = ε (LinearFlag.proj 4 K x) := Subtype.ext (by rw [hεapp]; rfl)
  rw [h1, hψε, projMap_proj]

end FieldKind

section RevComm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def LinearTwoFieldRevCommSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → n = 6 →
    ∀ (e : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (F : Type) [Field F] [Finite F] (ι : K →+* F) (σ : F ≃+* F), σ ≠ 1 → σ * σ = 1 →
      (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
    ∀ (Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)),
      (∀ a b, Xr a b ≤ rootSL2 a b) → (∀ a b, a ≠ b → Nat.card (Xr a b) = Nat.card K + 1) →
    ∀ (P : ∀ a b : Fin n, a ≠ b →
        FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n))),
      FieldRevComm e P

theorem false_of_fieldKind_two_six_of_revComm (hrev : LinearTwoFieldRevCommSixInput)
    (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : n = 6) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {a b : Fin n}
    (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
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
    (hmodel : LieModel Kc .PSL (n - 2) 2 (2 * 1)) : False := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := exists_subfield_involution (F := GaloisField 2 (2 * 1)) le_rfl
    hK1 (GaloisField.card 2 (2 * 1) (by norm_num))
  have hσι : ∀ c : K, σ (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  have hP := nonempty_fieldNeighbourParam_of_fieldKind_two_six hset hK e hn htC ht ι hσ1 hσσ hfix
    hab hX₀ hX₀c htX hZ hKcomp hDK hsN hτ hmodel
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have key : ∀ a' b' : Fin (m + 1), a' ≠ b' → ∃ Y : Subgroup (LinearFlag.projectiveSL (m + 1) K),
      Y ≤ rootSL2 a' b' ∧ Nat.card Y = Nat.card X₀ ∧
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e Y) ({a', b'}ᶜ : Finset (Fin (m + 1)))) :=
    fun a' b' hab' => exists_fieldNeighbourParam_of_one e htC ι hσι hab hX₀ hP hab'
  choose! Y hY1 hY2 hY3 using key
  classical
  set X₁ : Fin (m + 1) → Fin (m + 1) → Subgroup (LinearFlag.projectiveSL (m + 1) K) :=
    fun a' b' => if a' = b' then ⊥ else Y a' b' with hX₁
  have hX₁eq : ∀ a' b', a' ≠ b' → X₁ a' b' = Y a' b' := fun a' b' h => by simp [hX₁, h]
  have hX₁bot : ∀ a' b', a' = b' → X₁ a' b' = ⊥ := fun a' b' h => by simp [hX₁, h]
  have hXr : ∀ a' b', X₁ a' b' ≤ rootSL2 a' b' := fun a' b' => by
    by_cases h : a' = b'
    · rw [hX₁bot a' b' h]
      exact bot_le
    · rw [hX₁eq a' b' h]
      exact hY1 a' b' h
  have hXc : ∀ a' b', a' ≠ b' → Nat.card (X₁ a' b') = Nat.card K + 1 := fun a' b' h => by
    rw [hX₁eq a' b' h, hY2 a' b' h, hX₀c]
  let P : ∀ a' b' : Fin (m + 1), a' ≠ b' →
      FieldNeighbourParam e t ι σ (modelToG e (X₁ a' b')) ({a', b'}ᶜ : Finset (Fin (m + 1))) :=
    fun a' b' h => (show Nonempty (FieldNeighbourParam e t ι σ (modelToG e (X₁ a' b'))
      ({a', b'}ᶜ : Finset (Fin (m + 1)))) by rw [hX₁eq a' b' h]; exact hY3 a' b' h).some
  have hrc : FieldRevComm e P :=
    hrev G L hset (m + 1) K hK hn e t ht hKt (GaloisField 2 (2 * 1)) ι σ hσ1 hσσ hfix X₁ hXr hXc P
  exact false_of_fieldRow_compl hset (by omega) hK1 le_rfl e ht hKt ι hσ1 hσσ hfix hXr P hrc

end RevComm

end CFSG.SeitzReduction.LinearPilot
