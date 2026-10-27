module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalEmbed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamBLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionBasic
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionGenericSetting
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  {F : Type} [Field F] [Finite F]

theorem nonempty_fieldNeighbourParam_of_fieldRow (e : L ≃* LinearFlag.projectiveSL n K)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (Nb : Neighbour n) {m : ℕ}
    (eN : Nb.index ≃ Fin m) (hm : 3 ≤ m)
    (htX : t ∈ centralizer (modelToG e (Nb.torus K) : Set G))
    (hcomp : CFSG.Open.IsComponentOf
      (((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))))
      (centralizer ({(QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))
        ⟨t, htX⟩)} : Set (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
          oddCore (centralizer (modelToG e (Nb.torus K) : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
        oddCore (centralizer (modelToG e (Nb.torus K) : Set G))), IsPGroup 2 U →
      U ≤ centralizer ((((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))))) :
            Set (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
              oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) → Nat.card U ≤ 2)
    (hZ : center (((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
      oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))} (hKcomp : IsComponent Kc)
    (hDK : ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
        oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL m 2 (2 * f)) (hB : HasBLift Kc) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (Nb.torus K)) Nb.index) := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  have : CharP K 2 := charP_two_of_card_eq_two_pow hKc
  set Db := ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
    (centralizer (modelToG e (Nb.torus K) : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) with hDbdef
  set s := QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))) ⟨t, htX⟩
    with hsdef
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have hF5 : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ (2 * 2) := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨F', _, _, hF', ⟨ψ'⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have : Fintype F' := Fintype.ofFinite F'
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF', hF]
  let ψ₀ : Kc ≃* LinearFlag.projectiveSL m F := ψ'.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcardF))
  have hOut := isSolvable_outer_of_mulEquiv hm ψ₀
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
  have hne : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨ε, hεinj, hεrange, hεapp⟩ := exists_projectiveSL_embedding e Nb eN hm hne hZ hDK
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
    rw [hεrange, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  obtain ⟨ψ, hψε, hψτ⟩ := exists_mulEquiv_projMap_eq_of_isComponent hm (by omega) hKc ι hσ1 hσσ
    hfix ψ₀ hθ ε hεinj hεθ (by rw [hεrange]; exact hD'c)
  refine nonempty_fieldNeighbourParam_of_component e htL ι hσσ hfix Nb eN hm hF5 htX hcore hB hsN
    ψ ?_ hψτ
  intro x hx hk
  have h1 : (⟨_, hk⟩ : Kc) = ε (LinearFlag.proj m K x) := Subtype.ext (by rw [hεapp]; rfl)
  rw [h1, hψε, projMap_proj]

end FieldRow

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def RootTorusSwapRow {n : ℕ} {K : Type} [Field K] (e : L ≃* LinearFlag.projectiveSL n K)
    (t : G) {a b : Fin n} (hab : a ≠ b) : Prop :=
  ∃ htX : t ∈ centralizer (modelToG e (rootTorus (K := K) hab) : Set G),
    ∃ Kc : Subgroup (centralizer (modelToG e (rootTorus (K := K) hab) : Set G) ⧸
      oddCore (centralizer (modelToG e (rootTorus (K := K) hab) : Set G))),
      IsComponent Kc ∧
      ((modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))).subgroupOf
          (centralizer (modelToG e (rootTorus (K := K) hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (rootTorus (K := K) hab) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (rootTorus (K := K) hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (rootTorus (K := K) hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (rootTorus (K := K) hab) : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      center Kc = ⊥ ∧
      Nonempty (Kc ≃* ((modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))).subgroupOf
          (centralizer (modelToG e (rootTorus (K := K) hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (rootTorus (K := K) hab) : Set G)))))

theorem nonempty_fieldNeighbourParam_rootTorus_or_swap (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) (hdet : SLmEvenTypeDetAt (n - 2)) {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n}
    (hab : a ≠ b) {g y : G}
    (hyD : y ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))) (hy : orderOf y = 2)
    (hg : g⁻¹ * t * g = t * y)
    (hyP : ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ P ≤ L ∧ y ∈ P ∧ P ≤ centralizer ({y} : Set G))
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin n))ᶜ)) ∨
      RootTorusSwapRow e t hab := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have htX : t ∈ centralizer (modelToG e (rootTorus (K := K) hab) : Set G) :=
    mem_centralizer_map_symm e _ htC
  obtain ⟨hcomp, hsyl, -⟩ :=
    neighbour_standard_rootTorus_of_seitzSetting (X := modelToG e (rootTorus (K := K) hab))
      (D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))) hset hKc hf e hn htC ht
      hab rfl htX rfl
  obtain ⟨⟨Kc, hKcomp, hDKK, ⟨hKt, hDK, hsK, hsN, hτ, -, hmodel, -⟩ | hswap⟩, hZ⟩ :=
    neighbour_overgroup_rootTorus_field (X := modelToG e (rootTorus (K := K) hab))
      (D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))) hset hcat hdet hKc hf e
      hn htC ht hab rfl htX rfl hyD hy hg
  · left
    have hDperf : Group.IsPerfect (((modelToG e (blockSL (K := K)
        (({a, b} : Finset (Fin n))ᶜ))).subgroupOf
          (centralizer (modelToG e (rootTorus (K := K) hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (rootTorus (K := K) hab) : Set G))))) := ⟨hcomp.2.2.1⟩
    have hne := ne_bot_of_isQuasisimple hcomp.2.2
    have hKD : ⁅Kc, ((modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))).subgroupOf
        (centralizer (modelToG e (rootTorus (K := K) hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (rootTorus (K := K) hab) : Set G))))⁆ ≠ ⊥ := by
      intro h
      apply hne
      have h1 := Subgroup.commutator_mono hDK.le
        (le_refl (((modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))).subgroupOf
          (centralizer (modelToG e (rootTorus (K := K) hab) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (rootTorus (K := K) hab) : Set G))))))
      rw [h, isPerfect_iff.mp hDperf] at h1
      exact le_bot_iff.mp h1
    obtain ⟨-, -, hBl⟩ :=
      bLift_rootTorus_of_fused_of_seitzSetting (X := modelToG e (rootTorus (K := K) hab))
        (D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))) hset hKc hq e hn htC ht
        hab rfl rfl hyD hy hg hyP
    have hB := (hBl Kc Kc hKcomp hKcomp hKD hKD).1
    have hcard : Fintype.card ((Neighbour.root a b hab).index) = n - 2 := by
      rw [Fintype.card_coe, Neighbour.index_root, Finset.card_compl, Fintype.card_fin,
        Finset.card_pair hab]
    exact nonempty_fieldNeighbourParam_of_fieldRow e hKc hf htC ht ι hσ1 hσσ hfix
      (.root a b hab) (Fintype.equivFinOfCardEq hcard) (by omega) htX hcomp hsyl hZ hKcomp hDK.le
      hsN hτ hmodel hB
  · exact Or.inr ⟨htX, Kc, hKcomp, hDKK, hswap⟩

omit [Finite G] in
theorem exists_perfect_le_centralizer_of_isInvolutionClass_one {n : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n)
    (hnK : 5 ≤ n ∨ 4 ≤ Nat.card K) {y : L} (hy : IsInvolutionClass 1 (e y)) :
    ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ P ≤ L ∧ (y : G) ∈ P ∧
      P ≤ centralizer ({(y : G)} : Set G) := by
  refine ⟨modelToG e (perfectCore (centralizer ({e y} : Set (LinearFlag.projectiveSL n K)))),
    modelToG_perfect e (CFSG.Quasithin.perfectCore_perfect _), modelToG_le e _,
    (mem_modelToG e).2 ⟨e y, mem_perfectCore_centralizer_transvection' hn hnK hy, by simp⟩, ?_⟩
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  have hxc : x * e y = e y * x :=
    mem_centralizer_singleton_iff.mp (CFSG.Quasithin.perfectCore_le _ hx)
  rw [mem_centralizer_singleton_iff]
  have h1 := congrArg (fun z => ((e.symm z : L) : G)) hxc
  simpa only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul] using h1

theorem nonempty_fieldNeighbourParam_rootTorus_or_swap_of_transvection (hset : SeitzSetting G L)
    {n f : ℕ} (hcat : SLmCatalogueClausesAt (n - 2)) (hdet : SLmEvenTypeDetAt (n - 2))
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    {a b : Fin n} (hab : a ≠ b) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin n))ᶜ)) ∨
      RootTorusSwapRow e t hab := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  obtain ⟨g, y, hy1, hyD, hg⟩ := exists_conj_eq_mul_mem_blockSL_compl_pair e
    (le_centralizer_of_mem_centralizer htC) (by omega) hab hR5
  have hyG : (y : G) ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ)) :=
    (mem_modelToG e).2 ⟨e y, hyD, by simp⟩
  have hy2 : orderOf (y : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e y]
    exact hy1.orderOf_eq_two one_ne_zero
  exact nonempty_fieldNeighbourParam_rootTorus_or_swap hset hcat hdet hKc hf e hn htC ht hab hyG
    hy2 hg (exists_perfect_le_centralizer_of_isInvolutionClass_one e (by omega) (Or.inl hn) hy1)
    ι hσ1 hσσ hfix

end Seitz

end CFSG.SeitzReduction.LinearPilot
