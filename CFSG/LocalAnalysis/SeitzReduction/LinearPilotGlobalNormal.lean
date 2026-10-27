module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalSubfield
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalDescent
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore)
open CFSG.EvenSmallLie (StandardSetting)

section Perfect

variable {n : ℕ} {K : Type*} [Field K]

theorem isQuasisimple_projectiveSL (hn : 3 ≤ n) : CFSG.IsQuasisimple (projectiveSL n K) := by
  have hs : IsSimpleGroup (projectiveSL n K) := OutcomeLocal.isSimpleGroup_projectiveSL hn
  have hperf : Group.IsPerfect (projectiveSL n K) :=
    ⟨by rw [commutator_def]; exact commutator_projectiveSL_eq_top hn⟩
  have hZ : center (projectiveSL n K) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn
  let e : projectiveSL n K ⧸ center (projectiveSL n K) ≃* projectiveSL n K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨a, b, hab⟩ : ∃ a b : projectiveSL n K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hc : center (projectiveSL n K) = ⊤ :=
      eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun y => h y x
    rw [hZ] at hc
    exact bot_ne_top hc
  exact ⟨hperf, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab (by
    simpa using congrArg e h)⟩

theorem commutator_eq_self_of_mulEquiv_projectiveSL {G : Type*} [Group G] {L : Subgroup G}
    (hn : 3 ≤ n) (e : L ≃* projectiveSL n K) : ⁅L, L⁆ = L := by
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    have h := congrArg (Subgroup.map (e.symm : projectiveSL n K →* L))
      (commutator_projectiveSL_eq_top (K := K) hn)
    rwa [map_commutator, map_top_of_surjective _ e.symm.surjective] at h
  have hL : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [← hL, ← map_commutator, htop]

end Perfect

section Normalize

variable {n : ℕ} {K F : Type} [Field K] [Finite K] [Field F] [Finite F] [CharP F 2]

omit [Finite K] [CharP F 2] in
theorem natCard_eq_sq_of_fixedField (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nat.card F = Nat.card K ^ 2 := by
  have hσ2 : σ ^ 2 = 1 := by rw [sq, hσσ]
  rw [CatalogueBHigherLinearField.fixedField_card_square F σ hσ2 hσ1]
  congr 1
  rw [← Nat.card_range_of_injective ι.injective]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    (CatalogueBHigherLinearField.mem_fixedField F σ x).trans (hfix x))

theorem exists_mulEquiv_projMap_eq (hn : 3 ≤ n) (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {M : Type} [Group M]
    (ψ₀ : M ≃* projectiveSL n F) {θ : MulAut M} (hθ : θ * θ = 1) (ε : projectiveSL n K →* M)
    (hε : Function.Injective ε) (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ ψ : M ≃* projectiveSL n F, (∀ x, ψ (ε x) = projMap n ι x) ∧
      ∀ y, ψ (θ y) = fieldAut n F σ (ψ y) := by
  have : CharP K 2 := ι.charP ι.injective 2
  have : Finite M := Finite.of_equiv _ ψ₀.symm.toEquiv
  obtain ⟨f, hf, hK⟩ := exists_natCard_eq_two_pow_of_charP K
  have hF : Nat.card F = 2 ^ (2 * f) := by
    rw [natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix, hK, ← pow_mul, mul_comm]
  have hσι : ∀ c, σ (ι c) = ι c := fun c => (hfix _).mpr ⟨c, rfl⟩
  set β₀ := MulAut.congr ψ₀ θ with hβ₀def
  have hβ₀ : β₀ * β₀ = 1 := by rw [hβ₀def, ← map_mul, hθ, map_one]
  set Fx := fixedSubgroup θ with hFx
  set D₀ := perfectCore Fx with hD₀
  have hD₀F : D₀ ≤ Fx := CFSG.Quasithin.perfectCore_le Fx
  let eD₀ : projectiveSL n K ≃* D₀.subgroupOf Fx :=
    ((MonoidHom.ofInjective hε).trans (MulEquiv.subgroupCongr hεr)).trans
      (subgroupOfEquivOfLe hD₀F).symm
  have hcomp : IsComponent (D₀.subgroupOf Fx) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eD₀ (isQuasisimple_projectiveSL hn),
      (CFSG.Quasithin.perfectCore_normal Fx).isSubnormal⟩
  have hm : LieModel (D₀.subgroupOf Fx) .PSL n 2 f :=
    lieModel_of_mulEquiv_projectiveSL hn hf hK eD₀.symm
  let Ψ := fixedSubgroupCongrEquiv ψ₀ θ
  obtain ⟨H, hH⟩ := eq_conj_fieldAut_conj_inv_of_isComponent hn hf hF hσ1 hσσ hβ₀
    (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hcomp)
    (LieType.CurtisTits.lieModel_of_mulEquiv
      ((D₀.subgroupOf Fx).equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hm)
  set ψ₁ : M ≃* projectiveSL n F := ψ₀.trans (conjAut n F H)⁻¹ with hψ₁
  have hψ₁θ : ∀ y, ψ₁ (θ y) = fieldAut n F σ (ψ₁ y) := by
    intro y
    have h1 : ψ₀ (θ y) = β₀ (ψ₀ y) := by
      rw [hβ₀def]
      change ψ₀ (θ y) = ψ₀ (θ (ψ₀.symm (ψ₀ y)))
      rw [MulEquiv.symm_apply_apply]
    calc ψ₁ (θ y) = ((conjAut n F H)⁻¹ * β₀) (ψ₀ y) := by
          rw [hψ₁, MulEquiv.trans_apply, h1]
          rfl
      _ = (fieldAut n F σ * (conjAut n F H)⁻¹) (ψ₀ y) := by
          congr 1
          rw [hH]
          group
      _ = fieldAut n F σ (ψ₁ y) := rfl
  have hfixmap : (fixedSubgroup θ).map ψ₁.toMonoidHom = fixedSubgroup (fieldAut n F σ) := by
    ext z
    obtain ⟨y, rfl⟩ := ψ₁.surjective z
    rw [mem_map_equiv, ψ₁.symm_apply_apply]
    change θ y = y ↔ fieldAut n F σ (ψ₁ y) = ψ₁ y
    rw [← hψ₁θ]
    exact ψ₁.injective.eq_iff.symm
  have hrange : (ψ₁.toMonoidHom.comp ε).range = (projMap n ι).range := by
    rw [MonoidHom.range_comp, hεr, CFSG.Quasithin.map_perfectCore, hfixmap,
      perfectCore_fixedSubgroup_fieldAut hn ι hfix]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp ε) := ψ₁.injective.comp hε
  have hinj₂ : Function.Injective (projMap n ι) := projMap_injective (by omega) ι
  set δ : MulAut (projectiveSL n K) := ((MonoidHom.ofInjective hinj₁).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₂).symm with hδdef
  have hδ : ∀ x, projMap n ι (δ x) = ψ₁ (ε x) := by
    intro x
    have h1 := (MonoidHom.ofInjective hinj₂).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj₁ x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hcomm⟩ := exists_mulAut_projMap_comm hn ι hσι δ
  refine ⟨ψ₁.trans δ'⁻¹, fun x => ?_, fun y => ?_⟩
  · change δ'⁻¹ (ψ₁ (ε x)) = projMap n ι x
    rw [← hδ, ← hδ']
    exact MulAut.inv_apply_self _ _ _
  · change δ'⁻¹ (ψ₁ (θ y)) = fieldAut n F σ (δ'⁻¹ (ψ₁ y))
    rw [hψ₁θ]
    exact congrArg (fun φ : MulAut (projectiveSL n F) => φ (ψ₁ y)) hcomm.inv_left.eq

end Normalize

theorem perfectCore_inf_centralizer_eq_of_standardSetting {G : Type} [Group G] [Finite G]
    {L G₀ : Subgroup G} (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {n : ℕ} {K : Type*} [Field K] (hn : 3 ≤ n) (e : L ≃* projectiveSL n K) (hLG₀ : L ≤ G₀)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L := by
  refine le_antisymm (std_perfect_le hset hOut htC ht (CFSG.Quasithin.perfectCore_perfect _)
    ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right))
    (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hLG₀ fun x hx => ?_)
      (commutator_eq_self_of_mulEquiv_projectiveSL hn e))
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.mp htC x hx

end CFSG.SeitzReduction.LinearPilot
