module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelRoots
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcSigns
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthFacts
public import CFSG.ClassicalInvolution.RouteD.TypeE8Model
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBAdapt
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEAdapt
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGeom
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternToral

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Block

variable {F : Type} [Field F] {X : Type} [Group X]

theorem diagConj2_uSL (t : F) : diagConj2 (-1) 1 (uSL t) = uSL (-t) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_diagConj2, coe_uSL, Matrix.mul_apply, Matrix.diagonal_apply]

theorem blockSL_neg_one_conj (A : SL(2, F)) :
    blockSL F 3 2 1 (by omega) (-1) * blockSL F 3 2 0 (by omega) A *
        (blockSL F 3 2 1 (by omega) (-1))⁻¹ =
      blockSL F 3 2 0 (by omega) (diagConj2 (-1) 1 A) := by
  rw [mul_inv_eq_iff_eq_mul, CFSG.ClassicalInvolution.RouteD.Gaps.blockSL_neg_one_mul,
    diagConj3_blockSL_zero]

theorem blockSL_neg_one_conj_uSL (t : F) :
    blockSL F 3 2 1 (by omega) (-1) * blockSL F 3 2 0 (by omega) (uSL t) *
        (blockSL F 3 2 1 (by omega) (-1))⁻¹ = blockSL F 3 2 0 (by omega) (uSL (-t)) := by
  rw [blockSL_neg_one_conj, diagConj2_uSL]

end Block

section Transfer

variable (F : Type) [Field F] [Finite F]

@[expose] noncomputable def εm : ↥(e7Data_valid.minGroup F) →* ModGL .E7 F :=
  (adjointGroup .E7 F).subtype.comp (e7Isogeny F)

variable {F}

theorem εm_mem (x : ↥(e7Data_valid.minGroup F)) : εm F x ∈ adjointGroup .E7 F :=
  (e7Isogeny F x).2

theorem εm_surjective {w : ModGL .E7 F} (hw : w ∈ adjointGroup .E7 F) :
    ∃ x : ↥(e7Data_valid.minGroup F), εm F x = w := by
  obtain ⟨x, hx⟩ := e7Isogeny_surjective F ⟨w, hw⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem εm_ker_le_center : (εm F).ker ≤ Subgroup.center ↥(e7Data_valid.minGroup F) := by
  intro x hx
  have h1 : ((e7Isogeny F x : ↥(adjointGroup .E7 F)) : ModGL .E7 F) = 1 := MonoidHom.mem_ker.1 hx
  exact ker_le_center_of_isQuasisimple (isQuasisimple_e7 F) (exists_e7Isogeny_ne_one F)
    (MonoidHom.mem_ker.2 (Subtype.ext h1))

omit [Finite F] in
theorem mem_stdRankOne_adj_iff {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (r : ↥(adjointGroup .E7 F)) :
    r ∈ stdRankOne (e7AdjDatum F) γ ↔ ∃ A : SL2 F, (r : ModGL .E7 F) = rootSL2 .E7 F γ A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := F) (rootOperatorFamily .E7) hγ
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E7 F hγ).1
  change r ∈ rootGroup (rootOperatorFamily .E7) F γ ⊔
    rootGroup (rootOperatorFamily .E7) F (-γ) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem map_stdRankOne_εm {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    (stdRankOne (e7Datum F) γ).map (εm F) = rootRankOneGroup .E7 F γ := by
  have hmap : (stdRankOne (e7Datum F) γ).map (e7Isogeny F) = stdRankOne (e7AdjDatum F) γ := by
    change ((e7Datum F).rootGroup γ ⊔ (e7Datum F).rootGroup (-γ)).map (e7Isogeny F) =
      rootGroup (rootOperatorFamily .E7) F γ ⊔ rootGroup (rootOperatorFamily .E7) F (-γ)
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (map_e7Isogeny_rootGroup _ hγ)
      (map_e7Isogeny_rootGroup _ (CFSG.LieType.Chevalley.IsRoot.neg hγ))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : e7Isogeny F x ∈ stdRankOne (e7AdjDatum F) γ := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨A, hA⟩ := (mem_stdRankOne_adj_iff hγ _).1 hx'
    exact ⟨A, hA.symm⟩
  · rintro ⟨A, rfl⟩
    have hx' : (⟨rootSL2 .E7 F γ A, rootSL2_mem_adjointGroup _ _⟩ :
        ↥(adjointGroup .E7 F)) ∈ stdRankOne (e7AdjDatum F) γ :=
      (mem_stdRankOne_adj_iff hγ _).2 ⟨A, rfl⟩
    rw [← hmap] at hx'
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hx'
    exact ⟨x, hx, congrArg Subtype.val hxy⟩

theorem eq_of_map_εm_eq {R R' : Subgroup ↥(e7Data_valid.minGroup F)} (hR : ⁅R, R⁆ = R)
    (hR' : ⁅R', R'⁆ = R') (h : R.map (εm F) = R'.map (εm F)) : R = R' :=
  eq_of_map_eq_of_isPerfect (εm F) εm_ker_le_center hR hR' h

end Transfer

section Core

variable {G H : Type} [Group G] [Group H]

theorem map_conjSub (φ : G →* H) (g : G) (R : Subgroup G) :
    (conjSub g R).map φ = (R.map φ).map (MulAut.conj (φ g)).toMonoidHom := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem commutator_self_le (R : Subgroup G) : ⁅R, R⁆ ≤ R := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)

theorem conjSub_commutator (g : G) (R : Subgroup G) :
    ⁅conjSub g R, conjSub g R⁆ = conjSub g ⁅R, R⁆ := by
  unfold conjSub
  rw [← Subgroup.map_commutator]

end Core

section FrameCore

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem e7_frame_core (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (θW : SL(3, GaloisField p f) →* M₇)
    (hker : θW.ker ≤ Subgroup.center SL(3, GaloisField p f))
    {R₂ : Subgroup M₇} (hR₂ : R₂ ∈ fundamentalSubgroups .E7 D₇)
    (h1 : (B12 (GaloisField p f)).map θW = stdRankOne D₇ thetaE7)
    (h2 : (B23 (GaloisField p f)).map θW = R₂)
    (hne : stdRankOne D₇ thetaE7 ≠ R₂)
    (hnc : ¬ Commutes (stdRankOne D₇ thetaE7) R₂) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧
        (iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1) ∧
        conjSub x R₂ = stdRankOne D₇ γ := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), rfl⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (NeZero.ne f)
  have hsingle : Generic.FundamentalSingleClass .E7 D₇ :=
    fundamentalSingleClass .E7 0 p f Fact.out trivial hadm (by decide) (by decide)
  have hlong := isLongestRoot_single .E7 0 p f Fact.out trivial hadm
  have hθ : Generic.IsLongestRoot D₇ thetaE7 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2
        isRoot_thetaE7)
  have hRθF : stdRankOne D₇ thetaE7 ∈ fundamentalSubgroups .E7 D₇ :=
    ⟨1, thetaE7, Or.inl hθ, (conjSub_one _).symm⟩
  have hperf : ∀ R ∈ fundamentalSubgroups .E7 D₇, ⁅R, R⁆ = R := fun R hR =>
    le_antisymm (commutator_self_le R)
      (fundPerfect_core .E7 0 p f hp2 trivial hadm (by omega) R hR)
  obtain ⟨g, hg⟩ := hsingle _ hRθF R₂ hR₂
  have h2ne : (2 : GaloisField p f) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨hι₁, hι₁r, hι₂, hι₂r⟩ := pair_block_inj hker h1 h2
  set ι₁ := θW.comp (blockSL (GaloisField p f) 3 2 0 (by omega)) with hι₁def
  set ι₂ := θW.comp (blockSL (GaloisField p f) 3 2 1 (by omega)) with hι₂def
  set r : M₇ := θW (blockSL (GaloisField p f) 3 2 1 (by omega) (-1)) with hr
  have hrR : r ∈ R₂ := by
    rw [← hι₂r]
    exact ⟨-1, rfl⟩
  have hr2 : r * r = 1 := by
    rw [hr, ← map_mul, ← map_mul, show ((-1 : SL(2, GaloisField p f)) * (-1)) = 1 by simp,
      map_one, map_one]
  have hrconj : ∀ A : SL2 (GaloisField p f), r * ι₁ A * r⁻¹ = ι₁ (diagConj2 (-1) 1 A) := fun A => by
    simp only [hι₁def, hr, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, blockSL_neg_one_conj]
  have hrconj_u : ∀ t : GaloisField p f, r * ι₁ (uSL t) * r⁻¹ = ι₁ (uSL (-t)) := fun t => by
    rw [hrconj, diagConj2_uSL]
  have hnotcentral : ∀ t : GaloisField p f,
      ι₁ (uSL t) ∈ (εm (GaloisField p f)).ker → t = 0 := by
    intro t ht
    have hc := Subgroup.mem_center_iff.1 (εm_ker_le_center ht) r
    have h3 : ι₁ (uSL (-t)) = ι₁ (uSL t) := by
      rw [← hrconj_u t, mul_inv_eq_iff_eq_mul]
      exact hc
    have h4 := uSL_injective_of_field (hι₁ h3)
    have : (2 : GaloisField p f) * t = 0 := by linear_combination -h4
    exact (mul_eq_zero.1 this).resolve_left h2ne
  set Ψ : Multiplicative (GaloisField p f) →* ModGL .E7 (GaloisField p f) :=
    (εm (GaloisField p f)).comp (ι₁.comp CFSG.SL2MinimalFaithful.unipotentHom) with hΨ
  have hΨapply : ∀ t : GaloisField p f,
      Ψ (Multiplicative.ofAdd t) = εm (GaloisField p f) (ι₁ (uSL t)) := fun t => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := hnotcentral x.toAdd (MonoidHom.mem_ker.2 hx)
    exact toAdd_eq_zero.1 this
  have hεR : (stdRankOne D₇ thetaE7).map (εm (GaloisField p f)) =
      rootRankOneGroup .E7 (GaloisField p f) thetaE7 := map_stdRankOne_εm isRoot_thetaE7
  have hιL : ∀ A : SL2 (GaloisField p f),
      εm (GaloisField p f) (ι₁ A) ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7 := fun A => by
    rw [← hεR]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [← hι₁r]
    exact ⟨A, rfl⟩
  set U : Subgroup (SL2 (GaloisField p f)) :=
    Ψ.range.comap (rootSL2 .E7 (GaloisField p f) thetaE7) with hU
  have hρinj : Function.Injective (rootSL2 .E7 (GaloisField p f) thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 (GaloisField p f) thetaE7).2.2.2.2.2.2.2.1 hF).1
  have hΨle : Ψ.range ≤ (rootSL2 .E7 (GaloisField p f) thetaE7).range := by
    rintro _ ⟨x, rfl⟩
    exact hιL (uSL x.toAdd)
  have hUcard : Nat.card U = Nat.card (GaloisField p f) := by
    rw [← Subgroup.card_map_of_injective hρinj, hU, Subgroup.map_comap_eq_self hΨle]
    exact (Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  have hinv : ∀ A ∈ U, εm (GaloisField p f) r * rootSL2 .E7 (GaloisField p f) thetaE7 A *
      (εm (GaloisField p f) r)⁻¹ = (rootSL2 .E7 (GaloisField p f) thetaE7 A)⁻¹ := by
    intro A hA
    obtain ⟨x, hx⟩ := Subgroup.mem_comap.1 hA
    rw [← hx]
    have hx' : Ψ x = εm (GaloisField p f) (ι₁ (uSL x.toAdd)) := rfl
    have e1 : εm (GaloisField p f) r * εm (GaloisField p f) (ι₁ (uSL x.toAdd)) *
        (εm (GaloisField p f) r)⁻¹ = εm (GaloisField p f) (r * ι₁ (uSL x.toAdd) * r⁻¹) := by
      simp only [map_mul, map_inv]
    have e2 : (εm (GaloisField p f) (ι₁ (uSL x.toAdd)))⁻¹ =
        εm (GaloisField p f) (ι₁ (uSL (-x.toAdd))) := by
      rw [show uSL (-x.toAdd) = (uSL x.toAdd)⁻¹ from (uSL_inv_eq _).symm, map_inv, map_inv]
    rw [hx', e1, e2, hrconj_u]
  set c := εm (GaloisField p f) r with hc
  set u₂ := εm (GaloisField p f) g with hu₂
  have hu₂G : u₂ ∈ adjointGroup .E7 (GaloisField p f) := εm_mem g
  have hεR₂ : R₂.map (εm (GaloisField p f)) =
      (rootRankOneGroup .E7 (GaloisField p f) thetaE7).map (MulAut.conj u₂).toMonoidHom := by
    rw [hg, map_conjSub, hεR]
  have hc2 : c * c = 1 := by rw [hc, ← map_mul, hr2, map_one]
  have hcR₂ : c ∈ (rootRankOneGroup .E7 (GaloisField p f) thetaE7).map
      (MulAut.conj u₂).toMonoidHom := by
    rw [← hεR₂]
    exact Subgroup.mem_map_of_mem _ hrR
  have hc1 : c ≠ 1 := by
    intro h
    have hcen := Subgroup.mem_center_iff.1 (εm_ker_le_center (MonoidHom.mem_ker.2 h))
      (ι₁ (uSL 1))
    have h3 : ι₁ (uSL (-1)) = ι₁ (uSL 1) := by
      rw [← hrconj_u 1, mul_inv_eq_iff_eq_mul]
      exact hcen.symm
    have h4 := uSL_injective_of_field (hι₁ h3)
    exact h2ne (by linear_combination -h4)
  set dθ := rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) with hdθdef
  have hdθ : dθ = rootSL2 .E7 (GaloisField p f) thetaE7 (HSL (-1)) :=
    (rootTorusSL2_thetaE7 (-1)).symm
  have hdθL : dθ ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7 := ⟨HSL (-1), hdθ.symm⟩
  have hd2 : dθ * dθ = 1 := by rw [hdθ, ← map_mul, HSL_neg_one_mul_self, map_one]
  have hdne : dθ ≠ 1 := by
    rw [hdθdef, ← rootTorusSL2_thetaE7]
    exact rootTorusSL2_neg_one_ne_one hF thetaE7
  have hcn : ∀ x ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7,
      c * x * c⁻¹ ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7 := by
    intro x hx
    rw [← hεR] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← hι₁r] at hy
    obtain ⟨A, rfl⟩ := hy
    have : c * εm (GaloisField p f) (ι₁ A) * c⁻¹ =
        εm (GaloisField p f) (ι₁ (diagConj2 (-1) 1 A)) := by
      rw [← hrconj A]
      simp only [hc, map_mul, map_inv]
    rw [this]
    exact hιL _
  have hcdθ : c * dθ = dθ * c := by
    have hz : c * dθ * c⁻¹ ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7 := hcn dθ hdθL
    have hz2 : c * dθ * c⁻¹ * (c * dθ * c⁻¹) = 1 := by
      calc c * dθ * c⁻¹ * (c * dθ * c⁻¹) = c * (dθ * dθ) * c⁻¹ := by group
        _ = 1 := by rw [hd2]; group
    have hz1 : c * dθ * c⁻¹ ≠ 1 := fun h => hdne (by
      have := mul_inv_eq_one.1 h
      simpa using this)
    have := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF hodd hz hz2 hz1
    rw [rootTorusSL2_thetaE7] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hcclass : c = u₂ * dθ * u₂⁻¹ := by
    obtain ⟨x, hx, hxe⟩ := hcR₂
    have hxe' : u₂ * x * u₂⁻¹ = c := hxe
    have hx2 : x * x = 1 := by
      have : u₂ * (x * x) * u₂⁻¹ = c * c := by rw [← hxe']; group
      rw [hc2] at this
      have h3 : x * x = u₂⁻¹ * 1 * u₂ := by
        calc x * x = u₂⁻¹ * (u₂ * (x * x) * u₂⁻¹) * u₂ := by group
          _ = u₂⁻¹ * 1 * u₂ := by rw [this]
      rw [h3]
      group
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hc1
      rw [← hxe']
      group
    have := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF hodd hx hx2 hx1
    rw [rootTorusSL2_thetaE7] at this
    rw [← hxe', this]
  have hne' : (rootRankOneGroup .E7 (GaloisField p f) thetaE7).map (MulAut.conj u₂).toMonoidHom ≠
      rootRankOneGroup .E7 (GaloisField p f) thetaE7 := by
    intro h
    apply hne
    apply eq_of_map_εm_eq (hperf _ hRθF) (hperf _ hR₂)
    rw [hεR, hεR₂, h]
  have hnc' : ¬ ∀ x ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7,
      ∀ y ∈ (rootRankOneGroup .E7 (GaloisField p f) thetaE7).map (MulAut.conj u₂).toMonoidHom,
        x * y = y * x := by
    intro h
    apply hnc
    intro x hx y hy
    have hu : ∀ z ∈ stdRankOne D₇ thetaE7, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.center M₇ := by
      intro z hz
      apply εm_ker_le_center
      rw [MonoidHom.mem_ker]
      have hεz : εm (GaloisField p f) z ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7 := by
        rw [← hεR]
        exact Subgroup.mem_map_of_mem _ hz
      have hεy : εm (GaloisField p f) y ∈ (rootRankOneGroup .E7 (GaloisField p f) thetaE7).map
          (MulAut.conj u₂).toMonoidHom := by
        rw [← hεR₂]
        exact Subgroup.mem_map_of_mem _ hy
      have h3 := h _ hεz _ hεy
      simp only [map_mul, map_inv]
      calc εm (GaloisField p f) y * εm (GaloisField p f) z * (εm (GaloisField p f) y)⁻¹ *
          (εm (GaloisField p f) z)⁻¹ =
          εm (GaloisField p f) y * εm (GaloisField p f) z * ((εm (GaloisField p f) z) *
            εm (GaloisField p f) y)⁻¹ := by group
        _ = 1 := by rw [h3.symm]; group
    exact (commute_of_commutator_central (stdRankOne D₇ thetaE7) (hperf _ hRθF).ge y hu x hx).symm
  have hcd' : (u₂ * dθ * u₂⁻¹) * dθ = dθ * (u₂ * dθ * u₂⁻¹) := by
    rw [← hcclass]
    exact hcdθ
  have hinv' : ∀ A ∈ U, (u₂ * dθ * u₂⁻¹) * rootSL2 .E7 (GaloisField p f) thetaE7 A *
      (u₂ * dθ * u₂⁻¹)⁻¹ = (rootSL2 .E7 (GaloisField p f) thetaE7 A)⁻¹ := by
    intro A hA
    rw [← hcclass]
    exact hinv A hA
  obtain ⟨γ, w, hγ, hpair, hwG, hwd, hL⟩ :=
    exists_frame_adj_e7 hp2 hq hu₂G hcd' hUcard hinv' hne' hnc'
  obtain ⟨x, hx⟩ := εm_surjective hwG
  have hγF : stdRankOne D₇ γ ∈ fundamentalSubgroups .E7 D₇ := by
    have hγlong : Generic.IsLongestRoot D₇ γ :=
      isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
        ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2 hγ)
    exact ⟨1, γ, Or.inl hγlong, (conjSub_one _).symm⟩
  refine ⟨x, ?_, γ, hγ, hpair, ?_⟩
  · apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hRθF]) (hperf _ hRθF)
    rw [map_conjSub, hx, hεR, map_conj_rootRankOneGroup_of_commute hF hwG hwd]
  · apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hR₂]) (hperf _ hγF)
    rw [map_conjSub, hx, hεR₂, Subgroup.map_map, map_stdRankOne_εm hγ]
    exact hL

end FrameCore

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem conjSub_inv_conjSub {G : Type} [Group G] (g : G) (S : Subgroup G) :
    conjSub g⁻¹ (conjSub g S) = S := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv {G : Type} [Group G] (g : G) (S : Subgroup G) :
    conjSub g (conjSub g⁻¹ S) = S := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem e7Idx_fin (a : Fin 7) : e7Idx (a : ℕ) = a := Fin.ext (Nat.mod_eq_of_lt a.2)

theorem e7PairFrame_sc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∀ R₁ ∈ fundamentalSubgroups .E7 (e7Datum (GaloisField p f)),
      ∀ R₂ ∈ fundamentalSubgroups .E7 (e7Datum (GaloisField p f)),
      CFSG.ClassicalInvolution.RouteD.Gaps.ModelAdj (Subgroup.center (E7sc p f)) R₁ R₂ →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂) →
      ∀ a b : Fin 7, CFSG.Timmesfeld.edgeE 7 a b →
        ∃ g : E7sc p f, R₁ = conjSub g (rankOne (e7Datum (GaloisField p f)).rootGroup a) ∧
          R₂ = conjSub g (rankOne (e7Datum (GaloisField p f)).rootGroup b) := by
  intro R₁ hR₁ R₂ hR₂ hadj hlin a b hab
  obtain ⟨W, hW⟩ := hlin
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), rfl⟩
  have hsingle : Generic.FundamentalSingleClass .E7 (e7Datum (GaloisField p f)) :=
    fundamentalSingleClass .E7 0 p f Fact.out trivial hadm (by decide) (by decide)
  have hlong := isLongestRoot_single .E7 0 p f Fact.out trivial hadm
  have hθ : Generic.IsLongestRoot (e7Datum (GaloisField p f)) thetaE7 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2
        isRoot_thetaE7)
  have hRθF : stdRankOne (e7Datum (GaloisField p f)) thetaE7 ∈
      fundamentalSubgroups .E7 (e7Datum (GaloisField p f)) :=
    ⟨1, thetaE7, Or.inl hθ, (conjSub_one _).symm⟩
  obtain ⟨g₁, hg₁⟩ := hsingle _ hRθF R₁ hR₁
  obtain ⟨g₂, hg₂⟩ := hsingle _ hRθF R₂ hR₂
  obtain ⟨θW, -, hker, hU, hV⟩ := pair_normalize hW
  set θ' := (MulAut.conj g₁⁻¹).toMonoidHom.comp θW with hθ'
  have hker' : θ'.ker ≤ Subgroup.center SL(3, GaloisField p f) := fun x hx =>
    hker (MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff (MulAut.conj g₁⁻¹)).1
      (MonoidHom.mem_ker.1 hx)))
  have hmapθ' : ∀ S : Subgroup SL(3, GaloisField p f),
      S.map θ' = conjSub g₁⁻¹ (S.map θW) := fun S => by
    unfold conjSub
    rw [hθ', Subgroup.map_map]
  have h1' : (B12 (GaloisField p f)).map θ' = stdRankOne (e7Datum (GaloisField p f)) thetaE7 := by
    rw [hmapθ', hU, hg₁, conjSub_inv_conjSub]
  have h2' : (B23 (GaloisField p f)).map θ' = conjSub g₁⁻¹ R₂ := by
    rw [hmapθ', hV]
  have hR₂'F : conjSub g₁⁻¹ R₂ ∈ fundamentalSubgroups .E7 (e7Datum (GaloisField p f)) :=
    ⟨g₁⁻¹ * g₂, thetaE7, Or.inl hθ, by
      show conjSub g₁⁻¹ R₂ = conjSub (g₁⁻¹ * g₂) (stdRankOne (e7Datum (GaloisField p f)) thetaE7)
      rw [hg₂, conjSub_mul]⟩
  have hne' : stdRankOne (e7Datum (GaloisField p f)) thetaE7 ≠ conjSub g₁⁻¹ R₂ := by
    intro h
    apply hadj.1
    rw [hg₁, h, conjSub_conjSub_inv]
  have hnc' : ¬ Commutes (stdRankOne (e7Datum (GaloisField p f)) thetaE7) (conjSub g₁⁻¹ R₂) := by
    intro h
    apply hadj.2.1
    intro x hx y hy
    have hx' : g₁⁻¹ * x * g₁ ∈ stdRankOne (e7Datum (GaloisField p f)) thetaE7 := by
      rw [hg₁, mem_conjSub_iff] at hx
      exact hx
    have hy' : g₁⁻¹ * y * g₁ ∈ conjSub g₁⁻¹ R₂ := by
      rw [mem_conjSub_iff, inv_inv]
      have : g₁ * (g₁⁻¹ * y * g₁) * g₁⁻¹ = y := by group
      rw [this]
      exact hy
    have := h _ hx' _ hy'
    calc x * y = g₁ * (g₁⁻¹ * x * g₁ * (g₁⁻¹ * y * g₁)) * g₁⁻¹ := by group
      _ = g₁ * (g₁⁻¹ * y * g₁ * (g₁⁻¹ * x * g₁)) * g₁⁻¹ := by rw [this]
      _ = y * x := by group
  obtain ⟨x, hx1, γ, hγ, hpair, hx2⟩ :=
    e7_frame_core hp2 hq θ' hker' hR₂'F h1' h2' hne' hnc'
  obtain ⟨k, hk1, hk2⟩ := exists_conj_phase_one (GaloisField p f) hγ hpair
  obtain ⟨m, hm1, hm2⟩ := exists_conj_edge (GaloisField p f) hab
  rw [e7Idx_fin] at hm1 hm2
  have hR₁' : conjSub (k * x * g₁⁻¹) R₁ = stdRankOne (e7Datum (GaloisField p f)) thetaE7 := by
    rw [conjSub_mul, conjSub_mul, hg₁, conjSub_inv_conjSub, hx1, hk1]
  have hR₂' : conjSub (k * x * g₁⁻¹) R₂ =
      rankOne (e7Datum (GaloisField p f)).rootGroup (e7Idx 0) := by
    rw [conjSub_mul, conjSub_mul, hx2, hk2]
  refine ⟨(k * x * g₁⁻¹)⁻¹ * m, ?_, ?_⟩
  · rw [conjSub_mul, hm1, ← hR₁', conjSub_inv_conjSub]
  · rw [conjSub_mul, hm2, ← hR₂', conjSub_inv_conjSub]

theorem e7PairFrame (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    CFSG.ClassicalInvolution.RouteD.TypeE8.E7PairFrame p f :=
  e7PairFrame_sc hp2 hq

end Main

end CFSG.ClassicalInvolution.ModelFacts.E7Model
