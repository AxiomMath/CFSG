module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


section Bar

variable {G : Type} [Group G] [Finite G]

abbrev SecQ (Ω : Set (Subgroup G)) (c : G) : Type :=
  ↥(TwinDisc.coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreHull Ω c)

abbrev BarQ (Ω : Set (Subgroup G)) (c : G) : Type :=
  ↥(TwinDisc.coreLayer Ω c) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω c)

@[expose] noncomputable def barEquiv (Ω : Set (Subgroup G)) (c : G) : SecQ Ω c ≃* BarQ Ω c :=
  QuotientGroup.congr _ _
    (Subgroup.equivMapOfInjective (TwinDisc.coreHull Ω c) (Subgroup.centralizer ({c} : Set G)).subtype
      (Subgroup.centralizer ({c} : Set G)).subtype_injective)
    (CFSG.ComponentClassification.OddCore.equiv_invariant _)

theorem barEquiv_mk (Ω : Set (Subgroup G)) (c : G) (y : ↥(TwinDisc.coreHull Ω c)) :
    barEquiv Ω c (QuotientGroup.mk y) = QuotientGroup.mk (⟨((y : ↥(Subgroup.centralizer ({c} : Set G))) : G),
      ⟨(y : ↥(Subgroup.centralizer ({c} : Set G))), y.2, rfl⟩⟩ : ↥(TwinDisc.coreLayer Ω c)) := rfl

end Bar

section Facts

structure SecFacts {M : Type} [Group M] (P : Subgroup (MulAut M)) (zs : M) : Prop where
  center : Subgroup.center M = ⊥
  exp2 : ∀ β ∈ P, β * β = 1
  card : Nat.card ↥P ≤ 4
  refl : ∀ β ∈ P, β ≠ 1 → β ≠ MulAut.conj zs →
    ∃ xb : M, β xb = xb ∧ xb * zs * xb⁻¹ ≠ zs ∧ (xb * zs * xb⁻¹) * zs = zs * (xb * zs * xb⁻¹)
  nonsolv : ∀ L : Subgroup (MulAut M), L ≤ P → MulAut.conj zs ∉ L → ¬ Group.IsSolvable ↥(fixOf L)

variable {M N : Type} [Group M] [Group N]

theorem congr_conj (σ : M ≃* N) (g : M) :
    MulAut.congr σ (MulAut.conj g) = MulAut.conj (σ g) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_apply' (σ : M ≃* N) (β : MulAut M) (x : N) :
    (MulAut.congr σ β) x = σ (β (σ.symm x)) := rfl

theorem congr_symm_apply' (σ : M ≃* N) (β' : MulAut N) (x : M) :
    ((MulAut.congr σ).symm β') x = σ.symm (β' (σ x)) := rfl

theorem SecFacts.map_equiv {P : Subgroup (MulAut M)} {zs : M} (h : SecFacts P zs) (σ : M ≃* N)
    {P' : Subgroup (MulAut N)} (hP : P' = P.map (MulAut.congr σ).toMonoidHom) :
    SecFacts P' (σ zs) := by
  subst hP
  have hmem : ∀ β' ∈ P.map (MulAut.congr σ).toMonoidHom, (MulAut.congr σ).symm β' ∈ P := by
    rintro _ ⟨β, hβ, rfl⟩
    have : (MulAut.congr σ).symm ((MulAut.congr σ).toMonoidHom β) = β :=
      (MulAut.congr σ).symm_apply_apply β
    rw [this]
    exact hβ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hc : σ.symm y ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_center_iff.mp hy (σ g)
      apply σ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact this
    rw [h.center, Subgroup.mem_bot] at hc
    have := congrArg σ hc
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · rintro _ ⟨β, hβ, rfl⟩
    show MulAut.congr σ β * MulAut.congr σ β = 1
    rw [← map_mul, h.exp2 β hβ, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.congr σ).injective]
    exact h.card
  · intro β' hβ' h1 h2
    obtain ⟨xb, hxb1, hxb2, hxb3⟩ := h.refl _ (hmem β' hβ')
      (fun e => h1 ((MulEquiv.map_eq_one_iff (MulAut.congr σ).symm).mp e))
      (fun e => h2 (by
        rw [← (MulAut.congr σ).apply_symm_apply β', e, congr_conj]))
    refine ⟨σ xb, ?_, ?_, ?_⟩
    · have : σ.symm (β' (σ xb)) = xb := by rw [← congr_symm_apply']; exact hxb1
      have := congrArg σ this
      rwa [MulEquiv.apply_symm_apply] at this
    · intro e
      apply hxb2
      apply σ.injective
      rw [map_mul, map_mul, map_inv]
      exact e
    · have := congrArg σ hxb3
      simpa only [map_mul, map_inv] using this
  · intro L' hL' hc
    set L : Subgroup (MulAut M) := L'.map (MulAut.congr σ).symm.toMonoidHom with hL
    have hLP : L ≤ P := by
      rintro _ ⟨β', hβ', rfl⟩
      exact hmem β' (hL' hβ')
    have hLc : MulAut.conj zs ∉ L := by
      rintro ⟨β', hβ', hβ'c⟩
      apply hc
      have : β' = MulAut.congr σ (MulAut.conj zs) := by
        rw [← hβ'c]
        exact ((MulAut.congr σ).apply_symm_apply β').symm
      rw [this, congr_conj] at hβ'
      exact hβ'
    have hns := h.nonsolv L hLP hLc
    intro hs
    apply hns
    have hfix : ∀ x ∈ fixOf L, σ x ∈ fixOf L' := by
      intro x hx β' hβ'
      have h1 : ((MulAut.congr σ).symm β') x = x := hx _ ⟨β', hβ', rfl⟩
      rw [congr_symm_apply'] at h1
      have := congrArg σ h1
      rwa [MulEquiv.apply_symm_apply] at this
    let f : ↥(fixOf L) →* ↥(fixOf L') :=
      (σ.toMonoidHom.comp (fixOf L).subtype).codRestrict (fixOf L') fun x => hfix x x.2
    refine solvable_of_solvable_injective (f := f) ?_
    intro x y hxy
    apply Subtype.ext
    apply σ.injective
    exact congrArg Subtype.val hxy

end Facts

section Transfer

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem actOf_barEquiv (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb : b * b = 1)
    (g : ↥(Subgroup.centralizer ({b} : Set G))) (u : SecQ Ω b) :
    actOf hyp hb g (barEquiv Ω b u) =
      barEquiv Ω b (TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb) g u) := by
  refine QuotientGroup.induction_on u fun y => ?_
  rw [actOf_apply, barEquiv_mk, C25Y.layerAut_mk, TwinDisc.secAct_mk, barEquiv_mk]
  rfl

theorem actOf_eq_congr (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb : b * b = 1)
    (g : ↥(Subgroup.centralizer ({b} : Set G))) :
    actOf hyp hb g = MulAut.congr (barEquiv Ω b)
      (TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb) g) := by
  ext v
  obtain ⟨u, rfl⟩ := (barEquiv Ω b).surjective v
  rw [actOf_barEquiv, congr_apply', MulEquiv.symm_apply_apply]

theorem actImage_eq (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb : b * b = 1) :
    ((cA S R R').subgroupOf (Subgroup.centralizer ({b} : Set G))).map (actOf hyp hb) =
      (((cA S R R').subgroupOf (Subgroup.centralizer ({b} : Set G))).map
        (TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb))).map
          (MulAut.congr (barEquiv Ω b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g : 1
  exact actOf_eq_congr hyp hb g

theorem layerFacts_of_secFacts (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb : b * b = 1)
    (htC : z ∈ Subgroup.centralizer ({b} : Set G))
    (htY : (⟨z, htC⟩ : ↥(Subgroup.centralizer ({b} : Set G))) ∈ TwinDisc.coreHull Ω b)
    (hs : SecFacts (((cA S R R').subgroupOf (Subgroup.centralizer ({b} : Set G))).map
      (TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb)))
      (QuotientGroup.mk (⟨⟨z, htC⟩, htY⟩ : ↥(TwinDisc.coreHull Ω b)) : SecQ Ω b)) :
    LayerFacts hyp hb := by
  have zY : z ∈ TwinDisc.coreLayer Ω b := ⟨⟨z, htC⟩, htY, rfl⟩
  have h := hs.map_equiv (barEquiv Ω b) (actImage_eq hyp hb)
  have hz : barEquiv Ω b (QuotientGroup.mk (⟨⟨z, htC⟩, htY⟩ : ↥(TwinDisc.coreHull Ω b))) =
      (QuotientGroup.mk ⟨z, zY⟩ : BarQ Ω b) := rfl
  rw [hz] at h
  refine ⟨zY, h.center, ?_, h.card, ?_, ?_⟩
  · intro x hxA hxw
    exact h.exp2 _ ⟨⟨x, hxw⟩, Subgroup.mem_subgroupOf.mpr hxA, rfl⟩
  · intro x hxA hxw h1 h2
    exact h.refl _ ⟨⟨x, hxw⟩, Subgroup.mem_subgroupOf.mpr hxA, rfl⟩ h1 h2
  · intro L hL hc
    exact h.nonsolv L hL hc

end Transfer

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
