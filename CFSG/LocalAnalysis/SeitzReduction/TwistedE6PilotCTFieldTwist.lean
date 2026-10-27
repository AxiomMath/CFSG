module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldSL2
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYRigid

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)

local instance twistedE6PilotCTFieldTwistNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotCTFieldTwistNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section TwistBy

variable
  {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}

@[expose] noncomputable def FieldNeighbourIso2E6.twistBy
    {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G} {X : Subgroup G}
    {M D : Subgroup (ModGL TwistTag.E6.tag K)} {β₀ : MulAut M}
    (h : FieldNeighbourIso2E6 e t X M β₀ D)
    (hfixβ : ∀ (y : graphFixedRootGroup TwistTag.E6 K σ), (y : ModGL TwistTag.E6.tag K) ∈ D →
      ∀ hyM : (y : ModGL TwistTag.E6.tag K) ∈ M, β₀ ⟨y, hyM⟩ = ⟨y, hyM⟩) :
    FieldNeighbourIso2E6 e t X M β₀ D where
  Φ := β₀.trans h.Φ
  fix y hyD hyM := by
    change ((h.Φ (β₀ ⟨y, hyM⟩) : centralizerPerfectCore X) : G) = _
    rw [hfixβ y hyD hyM]
    exact h.fix y hyD hyM
  twist x := h.twist (β₀ x)

end TwistBy

section Twist

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]

theorem d4LeviTwist_fix (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∀ (y : graphFixedRootGroup TwistTag.E6 K σ), (y : ModGL TwistTag.E6.tag K) ∈ omegaMinusLevi σ →
      ∀ hyM : (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setD,
        d4LeviTwist (apply_apply_eq hK hσ) ⟨y, hyM⟩ = ⟨y, hyM⟩ := by
  intro y _ hyM
  apply Subtype.ext
  change twistHom TwistTag.E6 K σ (y : ModGL TwistTag.E6.tag K) = y
  exact (graphFixedRootGroup_le TwistTag.E6 K σ y.2).2

theorem relLevi_one_le_setD : relLevi K {1} ≤ subsystemGroup TwistTag.E6.tag K setD := by
  refine relLevi_le_subsystemGroup fun j hj => ?_
  rw [relNodeSet_one, Finset.mem_singleton] at hj
  subst hj
  exact Or.inr (Or.inr (Or.inl rfl))

theorem xUnit_yUnit_alpha4_mem_C0 {σ : K →+* K} {c : K} (hc : σ c = c) :
    xUnit TwistTag.E6.tag K nodeAlpha4 c ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      yUnit TwistTag.E6.tag K nodeAlpha4 c ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
      (xUnit_mem_graphFixedPosUnipotent perm_nodeAlpha4 hc),
    graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
      (yUnit_mem_graphFixedNegUnipotent perm_nodeAlpha4 hc)⟩

theorem exists_ne_zero_ne_one_of_four_le_2E6 {k : Type} [Field k] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) : ∃ c : k, c ≠ 0 ∧ c ≠ 1 := by
  classical
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  by_contra hall
  push Not at hall
  have : Fintype k := Fintype.ofFinite k
  have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := fun c _ => by
    by_cases hc : c = 0
    · simp [hc]
    · simp [hall c hc]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk] at h1
  have h2 := Finset.card_insert_le (0 : k) {1}
  rw [Finset.card_singleton] at h2
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  omega

theorem eq_of_forall_xUnit_yUnit_alpha4 {M : Type*} [Group M] {φ₁ φ₂ : relLevi K {1} →* M}
    (hx : ∀ (a : K) (h : xUnit TwistTag.E6.tag K nodeAlpha4 a ∈ relLevi K {1}),
      φ₁ ⟨_, h⟩ = φ₂ ⟨_, h⟩)
    (hy : ∀ (a : K) (h : yUnit TwistTag.E6.tag K nodeAlpha4 a ∈ relLevi K {1}),
      φ₁ ⟨_, h⟩ = φ₂ ⟨_, h⟩)
    (y : relLevi K {1}) : φ₁ y = φ₂ y := by
  have hle : relLevi K {1} ≤ (MonoidHom.eqLocus φ₁ φ₂).map (relLevi K {1}).subtype := by
    conv_lhs => rw [relLevi_one_eq_range, rankOneHom_range]
    rw [Subgroup.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · have h : xUnit TwistTag.E6.tag K nodeAlpha4 a ∈ relLevi K {1} := by
        rw [relLevi_one_eq_range, rankOneHom_range]
        exact Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
      exact ⟨⟨_, h⟩, hx a h, rfl⟩
    · have h : yUnit TwistTag.E6.tag K nodeAlpha4 a ∈ relLevi K {1} := by
        rw [relLevi_one_eq_range, rankOneHom_range]
        exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
      exact ⟨⟨_, h⟩, hy a h, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := hle y.2
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

theorem exists_fieldNeighbourIso2E6_Y_eq_on_relLevi_one (hf2 : 2 ≤ f) {k : Type} [Field k]
    [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G}
    (htL : t ∈ centralizer (L : Set G))
    (hY : FieldNeighbourIso2E6 e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
      (subsystemGroup TwistTag.E6.tag K setD) (d4LeviTwist (apply_apply_eq hK hσ))
      (omegaMinusLevi σ))
    (φ : relLevi K {1} →* G) (hφ : Function.Injective φ)
    (hrange : φ.range = pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {1})
    (hfixx : ∀ (c : K), σ c = c → ∀ (h : xUnit TwistTag.E6.tag K nodeAlpha4 c ∈ relLevi K {1})
      (hC : xUnit TwistTag.E6.tag K nodeAlpha4 c ∈ graphFixedRootGroup TwistTag.E6 K σ),
        φ ⟨_, h⟩ = ((e.symm ⟨_, hC⟩ : L) : G))
    (hfixy : ∀ (c : K), σ c = c → ∀ (h : yUnit TwistTag.E6.tag K nodeAlpha4 c ∈ relLevi K {1})
      (hC : yUnit TwistTag.E6.tag K nodeAlpha4 c ∈ graphFixedRootGroup TwistTag.E6 K σ),
        φ ⟨_, h⟩ = ((e.symm ⟨_, hC⟩ : L) : G)) :
    ∃ hY' : FieldNeighbourIso2E6 e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
      (subsystemGroup TwistTag.E6.tag K setD) (d4LeviTwist (apply_apply_eq hK hσ))
      (omegaMinusLevi σ),
      ∀ (y : relLevi K {1})
        (hyD : (y : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setD),
        ((hY'.Φ ⟨y, hyD⟩ : centralizerPerfectCore _) : G) = φ y := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨hA3, hAo, hAσ, hkσ⟩ := unitsRange_facts hf2 hk hσ
  have hAm : ∀ c ∈ (Units.map (algebraMap k K).toMonoidHom).range,
      c ^ Nat.card (Units.map (algebraMap k K).toMonoidHom).range = 1 := fun c hc => by
    have h1 := pow_card_eq_one' (x := (⟨c, hc⟩ : (Units.map (algebraMap k K).toMonoidHom).range))
    exact congrArg Subtype.val h1
  have hpieceY := hY.pieceCore_eq_map_relLevi_Y' hf hK hσ htL hA3 hAσ hAo hAm
    (I := ({1} : Finset (Fin Tag.F4.rank))) (by decide) (by decide)
    (modelToG_mono e (neighbourTorus_le_relLeviTorus _ .Y (by decide)))
  have hrinj := rankOneHom_injective_of_charTwo (K := K) TwistTag.E6 nodeAlpha4
  have hrmem : ∀ a, rankOneHom TwistTag.E6 K nodeAlpha4 a ∈ relLevi K {1} := fun a => by
    rw [relLevi_one_eq_range]
    exact ⟨a, rfl⟩
  let ψφ : SL2 K →* relLevi K {1} := (rankOneHom TwistTag.E6 K nodeAlpha4).codRestrict _ hrmem
  let ψY : SL2 K →* subsystemGroup TwistTag.E6.tag K setD :=
    (rankOneHom TwistTag.E6 K nodeAlpha4).codRestrict _ fun a => relLevi_one_le_setD (hrmem a)
  let f₁ : SL2 K →* G := φ.comp ψφ
  let f₂ : SL2 K →* G := (centralizerPerfectCore
    (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))).subtype.comp
      (hY.Φ.toMonoidHom.comp ψY)
  have hf₁ : Function.Injective f₁ :=
    hφ.comp fun a b h => hrinj (congrArg Subtype.val h)
  have hf₂ : Function.Injective f₂ :=
    Subtype.val_injective.comp (hY.Φ.injective.comp fun a b h => hrinj (congrArg Subtype.val h))
  have hψφ : Function.Surjective ψφ := by
    rintro ⟨y, hy⟩
    have hy' := hy
    rw [relLevi_one_eq_range] at hy'
    obtain ⟨a, rfl⟩ := hy'
    exact ⟨a, rfl⟩
  have hrange₁ : f₁.range = pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {1} := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hψφ, ← MonoidHom.range_eq_map, hrange]
  have hrange₂ : f₂.range = pieceCore e (Units.map (algebraMap k K).toMonoidHom).range {1} := by
    rw [hpieceY]
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨ψY a, mem_subgroupOf.2 (hrmem a), rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hy' := mem_subgroupOf.1 hy
      rw [relLevi_one_eq_range] at hy'
      obtain ⟨a, ha⟩ := hy'
      refine ⟨a, ?_⟩
      have : ψY a = y := Subtype.ext ha
      change ((hY.Φ (ψY a) : centralizerPerfectCore _) : G) = _
      rw [this]
      rfl
  set θ : MulAut (SL2 K) := ((MonoidHom.ofInjective hf₁).trans
    (MulEquiv.subgroupCongr (hrange₁.trans hrange₂.symm))).trans
      (MonoidHom.ofInjective hf₂).symm with hθdef
  have hθ : ∀ a, f₂ (θ a) = f₁ a := by
    intro a
    have h1 := (MonoidHom.ofInjective hf₂).apply_symm_apply
      (MulEquiv.subgroupCongr (hrange₁.trans hrange₂.symm) (MonoidHom.ofInjective hf₁ a))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨σE, hσE⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := fun c => by
    have h := apply_apply_eq hK hσ c
    rw [← hσE] at h
    exact h
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω' : σE ω ≠ ω := by
    rw [← hσE] at hω
    exact hω
  have hord : orderOf σE = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact d4_sigma_mul_self hσσ) (d4_sigma_ne_one hω')
  have hσEc : ∀ c, σE c = σ c := fun c => by rw [← hσE]; rfl
  have hfixY : ∀ (a : SL2 K) (hC : rankOneHom TwistTag.E6 K nodeAlpha4 a ∈
      graphFixedRootGroup TwistTag.E6 K σ), f₂ a = ((e.symm ⟨_, hC⟩ : L) : G) := by
    intro a hC
    have hD : rankOneHom TwistTag.E6 K nodeAlpha4 a ∈ omegaMinusLevi σ :=
      mem_inf.2 ⟨relLevi_one_le_setD (hrmem a), hC⟩
    exact hY.fix ⟨_, hC⟩ hD (relLevi_one_le_setD (hrmem a))
  have hθU : ∀ c : fixSubfield σE, θ (sl2Upper ((fixSubfield σE).subtype c)) =
      sl2Upper ((fixSubfield σE).subtype c) := by
    intro c
    have hcσ : σ ((fixSubfield σE).subtype c) = c := by rw [← hσEc]; exact c.2
    have hC := (xUnit_yUnit_alpha4_mem_C0 (σ := σ) hcσ).1
    have hu : rankOneHom TwistTag.E6 K nodeAlpha4 (sl2Upper ((fixSubfield σE).subtype c)) =
        xUnit TwistTag.E6.tag K nodeAlpha4 c :=
      rankOneHom_uSL nodeAlpha4 ((fixSubfield σE).subtype c)
    have hC' : rankOneHom TwistTag.E6 K nodeAlpha4 (sl2Upper ((fixSubfield σE).subtype c)) ∈
        graphFixedRootGroup TwistTag.E6 K σ := hu ▸ hC
    apply hf₂
    rw [hθ, hfixY _ hC']
    change φ (ψφ (sl2Upper ((fixSubfield σE).subtype c))) = _
    have hψ : ψφ (sl2Upper ((fixSubfield σE).subtype c)) = ⟨_, hu ▸ hrmem _⟩ := Subtype.ext hu
    rw [hψ]
    refine (hfixx _ hcσ _ hC).trans ?_
    congr 2
    exact Subtype.ext hu.symm
  have hθL : ∀ c : fixSubfield σE, θ (sl2Lower ((fixSubfield σE).subtype c)) =
      sl2Lower ((fixSubfield σE).subtype c) := by
    intro c
    have hcσ : σ ((fixSubfield σE).subtype c) = c := by rw [← hσEc]; exact c.2
    have hC := (xUnit_yUnit_alpha4_mem_C0 (σ := σ) hcσ).2
    have hv : rankOneHom TwistTag.E6 K nodeAlpha4 (sl2Lower ((fixSubfield σE).subtype c)) =
        yUnit TwistTag.E6.tag K nodeAlpha4 c :=
      rankOneHom_vSL nodeAlpha4 ((fixSubfield σE).subtype c)
    have hC' : rankOneHom TwistTag.E6 K nodeAlpha4 (sl2Lower ((fixSubfield σE).subtype c)) ∈
        graphFixedRootGroup TwistTag.E6 K σ := hv ▸ hC
    apply hf₂
    rw [hθ, hfixY _ hC']
    change φ (ψφ (sl2Lower ((fixSubfield σE).subtype c))) = _
    have hψ : ψφ (sl2Lower ((fixSubfield σE).subtype c)) = ⟨_, hv ▸ hrmem _⟩ := Subtype.ext hv
    rw [hψ]
    refine (hfixy _ hcσ _ hC).trans ?_
    congr 2
    exact Subtype.ext hv.symm
  have hk2 : ∃ c : fixSubfield σE, c ≠ 0 ∧ c ≠ 1 := by
    obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_four_le_2E6 hf2 hk
    refine ⟨⟨algebraMap k K c, by rw [mem_fixSubfield, hσEc]; exact hkσ c⟩, fun h => hc0 ?_,
      fun h => hc1 ?_⟩
    · have h' := congrArg Subtype.val h
      exact (algebraMap k K).injective (by simpa using h')
    · have h' := congrArg Subtype.val h
      exact (algebraMap k K).injective (by simpa using h')
  obtain ⟨ρ, hρ, hθρ⟩ := E8Pilot.exists_ringEquiv_of_forall_sl2 (fixSubfield σE).subtype hk2 θ
    hθU hθL
  have hφx : ∀ a : K, φ (ψφ (sl2Upper a)) =
      f₂ (sl2Upper (ρ a)) := fun a => by
    rw [← (hθρ a).1]
    exact (hθ _).symm
  have hφy : ∀ a : K, φ (ψφ (sl2Lower a)) =
      f₂ (sl2Lower (ρ a)) := fun a => by
    rw [← (hθρ a).2]
    exact (hθ _).symm
  have hψφx : ∀ (a : K) (h : xUnit TwistTag.E6.tag K nodeAlpha4 a ∈ relLevi K {1}),
      ψφ (sl2Upper a) = ⟨_, h⟩ := fun a _ =>
    Subtype.ext (rankOneHom_uSL nodeAlpha4 a)
  have hψφy : ∀ (a : K) (h : yUnit TwistTag.E6.tag K nodeAlpha4 a ∈ relLevi K {1}),
      ψφ (sl2Lower a) = ⟨_, h⟩ := fun a _ =>
    Subtype.ext (rankOneHom_vSL nodeAlpha4 a)
  rcases F4Pilot.eq_one_or_eq_of_forall_fixSubfield hord (fun c => hρ c) with hρ1 | hρσ
  · have hρa : ∀ a, ρ a = a := fun a => by rw [hρ1]; rfl
    refine ⟨hY, fun y hyD => ?_⟩
    have key := eq_of_forall_xUnit_yUnit_alpha4
      (φ₁ := (centralizerPerfectCore
        (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
          ).subtype.comp
          (hY.Φ.toMonoidHom.comp (Subgroup.inclusion relLevi_one_le_setD)))
      (φ₂ := φ) (fun a h => ?_) (fun a h => ?_) y
    · exact key
    · have e1 : φ ⟨_, h⟩ = f₂ (sl2Upper (ρ a)) := by
        rw [← hψφx a h]
        exact hφx a
      rw [e1, hρa]
      change ((hY.Φ ⟨_, relLevi_one_le_setD h⟩ : centralizerPerfectCore _) : G) =
        ((hY.Φ (ψY (sl2Upper a)) : centralizerPerfectCore _) : G)
      congr 2
      exact Subtype.ext (rankOneHom_uSL nodeAlpha4 a).symm
    · have e1 : φ ⟨_, h⟩ = f₂ (sl2Lower (ρ a)) := by
        rw [← hψφy a h]
        exact hφy a
      rw [e1, hρa]
      change ((hY.Φ ⟨_, relLevi_one_le_setD h⟩ : centralizerPerfectCore _) : G) =
        ((hY.Φ (ψY (sl2Lower a)) : centralizerPerfectCore _) : G)
      congr 2
      exact Subtype.ext (rankOneHom_vSL nodeAlpha4 a).symm
  · have hρa : ∀ a, ρ a = σE a := fun a => by rw [hρσ]
    refine ⟨hY.twistBy (d4LeviTwist_fix hK hσ), fun y hyD => ?_⟩
    have key := eq_of_forall_xUnit_yUnit_alpha4
      (φ₁ := (centralizerPerfectCore
        (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
          ).subtype.comp
          ((hY.twistBy (d4LeviTwist_fix hK hσ)).Φ.toMonoidHom.comp
            (Subgroup.inclusion relLevi_one_le_setD)))
      (φ₂ := φ) (fun a h => ?_) (fun a h => ?_) y
    · exact key
    · have e1 : φ ⟨_, h⟩ = f₂ (sl2Upper (ρ a)) := by
        rw [← hψφx a h]
        exact hφx a
      rw [e1, hρa]
      change ((hY.Φ (d4LeviTwist (apply_apply_eq hK hσ) ⟨_, relLevi_one_le_setD h⟩) :
          centralizerPerfectCore _) : G) =
        ((hY.Φ (ψY (sl2Upper (σE a))) : centralizerPerfectCore _) : G)
      congr 2
      apply Subtype.ext
      change twistHom TwistTag.E6 K σ (xUnit TwistTag.E6.tag K nodeAlpha4 a) =
        rankOneHom TwistTag.E6 K nodeAlpha4 (sl2Upper (σE a))
      rw [twistHom_xUnit, perm_nodeAlpha4, ← hσEc]
      exact (rankOneHom_uSL nodeAlpha4 (σE a)).symm
    · have e1 : φ ⟨_, h⟩ = f₂ (sl2Lower (ρ a)) := by
        rw [← hψφy a h]
        exact hφy a
      rw [e1, hρa]
      change ((hY.Φ (d4LeviTwist (apply_apply_eq hK hσ) ⟨_, relLevi_one_le_setD h⟩) :
          centralizerPerfectCore _) : G) =
        ((hY.Φ (ψY (sl2Lower (σE a))) : centralizerPerfectCore _) : G)
      congr 2
      apply Subtype.ext
      change twistHom TwistTag.E6 K σ (yUnit TwistTag.E6.tag K nodeAlpha4 a) =
        rankOneHom TwistTag.E6 K nodeAlpha4 (sl2Lower (σE a))
      rw [twistHom_yUnit, perm_nodeAlpha4, ← hσEc]
      exact (rankOneHom_vSL nodeAlpha4 (σE a)).symm

end Twist

end CFSG.SeitzReduction.TwistedE6Pilot
