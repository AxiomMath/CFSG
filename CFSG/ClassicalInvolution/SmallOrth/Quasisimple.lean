module

public import CFSG.ClassicalInvolution.SmallOrth.Primitive
public import CFSG.Open.Defs
public import CFSG.ClassicalInvolution.SmallOrth.Iwasawa
public import CFSG.ClassicalInvolution.SmallOrth.Perfect
public import CFSG.ClassicalInvolution.SmallOrth.Scalar

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

theorem isQuasisimple_of_iwasawa {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsQuasiPreprimitive G X] (I : MulAction.IwasawaStructure G X)
    (hperf : commutator G = ⊤) (hker : ∀ g : G, (∀ x : X, g • x = x) → g ∈ Subgroup.center G)
    (hmove : ∃ (g : G) (x : X), g • x ≠ x) : CFSG.Open.IsQuasisimple G := by
  refine ⟨hperf, ?_⟩
  obtain ⟨g₀, x₀, hgx₀⟩ := hmove
  have hnt : ∃ g : G, g ∉ Subgroup.center G := by
    by_contra! hall
    have hbot : commutator G = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact (Subgroup.eq_top_iff' _).mpr hall
    rw [hperf] at hbot
    have : g₀ ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_top g₀
    rw [Subgroup.mem_bot] at this
    exact hgx₀ (by rw [this, one_smul])
  obtain ⟨g₁, hg₁⟩ := hnt
  refine
    { exists_pair_ne := ⟨QuotientGroup.mk g₁, 1,
        fun h => hg₁ ((QuotientGroup.eq_one_iff g₁).mp h)⟩
      eq_bot_or_eq_top_of_normal := ?_ }
  intro H hH
  set N : Subgroup G := H.comap (QuotientGroup.mk' (Subgroup.center G)) with hN
  have hNn : N.Normal := Subgroup.Normal.comap hH _
  by_cases hfix : MulAction.fixedPoints N X = Set.univ
  · left
    rw [eq_bot_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective h
    have hnN : n ∈ N := hh
    have : n ∈ Subgroup.center G := by
      apply hker
      intro x
      have hx : x ∈ MulAction.fixedPoints N X := hfix ▸ Set.mem_univ x
      exact hx ⟨n, hnN⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff n).mpr this
  · right
    have hle := I.commutator_le N hfix
    rw [hperf, top_le_iff] at hle
    rw [eq_top_iff]
    intro h _
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective h
    have : n ∈ N := hle ▸ Subgroup.mem_top n
    exact this

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem isQuasisimple_elementaryGroup_of_preprimitive (P : HypPair Q) (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hA : HasAnisoPerp Q) {τ : K} (hτ : τ ≠ 0)
    (hτ2 : τ ^ 2 ≠ 1)
    (hprim : MulAction.IsPreprimitive (elementaryGroup Q) (singularLines Q)) :
    CFSG.Open.IsQuasisimple ↥(elementaryGroup Q) := by
  obtain ⟨a, ha, hc⟩ := hA P
  refine isQuasisimple_of_iwasawa (iwasawa Q)
    (commutator_elementaryGroup_eq_top_small h2 hQ hA hτ hτ2) ?_ ?_
  · intro g hg
    have hscal := mem_scalars_of_forall_singular_small P ha hc
      (elementaryGroup_le_orthogonalGroup Q g.2) (fun v hv hQv => by
        have := hg (lineMk v hv hQv)
        rw [smul_lineMk, lineMk_eq_lineMk_iff] at this
        obtain ⟨c, hc⟩ := this
        exact ⟨c, hc.symm⟩)
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (commute_of_mem_scalars hscal h.1).symm
  · obtain ⟨g, hg, c, hc0, hgc⟩ := exists_mem_elementaryGroup_apply_e_eq_smul_f P ha hc
    refine ⟨⟨g, hg⟩, lineMk P.e P.e_ne_zero P.Q_e, fun h => ?_⟩
    rw [smul_lineMk, lineMk_eq_lineMk_iff] at h
    obtain ⟨b, hb⟩ := h
    have h1 : (g : V ≃ₗ[K] V) P.e = c • P.f := hgc
    have := congrArg (polar Q P.e) (hb.trans h1)
    rw [polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef] at this
    exact hc0 (by simpa using this.symm)

theorem isQuasisimple_elementaryGroup_of_noOrth (P : HypPair Q) (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hA : HasAnisoPerp Q) {τ : K} (hτ : τ ≠ 0)
    (hτ2 : τ ^ 2 ≠ 1) (hW1 : ∀ P P' : HypPair Q, ¬ P.Orth P') :
    CFSG.Open.IsQuasisimple ↥(elementaryGroup Q) :=
  isQuasisimple_elementaryGroup_of_preprimitive P h2 hQ hA hτ hτ2
    (isPreprimitive_singularLines_of_noOrth hQ hA hW1 P)

end CFSG.ClassicalGroups.Orthogonal.Small
