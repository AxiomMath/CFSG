module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeKillStatement
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListDescent

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]


theorem twistedE6_rootSpan_le_posUnipotent {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β ∧ 0 < height β) :
    rootSpan TwistTag.E6.tag K S ≤ posUnipotent TwistTag.E6.tag K :=
  classDescent_rootSpan_mono hS

theorem twistedE6_mem_graphFixedRootGroup_of_rootSpan (σ : K →+* K)
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β ∧ 0 < height β) {p : ModGL TwistTag.E6.tag K}
    (hp : p ∈ rootSpan TwistTag.E6.tag K S) (hpΓ : p ∈ twistedFixedGroup TwistTag.E6 K σ) :
    p ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (Subgroup.mem_inf.2 ⟨twistedE6_rootSpan_le_posUnipotent hS hp, hpΓ⟩)

theorem twistedE6_level_step [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (hkill : TwistedE6Kill K σ) (J : List (Fin TwistTag.E6.tag.rank))
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    (word : Fin TwistTag.E6.tag.rank → List (Fin TwistTag.E6.foldedTag.rank))
    (θ γ : Fin TwistTag.E6.tag.rank → ℤ) (PL PS : List (Fin TwistTag.E6.tag.rank → ℤ))
    (hω : ∀ i ∈ J, ∀ a ∈ word i, ∀ j ∈ TwistTag.E6.orbitWord a, j ∈ J)
    (hL : ∀ i ∈ J, TwistTag.E6.perm i = i →
      twistedE6RelAct (word i) (Pi.single i 1) = θ ∧
        ∀ δ ∈ twistedE6PosRoots, (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ J → δ l = 0) →
          classKillPair i δ = 0 → twistedE6RelAct (word i) δ ∈ PL)
    (hS : ∀ i ∈ J, TwistTag.E6.perm i ≠ i →
      twistedE6RelAct (word i) (Pi.single i 1) = γ ∧
        twistedE6RelAct (word i) (Pi.single (TwistTag.E6.perm i) 1) =
          permLattice TwistTag.E6.perm γ ∧
        ∀ δ ∈ twistedE6PosRoots, (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ J → δ l = 0) →
          classKillPair i δ = 0 → classKillPair (TwistTag.E6.perm i) δ = 0 →
            twistedE6RelAct (word i) δ ∈ PS)
    {ℓ : ModGL TwistTag.E6.tag K}
    (hℓ : ℓ ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag {j | j ∈ J}))
    (hℓΓ : ℓ ∈ twistedFixedGroup TwistTag.E6 K σ) (h2 : ℓ ^ 2 = 1) (h1 : ℓ ≠ 1) :
    ∃ g ∈ cascadeConjGroup TwistTag.E6.tag K {j | j ∈ J},
      g ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      ((∃ c : K, c ≠ 0 ∧ σ c = c ∧ ∃ z ∈ rootSpan TwistTag.E6.tag K {δ | δ ∈ PL},
          z ∈ twistedFixedGroup TwistTag.E6 K σ ∧
          g * ℓ * g⁻¹ = pinnedX TwistTag.E6.tag K θ c * z) ∨
        (∃ c : K, c ≠ 0 ∧ ∃ z ∈ rootSpan TwistTag.E6.tag K {δ | δ ∈ PS},
          z ∈ twistedFixedGroup TwistTag.E6 K σ ∧
          g * ℓ * g⁻¹ = twistedE6PairX σ γ c * z)) := by
  set J' : Set (Fin TwistTag.E6.tag.rank) := {j | j ∈ J} with hJ'def
  have hJ' : ∀ j ∈ J', TwistTag.E6.perm j ∈ J' := fun j hj => hJ j hj
  have hΓC : graphFixedRootGroup TwistTag.E6 K σ ≤ twistedFixedGroup TwistTag.E6 K σ :=
    graphFixedRootGroup_le _ _ _
  obtain ⟨ω, hωJ, i, hiJ, hmem, hnot⟩ :=
    exists_twistedE6RelWeyl_conj_not_mem_simpleRadical J' hJ' hℓ h1
  set n := twistedE6RelWeyl K ω with hn
  have hnC : n ∈ graphFixedRootGroup TwistTag.E6 K σ := twistedE6RelWeyl_mem σ ω
  have hnG : n ∈ cascadeConjGroup TwistTag.E6.tag K J' :=
    twistedE6RelWeyl_mem_cascadeConjGroup hωJ
  set y := n * ℓ * n⁻¹ with hy
  have hyΓ : y ∈ twistedFixedGroup TwistTag.E6 K σ :=
    mul_mem (mul_mem (hΓC hnC) hℓΓ) (inv_mem (hΓC hnC))
  have hy2 : y ^ 2 = 1 := by rw [hy, conj_pow, h2, mul_one, mul_inv_cancel]
  obtain ⟨c, u, hu, hyeq⟩ := classDescent_exists_pinnedX_mul hiJ hmem
  have hc : c ≠ 0 := fun hc0 => hnot (by
    rw [hyeq, hc0, pinnedX_zero, one_mul]
    refine classDescent_rootSpan_mono ?_ hu
    rintro α ⟨hα, hαi⟩
    exact ⟨hα.2.1, hα.2.2, hαi⟩)
  have hperp : ∀ {δ : Fin TwistTag.E6.tag.rank → ℤ},
      δ ∈ parabolicPosRoots TwistTag.E6.tag J' →
        δ ∈ twistedE6PosRoots ∧ ∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ J → δ l = 0 :=
    fun hδ => ⟨mem_twistedE6PosRoots hδ.2.1 hδ.2.2, fun l _ hl => hδ.1.2 l hl⟩
  set n' := twistedE6RelWeyl K (word i) with hn'
  have hn'C : n' ∈ graphFixedRootGroup TwistTag.E6 K σ := twistedE6RelWeyl_mem σ _
  have hn'G : n' ∈ cascadeConjGroup TwistTag.E6.tag K J' :=
    twistedE6RelWeyl_mem_cascadeConjGroup (hω i hiJ)
  have hVJ : rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J') ≤
      cascadeConjGroup TwistTag.E6.tag K J' := rootSpan_le_cascadeConjGroup J'
  by_cases hi : TwistTag.E6.perm i = i
  ·
    have hσc : σ c = c := twistedE6_sigma_eq_of_fixed σ hJ' hi hu (hyeq ▸ hyΓ)
    have hxC : pinnedX TwistTag.E6.tag K (Pi.single i 1) c ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_single _ i)
        (by rw [twistedE6_permLattice_single, hi]) hσc
    have huΓ : u ∈ twistedFixedGroup TwistTag.E6 K σ := by
      have : u = (pinnedX TwistTag.E6.tag K (Pi.single i 1) c)⁻¹ * y := by rw [hyeq]; group
      rw [this]
      exact mul_mem (inv_mem (hΓC hxC)) hyΓ
    obtain ⟨p, hp, hpΓ, u'', hu'', hu''Γ, hpe⟩ :=
      hkill.1 J' hJ' i hiJ hi c hc hσc u hu huΓ (by rw [← hyeq]; exact hy2)
    obtain ⟨hθ, hPL⟩ := hL i hiJ hi
    set z := n' * u'' * n'⁻¹ with hz
    have hzP : z ∈ rootSpan TwistTag.E6.tag K {δ | δ ∈ PL} :=
      twistedE6RelWeyl_conj_mem_rootSpan (word i) (fun β hβ => hβ.1.1.1) (fun β hβ => by
        obtain ⟨h1, h2⟩ := hperp hβ.1
        exact hPL β h1 h2 hβ.2) hu''
    have hpC : p ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      twistedE6_mem_graphFixedRootGroup_of_rootSpan σ (fun β hβ => hβ.1.2) hp hpΓ
    refine ⟨n' * p * n, mul_mem (mul_mem hn'G (hVJ (classDescent_rootSpan_mono
      Set.sdiff_subset hp))) hnG, mul_mem (mul_mem hn'C hpC) hnC, Or.inl ⟨c, hc, hσc, z, hzP,
      mul_mem (mul_mem (hΓC hn'C) hu''Γ) (inv_mem (hΓC hn'C)), ?_⟩⟩
    have e1 : n' * pinnedX TwistTag.E6.tag K (Pi.single i 1) c * n'⁻¹ =
        pinnedX TwistTag.E6.tag K θ c := by
      rw [hn', twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ i), hθ]
    calc n' * p * n * ℓ * (n' * p * n)⁻¹ = n' * (p * y * p⁻¹) * n'⁻¹ := by rw [hy]; group
      _ = n' * pinnedX TwistTag.E6.tag K (Pi.single i 1) c * n'⁻¹ * z := by
          rw [hyeq, hpe, hz]; group
      _ = pinnedX TwistTag.E6.tag K θ c * z := by rw [e1]
  ·
    have hρiJ : TwistTag.E6.perm i ∈ J' := hJ' i hiJ
    have hne := twistedE6_single_ne_single_perm hi
    have hρS : (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) ∈
        parabolicPosRoots TwistTag.E6.tag J' \ {Pi.single i 1} :=
      ⟨⟨⟨isRoot_single _ _, fun l hl => Pi.single_eq_of_ne (by rintro rfl; exact hl hρiJ) 1⟩,
        isRoot_single _ _, by rw [height_single]; exact one_pos⟩,
        fun h => hne (Set.mem_singleton_iff.1 h).symm⟩
    obtain ⟨c', u', hu', hueq⟩ := twistedE6_exists_pinnedX_mul_of_closed
      (fun α hα => hα.1.2) (twistedE6_parabolic_diff_closed J' (T := {Pi.single i 1})
        fun β hβ => by rw [Set.mem_singleton_iff.1 hβ, height_single]) hρS hu
    have hsets : ((parabolicPosRoots TwistTag.E6.tag J' \ {Pi.single i 1}) \
        {Pi.single (TwistTag.E6.perm i) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
          parabolicPosRoots TwistTag.E6.tag J' \
            {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1} := by
      rw [Set.sdiff_sdiff, Set.singleton_union]
    rw [hsets] at hu'
    have hyeq' : y = pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) c' * u' := by
      rw [hyeq, hueq, mul_assoc]
    have hc' : c' = σ c := twistedE6_eq_sigma_of_pair σ hJ' hi hu' (hyeq' ▸ hyΓ)
    have hpair : twistedE6PairX σ (Pi.single i 1) c =
        pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
          pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) c' := by
      rw [twistedE6PairX, twistedE6_permLattice_single, hc']
    have hyeq'' : y = twistedE6PairX σ (Pi.single i 1) c * u' := by rw [hyeq', hpair]
    have hPC : twistedE6PairX σ (Pi.single i 1) c ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_single _ i) c
    have hu'Γ : u' ∈ twistedFixedGroup TwistTag.E6 K σ := by
      have : u' = (twistedE6PairX σ (Pi.single i 1) c)⁻¹ * y := by rw [hyeq'']; group
      rw [this]
      exact mul_mem (inv_mem (hΓC hPC)) hyΓ
    obtain ⟨p, hp, hpΓ, u'', hu'', hu''Γ, hpe⟩ :=
      hkill.2 J' hJ' i hiJ hi c hc u' hu' hu'Γ (by rw [← hyeq'']; exact hy2)
    obtain ⟨hγ1, hγ2, hPS⟩ := hS i hiJ hi
    set z := n' * u'' * n'⁻¹ with hz
    have hzP : z ∈ rootSpan TwistTag.E6.tag K {δ | δ ∈ PS} :=
      twistedE6RelWeyl_conj_mem_rootSpan (word i) (fun β hβ => hβ.1.1.1.1) (fun β hβ => by
        obtain ⟨h1, h2⟩ := hperp hβ.1.1
        exact hPS β h1 h2 hβ.1.2 hβ.2.2) hu''
    have hpC : p ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      twistedE6_mem_graphFixedRootGroup_of_rootSpan σ (fun β hβ => hβ.1.2) hp hpΓ
    refine ⟨n' * p * n, mul_mem (mul_mem hn'G (hVJ (classDescent_rootSpan_mono
      Set.sdiff_subset hp))) hnG, mul_mem (mul_mem hn'C hpC) hnC, Or.inr ⟨c, hc, z, hzP,
      mul_mem (mul_mem (hΓC hn'C) hu''Γ) (inv_mem (hΓC hn'C)), ?_⟩⟩
    have e1 : n' * twistedE6PairX σ (Pi.single i 1) c * n'⁻¹ = twistedE6PairX σ γ c := by
      rw [twistedE6PairX, twistedE6PairX, twistedE6_permLattice_single,
        show n' * (pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
            pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c)) * n'⁻¹ =
          (n' * pinnedX TwistTag.E6.tag K (Pi.single i 1) c * n'⁻¹) *
            (n' * pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c) * n'⁻¹) by
          group, hn', twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ i),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), hγ1, hγ2]
    calc n' * p * n * ℓ * (n' * p * n)⁻¹ = n' * (p * y * p⁻¹) * n'⁻¹ := by rw [hy]; group
      _ = n' * twistedE6PairX σ (Pi.single i 1) c * n'⁻¹ * z := by
          rw [hyeq'', hpe, hz]; group
      _ = twistedE6PairX σ γ c * z := by rw [e1]

end CFSG.SeitzReduction
