module

public import CFSG.ClassicalInvolution.Q3.Q3TWY9
public import CFSG.ClassicalInvolution.Q3.Q3TY12
public import CFSG.ClassicalInvolution.RouteD.GapsToralB
public import CFSG.ClassicalInvolution.Q3.Q3TY6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem twin_locImg_le3 (c : TCtx3 tY nY Ω K z) {T : Subgroup G} (hT : IsTwinAt Ω K T z) :
    locImg Ω z T ≤ c.d.Q₁ := by
  by_contra hTQ
  obtain ⟨R, hR, hTR⟩ := c.exists_fund_of_ne hT.mem hT.ne hTQ
  obtain ⟨R', hR', W, hW⟩ := c.hY.std R hR
  obtain ⟨N', hN'z, -, -, hN'R⟩ := c.exists_member_of_fund hR'
  have hne : N' ≠ T := fun h => by
    subst h
    exact ne_of_linearBlockStandardPair hW
      (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.hY.pow3 R hR) (c.hY.pow3 R' hR')
        (by rw [← hTR, hN'R]))
  have hc := hT.comm_T N' hN'z hne
  exact not_commutes_of_linearBlockStandardPair hW
    ((c.commutes_iff_fund hT.mem hN'z hR hTR hN'R).mp hc)

theorem conjSub_layer_member3 (c : TCtx3 tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNQ : ¬ locImg Ω z N ≤ c.d.Q₁) :
    conjSub t N ∈ centralizingMembers Ω {z} ∧ conjSub t N ≠ K ∧
      ¬ locImg Ω z (conjSub t N) ≤ c.d.Q₁ := by
  have hΩ := c.hΩ.conjInvariant
  have hNz := conjSub_mem_centralizingMembers3 hΩ htz hN
  refine ⟨hNz, fun h => hNK ?_, fun h => ?_⟩
  · have := congrArg (conjSub t) h
    rwa [conjSub_conjSub_self h2t, hKt] at this
  · obtain ⟨T, hT, hTeq⟩ := c.exists_twin
    have hconj := c.conjSub_twin_eq3 htz h2t hKt hT hTeq.le
    have h1 := c.eq_of_locImg_le_Q₁ hNz hT h hTeq.le
    apply hNQ
    have : N = T := by rw [← conjSub_conjSub_self h2t N, h1, hconj]
    rw [this, hTeq]

theorem locAut_mem_range3 (c : TCtx3 tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      R.map c.d.ψ) (k : (modelUniv tY nY 3 1 Nat.prime_three).K) :
    locAut c.hΩ.conjInvariant htz (c.d.ψ k) ∈ c.d.ψ.range := by
  have hS : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      (R.map c.d.ψ).map (locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    intro R hR
    obtain ⟨N, hNz, hNK, hNQ, hNeq⟩ := c.exists_member_of_fund hR
    obtain ⟨hN'z, hN'K, hN'Q⟩ := conjSub_layer_member3 c htz h2t hKt hNz hNK hNQ
    obtain ⟨R', -, hR'eq⟩ := c.exists_fund_of_ne hN'z hN'K hN'Q
    rw [← hNeq, locAut_locImg c.hΩ.conjInvariant htz, hR'eq]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hmap : c.d.ψ.range.map (locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hR => hS R hR
  exact hmap ⟨_, ⟨k, rfl⟩, rfl⟩

end Layer

section Model

variable {V : Type} [AddCommGroup V] [Module 𝔽₃ V] {Q : QuadraticForm 𝔽₃ V}

theorem commute_of_fixed3 {X : Type} [Group X] (θ : spinGroup Q →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup Q)) (hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z)
    (σ : X ≃* X) (α : spinGroup Q ≃* spinGroup Q) (hαθ : ∀ y, θ (α y) = σ (θ y))
    {R : Subgroup (spinGroup Q)} (hR : Pow3 R) (hfix : ∀ r ∈ R, σ (θ r) = θ r)
    {g₀ : V ≃ₗ[𝔽₃] V}
    (hconj : ∀ y v, spinAction Q (α y) (g₀ v) = g₀ (spinAction Q y v)) :
    ∀ l ∈ R.map (spinAction Q), g₀ * l = l * g₀ := by
  rintro _ ⟨r, hr, rfl⟩
  have hαr : α r = r := eq_of_fixed_of_pow3 θ hker hcop α σ hαθ hR hfix r hr
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hconj r v, hαr]

end Model

end CFSG.ClassicalInvolution.Q3.Q3TWY
