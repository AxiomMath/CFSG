module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAut
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.InducedInner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslType

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB

section Shell

variable {Xs Gs T : Type} [Group Xs] [Finite Xs] [Group Gs] [Group T] [Finite T]

theorem s1431_false_of_lift_blocks_gl (π : Xs →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Xs) (act : Gs →* MulAut Xs) (actT : Gs →* MulAut T)
    (hact : ∀ (g : Gs) (x : Xs), π (act g x) = actT g (π x))
    {A : Subgroup (MulAut T)} {ψ : MulAut T} {J : Subgroup T} {q : ℕ} (c : S1431Cfg T A ψ J q)
    (hA : ∀ a ∈ A, ∃ g : Gs, actT g = a)
    (data : ∀ g : Gs, actT g ^ 3 = 1 → actT g ≠ 1 → Group.IsSolvable ↥(fixSub (actT g)) ∨
      ∃ (ι : Type) (_ : Finite ι) (N : ι → Subgroup Xs),
        (∀ y : T, actT g y = y ↔ y ∈ (fixSubgroup (act g)).map π) ∧
        (∀ i, N i ≤ fixSubgroup (act g)) ∧
        (∀ i, ∀ x ∈ fixSubgroup (act g), ∀ m ∈ N i, x * m * x⁻¹ ∈ N i) ∧
        (∀ i, CFSG.IsQuasisimple (N i)) ∧
        (∃ k : ℕ, ∀ x ∈ derivedSeries ↥(fixSubgroup (act g)) k, (x : Xs) ∈ ⨆ i, N i) ∧
        (∀ i, IsTypeL2 q (N i) → ∀ h : Gs, actT h ^ 3 = 1 → actT h * actT g = actT g * actT h →
          ∃ s ∈ N i, ∀ m ∈ N i, act h m = s * m * s⁻¹)) : False := by
  classical
  refine c.false_of_induced_inner ?_
  intro η hηA hηψ hstab
  obtain ⟨g, hg⟩ := hA ψ c.mem
  obtain ⟨h, hh⟩ := hA η hηA
  have hψ3 : ψ ^ 3 = 1 := c.elemAbelian.2 ψ c.mem
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  have hcomm : η * ψ = ψ * η := by
    have := c.elemAbelian.1.is_comm.comm ⟨η, hηA⟩ ⟨ψ, c.mem⟩
    exact congrArg Subtype.val this
  rcases data g (by rw [hg]; exact hψ3) (by rw [hg]; exact c.ne_one) with hsolv | hdata
  · exfalso
    rw [hg] at hsolv
    have hJX : J ≤ fixSub ψ := c.comp.1
    haveI : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJX)
    haveI : Group.IsSolvable (barOf 3 J) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J))
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple
      (isQuasisimple_quotient_of_glaPComponent c.comp) this
  obtain ⟨ι, hfin, N, htw, hNc, hNn, hNq, hk, key⟩ := hdata
  set C := fixSubgroup (act g) with hC
  set X := fixSub ψ with hX
  have hXC : X = C.map π := by
    ext y
    rw [hX, mem_fixSub, ← hg]
    exact htw y
  have hJ : GLAPComponent 3 X J := c.comp
  let N' : ι → Subgroup T := fun i => (N i).map π
  have hNX : ∀ i, N' i ≤ X := fun i => by
    rw [hXC]
    exact Subgroup.map_mono (hNc i)
  have hNn' : ∀ i, ∀ x ∈ X, ∀ m ∈ N' i, x * m * x⁻¹ ∈ N' i := by
    intro i x hx m hm
    rw [hXC] at hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact ⟨x0 * m0 * x0⁻¹, hNn i x0 hx0 m0 hm0, by simp⟩
  have hNq' : ∀ i, CFSG.IsQuasisimple (N' i) := by
    intro i
    refine CFSG.LocalCores.isQuasisimple_map (hNq i) π fun hle => ?_
    have hle' : N i ≤ Subgroup.centralizer (N i : Set Xs) := fun x hx =>
      (Subgroup.mem_centralizer_iff).2 fun y hy => (Subgroup.mem_center_iff.mp (hker (hle hx)) y)
    exact not_le_centralizer_of_isQuasisimple (isQuasisimple_open (hNq i)) hle'
  have hk' : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : T) ∈ ⨆ i, N' i := by
    obtain ⟨k, hk⟩ := hk
    have hmemX : ∀ x : ↥C, π (x : Xs) ∈ X := by
      intro x
      rw [hXC]
      exact ⟨_, x.2, rfl⟩
    let π' : ↥C →* ↥X := (π.comp C.subtype).codRestrict X hmemX
    have hπ's : Function.Surjective π' := by
      intro z
      have hz : (z : T) ∈ C.map π := by
        rw [← hXC]
        exact z.2
      obtain ⟨x, hx, hxz⟩ := hz
      exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
    refine ⟨k, fun x hx => ?_⟩
    rw [← map_derivedSeries_eq hπ's k] at hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    have hmem := hk x0 hx0
    have h2 : π (x0 : Xs) ∈ (⨆ i, N i).map π := ⟨_, hmem, rfl⟩
    rw [Subgroup.map_iSup] at h2
    exact h2
  have hφX : ∀ y : T, η y ∈ X ↔ y ∈ X := by
    intro y
    rw [hX, mem_fixSub, mem_fixSub]
    have h1 : ψ (η y) = η (ψ y) := by
      have := congrArg (fun a : MulAut T => a y) hcomm
      exact this.symm
    rw [h1]
    exact ⟨fun hy => η.injective hy, fun hy => by rw [hy]⟩
  have hφ : ∀ i, barX 3 X (N' i) = barX 3 X J →
      ∃ m ∈ N' i, ∀ m' ∈ N' i, η m' = m * m' * m⁻¹ := by
    intro i hi
    have hT' : IsTypeL2 q ↥(N' i) :=
      isTypeL2_of_barX_eq hJ (hNX i) (hNn' i) (hNq' i) hi.symm c.typeL2
    have hT : IsTypeL2 q ↥(N i) := by
      refine (isTypeL2_congr_of_central (hNq i).1 (π.subgroupMap (N i))
        (π.subgroupMap_surjective (N i)) ?_).2 hT'
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : π (x : Xs) = 1 := congrArg Subtype.val hx
      have hxc : (x : Xs) ∈ Subgroup.center Xs := hker hx1
      rw [Subgroup.mem_center_iff]
      intro x'
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hxc) (x' : Xs))
    obtain ⟨s, hs, hsm⟩ := key i hT h (by rw [hh]; exact hη3) (by rw [hh, hg]; exact hcomm)
    refine ⟨π s, ⟨s, hs, rfl⟩, ?_⟩
    rintro _ ⟨m0, hm0, rfl⟩
    rw [← hh, ← hact, hsm m0 hm0]
    simp
  obtain ⟨j₀, hj₀, hbj⟩ := exists_inner_of_blocks_aut hJ N' hNX hNn' hNq' hk' hφX hφ
  exact isInnerAut_inducedBarHom_of_barX_aut hJ hstab hj₀ hbj

end Shell

end CFSG.HardMathSupport.Dickson.Sec6.I1431
