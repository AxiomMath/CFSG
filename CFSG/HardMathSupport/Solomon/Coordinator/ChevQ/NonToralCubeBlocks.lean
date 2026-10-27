module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreNorm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCubeFrame

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

section Generic

theorem exists_plane_element {G : Type*} [Group G] {E₀ : Subgroup G}
    (hc : Nat.card E₀ = 3 ^ 3) :
    ∃ P : Subgroup G, P ≤ E₀ ∧ Nat.card P = 3 ^ 2 ∧
      ∃ z ∈ E₀, z ∉ P ∧ E₀ ≤ P ⊔ Subgroup.zpowers z := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨P, hPE, hPc⟩ := exists_subgroup_card_sq_le hp3 hc
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hPc]; norm_num)
  obtain ⟨z, hzE, hzP⟩ : ∃ z ∈ E₀, z ∉ P := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show E₀ ≤ P from fun x hx => h x hx)
    rw [hc, hPc] at hle
    omega
  refine ⟨P, hPE, hPc, z, hzE, hzP, ?_⟩
  set C := P ⊔ Subgroup.zpowers z with hC
  have hCE : C ≤ E₀ := sup_le hPE (Subgroup.zpowers_le.2 hzE)
  have hPC : P ≤ C := le_sup_left
  have hzC : z ∈ C := (le_sup_right : Subgroup.zpowers z ≤ C) (Subgroup.mem_zpowers z)
  have hlt : P < C := lt_of_le_of_ne hPC fun h => hzP (h ▸ hzC)
  haveI : Finite C :=
    Finite.of_injective (Subgroup.inclusion hCE) (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card C ∣ 3 ^ 3 := hc ▸ Subgroup.card_dvd_of_le hCE
  obtain ⟨k, hk3, hkC⟩ := (Nat.dvd_prime_pow hp3).1 h2
  rw [hPc, hkC] at h1
  have hk : k = 3 := by
    have : 2 < k := (Nat.pow_lt_pow_iff_right hp3.one_lt).1 h1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hCE (by rw [hc, hkC, hk])).symm.le

end Generic

section Finish

variable {τ : Tag} {K : Type} [Field K] [Finite K]


theorem CubeFrame.normalizes_of_blocks (hτ : τ = Tag.E7 ∨ τ = Tag.E8) (hCore : NonToralBlockCore)
    {E₀ P : Subgroup (adjointGroup τ K)} (hE₀ : IsElemAbelian 3 E₀) (hPE : P ≤ E₀)
    {D : LangPlaneData τ K P} {z : adjointGroup τ K} (hz : z ∈ E₀)
    (hE : E₀ ≤ P ⊔ Subgroup.zpowers z) (F : CubeFrame D z)
    (B : KernelBlocks τ (familyKernel F.a))
    (hB : ∀ j : Fin 3, (fun α => F.ω • α) '' B.blk j = B.blk (j + 1)) :
    NormalizesRGroup (ringChar K) E₀ := by
  classical
  obtain ⟨u₁, k, hu₁G, hu₁M, hu₁r, hF, h12, hnt⟩ :=
    hCore τ hτ K D.Fr D.hFr F.a B F.b F.ω hB F.m F.x F.m_mem F.x_stab
  have hz3 : z ^ 3 = 1 := hE₀.2 z hz
  have hPz : ∀ p ∈ P, Commute z p := fun p hp =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨z, hz⟩ ⟨p, hPE hp⟩)
  obtain ⟨u, hu1, hur, hcu⟩ := exists_rational_centralizing_of_frame_orbit hτ D.Fr D.hFr F.g
    F.g_mem E₀ P z hz3 hE hPz (monomialElt τ (AlgebraicClosure K) F.b F.ω)
    (F.m * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) F.x) F.conj_z F.frame u₁ k hu₁G
    hu₁r hF h12 hnt (fun p hp => F.commute_plane hu₁M p hp)
  exact SeitzExcOpenRest4.normalizesRGroup_of_commute hu1 hur hcu

end Finish

section Toral

variable {τ : Tag} {K : Type} [Field K] [Finite K]


theorem CubeFrame.nonempty_langPlaneData {P : Subgroup (adjointGroup τ K)}
    {D : LangPlaneData τ K P} {z : adjointGroup τ K} (F : CubeFrame D z)
    (hmon : MonomialToralAt τ 3) (hK3 : ¬ 3 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup τ K)}
    (hE₀ : IsElemAbelian 3 E₀) (hz : z ∈ E₀) (hE : E₀ ≤ P ⊔ Subgroup.zpowers z)
    (hω : F.ω ∈ kernelWeylGroup (familyChar F.a)) : Nonempty (LangPlaneData τ K E₀) := by
  obtain ⟨h, hh, hh'⟩ := F.exists_torus hmon hK3 hE (hE₀.2 z hz) hω
  exact SeitzExcOpenRest8bAux.langPlaneData_of_toral Nat.prime_three hK3 hE₀.2 hh hh'

end Toral

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
