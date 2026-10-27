module

public import CFSG.ClassicalInvolution.Q3.Q3E8Facts
public import CFSG.ClassicalInvolution.Q3.Q3E8BXCtx

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false



theorem le_centralizer_mul_of_le3 {G : Type} [Group G] {w₁ w₂ : G} {L : Subgroup G}
    (h₁ : L ≤ Subgroup.centralizer ({w₁} : Set G))
    (h₂ : L ≤ Subgroup.centralizer ({w₂} : Set G)) :
    L ≤ Subgroup.centralizer ({w₁ * w₂} : Set G) := fun k hk => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have a := Subgroup.mem_centralizer_singleton_iff.mp (h₁ hk)
  have b := Subgroup.mem_centralizer_singleton_iff.mp (h₂ hk)
  calc k * (w₁ * w₂) = (k * w₁) * w₂ := by group
    _ = (w₁ * k) * w₂ := by rw [a]
    _ = w₁ * (k * w₂) := by group
    _ = w₁ * (w₂ * k) := by rw [b]
    _ = (w₁ * w₂) * k := by group

section Shape

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {t : StatedLieTag}
  {n : ℕ}

theorem XCtx3.exists_visible_equiv (X : XCtx3 t n Ω x) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember3 K z) (hKx : K ∈ centralizingMembers Ω {x})
    {R₀ : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hKR₀ : locImg Ω x K = R₀.map X.ψ) {k : (modelUniv t n 3 1 Nat.prime_three).K}
    (hk : X.ψ k = locElt Ω x z (le_centralizingLayer hKx hz.mem))
    (hvis : ∀ N ∈ centralizingMembers Ω {x, z}, locImg Ω x N ≤ X.ψ.range) :
    ∃ e : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃
        {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K //
          R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D ∧
            R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n 3 1 Nat.prime_three).K)},
      (∀ N N', Commutes N.1 N'.1 ↔ Commutes (e N).1 (e N').1) ∧
        ∀ h : K ∈ centralizingMembers Ω {x, z}, (e ⟨K, h⟩).1 = R₀ := by
  classical
  have hzY : z ∈ locLayer Ω x := le_centralizingLayer hKx hz.mem
  have hpair : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {x, z} ↔
      N ∈ centralizingMembers Ω {x} ∧ N ≤ Subgroup.centralizer ({z} : Set G) := fun {N} =>
    NonClassical.mem_centralizingMembers_pair
  have hpart : ∀ N : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}},
      ∃ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
        locImg Ω x N.1 = R.map X.ψ := fun N =>
    X.fam_range N.1 (hpair.mp N.2).1 (hvis N.1 N.2)
  choose f hf hfR using hpart
  have hfC : ∀ N, f N ≤ Subgroup.centralizer ({k} : Set (modelUniv t n 3 1 Nat.prime_three).K) :=
    fun N => (X.centralizes_iff (hpair.mp N.2).1 (hf N) (hfR N) hzY hk).mp (hpair.mp N.2).2
  have hinj : Function.Injective fun N : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} =>
      (⟨f N, hf N, hfC N⟩ : {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K //
        R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D ∧
          R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n 3 1 Nat.prime_three).K)}) := by
    intro N N' h
    have h1 : f N = f N' := congrArg Subtype.val h
    exact Subtype.ext (X.eq_of_locImg_eq (hpair.mp N.2).1 (hpair.mp N'.2).1
      ((hfR N).trans ((congrArg (fun R => R.map X.ψ) h1).trans (hfR N').symm)))
  have hsurj : Function.Surjective fun N : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} =>
      (⟨f N, hf N, hfC N⟩ : {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K //
        R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D ∧
          R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n 3 1 Nat.prime_three).K)}) := by
    rintro ⟨R, hR, hRk⟩
    obtain ⟨N, hNx, hNR⟩ := X.exists_member_of_fund hR
    have hNz : N ≤ Subgroup.centralizer ({z} : Set G) :=
      (X.centralizes_iff hNx hR hNR hzY hk).mpr hRk
    have hNv : N ∈ centralizingMembers Ω {x, z} := hpair.mpr ⟨hNx, hNz⟩
    refine ⟨⟨N, hNv⟩, Subtype.ext ?_⟩
    exact X.eq_of_map_eq (hf ⟨N, hNv⟩) hR ((hfR ⟨N, hNv⟩).symm.trans hNR)
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun N N' => ?_, fun h => ?_⟩
  · exact X.commutes_iff_fund (hpair.mp N.2).1 (hpair.mp N'.2).1 (hf N) (hfR N) (hfR N')
  · exact X.eq_of_map_eq (hf ⟨K, h⟩) hR₀ ((hfR ⟨K, h⟩).symm.trans hKR₀)

theorem XCtx3.shape_of_visible_D8 (X : XCtx3 t n Ω x) (hRow : E8D8Row3) (hft : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z) (hKx : K ∈ centralizingMembers Ω {x})
    {R₀ : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hKR₀ : locImg Ω x K = R₀.map X.ψ)
    (hvis : ∀ N ∈ centralizingMembers Ω {x, z}, locImg Ω x N ≤ X.ψ.range)
    (φP : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃ TypeE8.D8Layer 3 1)
    (hφP : ∀ N N', Commutes N.1 N'.1 ↔ TypeE8.D8Layer.rel 3 1 (φP N) (φP N'))
    (hKP : ∀ h : K ∈ centralizingMembers Ω {x, z}, φP ⟨K, h⟩ = none) :
    t = .POmegaPlus ∧ n = 8 := by
  have hzY : z ∈ locLayer Ω x := le_centralizingLayer hKx hz.mem
  obtain ⟨k, hkR, hk⟩ : ∃ k ∈ R₀, X.ψ k = locElt Ω x z hzY := by
    have : locElt Ω x z hzY ∈ R₀.map X.ψ :=
      hKR₀ ▸ locElt_mem_locImg (le_centralizingLayer hKx) hz.mem
    obtain ⟨k, hk, hkψ⟩ := this
    exact ⟨k, hk, hkψ⟩
  have hcent : R₀ ≤ Subgroup.centralizer ({k} : Set (modelUniv t n 3 1 Nat.prime_three).K) := by
    refine (le_centralizer_iff_map3 X.ψ X.ker_le X.ker_cop (X.hpc.pow3 R₀ hR₀) k).mpr ?_
    rw [← hKR₀, hk]
    exact (le_centralizer_iff_locImg3 X.hΩ X.hex X.hP1 X.hO3 hKx ⟨z, hzY⟩).mp
      (isSubnormal_le hz.subnormal)
  have hkc : ∀ r ∈ R₀, r * k = k * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcent hr)
  obtain ⟨e, he, heK⟩ := X.exists_visible_equiv hz hKx hR₀ hKR₀ hk hvis
  refine hRow t n hft hG2 hD4 hadm R₀ hR₀ k hkR hkc (e.symm.trans φP) ?_ ?_
  · intro R R'
    have h1 := he (e.symm R) (e.symm R')
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    exact h1.symm.trans (hφP _ _)
  · intro R hR
    have hKv : K ∈ centralizingMembers Ω {x, z} :=
      NonClassical.mem_centralizingMembers_pair.mpr ⟨hKx, isSubnormal_le hz.subnormal⟩
    have h1 : e ⟨K, hKv⟩ = R := Subtype.ext ((heK hKv).trans hR.symm)
    have h2 : e.symm R = ⟨K, hKv⟩ := by
      rw [← h1]
      exact e.symm_apply_apply _
    show φP (e.symm R) = none
    rw [h2]
    exact hKP hKv

end Shape

theorem cp_at_member3_of_hO3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hR : RouteD3Setup K z)
    (hO3 : LocalOddThreeFree3 (conjClass3 K) z) {N : Subgroup G} (hN : N ∈ conjClass3 K)
    {y : G} (hy : IsClassicalMember3 N y) {L : Subgroup G}
    (hL : L ∈ centralizingMembers (conjClass3 K) {y}) : Commutes N L ∨ L = N := by
  obtain ⟨g, hg⟩ := id hN
  have hyg : y = g * z * g⁻¹ := involution_unique3 hy (hg ▸ hR.cls.conj g)
  have hP1y : LocalOddCentral (conjClass3 K) {y} := by
    rw [hyg]
    exact Gaps.localOddCentral_conj hR.inClass.conjInvariant g z hR.setup.2
  have hO3y : LocalOddThreeFree3 (conjClass3 K) y := by
    rw [hyg]
    exact localOddThreeFree3_conj hR.inClass.conjInvariant g z hO3
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hy.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {y} hync
  have hNy : N ∈ centralizingMembers (conjClass3 K) {y} := ⟨hN, isSubnormal_le hy.subnormal⟩
  exact commutes_or_eq_of_involution3 (Gaps.fundNoncentral 3) hR.inClass hR.setup.1 hP1y hO3y D
    hNy hL hy

end CFSG.ClassicalInvolution.Q3.Q3W
