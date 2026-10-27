module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SLink
public import CFSG.ClassicalInvolution.Q3.Q3E8BShape
public import CFSG.ClassicalInvolution.Q3.Q3NGStar
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.Q3.Q3TCP1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.NonClassical (F4Layer)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement


section Shape

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {t : StatedLieTag}
  {n : ℕ}

theorem shape_of_visible_f4 (X : XCtx3 t n Ω x) (hRow : F4Row3) (hft : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z) (hKx : K ∈ centralizingMembers Ω {x})
    {R₀ : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)
    (hKR₀ : locImg Ω x K = R₀.map X.ψ)
    (hvis : ∀ N ∈ centralizingMembers Ω {x, z}, locImg Ω x N ≤ X.ψ.range)
    (φP : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃ F4Layer 3 1)
    (hφP : ∀ N N', Commutes N.1 N'.1 ↔ NonClassical.F4Layer.rel (φP N) (φP N'))
    (hKP : ∀ h : K ∈ centralizingMembers Ω {x, z}, φP ⟨K, h⟩ = none) :
    t = .POmegaOdd ∧ n = 4 := by
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

section Partner

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem locElt_central_of_eq {x y : G} (hy : y ∈ locLayer Ω x) (hyx : y = x) :
    ∀ v : locQuot Ω x, v * locElt Ω x y hy = locElt Ω x y hy * v := by
  intro v
  obtain ⟨v', rfl⟩ := QuotientGroup.mk'_surjective _ v
  unfold locElt
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.mp
    (centralizingLayer_le_centralizer Ω {x} v'.2)
  show (v' : G) * y = y * v'
  rw [hyx]
  exact this

theorem map_commutator_of_central {A B : Type*} [Group A] [Group B] (ψ : A →* B) {e : A}
    (he : ∀ v, v * ψ e = ψ e * v) (y : A) : ψ (e * y * e⁻¹ * y⁻¹) = 1 := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← he (ψ y)]
  simp

theorem exists_partner_of_xctx (hpart : F4PartnerFact3) {x : G}
    (X : XCtx3 .POmegaOdd 4 Ω x)
    (hcf : ∀ R ∈ fundamentalSubgroups .POmegaOdd
        (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).D, ∀ r ∈ R,
        r ∈ Subgroup.center (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).K → r = 1)
    {K J : Subgroup G} {z w : G} (hz : IsClassicalMember3 K z) (hw : IsClassicalMember3 J w)
    (hx : z * w = x) (hKx : K ∈ centralizingMembers Ω {x}) (hJx : J ∈ centralizingMembers Ω {x})
    (hKJ : Commutes K J) (hne : K ≠ J)
    {R₀ R₃ : Subgroup (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).D)
    (hR₃ : R₃ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).D)
    (hKR : locImg Ω x K = R₀.map X.ψ) (hJR : locImg Ω x J = R₃.map X.ψ) :
    ∃ β ∈ centralizingMembers Ω {x},
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) ∧
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β J := by
  have hR₀₃ : R₀ ≠ R₃ := by
    intro e
    exact hne (X.eq_of_locImg_eq hKx hJx (by rw [hKR, hJR, e]))
  have hcomm : Commutes R₀ R₃ := (X.commutes_iff_fund hKx hJx hR₀ hKR hJR).mp hKJ
  obtain ⟨r, hr, hψr⟩ := X.exists_involution_of_fund hcf hKx hR₀ hKR hz
  obtain ⟨r', hr', hψr'⟩ := X.exists_involution_of_fund hcf hJx hR₃ hJR hw
  have hzY : z ∈ locLayer Ω x := le_centralizingLayer hKx hz.mem
  have hwY : w ∈ locLayer Ω x := le_centralizingLayer hJx hw.mem
  have hxY : z * w ∈ locLayer Ω x := (locLayer Ω x).mul_mem hzY hwY
  have hE : ∀ v, v * X.ψ (r * r') = X.ψ (r * r') * v := by
    intro v
    have h1 : X.ψ (r * r') = locElt Ω x (z * w) hxY := by
      rw [map_mul, hψr, hψr', locElt_mul hzY hwY]
    rw [h1]
    exact locElt_central_of_eq hxY hx v
  have hcen : ∀ y : (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).K,
      r * r' * y * (r * r')⁻¹ * y⁻¹ ∈
        Subgroup.center (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).K := fun y =>
    X.ker_le (MonoidHom.mem_ker.mpr (map_commutator_of_central X.ψ hE y))
  have hr_ne : r ≠ 1 := fun h => by
    have := hr.2
    rw [h, orderOf_one] at this
    omega
  have hr'_ne : r' ≠ 1 := fun h => by
    have := hr'.2
    rw [h, orderOf_one] at this
    omega
  obtain ⟨R'', hR'', ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩ := hpart R₀ hR₀ R₃ hR₃ hR₀₃ hcomm
    ⟨r, hr.1, hr_ne, r', hr'.1, hr'_ne, hcen⟩
  obtain ⟨β, hβx, hβR⟩ := X.exists_member_of_fund hR''
  exact ⟨β, hβx, X.stdPair_of_fund hKx hβx hW₁ hKR hβR, X.stdPair_of_fund hβx hJx hW₂ hβR hJR⟩

end Partner

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
