module

public import CFSG.ClassicalInvolution.Q3.Q3ExcFrob
public import CFSG.ClassicalInvolution.Q3.Q3ExcBN
public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwDatum
public import CFSG.ClassicalInvolution.Q3.Q3ExcComp

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.LieType.AlgebraicGroups
open scoped Pointwise

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

structure Exc3Frob (c : ModGL τ k) : Prop where
  frob : ∀ x : adjointGroup τ k, (D.F x : ModGL τ k) = frobTwistGL τ k p₀ D.e c x
  normalizes : c ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k))
  sq_mem : c * c ∈ torusGroup τ k

variable {D}

namespace Exc3Frob

variable {c : ModGL τ k} (h : Exc3Frob D c)

include h

theorem frob_mem_kernelSpan {s : ModGL τ k} (hs : s ∈ D.kernelSpan) :
    frobTwistGL τ k p₀ D.e c s ∈ D.kernelSpan := by
  have hsG : s ∈ adjointGroup τ k := rootSpan_le_adjointGroup k _ hs
  have hmap := D.map_rootSpan_subgroupOf (S := kernelRoots D.χ) (fun _ h => h)
    D.bijOn_kernelRoots
  have h1 : D.F ⟨s, hsG⟩ ∈ ((rootSpan τ k (kernelRoots D.χ)).subgroupOf (adjointGroup τ k)).map
      D.F.toMonoidHom := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  rw [hmap] at h1
  have h2 := Subgroup.mem_subgroupOf.1 h1
  rw [h.frob] at h2
  exact h2

theorem pow_mem_kernelFixedGroup {x : adjointGroup τ k} (hx : x ∈ D.totalFixedGroup) :
    x ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ D.kernelFixedGroup := by
  obtain ⟨hxM, hxF⟩ := D.mem_totalFixedGroup.1 hx
  have hxF' : frobTwistGL τ k p₀ D.e c (x : ModGL τ k) = x := by
    rw [← h.frob, hxF]
  have hpow := exc3_pow_mem_rootSpan_of_fixed D.e h.normalizes h.sq_mem
    (S := D.kernelSpan) (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
    (fun s hs => h.frob_mem_kernelSpan hs) hxM hxF'
  refine D.mem_kernelFixedGroup.2 ⟨?_, ?_⟩
  · simpa using hpow
  · rw [map_pow, hxF]

theorem pow_mem_orbitGroupC {γ : adjointGroup τ k} (hγ : γ ∈ D.fixedGroup) :
    γ ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ D.orbitGroupC := by
  have hmul : γ ∈ (D.fixedTorus : Set (adjointGroup τ k)) *
      (D.orbitGroupC : Set (adjointGroup τ k)) := by
    rw [← D.coe_fixedGroup_eq_mul]
    exact hγ
  obtain ⟨t, ht, c', hc', rfl⟩ := hmul
  have hT := D.mem_fixedTorus.1 ht
  have htT : (t : ModGL τ k) ∈ torusGroup τ k := unionTorus_le_torusGroup hT.1
  have htF : frobTwistGL τ k p₀ D.e c (t : ModGL τ k) = t := by rw [← h.frob, hT.2]
  have hpow : (t : ModGL τ k) ^ ((p₀ ^ D.e) ^ 2 - 1) = 1 :=
    exc3_pow_eq_one_of_fixed_torus D.e h.normalizes h.sq_mem htT htF
  set N := D.orbitGroupC.subgroupOf D.fixedGroup with hNdef
  have hN : N.Normal := D.orbitGroupC_normal
  let t' : D.fixedGroup := ⟨t, D.fixedTorus_le_fixedGroup ht⟩
  let c'' : D.fixedGroup := ⟨c', D.orbitGroupC_le_fixedGroup hc'⟩
  have hc''N : c'' ∈ N := Subgroup.mem_subgroupOf.2 hc'
  have ht'pow : t' ^ ((p₀ ^ D.e) ^ 2 - 1) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hpow
  have hmem : (t' * c'') ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff c'').2 hc''N, mul_one, ← QuotientGroup.mk_pow, ht'pow,
      QuotientGroup.mk_one]
  have := Subgroup.mem_subgroupOf.1 hmem
  simpa using this

theorem frob_eq_of_mem_orbitGroup {z : ModGL τ k} (hz : z ∈ D.orbitGroup) :
    frobTwistGL τ k p₀ D.e c z = z := by
  have hzG : z ∈ adjointGroup τ k := D.orbitGroup_le_adjointGroup hz
  have hzC : (⟨z, hzG⟩ : adjointGroup τ k) ∈ D.orbitGroupC := Subgroup.mem_subgroupOf.2 hz
  have h1 := (D.mem_fixedGroup.1 (D.orbitGroupC_le_fixedGroup hzC)).2
  have h2 := h.frob ⟨z, hzG⟩
  rw [h1] at h2
  exact h2.symm

theorem exc3Big_orbitGroup (hq3 : p₀ ^ D.e = 3) (hq : CFSG.IsQuasisimple D.orbitGroup) :
    Exc3Big D.orbitGroup := by
  refine ⟨hq, fun z hz hzc => ?_⟩
  have hT : z ∈ torusGroup τ k := exc3_center_orbitGroup_le_torus D hq.1 z hz hzc
  have hF := h.frob_eq_of_mem_orbitGroup hz
  have := exc3_pow_eq_one_of_fixed_torus D.e h.normalizes h.sq_mem hT hF
  rw [hq3] at this
  exact ⟨3, by simpa using this⟩

end Exc3Frob

theorem exc3_simpleRoots_orthogonal_of_orbits_eq {O₀ : Set (Fin τ.rank → ℤ)}
    (hA : D.orbits = {O₀}) {i : KernelComponent D.χ} (hi : i ∈ D.J) :
    ∀ β ∈ simpleRoots (componentRoots D.χ i), ∀ β' ∈ simpleRoots (componentRoots D.χ i),
      β ≠ β' → iform β β' = 0 := by
  intro β hβ β' hβ' hne
  have hΔ : ∀ γ ∈ simpleRoots (componentRoots D.χ i), γ ∈ D.simpleRootsJ := fun γ hγ =>
    D.mem_simpleRootsJ_iff.2 ⟨i, hi, hγ⟩
  have hO₀ : O₀ ∈ D.orbits := by rw [hA]; exact Set.mem_singleton O₀
  have hmem : ∀ γ ∈ simpleRoots (componentRoots D.χ i), γ ∈ O₀ := fun γ hγ => by
    have h1 := D.thetaOrbit_mem_orbits (hΔ γ hγ)
    rw [hA, Set.mem_singleton_iff] at h1
    rw [← h1]
    exact self_mem_thetaOrbit _ _
  have hβK : β ∈ kernelRoots D.χ := D.mem_kernelRoots_of_mem_simpleRootsJ (hΔ β hβ)
  have hO₀β := D.eq_thetaOrbit_of_mem_orbits hO₀ (hmem β hβ)
  exact D.orbit_orthogonal β hβK β (self_mem_thetaOrbit _ _) β'
    (by rw [← hO₀β]; exact hmem β' hβ') hne

theorem exc3_isQuasisimple_orbitGroup (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hnon : ∀ β ∈ kernelRoots D.χ, ∃ γ ∈ kernelRoots D.χ, iform β γ = 1) :
    CFSG.IsQuasisimple D.orbitGroup := by
  by_cases h2 : 2 ≤ D.orbits.ncard
  · exact (orthogonal_semilinear_fixed_root_quasisimplicity D).2.2.1 h2
  · exfalso
    obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
    obtain ⟨α₀, hα₀⟩ := Quotient.exists_rep i₀
    have hα₀K : α₀.1 ∈ componentRoots D.χ i₀ := ⟨α₀.2, by rw [← hα₀]⟩
    have hi₀ : i₀ ∈ D.J := by
      rw [hJ]
      exact ⟨0, α₀.1, hα₀K, α₀.1, hα₀K, by simp⟩
    obtain ⟨-, -, β₀, hβ₀, -⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i₀) hα₀K
    have hβ₀J : β₀ ∈ D.simpleRootsJ := D.mem_simpleRootsJ_iff.2 ⟨i₀, hi₀, hβ₀⟩
    have hne : D.orbits.Nonempty := ⟨_, D.thetaOrbit_mem_orbits hβ₀J⟩
    have hfin : D.orbits.Finite := CFSG.ClassicalInvolution.Upgrade.finite_orbits D
    have hcard : D.orbits.ncard = 1 := by
      have := (Set.ncard_pos hfin).2 hne
      omega
    obtain ⟨O₀, hO₀⟩ := Set.ncard_eq_one.1 hcard
    exact CFSG.ClassicalInvolution.Upgrade.false_of_orthogonal_simpleRoots hτ i₀ hβ₀
      (exc3_simpleRoots_orthogonal_of_orbits_eq hO₀ hi₀) hnon

section SingleClass

variable [Subsingleton (KernelComponent D.χ)]

theorem exc3_rootSpanJ_eq_kernelSpan : D.rootSpanJ = D.kernelSpan := by
  have hall : ∀ i : KernelComponent D.χ, i ∈ D.J := by
    intro i
    obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
    obtain ⟨α₀, hα₀⟩ := Quotient.exists_rep i₀
    have hα₀K : α₀.1 ∈ componentRoots D.χ i₀ := ⟨α₀.2, by rw [← hα₀]⟩
    have hi₀ : i₀ ∈ D.J := by
      rw [hJ]
      exact ⟨0, α₀.1, hα₀K, α₀.1, hα₀K, by simp⟩
    rwa [Subsingleton.elim i i₀]
  unfold OrthogonalSemilinearFixedRootDatum.rootSpanJ OrthogonalSemilinearFixedRootDatum.kernelSpan
    unionRootSpan
  congr 1
  ext α
  exact ⟨fun hα => hα.1, fun hα => ⟨hα, hall _⟩⟩

theorem exc3_kernelFixedGroup_eq_fixedGroup : D.kernelFixedGroup = D.fixedGroup := by
  ext x
  rw [D.mem_kernelFixedGroup, D.mem_fixedGroup, exc3_rootSpanJ_eq_kernelSpan]

variable {c : ModGL τ k} (h : Exc3Frob D c)

include h

theorem Exc3Frob.pow_pow_mem_orbitGroupC {x : adjointGroup τ k} (hx : x ∈ D.totalFixedGroup) :
    (x ^ ((p₀ ^ D.e) ^ 2 - 1)) ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ D.orbitGroupC := by
  have h1 := h.pow_mem_kernelFixedGroup hx
  rw [exc3_kernelFixedGroup_eq_fixedGroup] at h1
  exact h.pow_mem_orbitGroupC h1

end SingleClass

end CFSG.ClassicalInvolution.Q3
