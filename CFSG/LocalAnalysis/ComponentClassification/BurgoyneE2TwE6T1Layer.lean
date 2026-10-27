module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Layer
public import CFSG.ClassicalInvolution.Q3.Q3ExcE6Data
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Q3 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped commutatorElement Pointwise


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

omit
  [IsAlgClosed k] in
theorem torus_mul_comm_e6 {h h' : ModGL TwistTag.E6.tag k} (hh : h ∈ torusGroup TwistTag.E6.tag k)
    (hh' : h' ∈ torusGroup TwistTag.E6.tag k) : h * h' = h' * h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a hh'

section Derived

variable (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)

theorem commutator_fixedGroup_le_e6 : ⁅D.fixedGroup, D.fixedGroup⁆ ≤ D.orbitGroupC := by
  refine TwE7.commutator_le_of_eq_mul (fun h hh n hn => ?_) D.fixedTorus_le_fixedGroup
    (fun a ha b hb => ?_) (fun h hh => ?_)
  · have hnorm := D.orbitGroupC_normal
    have h1 := hnorm.conj_mem ⟨n, D.orbitGroupC_le_fixedGroup hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.1 h1
  · apply Subtype.ext
    exact torus_mul_comm_e6 (unionTorus_le_torusGroup (D.mem_fixedTorus.1 ha).1)
      (unionTorus_le_torusGroup (D.mem_fixedTorus.1 hb).1)
  · have hmul : h ∈ (D.fixedTorus : Set (adjointGroup TwistTag.E6.tag k)) *
        (D.orbitGroupC : Set (adjointGroup TwistTag.E6.tag k)) := by
      rw [← D.coe_fixedGroup_eq_mul]
      exact hh
    obtain ⟨a, ha, n, hn, rfl⟩ := hmul
    exact ⟨a, ha, n, hn, rfl⟩

theorem commutator_torusKernelSpan_le_e6 :
    ⁅D.torusKernelSpan, D.torusKernelSpan⁆ ≤ D.kernelSpan := by
  have hTN : torusGroup TwistTag.E6.tag k ≤
      Subgroup.normalizer (D.kernelSpan : Set (ModGL TwistTag.E6.tag k)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hMN : D.torusKernelSpan ≤
      Subgroup.normalizer (D.kernelSpan : Set (ModGL TwistTag.E6.tag k)) :=
    sup_le hTN (Subgroup.le_normalizer)
  refine TwE7.commutator_le_of_eq_mul (fun h hh n hn => ?_) le_sup_left
    (fun a ha b hb => torus_mul_comm_e6 ha hb) (fun h hh => ?_)
  · exact (Subgroup.mem_normalizer_iff.1 (hMN hh) n).1 hn
  · rw [OrthogonalSemilinearFixedRootDatum.torusKernelSpan, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hh
    obtain ⟨a, ha, n, hn, rfl⟩ := hh
    exact ⟨a, ha, n, hn, rfl⟩

theorem commutator_totalFixedGroup_le_e6 [Subsingleton (KernelComponent D.χ)] :
    ⁅D.totalFixedGroup, D.totalFixedGroup⁆ ≤ D.fixedGroup := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨hxM, hxF⟩ := D.mem_totalFixedGroup.1 hx
  obtain ⟨hyM, hyF⟩ := D.mem_totalFixedGroup.1 hy
  refine D.mem_fixedGroup.2 ⟨?_, ?_⟩
  · rw [exc3_rootSpanJ_eq_kernelSpan]
    have h1 : ⁅(x : ModGL TwistTag.E6.tag k), (y : ModGL TwistTag.E6.tag k)⁆ ∈
        ⁅D.torusKernelSpan, D.torusKernelSpan⁆ := Subgroup.commutator_mem_commutator hxM hyM
    have h2 := commutator_torusKernelSpan_le_e6 D h1
    simpa [commutatorElement_def] using h2
  · rw [map_commutatorElement, hxF, hyF]

theorem orbitGroup_eq_derived_e6 [Subsingleton (KernelComponent D.χ)]
    (hq : CFSG.IsQuasisimple D.orbitGroup) :
    D.orbitGroup = ⁅⁅D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype,
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype⁆,
      ⁅D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype,
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype⁆⁆ := by
  have hperf : ⁅D.orbitGroup, D.orbitGroup⁆ = D.orbitGroup := Subgroup.isPerfect_iff.1 hq.1
  have hCX : D.orbitGroup ≤ D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype :=
    (exc3_orbitGroup_le_fixedGroup D).trans (exc3_fixedGroup_le_totalFixedGroup D)
  refine le_antisymm ?_ ?_
  · calc D.orbitGroup = ⁅⁅D.orbitGroup, D.orbitGroup⁆, ⁅D.orbitGroup, D.orbitGroup⁆⁆ := by
          rw [hperf, hperf]
      _ ≤ _ := Subgroup.commutator_mono (Subgroup.commutator_mono hCX hCX)
          (Subgroup.commutator_mono hCX hCX)
  · have hXΓ : ⁅D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype,
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype⁆ ≤
          D.fixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono (commutator_totalFixedGroup_le_e6 D)
    have hΓC : ⁅D.fixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype,
        D.fixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype⁆ ≤ D.orbitGroup := by
      rw [← Subgroup.map_commutator]
      refine (Subgroup.map_mono (commutator_fixedGroup_le_e6 D)).trans ?_
      rw [OrthogonalSemilinearFixedRootDatum.orbitGroupC, Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    exact (Subgroup.commutator_mono hXΓ hXΓ).trans hΓC

end Derived

omit [IsAlgClosed k] in
theorem exists_twenty_datum (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) [IsAlgClosed k] :
    ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k) (u : ModGL TwistTag.E6.tag k),
      D.e = e ∧ D.χ = signMaskChar TwistTag.E6.tag 20 ∧
      (∀ γ, D.θ (toReal γ) =
        toReal (thetaMap (ToralSign.wordElt TwistTag.E6.tag []) TwistTag.E6.perm γ)) ∧
      Subsingleton (KernelComponent D.χ) ∧ CFSG.IsQuasisimple D.orbitGroup ∧
      u ∈ torusGroup TwistTag.E6.tag k ⊔
        rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 20)) ∧
      (D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype).map
          (MulAut.conj u).toMonoidHom =
        fixedPointsIn (torusGroup TwistTag.E6.tag k ⊔
          rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 20)))
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) := by
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp2 e he
  have hr : (⟨20, 27, 1, e6OmegaWords20⟩ : SignRep .E6) ∈ e6SignDiagramReps := by
    simp [e6SignDiagramReps]
  have hl : ([] : List (Fin Tag.E6.rank)) ∈
      (⟨20, 27, 1, e6OmegaWords20⟩ : SignRep .E6).omegaWords := by
    simp [e6OmegaWords20]
  obtain ⟨D, h, -, hDχ, hDe, hDθ, -, hX, u, hu, hconj⟩ := exc3_exists_pinned_datum p hp2 hk he
    (τ := TwistTag.E6.tag) (Or.inr (Or.inl rfl)) TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6
    (h6.theta _ hr [] hl) (Q₀ := wordWeylMatrix TwistTag.E6.tag k [] * diagramMap TwistTag.E6 k)
    (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 [] hγ)
    (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer TwistTag.E6))
    (map_conj_wordWeylMatrix_mul [] (map_conj_diagramMap TwistTag.E6 k (Or.inl rfl)))
    (n6 _ hr [] hl)    (e6_kernelRoots_nonempty hr)
  have hQ₀ : wordWeylMatrix TwistTag.E6.tag k [] * diagramMap TwistTag.E6 k =
      diagramMap TwistTag.E6 k := by
    rw [wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hconj
  have hsub : Subsingleton (KernelComponent D.χ) := by
    rw [hDχ]
    exact e6_subsingleton_twenty
  have hnon : ∀ β ∈ kernelRoots D.χ, ∃ γ ∈ kernelRoots D.χ, iform β γ = 1 := by
    rw [hDχ]
    exact e6_forall_exists_iform_twenty
  refine ⟨D, u, hDe, hDχ, hDθ, hsub, exc3_isQuasisimple_orbitGroup (Or.inr (Or.inl rfl)) hnon, hu,
    ?_⟩
  rw [hX]
  exact hconj

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
