module

public import CFSG.ClassicalInvolution.Q3.Q3ExcE7Tw

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Q3 CFSG.LieType.HighestRoot CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped commutatorElement Pointwise

theorem commutator_le_of_eq_mul {G : Type*} [Group G] {H A N : Subgroup G}
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hAH : A ≤ H)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hH : ∀ h ∈ H, ∃ a ∈ A, ∃ n ∈ N, h = a * n) :
    ⁅H, H⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := hH x hx
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := hH y hy
  have hcomm : a₁ * a₂ * a₁⁻¹ = a₂ := by rw [hA a₁ ha₁ a₂ ha₂]; group
  have e : ⁅a₁ * n₁, a₂ * n₂⁆ = (a₁ * (n₁ * (a₂ * (n₂ * n₁⁻¹) * a₂⁻¹)) * a₁⁻¹) *
      ((a₁ * a₂ * a₁⁻¹) * n₂⁻¹ * a₂⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, hcomm]
  exact mul_mem (hN a₁ (hAH ha₁) _ (mul_mem hn₁ (hN a₂ (hAH ha₂) _ (mul_mem hn₂ (inv_mem hn₁)))))
    (hN a₂ (hAH ha₂) _ (inv_mem hn₂))


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

omit
  [IsAlgClosed k] [Fact p.Prime] [CharP k p] in
theorem torus_mul_comm {h h' : ModGL .E7 k} (hh : h ∈ torusGroup .E7 k)
    (hh' : h' ∈ torusGroup .E7 k) : h * h' = h' * h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a hh'

section Derived

variable (D : OrthogonalSemilinearFixedRootDatum .E7 p k)

theorem commutator_fixedGroup_le : ⁅D.fixedGroup, D.fixedGroup⁆ ≤ D.orbitGroupC := by
  refine commutator_le_of_eq_mul (fun h hh n hn => ?_) D.fixedTorus_le_fixedGroup
    (fun a ha b hb => ?_) (fun h hh => ?_)
  · have hnorm := D.orbitGroupC_normal
    have h1 := hnorm.conj_mem ⟨n, D.orbitGroupC_le_fixedGroup hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.1 h1
  · apply Subtype.ext
    exact torus_mul_comm (unionTorus_le_torusGroup (D.mem_fixedTorus.1 ha).1)
      (unionTorus_le_torusGroup (D.mem_fixedTorus.1 hb).1)
  · have hmul : h ∈ (D.fixedTorus : Set (adjointGroup .E7 k)) *
        (D.orbitGroupC : Set (adjointGroup .E7 k)) := by
      rw [← D.coe_fixedGroup_eq_mul]
      exact hh
    obtain ⟨a, ha, n, hn, rfl⟩ := hmul
    exact ⟨a, ha, n, hn, rfl⟩

theorem commutator_torusKernelSpan_le :
    ⁅D.torusKernelSpan, D.torusKernelSpan⁆ ≤ D.kernelSpan := by
  have hTN : torusGroup .E7 k ≤ Subgroup.normalizer (D.kernelSpan : Set (ModGL .E7 k)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hMN : D.torusKernelSpan ≤ Subgroup.normalizer (D.kernelSpan : Set (ModGL .E7 k)) :=
    sup_le hTN (Subgroup.le_normalizer)
  refine commutator_le_of_eq_mul (fun h hh n hn => ?_) le_sup_left
    (fun a ha b hb => torus_mul_comm ha hb) (fun h hh => ?_)
  · exact (Subgroup.mem_normalizer_iff.1 (hMN hh) n).1 hn
  · rw [OrthogonalSemilinearFixedRootDatum.torusKernelSpan, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hh
    obtain ⟨a, ha, n, hn, rfl⟩ := hh
    exact ⟨a, ha, n, hn, rfl⟩

theorem commutator_totalFixedGroup_le [Subsingleton (KernelComponent D.χ)] :
    ⁅D.totalFixedGroup, D.totalFixedGroup⁆ ≤ D.fixedGroup := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨hxM, hxF⟩ := D.mem_totalFixedGroup.1 hx
  obtain ⟨hyM, hyF⟩ := D.mem_totalFixedGroup.1 hy
  refine D.mem_fixedGroup.2 ⟨?_, ?_⟩
  · rw [exc3_rootSpanJ_eq_kernelSpan]
    have h1 : ⁅(x : ModGL .E7 k), (y : ModGL .E7 k)⁆ ∈
        ⁅D.torusKernelSpan, D.torusKernelSpan⁆ := Subgroup.commutator_mem_commutator hxM hyM
    have h2 := commutator_torusKernelSpan_le D h1
    simpa [commutatorElement_def] using h2
  · rw [map_commutatorElement, hxF, hyF]

theorem orbitGroup_eq_derived [Subsingleton (KernelComponent D.χ)]
    (hq : CFSG.IsQuasisimple D.orbitGroup) :
    D.orbitGroup = ⁅⁅D.totalFixedGroup.map (adjointGroup .E7 k).subtype,
        D.totalFixedGroup.map (adjointGroup .E7 k).subtype⁆,
      ⁅D.totalFixedGroup.map (adjointGroup .E7 k).subtype,
        D.totalFixedGroup.map (adjointGroup .E7 k).subtype⁆⁆ := by
  have hperf : ⁅D.orbitGroup, D.orbitGroup⁆ = D.orbitGroup := Subgroup.isPerfect_iff.1 hq.1
  have hCX : D.orbitGroup ≤ D.totalFixedGroup.map (adjointGroup .E7 k).subtype :=
    (exc3_orbitGroup_le_fixedGroup D).trans (exc3_fixedGroup_le_totalFixedGroup D)
  refine le_antisymm ?_ ?_
  · calc D.orbitGroup = ⁅⁅D.orbitGroup, D.orbitGroup⁆, ⁅D.orbitGroup, D.orbitGroup⁆⁆ := by
          rw [hperf, hperf]
      _ ≤ _ := Subgroup.commutator_mono (Subgroup.commutator_mono hCX hCX)
          (Subgroup.commutator_mono hCX hCX)
  · have hXΓ : ⁅D.totalFixedGroup.map (adjointGroup .E7 k).subtype,
        D.totalFixedGroup.map (adjointGroup .E7 k).subtype⁆ ≤
          D.fixedGroup.map (adjointGroup .E7 k).subtype := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono (commutator_totalFixedGroup_le D)
    have hΓC : ⁅D.fixedGroup.map (adjointGroup .E7 k).subtype,
        D.fixedGroup.map (adjointGroup .E7 k).subtype⁆ ≤ D.orbitGroup := by
      rw [← Subgroup.map_commutator]
      refine (Subgroup.map_mono (commutator_fixedGroup_le D)).trans ?_
      rw [OrthogonalSemilinearFixedRootDatum.orbitGroupC, Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    exact (Subgroup.commutator_mono hXΓ hXΓ).trans hΓC

end Derived

omit [IsAlgClosed k] in
variable (p k) in
abbrev twCent (e : ℕ) (x : ModGL .E7 k) : Subgroup (ModGL .E7 k) :=
  ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1),
      fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)⁆ ⊓
    Subgroup.centralizer {x}

theorem exists_twisted_datum (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {r : SignRep .E7}
    (hr : r ∈ e7SignDiagramReps) {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords)
    (hl0 : l ≠ []) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (c u : ModGL .E7 k),
      Exc3Frob D c ∧ D.e = e ∧ D.χ = signMaskChar .E7 r.mask ∧
      (∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 l) 1 γ)) ∧
      Subsingleton (KernelComponent D.χ) ∧ CFSG.IsQuasisimple D.orbitGroup ∧
      u ∈ torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (signMaskChar .E7 r.mask)) ∧
      (D.totalFixedGroup.map (adjointGroup .E7 k).subtype).map (MulAut.conj u).toMonoidHom =
        fixedPointsIn (torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (signMaskChar .E7 r.mask)))
          (frobTwistGL .E7 k p e (wordWeylMatrix .E7 k l * 1)) := by
  classical
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp2 e he
  have hmask := mask_eq_two_or_three_of_ne_nil hr hl hl0
  have hne : (kernelRoots (signMaskChar .E7 r.mask)).Nonempty := by
    rcases hmask with hm | hm <;> rw [hm]
    · exact e7_kernelRoots_nonempty_two
    · exact e7_kernelRoots_nonempty_three
  have hsub : Subsingleton (KernelComponent (signMaskChar .E7 r.mask)) := by
    rcases hmask with hm | hm <;> rw [hm]
    · exact e7_subsingleton_two
    · exact e7_subsingleton_three
  have hnon : ∀ β ∈ kernelRoots (signMaskChar .E7 r.mask),
      ∃ γ ∈ kernelRoots (signMaskChar .E7 r.mask), iform β γ = 1 := by
    rcases hmask with hm | hm <;> rw [hm]
    · exact e7_forall_exists_iform_two
    · exact e7_forall_exists_iform_three
  have hQ₀T : wordWeylMatrix .E7 k l * 1 ∈
      Subgroup.normalizer (torusGroup .E7 k : Set (ModGL .E7 k)) :=
    mul_mem (wordWeylMatrix_mem_normalizer l) (one_mem _)
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX, u, hu, hconj⟩ := exc3_exists_pinned_datum p hp2 hk he
    (Or.inr (Or.inr rfl)) (ρ := 1) (fun _ _ => rfl) (fun _ _ => rfl) (h7.theta r hr l hl)
    (fun γ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) hQ₀T
    (map_conj_wordWeylMatrix_mul l (map_conj_one_adjointGroup _ k)) (n7 r hr l hl) hne
  have hsubD : Subsingleton (KernelComponent D.χ) := by rw [hDχ]; exact hsub
  have hnonD : ∀ β ∈ kernelRoots D.χ, ∃ γ ∈ kernelRoots D.χ, iform β γ = 1 := by
    rw [hDχ]; exact hnon
  have hcT : h * (wordWeylMatrix .E7 k l * 1) ∈
      Subgroup.normalizer (torusGroup .E7 k : Set (ModGL .E7 k)) :=
    mul_mem (Subgroup.le_normalizer hhT) hQ₀T
  have hN2 : wordWeylMatrix .E7 k l * wordWeylMatrix .E7 k l ∈ torusGroup .E7 k :=
    e7_wordWeylMatrix_sq_mem_torus hr hl hl0
  have hc2 : (h * (wordWeylMatrix .E7 k l * 1)) * (h * (wordWeylMatrix .E7 k l * 1)) ∈
      torusGroup .E7 k := by
    have e : (h * (wordWeylMatrix .E7 k l * 1)) * (h * (wordWeylMatrix .E7 k l * 1)) =
        h * ((wordWeylMatrix .E7 k l * 1) * h * (wordWeylMatrix .E7 k l * 1)⁻¹) *
          (wordWeylMatrix .E7 k l * wordWeylMatrix .E7 k l) := by group
    rw [e]
    exact mul_mem (mul_mem hhT ((Subgroup.mem_normalizer_iff.1 hQ₀T h).1 hhT)) hN2
  have hfrob : Exc3Frob D (h * (wordWeylMatrix .E7 k l * 1)) :=
    ⟨fun x => by rw [hDe]; exact hDF x, hcT, hc2⟩
  refine ⟨D, h * (wordWeylMatrix .E7 k l * 1), u, hfrob, hDe, hDχ, hDθ, hsubD,
    exc3_isQuasisimple_orbitGroup (Or.inr (Or.inr (Or.inl rfl))) hnonD, hu, ?_⟩
  rw [hX]
  exact hconj

omit [IsAlgClosed k]
  in
theorem conj_mem_of_mem_twCent {e : ℕ} {x : ModGL .E7 k} {a : Fin Tag.E7.rank → kˣ}
    {l : List (Fin Tag.E7.rank)} {g₁ : ModGL .E7 k} (hg₁ : g₁ ∈ adjointGroup .E7 k)
    (hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit .E7 a)
    (hcoc : g₁ * (frobTwistGL .E7 k p e 1 g₁)⁻¹ = wordWeylMatrix .E7 k l)
    {y : ModGL .E7 k} (hy : y ∈ twCent p k e x) :
    g₁ * y * g₁⁻¹ ∈ toralCentralizer .E7 k a ∧
      frobTwistGL .E7 k p e (wordWeylMatrix .E7 k l * 1) (g₁ * y * g₁⁻¹) = g₁ * y * g₁⁻¹ := by
  set F := frobTwistGL .E7 k p e 1 with hF
  set N := wordWeylMatrix .E7 k l with hN
  have hF₀F : ∀ w, frobTwistGL .E7 k p e (N * 1) w = N * F w * N⁻¹ := by
    intro w
    simp only [hF, frobTwistGL_apply, mul_one, one_mul, inv_one]
  have hFg₁ : F g₁ = N⁻¹ * g₁ := by
    have h1 : (F g₁)⁻¹ = g₁⁻¹ * N := by rw [← hcoc]; group
    calc F g₁ = ((F g₁)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (g₁⁻¹ * N)⁻¹ := by rw [h1]
      _ = N⁻¹ * g₁ := by group
  have hRsub : ⁅fixedPointsIn (adjointGroup .E7 k) F, fixedPointsIn (adjointGroup .E7 k) F⁆ ≤
      fixedPointsIn (adjointGroup .E7 k) F := Subgroup.commutator_le_of_le le_rfl le_rfl
  obtain ⟨hyc, hycx⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨hyG, hyF⟩ := mem_fixedPointsIn.1 (hRsub hyc)
  have hxy : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hycx
  refine ⟨mem_toralCentralizer.2 ⟨mul_mem (mul_mem hg₁ hyG) (inv_mem hg₁), ?_⟩, ?_⟩
  · rw [← hg₁x]
    calc g₁ * x * g₁⁻¹ * (g₁ * y * g₁⁻¹) * (g₁ * x * g₁⁻¹)⁻¹ = g₁ * (x * y * x⁻¹) * g₁⁻¹ := by
          group
      _ = g₁ * y * g₁⁻¹ := by rw [← hxy]; group
  · rw [hF₀F, map_mul, map_mul, map_inv, hFg₁, hyF]
    group

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
