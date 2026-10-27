module

public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Untwist

variable {τ : Tag} {k : Type} [Field k]

@[expose] def UntwistAt (F : ModGL τ k →* ModGL τ k) (a : Fin τ.rank → kˣ) : Prop :=
  ∀ c ∈ toralCentralizer τ k a, ∃ u ∈ toralCentralizer τ k a,
    u * c * (F u)⁻¹ ∈ toralRootGroup τ k a

theorem untwistAt_of_eq (F : ModGL τ k →* ModGL τ k) (a : Fin τ.rank → kˣ)
    (h : toralRootGroup τ k a = toralCentralizer τ k a) : UntwistAt F a := fun c hc =>
  ⟨1, one_mem _, by rw [one_mul, map_one, inv_one, mul_one, h]; exact hc⟩

end Untwist

section Main

variable (p : ℕ) [Fact p.Prime] (t : TwistTag) {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_twisted_toral_reduction (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (reps : List (SignRep t.tag))
    (hfix : ∀ r ∈ reps, permChar t.perm (signMaskChar t.tag r.mask) = signMaskChar t.tag r.mask)
    (hrep : ∀ χ, permChar t.perm χ ∈ charOrbit χ →
      ∃ r ∈ reps, χ ∈ charOrbit (signMaskChar t.tag r.mask))
    (hunt : ∀ r ∈ reps, UntwistAt (frobTwistGL t.tag k p e (diagramMap t k))
      (signCharTuple (signMaskChar t.tag r.mask)))
    {x : ModGL t.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ reps, ∃ g₁ ∈ adjointGroup t.tag k,
      frobTwistGL t.tag k p e (diagramMap t k) g₁ = g₁ ∧
      g₁ * x * g₁⁻¹ = rootDiagUnit t.tag (signCharTuple (signMaskChar t.tag r.mask)) ∧
      ∀ L : Subgroup (ModGL t.tag k),
        (L ≤ ⁅fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)),
            fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k))⁆ ⊓
              Subgroup.centralizer {x} ∧
          CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup t.tag k)
            (frobTwistGL t.tag k p e (diagramMap t k)), fixedPointsIn (adjointGroup t.tag k)
            (frobTwistGL t.tag k p e (diagramMap t k))⁆ ⊓ Subgroup.centralizer {x}))) ↔
        (L.map (MulAut.conj g₁).toMonoidHom ≤ fixedPointsIn
            (torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots (signMaskChar t.tag r.mask)))
            (frobTwistGL t.tag k p e (diagramMap t k)) ∧
          CFSG.IsPComponent 2 ((L.map (MulAut.conj g₁).toMonoidHom).subgroupOf (fixedPointsIn
            (torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots (signMaskChar t.tag r.mask)))
            (frobTwistGL t.tag k p e (diagramMap t k))))) := by
  classical
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set D := diagramMap t k with hD_def
  have hD : (adjointGroup t.tag k).map (MulAut.conj D).toMonoidHom = adjointGroup t.tag k :=
    map_conj_diagramMap t k (Or.inl rfl)
  have hRfin : Finite (fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e D)) :=
    finite_fixedPointsIn_frobTwistGL p he (by cases t <;> decide)
      (units_map_entrywiseHom_diagramMap (t := t) (iterateFrobenius k p e))
      (diagramMap_pow_order t k)
  set F := frobTwistGL t.tag k p e D with hF
  set R := fixedPointsIn (adjointGroup t.tag k) F with hR
  have hFG : ∀ g ∈ adjointGroup t.tag k, F g ∈ adjointGroup t.tag k := fun g hg =>
    conj_mem_adjointGroup_of_map_eq hD _ (entrywiseFrobGL_mem p e hg)
  obtain ⟨hxG, hxF⟩ := mem_fixedPointsIn.1 hx
  obtain ⟨g, hg, r, hr, hgx, hFt⟩ := exists_conj_eq_rootDiagUnit_of_reps hp t.perm F hFG
    (fun b hb => frobTwistGL_diagramMap_rootDiagUnit_of_sign p t e hb) reps hfix hrep hxG hxF hx2
  set χ := signMaskChar t.tag r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk χ
  have hFgx : F g * x * (F g)⁻¹ = rootDiagUnit t.tag a := by
    rw [← hFt, ← hgx, map_mul, map_mul, map_inv, hxF]
  have hcZ : g * (F g)⁻¹ ∈ toralCentralizer t.tag k a := by
    refine mem_toralCentralizer.2 ⟨mul_mem hg (inv_mem (hFG g hg)), ?_⟩
    calc rootDiagUnit t.tag a * (g * (F g)⁻¹) * (rootDiagUnit t.tag a)⁻¹ =
        (g * x * g⁻¹) * (g * (F g)⁻¹) * (rootDiagUnit t.tag a)⁻¹ := by rw [hgx]
      _ = g * (F g)⁻¹ * (F g * x * (F g)⁻¹) * (rootDiagUnit t.tag a)⁻¹ := by group
      _ = g * (F g)⁻¹ := by rw [hFgx]; group
  obtain ⟨u, huZ, hum⟩ := hunt r hr (g * (F g)⁻¹) hcZ
  have huG : u ∈ adjointGroup t.tag k := (mem_toralCentralizer.1 huZ).1
  have huc : rootDiagUnit t.tag a * u * (rootDiagUnit t.tag a)⁻¹ = u := (mem_toralCentralizer.1 huZ).2
  set g' := u * g with hg'_def
  have hg'G : g' ∈ adjointGroup t.tag k := mul_mem huG hg
  have hg'x : g' * x * g'⁻¹ = rootDiagUnit t.tag a := by
    calc g' * x * g'⁻¹ = u * (g * x * g⁻¹) * u⁻¹ := by rw [hg'_def]; group
      _ = u * rootDiagUnit t.tag a * u⁻¹ := by rw [hgx]
      _ = rootDiagUnit t.tag a := by
        have h1 : u * rootDiagUnit t.tag a = rootDiagUnit t.tag a * u := by
          calc u * rootDiagUnit t.tag a =
              (rootDiagUnit t.tag a * u * (rootDiagUnit t.tag a)⁻¹) * rootDiagUnit t.tag a := by
                rw [huc]
            _ = rootDiagUnit t.tag a * u := by group
        rw [h1]
        group
  have hcv : ∃ m ∈ toralRootGroup t.tag k a, g' * (F g')⁻¹ = m * 1 := by
    refine ⟨g' * (F g')⁻¹, ?_, by rw [mul_one]⟩
    have e1 : g' * (F g')⁻¹ = u * (g * (F g)⁻¹) * (F u)⁻¹ := by
      rw [hg'_def, map_mul, mul_inv_rev]
      group
    rw [e1]
    exact hum
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have := commutator_subgroupOf_normal R
  have := isSolvable_quotient_commutator_subgroupOf R
  obtain ⟨z, hzM, hzg, hconj, hQfin, -, -, hcomp⟩ := rational_centralizer_cocycle_reduction_of_map_conj
    p hp he hD hRfin hRsub ha hg'G hg'x hFt (v := 1) (one_mem _) hcv
  have hone : (MulAut.conj (1 : ModGL t.tag k)).toMonoidHom.comp F = F := by
    ext y
    simp
  rw [hone, toralRootGroup, hker] at hcomp
  refine ⟨r, hr, z * g', ?_, ?_, ?_, fun L => ?_⟩
  · have hzG : z ∈ adjointGroup t.tag k := (mem_toralCentralizer.1
      ((exceptional_toral_centralizer_identity_component t.tag k hk a ha).2.2.1.1 hzM)).1
    exact mul_mem hzG hg'G
  · have h1 := hzg
    rw [mul_inv_eq_one] at h1
    exact h1.symm
  · have hz : z * rootDiagUnit t.tag a * z⁻¹ = rootDiagUnit t.tag a := by
      have hzZ := (exceptional_toral_centralizer_identity_component t.tag k hk a ha).2.2.1.1 hzM
      have hzc := (mem_toralCentralizer.1 hzZ).2
      calc z * rootDiagUnit t.tag a * z⁻¹ =
          (rootDiagUnit t.tag a * z * (rootDiagUnit t.tag a)⁻¹) * rootDiagUnit t.tag a * z⁻¹ := by
            rw [hzc]
        _ = rootDiagUnit t.tag a := by group
    calc z * g' * x * (z * g')⁻¹ = z * (g' * x * g'⁻¹) * z⁻¹ := by group
      _ = rootDiagUnit t.tag a := by rw [hg'x, hz]
  · exact (hcomp 2 Nat.prime_two).1 L

end Main

end CFSG.ClassicalInvolution.ModelFacts
