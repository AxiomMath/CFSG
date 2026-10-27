module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups commutatorElement

section Datum

variable (p : ℕ) [Fact p.Prime] (t : TwistTag) {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exc3_exists_datum_conj_centralizer (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (reps : List (SignRep t.tag)) {r₀ : ℕ}
    (hB : ∀ i j, t.tag.symmetrizedCartan (t.perm i) (t.perm j) = t.tag.symmetrizedCartan i j)
    (hfix : ∀ r ∈ reps, permChar t.perm (signMaskChar t.tag r.mask) = signMaskChar t.tag r.mask)
    (hrep : ∀ χ, permChar t.perm χ ∈ charOrbit χ →
      ∃ r ∈ reps, χ ∈ charOrbit (signMaskChar t.tag r.mask))
    (hunt : ∀ r ∈ reps, UntwistAt (frobTwistGL t.tag k p e (diagramMap t k))
      (signCharTuple (signMaskChar t.tag r.mask)))
    (hθ : ∀ r ∈ reps, ThetaProperties t.perm r₀ (signMaskChar t.tag r.mask) (wordElt t.tag []))
    (hpin : ∀ r ∈ reps, IsTwistPinningNormalization t.tag k p e (signMaskChar t.tag r.mask)
      (thetaMap (wordElt t.tag []) t.perm) (wordWeylMatrix t.tag k [] * diagramMap t k))
    (hne : ∀ r ∈ reps, (kernelRoots (signMaskChar t.tag r.mask)).Nonempty)
    (hZ : ∀ r ∈ reps, ∀ y ∈ toralCentralizer t.tag k (signCharTuple (signMaskChar t.tag r.mask)),
      frobTwistGL t.tag k p e (diagramMap t k) y = y →
        y ∈ toralRootGroup t.tag k (signCharTuple (signMaskChar t.tag r.mask)))
    {x : ModGL t.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ reps, ∃ (D : OrthogonalSemilinearFixedRootDatum t.tag p k) (h g₁ : ModGL t.tag k)
      (s : Fin t.tag.rank → kˣ),
      g₁ ∈ adjointGroup t.tag k ∧ h ∈ torusGroup t.tag k ∧
      frobTwistGL t.tag k p e (diagramMap t k) g₁ = g₁ ∧
      frobTwistGL t.tag k p e (diagramMap t k) (rootDiagUnit t.tag s) =
        h⁻¹ * rootDiagUnit t.tag s ∧
      g₁ * x * g₁⁻¹ = rootDiagUnit t.tag (signCharTuple (signMaskChar t.tag r.mask)) ∧
      D.χ = signMaskChar t.tag r.mask ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (thetaMap (wordElt t.tag []) t.perm γ)) ∧
      (∀ y : adjointGroup t.tag k, (D.F y : ModGL t.tag k) =
        frobTwistGL t.tag k p e (h * diagramMap t k) y) ∧
      (fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)) ⊓
        Subgroup.centralizer {x}).map (MulAut.conj (rootDiagUnit t.tag s * g₁)).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup t.tag k).subtype := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, -⟩ :=
    exists_twisted_toral_reduction p t hp he reps hfix hrep hunt hx hx2
  set χ := signMaskChar t.tag r.mask with hχ
  set F := frobTwistGL t.tag k p e (diagramMap t k) with hF
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk2 χ
  set M := torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots χ) with hM_def
  have hMeq : toralRootGroup t.tag k a = M := by rw [toralRootGroup, hker]
  have hMG : M ≤ adjointGroup t.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hMZ : ∀ y ∈ M, rootDiagUnit t.tag a * y * (rootDiagUnit t.tag a)⁻¹ = y := fun y hy =>
    (mem_toralCentralizer.1 (toralRootGroup_le a (hMeq ▸ hy))).2
  have hD : (adjointGroup t.tag k).map (MulAut.conj (diagramMap t k)).toMonoidHom =
      adjointGroup t.tag k := map_conj_diagramMap t k (Or.inl rfl)
  have hτ : t.tag = .D4 ∨ t.tag = .E6 ∨ t.tag = .E7 := by cases t <;> simp [TwistTag.tag]
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX⟩ := exists_pinned_datum p hp hk he hτ (ρ := t.perm)
    t.cartan_perm hB (hθ r hr) (Q₀ := wordWeylMatrix t.tag k [] * diagramMap t k)
    (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX t [] hγ)
    (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer t))
    (map_conj_wordWeylMatrix_mul [] hD) (hpin r hr) (hne r hr)
  have hQ₀ : wordWeylMatrix t.tag k [] * diagramMap t k = diagramMap t k := by
    rw [wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hDF hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_frob_eq p t he a₀⁻¹
  set u := rootDiagUnit t.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL t.tag k p e (h * diagramMap t k) y = h * F y * h⁻¹ :=
    fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) :=
    map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  have hud : u * rootDiagUnit t.tag a * u⁻¹ = rootDiagUnit t.tag a := by
    have h1 := hMZ u huM
    calc u * rootDiagUnit t.tag a * u⁻¹ =
        (rootDiagUnit t.tag a * u * (rootDiagUnit t.tag a)⁻¹) * rootDiagUnit t.tag a * u⁻¹ := by
          rw [h1]
      _ = rootDiagUnit t.tag a := by group
  refine ⟨r, hr, D, h, g₁, s, hg₁G, hhT, hFg₁, hFu, hg₁x, hDχ, hDe, hDθ, fun y => hDF y, ?_⟩
  ext y
  constructor
  · rintro ⟨z, ⟨hzR, hzx⟩, rfl⟩
    obtain ⟨hzG, hzF⟩ := mem_fixedPointsIn.1 hzR
    have hzx' : z * x = x * z :=
      Subgroup.mem_centralizer_singleton_iff.1 (hzx : z ∈ Subgroup.centralizer {x})
    have hy₁G : g₁ * z * g₁⁻¹ ∈ adjointGroup t.tag k := mul_mem (mul_mem hg₁G hzG) (inv_mem hg₁G)
    have hy₁F : F (g₁ * z * g₁⁻¹) = g₁ * z * g₁⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFg₁, hzF]
    have hy₁d : rootDiagUnit t.tag a * (g₁ * z * g₁⁻¹) * (rootDiagUnit t.tag a)⁻¹ =
        g₁ * z * g₁⁻¹ := by
      rw [← hg₁x]
      calc g₁ * x * g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁ * x * g₁⁻¹)⁻¹ =
          g₁ * (x * z * x⁻¹) * g₁⁻¹ := by group
        _ = g₁ * z * g₁⁻¹ := by rw [← hzx']; group
    have hy₁M : g₁ * z * g₁⁻¹ ∈ M := hMeq ▸ hZ r hr _ (mem_toralCentralizer.2 ⟨hy₁G, hy₁d⟩) hy₁F
    have hmem : u * (g₁ * z * g₁⁻¹) * u⁻¹ ∈
        fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) := by
      rw [← hconj]
      exact ⟨_, mem_fixedPointsIn.2 ⟨hy₁M, hy₁F⟩, rfl⟩
    rw [← hX] at hmem
    have e : (MulAut.conj (u * g₁)).toMonoidHom z = u * (g₁ * z * g₁⁻¹) * u⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      group
    rw [e]
    exact hmem
  · intro hy
    rw [hX] at hy
    rw [← hconj] at hy
    obtain ⟨y₁, hy₁, rfl⟩ := hy
    obtain ⟨hy₁M, hy₁F⟩ := mem_fixedPointsIn.1 hy₁
    have hy₁G := hMG hy₁M
    have hz : g₁⁻¹ * y₁ * g₁ ∈ fixedPointsIn (adjointGroup t.tag k) F ⊓
        Subgroup.centralizer {x} := by
      refine ⟨mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem hg₁G) hy₁G) hg₁G, ?_⟩, ?_⟩
      · rw [map_mul, map_mul, map_inv, hFg₁, hy₁F]
      · show g₁⁻¹ * y₁ * g₁ ∈ Subgroup.centralizer ({x} : Set (ModGL t.tag k))
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hMZ y₁ hy₁M
        have hx' : x = g₁⁻¹ * rootDiagUnit t.tag a * g₁ := by
          rw [← hg₁x]
          group
        symm
        calc x * (g₁⁻¹ * y₁ * g₁) = g₁⁻¹ * (rootDiagUnit t.tag a * y₁) * g₁ := by
              rw [hx']
              group
          _ = g₁⁻¹ * (y₁ * rootDiagUnit t.tag a) * g₁ := by
              have h2 : rootDiagUnit t.tag a * y₁ = y₁ * rootDiagUnit t.tag a := by
                calc rootDiagUnit t.tag a * y₁ =
                    (rootDiagUnit t.tag a * y₁ * (rootDiagUnit t.tag a)⁻¹) *
                      rootDiagUnit t.tag a := by group
                  _ = y₁ * rootDiagUnit t.tag a := by rw [h1]
              rw [h2]
          _ = (g₁⁻¹ * y₁ * g₁) * x := by
              rw [hx']
              group
    refine ⟨_, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group
    rfl

end Datum

section E6

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exc3_e6_datum_conj (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ e6SignDiagramReps, ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
      (h g₁ : ModGL TwistTag.E6.tag k) (s : Fin TwistTag.E6.tag.rank → kˣ),
      g₁ ∈ adjointGroup TwistTag.E6.tag k ∧ h ∈ torusGroup TwistTag.E6.tag k ∧
      frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) g₁ = g₁ ∧
      frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)
        (rootDiagUnit TwistTag.E6.tag s) = h⁻¹ * rootDiagUnit TwistTag.E6.tag s ∧
      g₁ * x * g₁⁻¹ = rootDiagUnit TwistTag.E6.tag
        (signCharTuple (signMaskChar TwistTag.E6.tag r.mask)) ∧
      D.χ = signMaskChar TwistTag.E6.tag r.mask ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ)) ∧
      (∀ y : adjointGroup TwistTag.E6.tag k, (D.F y : ModGL TwistTag.E6.tag k) =
        frobTwistGL TwistTag.E6.tag k p e (h * diagramMap TwistTag.E6 k) y) ∧
      (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ⊓
        Subgroup.centralizer {x}).map
          (MulAut.conj (rootDiagUnit TwistTag.E6.tag s * g₁)).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  obtain ⟨r, hr, D, h, g₁, s, hg₁, hh, hFg₁, hFs, hg₁x, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    exc3_exists_datum_conj_centralizer p TwistTag.E6 hp hk he e6SignDiagramReps (r₀ := 2)
      symmetrizedCartan_perm_E6 h6.permChar_eq h6.exists_rep
      (fun r _ => untwistAt_of_eq _ _ (e6_toralRootGroup_eq hk2 (signCharTuple_sign _)))
      (fun r hr => h6.theta r hr [] (nil_mem_omegaWords_e6 hr))
      (fun r hr => n6 r hr [] (nil_mem_omegaWords_e6 hr))
      (fun r hr => e6_kernelRoots_nonempty hr)
      (fun r _ y hy _ => (e6_toralRootGroup_eq hk2 (signCharTuple_sign _)).symm ▸ hy) hx hx2
  refine ⟨r, hr, D, h, g₁, s, hg₁, hh, hFg₁, hFs, hg₁x, hDχ, hDe, fun γ => ?_, hDF, hcent⟩
  have := hDθ γ
  rwa [wordElt_nil, thetaMap_one] at this

end E6

end CFSG.ClassicalInvolution.Q3
