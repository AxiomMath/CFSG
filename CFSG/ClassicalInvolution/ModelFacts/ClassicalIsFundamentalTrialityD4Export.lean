module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Chain

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

section Commutator

variable {k : Type} [Field k] [IsAlgClosed k]

theorem commutator_mem_toralRootGroup_of_d4 (hk2 : ringChar k ≠ 2)
    {a : Fin Tag.D4.rank → kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {y z : ModGL Tag.D4 k}
    (hy : y ∈ toralCentralizer Tag.D4 k a) (hz : z ∈ toralCentralizer Tag.D4 k a) :
    ⁅y, z⁆ ∈ toralRootGroup Tag.D4 k a := by
  obtain ⟨-, -, -, -, -, -, h⟩ := exceptional_toral_centralizer_identity_component Tag.D4 k hk2
    a ha
  set N := (toralRootGroup Tag.D4 k a).subgroupOf (toralCentralizer Tag.D4 k a) with hN
  have hel := (h rfl).2
  have hc : (QuotientGroup.mk (⟨y, hy⟩ : toralCentralizer Tag.D4 k a) :
      toralCentralizer Tag.D4 k a ⧸ N) * QuotientGroup.mk ⟨z, hz⟩ =
      QuotientGroup.mk ⟨z, hz⟩ * QuotientGroup.mk ⟨y, hy⟩ :=
    hel.1.is_comm.comm _ _
  have h1 := commutatorElement_eq_one_iff_mul_comm.2 hc
  have h2 := map_commutatorElement (QuotientGroup.mk' N) (⟨y, hy⟩ : toralCentralizer Tag.D4 k a)
    ⟨z, hz⟩
  have h3 : (QuotientGroup.mk ⁅(⟨y, hy⟩ : toralCentralizer Tag.D4 k a), ⟨z, hz⟩⁆ :
      toralCentralizer Tag.D4 k a ⧸ N) = 1 := by
    have : (QuotientGroup.mk' N) ⁅(⟨y, hy⟩ : toralCentralizer Tag.D4 k a), ⟨z, hz⟩⁆ = 1 :=
      h2.trans h1
    exact this
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)

end Commutator

section Datum

variable (p : ℕ) [Fact p.Prime] (t : TwistTag) {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_conj_perfect (hp : p ≠ 2)
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
    (hab : ∀ r ∈ reps, ∀ y ∈ toralCentralizer t.tag k (signCharTuple (signMaskChar t.tag r.mask)),
      ∀ z ∈ toralCentralizer t.tag k (signCharTuple (signMaskChar t.tag r.mask)),
        ⁅y, z⁆ ∈ toralRootGroup t.tag k (signCharTuple (signMaskChar t.tag r.mask)))
    {x : ModGL t.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ reps, ∃ (D : OrthogonalSemilinearFixedRootDatum t.tag p k) (w h : ModGL t.tag k),
      w ∈ adjointGroup t.tag k ∧ h ∈ torusGroup t.tag k ∧
      w * x * w⁻¹ = rootDiagUnit t.tag (signCharTuple (signMaskChar t.tag r.mask)) ∧
      D.χ = signMaskChar t.tag r.mask ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (thetaMap (wordElt t.tag []) t.perm γ)) ∧
      (∀ y : adjointGroup t.tag k, (D.F y : ModGL t.tag k) =
        frobTwistGL t.tag k p e (h * diagramMap t k) y) ∧
      ∀ P : Subgroup (ModGL t.tag k),
        P ≤ fixedPointsIn (adjointGroup t.tag k)
          (frobTwistGL t.tag k p e (diagramMap t k)) ⊓ Subgroup.centralizer {x} →
        ⁅P, P⁆ = P →
          P.map (MulAut.conj w).toMonoidHom ≤ D.totalFixedGroup.map (adjointGroup t.tag k).subtype
    := by
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
  refine ⟨r, hr, D, u * g₁, h, mul_mem (hMG huM) hg₁G, hhT, ?_, hDχ, hDe, hDθ,
    fun y => hDF y, ?_⟩
  · calc u * g₁ * x * (u * g₁)⁻¹ = u * (g₁ * x * g₁⁻¹) * u⁻¹ := by group
      _ = rootDiagUnit t.tag a := by rw [hg₁x, hud]
  · intro P hP hperf
    set P' : Subgroup (ModGL t.tag k) := P.map (MulAut.conj g₁).toMonoidHom with hP'
    have hP'Z : ∀ y ∈ P', y ∈ toralCentralizer t.tag k a ∧ F y = y := by
      rintro _ ⟨z, hzP, rfl⟩
      obtain ⟨hzR, hzx⟩ := hP hzP
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
      exact ⟨mem_toralCentralizer.2 ⟨hy₁G, hy₁d⟩, hy₁F⟩
    have hP'M : P' ≤ M := by
      have hperf' : ⁅P', P'⁆ = P' := by
        rw [hP', ← Subgroup.map_commutator, hperf]
      calc P' = ⁅P', P'⁆ := hperf'.symm
        _ ≤ M := by
          refine Subgroup.commutator_le.2 fun y hy z hz => ?_
          rw [← hMeq]
          exact hab r hr y (hP'Z y hy).1 z (hP'Z z hz).1
    rintro _ ⟨z, hzP, rfl⟩
    have hy₁P' : g₁ * z * g₁⁻¹ ∈ P' := ⟨z, hzP, rfl⟩
    have hy₁M : g₁ * z * g₁⁻¹ ∈ M := hP'M hy₁P'
    have hy₁F : F (g₁ * z * g₁⁻¹) = g₁ * z * g₁⁻¹ := (hP'Z _ hy₁P').2
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

end Datum

section D4

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem d4_kernelRoots_nonempty {r : SignRep .D4} (hr : r ∈ d4SignDiagramReps) :
    (kernelRoots (signMaskChar Tag.D4 r.mask)).Nonempty := by
  simp only [d4SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h : ∃ m, (m = 0 ∨ m = 4) ∧ r.mask = m := by
    rcases hr with rfl | rfl
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨4, Or.inr rfl, rfl⟩
  obtain ⟨m, hm, hrm⟩ := h
  rw [hrm]
  have h1 : (List.range d4Certificate.roots.length).any (inKernel d4Certificate m) = true := by
    rcases hm with rfl | rfl <;> decide +kernel
  simp only [List.any_eq_true, List.mem_range] at h1
  obtain ⟨j, hj, hker⟩ := h1
  exact ⟨_, (mem_kernelRoots_iff d4Certificate_check).2 ⟨j, hj, rfl, hker⟩⟩

theorem d4_exists_datum_conj_perfect (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.D4.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ d4SignDiagramReps, ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.D4.tag p k)
      (w h : ModGL TwistTag.D4.tag k),
      w ∈ adjointGroup TwistTag.D4.tag k ∧ h ∈ torusGroup TwistTag.D4.tag k ∧
      w * x * w⁻¹ = rootDiagUnit TwistTag.D4.tag
        (signCharTuple (signMaskChar TwistTag.D4.tag r.mask)) ∧
      D.χ = signMaskChar TwistTag.D4.tag r.mask ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.D4.perm γ)) ∧
      (∀ y : adjointGroup TwistTag.D4.tag k, (D.F y : ModGL TwistTag.D4.tag k) =
        frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k) y) ∧
      ∀ P : Subgroup (ModGL TwistTag.D4.tag k),
        P ≤ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) ⊓
            Subgroup.centralizer {x} →
        ⁅P, P⁆ = P →
          P.map (MulAut.conj w).toMonoidHom ≤
            D.totalFixedGroup.map (adjointGroup TwistTag.D4.tag k).subtype := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  obtain ⟨r, hr, D, w, h, hw, hh, hwx, hDχ, hDe, hDθ, hDF, hP⟩ :=
    exists_datum_conj_perfect p TwistTag.D4 hp hk he d4SignDiagramReps (r₀ := 3)
      symmetrizedCartan_perm_D4 h4.permChar_eq h4.exists_rep (untwistAt_d4 p hp e)
      (fun r hr => h4.theta r hr [] (nil_mem_omegaWords_d4 hr))
      (fun r hr => n4 r hr [] (nil_mem_omegaWords_d4 hr))
      (fun r hr => d4_kernelRoots_nonempty hr)
      (fun r _ y hy z hz => commutator_mem_toralRootGroup_of_d4 hk2 (signCharTuple_sign _) hy hz)
      hx hx2
  refine ⟨r, hr, D, w, h, hw, hh, hwx, hDχ, hDe, fun γ => ?_, hDF, hP⟩
  have := hDθ γ
  rwa [wordElt_nil, thetaMap_one] at this

end D4

end CFSG.ClassicalInvolution.ModelFacts
