module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Orb
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Datum
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Fixed
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum


variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

@[expose] noncomputable def conjOrbitGroup (D' : OrthogonalSemilinearFixedRootDatum τ p k)
    (J' : Set.range D'.classOrbit) (w : ModGL τ k) : Subgroup (ModGL τ k) :=
  ((D'.withOrbit J').orbitGroupC.map (adjointGroup τ k).subtype).map (MulAut.conj w).toMonoidHom

theorem conjOrbitGroup_eq_closure (D' : OrthogonalSemilinearFixedRootDatum τ p k)
    (J' : Set.range D'.classOrbit) (w : ModGL τ k) :
    conjOrbitGroup D' J' w = closure ((fun g => w * g * w⁻¹) ''
      {g | ∃ O ∈ (D'.withOrbit J').orbits, ∃ c : (D'.withOrbit J').orbitField O,
        g = (D'.withOrbit J').orbitX O c ∨ g = (D'.withOrbit J').orbitY O c}) := by
  rw [conjOrbitGroup, orbitGroupC,
    map_subgroupOf_eq_of_le (D'.withOrbit J').orbitGroup_le_adjointGroup, orbitGroup,
    MonoidHom.map_closure]
  rfl

section Reduction

variable {D : ModGL τ k} {x g₁ N : ModGL τ k} {a : Fin τ.rank → kˣ} {e : ℕ}

omit
  [IsAlgClosed k] in
theorem map_conj_le_inf (hg₁G : g₁ ∈ adjointGroup τ k)
    (hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit τ a)
    (hg₁F : g₁ * (frobTwistGL τ k p e D g₁)⁻¹ = N) :
    (fixedPointsIn (toralRootGroup τ k a) (frobTwistGL τ k p e (N * D))).map
        (MulAut.conj g₁⁻¹).toMonoidHom ≤
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) ⊓ centralizer {x} := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨hqM, hqF⟩ := mem_fixedPointsIn.1 hq
  have hqC := toralRootGroup_le a hqM
  obtain ⟨hqG, hqd⟩ := mem_toralCentralizer.1 hqC
  have hFg : frobTwistGL τ k p e D g₁ = N⁻¹ * g₁ := by
    rw [← hg₁F]
    group
  have hFq : frobTwistGL τ k p e D q = N⁻¹ * q * N := by
    have h1 := frobTwistGL_mul_left_apply p e N D q
    rw [hqF] at h1
    calc frobTwistGL τ k p e D q = N⁻¹ * (N * frobTwistGL τ k p e D q * N⁻¹) * N := by group
      _ = N⁻¹ * q * N := by rw [← h1]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  refine mem_inf.2 ⟨mem_fixedPointsIn.2 ⟨?_, ?_⟩, mem_centralizer_singleton_iff.2 ?_⟩
  · exact mul_mem (mul_mem (inv_mem hg₁G) hqG) hg₁G
  · rw [map_mul, map_mul, map_inv, hFg, hFq]
    group
  · have hx : x = g₁⁻¹ * rootDiagUnit τ a * g₁ := by
      rw [← hg₁x]
      group
    rw [hx]
    calc g₁⁻¹ * q * g₁ * (g₁⁻¹ * rootDiagUnit τ a * g₁) = g₁⁻¹ * (q * rootDiagUnit τ a) * g₁ := by
          group
      _ = g₁⁻¹ * (rootDiagUnit τ a * q) * g₁ := by
          congr 2
          calc q * rootDiagUnit τ a = rootDiagUnit τ a * q * (rootDiagUnit τ a)⁻¹ *
              rootDiagUnit τ a := by rw [hqd]
            _ = rootDiagUnit τ a * q := by group
      _ = g₁⁻¹ * rootDiagUnit τ a * g₁ * (g₁⁻¹ * q * g₁) := by group

omit [IsAlgClosed k] in
theorem map_conj_normal (hg₁G : g₁ ∈ adjointGroup τ k)
    (hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit τ a)
    (hg₁F : g₁ * (frobTwistGL τ k p e D g₁)⁻¹ = N) :
    (((fixedPointsIn (toralRootGroup τ k a) (frobTwistGL τ k p e (N * D))).map
        (MulAut.conj g₁⁻¹).toMonoidHom).subgroupOf
      (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) ⊓ centralizer {x})).Normal := by
  refine ⟨fun n hn y => ?_⟩
  obtain ⟨y, hy⟩ := y
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨q, hq, hqn⟩ := hn
  obtain ⟨hqM, hqF⟩ := mem_fixedPointsIn.1 hq
  obtain ⟨hyR, hyx⟩ := mem_inf.1 hy
  obtain ⟨hyG, hyF⟩ := mem_fixedPointsIn.1 hyR
  have hyx' : y * x = x * y := mem_centralizer_singleton_iff.1 hyx
  set c : ModGL τ k := g₁ * y * g₁⁻¹ with hc
  have hFg : frobTwistGL τ k p e D g₁ = N⁻¹ * g₁ := by
    rw [← hg₁F]
    group
  have hcC : c ∈ toralCentralizer τ k a := by
    refine mem_toralCentralizer.2 ⟨mul_mem (mul_mem hg₁G hyG) (inv_mem hg₁G), ?_⟩
    have hx : x = g₁⁻¹ * rootDiagUnit τ a * g₁ := by
      rw [← hg₁x]
      group
    rw [hx] at hyx'
    have h1 : rootDiagUnit τ a * c = c * rootDiagUnit τ a := by
      calc rootDiagUnit τ a * c = g₁ * ((g₁⁻¹ * rootDiagUnit τ a * g₁) * y) * g₁⁻¹ := by
            rw [hc]
            group
        _ = g₁ * (y * (g₁⁻¹ * rootDiagUnit τ a * g₁)) * g₁⁻¹ := by rw [hyx']
        _ = c * rootDiagUnit τ a := by
            rw [hc]
            group
    rw [h1]
    group
  have hcF : frobTwistGL τ k p e (N * D) c = c := by
    rw [frobTwistGL_mul_left_apply, hc, map_mul, map_mul, map_inv, hFg, hyF]
    group
  have hcn := toralCentralizer_le_normalizer a hcC
  have hcq : c * q * c⁻¹ ∈
      fixedPointsIn (toralRootGroup τ k a) (frobTwistGL τ k p e (N * D)) := by
    refine mem_fixedPointsIn.2 ⟨(mem_normalizer_iff.1 hcn q).1 hqM, ?_⟩
    rw [map_mul, map_mul, map_inv, hcF, hqF]
  refine ⟨_, hcq, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hqn ⊢
  rw [hc, coe_mul, coe_mul, coe_inv, ← hqn]
  group

end Reduction

theorem exists_conjOrbitGroup_component (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    (hwit : ∀ m ∈ reps, ∃ β ∈ kernelRoots (signMaskChar τ m.mask),
      ∃ γ ∈ kernelRoots (signMaskChar τ m.mask), iform β γ = 1)
    {x : ModGL τ k}
    (hred : ∃ m ∈ reps, ∃ l ∈ m.omegaWords, ∃ g₁ ∈ adjointGroup τ k,
      g₁ * x * g₁⁻¹ = rootDiagUnit τ (signCharTuple (k := k) (signMaskChar τ m.mask)) ∧
        g₁ * (frobTwistGL τ k p e D g₁)⁻¹ = wordWeylMatrix τ k l) :
    ∃ (D' : OrthogonalSemilinearFixedRootDatum τ p k) (J' : Set.range D'.classOrbit)
      (w : ModGL τ k),
      conjOrbitGroup D' J' w ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
        fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ centralizer {x} ∧
      ((conjOrbitGroup D' J' w).subgroupOf
        (⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
          fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
            centralizer {x})).IsSubnormal ∧
      GorensteinWalter.IsQuasisimple (conjOrbitGroup D' J' w) := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, l, hl, g₁, hg₁G, hg₁x, hg₁F⟩ := hred
  set χ := signMaskChar τ r.mask with hχ
  set Q₀ := wordWeylMatrix τ k l * D with hQ₀_def
  set M := torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) with hM_def
  set R := fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) with hR_def
  set a := signCharTuple (k := k) χ with ha_def
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk2 χ
  have hMT : toralRootGroup τ k a = M := by rw [toralRootGroup, hker]
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := hwit r hr
  have hne : (kernelRoots χ).Nonempty := ⟨β, hβ⟩
  have hθ := htheta r hr l hl
  have hQ₀T : Q₀ ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    mul_mem (wordWeylMatrix_mem_normalizer l) hDT
  obtain ⟨D', h, hhT, hDχ, -, -, -, hX⟩ := exists_pinned_datum p hp hk he hτ hA hB hθ
    (hDX l) hQ₀T (map_conj_wordWeylMatrix_mul l hDG) (hpin r hr l hl) hne
  obtain ⟨-, ⟨hMc, -, hMsm, -, -⟩, -⟩ := exceptional_toral_centralizer_identity_component τ k hk2
    a (signCharTuple_sign χ)
  rw [toralRootPointSubgroup, toralRootGroup, hker] at hMc hMsm
  have hF₀M : ∀ g ∈ M, frobTwistGL τ k p e Q₀ g ∈ M := by
    intro g hg
    have hS : (rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q₀) =
        rootSpan τ k (kernelRoots χ) := by
      rw [map_frobTwistGL_rootSpan_of_conj p e (hDX l) fun _ hα => hα.1, hθ.image_kernelRoots]
    have hM₀ : M.map (frobTwistGL τ k p e Q₀) = M := by
      rw [hM_def, Subgroup.map_sup, map_frobTwistGL_torusGroup p e hQ₀T, hS]
    rw [← hM₀]
    exact ⟨g, hg, rfl⟩
  obtain ⟨z, hzM, hz⟩ := exists_eq_inv_mul_frobTwistGL p he Q₀ hMc hMsm hF₀M
    (Subgroup.mem_sup_left hhT)
  have hFu : frobTwistGL τ k p e Q₀ z⁻¹ = h⁻¹ * z⁻¹ := by
    rw [map_inv, hz]
    group
  have hFh : ∀ y, frobTwistGL τ k p e (h * Q₀) y = h * frobTwistGL τ k p e Q₀ y * h⁻¹ :=
    fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M (frobTwistGL τ k p e Q₀)).map (MulAut.conj z⁻¹).toMonoidHom =
      fixedPointsIn M (frobTwistGL τ k p e (h * Q₀)) :=
    map_conj_fixedPointsIn_eq M _ _ (inv_mem hzM) hFh hFu
  set w := g₁⁻¹ * z with hw
  set f : adjointGroup τ k →* ModGL τ k :=
    (MulAut.conj w).toMonoidHom.comp (adjointGroup τ k).subtype with hf
  have hfi : Function.Injective f := (MulAut.conj w).injective.comp Subtype.val_injective
  have hXf : D'.totalFixedGroup.map f = (fixedPointsIn M (frobTwistGL τ k p e Q₀)).map
      (MulAut.conj g₁⁻¹).toMonoidHom := by
    rw [hf, ← map_map, hX, ← hconj, map_map]
    congr 1
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hw]
    group
  have hQ'le := map_conj_le_inf (a := a) (N := wordWeylMatrix τ k l) hg₁G hg₁x hg₁F
  have hQ'n := map_conj_normal (a := a) (N := wordWeylMatrix τ k l) hg₁G hg₁x hg₁F
  rw [hMT] at hQ'le hQ'n
  have hβ' : β ∈ kernelRoots D'.χ := hDχ ▸ hβ
  have hγ' : γ ∈ kernelRoots D'.χ := hDχ ▸ hγ
  set J' := classJ D' hβ' with hJ'
  obtain ⟨hCX, hCsn, hCq⟩ := orbitGroupC_isComponent D' J'
    (two_le_ncard_simpleRootsJ D' hβ' hγ' hβγ)
  have hY : conjOrbitGroup D' J' w = (D'.withOrbit J').orbitGroupC.map f := by
    rw [conjOrbitGroup, map_map]
  have hYq : GorensteinWalter.IsQuasisimple (conjOrbitGroup D' J' w) := by
    rw [hY]
    exact gw_isQuasisimple_of_mulEquiv
      ((D'.withOrbit J').orbitGroupC.equivMapOfInjective f hfi) hCq
  have hYle : conjOrbitGroup D' J' w ≤ R ⊓ centralizer {x} := by
    rw [hY]
    exact (map_mono hCX).trans (hXf ▸ hQ'le)
  have hYR' : conjOrbitGroup D' J' w ≤ ⁅R, R⁆ := by
    rw [← commutator_eq_self_of_gw hYq]
    exact commutator_mono (hYle.trans inf_le_left) (hYle.trans inf_le_left)
  have hYsn : ((conjOrbitGroup D' J' w).subgroupOf (R ⊓ centralizer {x})).IsSubnormal := by
    have h1 := isSubnormal_subgroupOf_map f hfi hCX hCsn
    rw [← hY, hXf] at h1
    exact isSubnormal_subgroupOf_trans (hY ▸ hXf ▸ map_mono hCX) hQ'le h1 hQ'n
  refine ⟨D', J', w, le_inf hYR' (hYle.trans inf_le_right), ?_, hYq⟩
  exact isSubnormal_subgroupOf_mono (inf_le_inf_right _ (commutator_le_self R)) hYsn

end CFSG.ComponentClassification.HarrisLit.L33.SR.E1
