module

public import CFSG.ClassicalInvolution.Q3.Q3PlanDatumMeta
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7Conj
public import CFSG.ClassicalInvolution.Q3.Q3ExcPinned
public import CFSG.LieType.HighestRoot.CentChevalleyToral

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.HighestRoot
open scoped MatrixGroups commutatorElement

section Twist

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]


theorem e7_twisted_datum' (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {r : SignRep .E7}
    (hr : r ∈ e7SignDiagramReps) {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords)
    (hl0 : l ≠ []) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (u : ModGL .E7 k)
      (Xh : Subgroup (ModGL .E7 k)), D.e = e ∧
      D.totalFixedGroup.map (adjointGroup .E7 k).subtype = Xh ∧
      Xh.map (MulAut.conj u).toMonoidHom =
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
  have hQ₀T : wordWeylMatrix .E7 k l * 1 ∈
      Subgroup.normalizer (torusGroup .E7 k : Set (ModGL .E7 k)) :=
    mul_mem (wordWeylMatrix_mem_normalizer l) (one_mem _)
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX, u, hu, hconj⟩ := exc3_exists_pinned_datum p hp2 hk he
    (Or.inr (Or.inr rfl)) (ρ := 1) (fun _ _ => rfl) (fun _ _ => rfl) (h7.theta r hr l hl)
    (fun γ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) hQ₀T
    (map_conj_wordWeylMatrix_mul l (map_conj_one_adjointGroup _ k)) (n7 r hr l hl) hne
  exact ⟨D, u, _, hDe, hX, hconj⟩

theorem e7_twisted_derived (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (h3 : 3 < p ^ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    {R : Subgroup (ModGL .E7 k)}
    (hR : R = fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)) (hRfin : Finite R)
    {x : ModGL .E7 k} {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords) (hl0 : l ≠ [])
    {g₁ : ModGL .E7 k} (hg₁ : g₁ ∈ adjointGroup .E7 k)
    (hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 r.mask)))
    (hcoc : g₁ * (frobTwistGL .E7 k p e 1 g₁)⁻¹ = wordWeylMatrix .E7 k l)
    {J : Subgroup (ModGL .E7 k)} (hJs : IsSubnormal J (⁅R, R⁆ ⊓ Subgroup.centralizer {x}))
    (hsolv : Group.IsSolvable J) (hodd : IsOddGenerated J) : derivedSeries ↥J 2 = ⊥ := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  obtain ⟨D, u, Xh, hDe, hX, hconj⟩ := e7_twisted_datum' hp2 he hk hr hl hl0
  have h3D : 3 < D.q := by
    change 3 < p ^ D.e
    rw [hDe]
    exact h3
  set F := frobTwistGL .E7 k p e 1 with hF
  set Nw := wordWeylMatrix .E7 k l with hNw
  set F₀ := frobTwistGL .E7 k p e (Nw * 1) with hF₀
  set χ := signMaskChar .E7 r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk2 χ
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots χ) with hM
  have hF₀F : ∀ w, F₀ w = Nw * F w * Nw⁻¹ := by
    intro w
    simp only [hF₀, hF, frobTwistGL_apply, mul_one, one_mul, inv_one]
  have hFg₁ : F g₁ = Nw⁻¹ * g₁ := by
    have h1 : (F g₁)⁻¹ = g₁⁻¹ * Nw := by rw [← hcoc]; group
    calc F g₁ = ((F g₁)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (g₁⁻¹ * Nw)⁻¹ := by rw [h1]
      _ = Nw⁻¹ * g₁ := by group
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hRF : ∀ y ∈ R, y ∈ adjointGroup .E7 k ∧ F y = y := fun y hy => by
    rw [hR] at hy
    exact mem_fixedPointsIn.1 hy
  have hconjY : ∀ y ∈ ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL .E7 k)),
      g₁ * y * g₁⁻¹ ∈ toralCentralizer .E7 k a ∧ F₀ (g₁ * y * g₁⁻¹) = g₁ * y * g₁⁻¹ := by
    intro y hy
    obtain ⟨hyc, hycx⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨hyG, hyF⟩ := hRF y (hRsub hyc)
    have hxy : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hycx
    refine ⟨mem_toralCentralizer.2 ⟨mul_mem (mul_mem hg₁ hyG) (inv_mem hg₁), ?_⟩, ?_⟩
    · rw [← hg₁x]
      calc g₁ * x * g₁⁻¹ * (g₁ * y * g₁⁻¹) * (g₁ * x * g₁⁻¹)⁻¹ = g₁ * (x * y * x⁻¹) * g₁⁻¹ := by
            group
        _ = g₁ * y * g₁⁻¹ := by rw [← hxy]; group
    · rw [hF₀F, map_mul, map_mul, map_inv, hFg₁, hyF]
      group
  have hMeq : M = toralRootGroup .E7 k a := by rw [hM, toralRootGroup, hker]
  set G := ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL .E7 k)) with hG
  set φ := (MulAut.conj g₁).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g₁).injective
  have hφapp : ∀ y, φ y = g₁ * y * g₁⁻¹ := fun y => rfl
  have hGfin : Finite G := Finite.of_injective
    (fun y : G => (⟨y.1, hRsub (Subgroup.mem_inf.1 y.2).1⟩ : R))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have : Finite (G.map φ) := Finite.of_equiv _ (G.equivMapOfInjective φ hφinj).toEquiv
  have hY2 : ∀ y ∈ G.map φ, y ^ 2 ∈ fixedPointsIn M F₀ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hZ, hFy⟩ := hconjY y hy
    have hsq := sq_mem_toralRootGroup hk2 ha hZ
    rw [toralRootGroup, hker] at hsq
    refine mem_fixedPointsIn.2 ⟨hsq, ?_⟩
    rw [map_pow, hφapp, hFy]
  have hYn : ∀ y ∈ G.map φ, ∀ v ∈ fixedPointsIn M F₀, y * v * y⁻¹ ∈ fixedPointsIn M F₀ := by
    rintro _ ⟨y, hy, rfl⟩ v hv
    obtain ⟨hZ, hFy⟩ := hconjY y hy
    obtain ⟨hvM, hvF⟩ := mem_fixedPointsIn.1 hv
    have hnorm := (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hZ) v).1
      (by rw [← hMeq]; exact hvM)
    refine mem_fixedPointsIn.2 ⟨by rw [hMeq]; exact hnorm, ?_⟩
    rw [hφapp, map_mul, map_mul, map_inv, hFy, hvF]
  have hMG : M ≤ adjointGroup .E7 k :=
    sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup k _)
  have hCY : ∀ J' : Set.range D.classOrbit,
      ((D.withOrbit J').orbitGroup).map (MulAut.conj u).toMonoidHom ≤ G.map φ := by
    intro J'
    set C := (D.withOrbit J').orbitGroup with hC
    have hCXh : C ≤ Xh := by
      rw [← hX]
      exact CFSG.ClassicalInvolution.isSubnormal_le (orbitGroup_isSubnormal D J')
    have hperf : ⁅C, C⁆ = C := by
      rcases orbitGroup_eq_bot_or_isQuasisimple D h3D J' with hbot | hqs
      · have hbot' : C = ⊥ := hbot
        rw [hbot']
        exact Subgroup.commutator_bot_left _
      · exact Subgroup.isPerfect_iff.1 ⟨hqs.1⟩
    set P₁ := C.map (MulAut.conj u).toMonoidHom with hP₁
    set P := P₁.map (MulAut.conj g₁⁻¹).toMonoidHom with hP
    have hPperf : ⁅P, P⁆ = P := by
      rw [hP, hP₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hperf]
    have hP₁X : ∀ w ∈ P₁, w ∈ fixedPointsIn M F₀ := by
      intro w hw
      rw [← hconj]
      obtain ⟨c', hc', rfl⟩ := hw
      exact Subgroup.mem_map_of_mem _ (hCXh hc')
    have hPR : P ≤ R := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨hwM, hwF⟩ := mem_fixedPointsIn.1 (hP₁X w hw)
      have hFw : F w = Nw⁻¹ * w * Nw := by
        have h := hF₀F w
        rw [hwF] at h
        calc F w = Nw⁻¹ * (Nw * F w * Nw⁻¹) * Nw := by group
          _ = Nw⁻¹ * w * Nw := by rw [← h]
      rw [hR]
      refine mem_fixedPointsIn.2 ⟨?_, ?_⟩
      · exact mul_mem (mul_mem (inv_mem hg₁) (hMG hwM)) hg₁
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [map_mul, map_mul, map_inv, hFg₁, hFw]
        group
    have hPG : P ≤ G := by
      have hPR' : P ≤ ⁅R, R⁆ := by
        rw [← hPperf]
        exact Subgroup.commutator_mono hPR hPR
      refine le_inf hPR' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hwM := (mem_fixedPointsIn.1 (hP₁X w hw)).1
      have hwZ := toralRootGroup_le a (hMeq ▸ hwM)
      have hd := (mem_toralCentralizer.1 hwZ).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxd : x = g₁⁻¹ * rootDiagUnit .E7 a * g₁ := by rw [← hg₁x]; group
      have hdw : rootDiagUnit .E7 a * w = w * rootDiagUnit .E7 a := by
        calc rootDiagUnit .E7 a * w = (rootDiagUnit .E7 a * w * (rootDiagUnit .E7 a)⁻¹) *
            rootDiagUnit .E7 a := by group
          _ = w * rootDiagUnit .E7 a := by rw [hd]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hxd]
      calc g₁⁻¹ * w * g₁⁻¹⁻¹ * (g₁⁻¹ * rootDiagUnit .E7 a * g₁) =
          g₁⁻¹ * (w * rootDiagUnit .E7 a) * g₁ := by group
        _ = g₁⁻¹ * (rootDiagUnit .E7 a * w) * g₁ := by rw [hdw]
        _ = (g₁⁻¹ * rootDiagUnit .E7 a * g₁) * (g₁⁻¹ * w * g₁⁻¹⁻¹) := by group
    intro w hw
    refine ⟨g₁⁻¹ * w * g₁, hPG ⟨w, hw, rfl⟩, ?_⟩
    rw [hφapp]
    group
  have hJsub : IsSubnormal (J.map φ) (G.map φ) :=
    CFSG.ClassicalInvolution.isSubnormal_map_mulEquiv (MulAut.conj g₁) hJs
  have hJsolv : Group.IsSolvable ↥(J.map φ) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (J.equivMapOfInjective φ hφinj).symm.toMonoidHom)
      (J.equivMapOfInjective φ hφinj).symm.injective
  exact derivedSeries_eq_bot_of_map φ hφinj
    (derivedSeries_two_eq_bot_of_datum D h3D u hX hconj (Y := G.map φ) hCY hY2 hYn hJsub hJsolv
      (hodd.map φ hφinj))

end Twist

end CFSG.ClassicalInvolution.Q3
