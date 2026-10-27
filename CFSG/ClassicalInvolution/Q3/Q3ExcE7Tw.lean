module

public import CFSG.ClassicalInvolution.Q3.Q3ExcTwist
public import CFSG.ClassicalInvolution.Q3.Q3ExcPinned
public import CFSG.ClassicalInvolution.Q3.Q3ExcE7Data
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7Conj
public import CFSG.LieType.HighestRoot.CentChevalleyToral

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.HighestRoot
open scoped MatrixGroups

section Datum

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

omit [IsAlgClosed k] [Fact p.Prime] [CharP k p] in
theorem e7_wordWeylMatrix_sq_mem_torus {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords) (hl0 : l ≠ []) :
    wordWeylMatrix .E7 k l * wordWeylMatrix .E7 k l ∈ torusGroup .E7 k := by
  refine mem_torusGroup_of_mapsRootLines_one
    (mul_mem (wordWeylMatrix_mem_monomialSubgroup l) (wordWeylMatrix_mem_monomialSubgroup l)) ?_
  have h := (mapsRootLines_wordWeylMatrix (k := k) (τ := .E7) l).mul
    (mapsRootLines_wordWeylMatrix (k := k) (τ := .E7) l)
  rwa [e7_word_sq hr hl hl0] at h

theorem e7_twisted_datum (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {r : SignRep .E7}
    (hr : r ∈ e7SignDiagramReps) {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords)
    (hl0 : l ≠ []) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (c u : ModGL .E7 k)
      (Xh : Subgroup (ModGL .E7 k)), Exc3Frob D c ∧ D.e = e ∧
      Subsingleton (KernelComponent D.χ) ∧ CFSG.IsQuasisimple D.orbitGroup ∧
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
  have hq3D : p ^ D.e = 3 := by rw [hDe]; exact hq3
  exact ⟨D, h * (wordWeylMatrix .E7 k l * 1), u, _, hfrob, hDe, hsubD,
    exc3_isQuasisimple_orbitGroup (Or.inr (Or.inr (Or.inl rfl))) hnonD, hX, hconj⟩

end Datum

section Core

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem e7_twisted_core (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (hRfin : Finite (fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)))
    {x : ModGL .E7 k} {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords) (hl0 : l ≠ [])
    {g₁ : ModGL .E7 k} (hg₁ : g₁ ∈ adjointGroup .E7 k)
    (hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 r.mask)))
    (hcoc : g₁ * (frobTwistGL .E7 k p e 1 g₁)⁻¹ = wordWeylMatrix .E7 k l) :
    (∀ N : Subgroup (ModGL .E7 k),
      N ≤ ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)⁆ ⊓
          Subgroup.centralizer {x} →
      (∀ y ∈ ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)⁆ ⊓
          Subgroup.centralizer {x}, ∀ n ∈ N, y * n * y⁻¹ ∈ N) →
      Odd (Nat.card N) → N = ⊥) ∧
    (∀ L : Subgroup (ModGL .E7 k),
      L ≤ ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)⁆ ⊓
          Subgroup.centralizer {x} →
      Nonempty (SL(2, ZMod 3) ≃* L) →
      IsSubnormal L (⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)⁆ ⊓
          Subgroup.centralizer {x}) → False) := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  obtain ⟨D, c, u, Xh, hfrob, hDe, hsub, hqs, hX, hconj⟩ := e7_twisted_datum hp2 he hq3 hk hr hl hl0
  have hq3D : p ^ D.e = 3 := by rw [hDe]; exact hq3
  set F := frobTwistGL .E7 k p e 1 with hF
  set R := fixedPointsIn (adjointGroup .E7 k) F with hR
  set N := wordWeylMatrix .E7 k l with hN
  set F₀ := frobTwistGL .E7 k p e (N * 1) with hF₀
  set χ := signMaskChar .E7 r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk2 χ
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots χ) with hM
  have hF₀F : ∀ w, F₀ w = N * F w * N⁻¹ := by
    intro w
    simp only [hF₀, hF, frobTwistGL_apply, mul_one, one_mul, inv_one]
  have hFg₁ : F g₁ = N⁻¹ * g₁ := by
    have h1 : (F g₁)⁻¹ = g₁⁻¹ * N := by rw [← hcoc]; group
    calc F g₁ = ((F g₁)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (g₁⁻¹ * N)⁻¹ := by rw [h1]
      _ = N⁻¹ * g₁ := by group
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hconjY : ∀ y ∈ ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL .E7 k)),
      g₁ * y * g₁⁻¹ ∈ toralCentralizer .E7 k a ∧ F₀ (g₁ * y * g₁⁻¹) = g₁ * y * g₁⁻¹ := by
    intro y hy
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
  have hCmX : ∀ c' ∈ D.orbitGroup, u * c' * u⁻¹ ∈ fixedPointsIn M F₀ := by
    intro c' hc'
    have h1 : c' ∈ Xh := by
      rw [← hX]
      exact exc3_fixedGroup_le_totalFixedGroup D (exc3_orbitGroup_le_fixedGroup D hc')
    have h2 : u * c' * u⁻¹ ∈ Xh.map (MulAut.conj u).toMonoidHom := Subgroup.mem_map_of_mem _ h1
    rw [hconj] at h2
    exact h2
  set P₁ := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hP₁
  set P := P₁.map (MulAut.conj g₁⁻¹).toMonoidHom with hP
  have hperf : ⁅D.orbitGroup, D.orbitGroup⁆ = D.orbitGroup := Subgroup.isPerfect_iff.1 hqs.1
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, hP₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hperf]
  have hP₁X : ∀ w ∈ P₁, w ∈ fixedPointsIn M F₀ := by
    rintro _ ⟨c', hc', rfl⟩
    exact hCmX c' hc'
  have hPR : P ≤ R := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwM, hwF⟩ := mem_fixedPointsIn.1 (hP₁X w hw)
    have hFw : F w = N⁻¹ * w * N := by
      have h := hF₀F w
      rw [hwF] at h
      calc F w = N⁻¹ * (N * F w * N⁻¹) * N := by group
        _ = N⁻¹ * w * N := by rw [← h]
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
  have hCY : D.orbitGroup.map (MulAut.conj u).toMonoidHom ≤ G.map φ := by
    intro w hw
    refine ⟨g₁⁻¹ * w * g₁, hPG ⟨w, hw, rfl⟩, ?_⟩
    rw [hφapp]
    group
  have := hsub
  obtain ⟨hA, hB⟩ := exc3_twisted_structure (D := D) hfrob hq3D hqs u hX hconj hCY hY2 hYn
  refine ⟨fun N hNG hNn hodd => ?_, fun L hLG ⟨eL⟩ hL => ?_⟩
  · have hN' : ∀ y ∈ G.map φ, ∀ n ∈ N.map φ, y * n * y⁻¹ ∈ N.map φ := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨n, hn, rfl⟩
      have h := Subgroup.mem_map_of_mem φ (hNn y hy n hn)
      rw [map_mul, map_mul, map_inv] at h
      exact h
    have hodd' : Odd (Nat.card (N.map φ)) := by
      rwa [← Nat.card_congr (N.equivMapOfInjective φ hφinj).toEquiv]
    exact (Subgroup.map_eq_bot_iff_of_injective N hφinj).1
      (hA (N.map φ) (Subgroup.map_mono hNG) hN' hodd')
  · exact hB (L.map φ) (Subgroup.map_mono hLG)
      ⟨eL.trans (L.equivMapOfInjective φ hφinj)⟩ (isSubnormal_map_mulEquiv (MulAut.conj g₁) hL)

end Core

end CFSG.ClassicalInvolution.Q3
