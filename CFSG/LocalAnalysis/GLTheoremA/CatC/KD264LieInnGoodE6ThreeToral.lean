module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SubnormalTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KilledPlaneCubeRoot
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

section RootKernel


theorem e6Three_exists_root_triPairing_eq_zero (k : Fin Tag.E6.rank → ZMod 3) :
    ∃ γ, IsRoot Tag.E6 γ ∧ triPairing k γ = 0 := by
  have h : ∀ k : Fin Tag.E6.rank → ZMod 3, ∃ l ∈ Tag.E6.artifactRoots,
      triPairing (τ := Tag.E6) k (CFSG.RankThree.Lattice.toVec Tag.E6.rank l) = 0 := by
    decide +kernel
  obtain ⟨l, hl, h0⟩ := h k
  exact ⟨CFSG.RankThree.Lattice.toVec Tag.E6.rank l, CFSG.RankThree.Lattice.isRoot_toVec hl, h0⟩

theorem e6Three_exists_root_rootChar_eq_one {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (h3 : ∀ i, a i ^ 3 = 1) : ∃ γ, IsRoot Tag.E6 γ ∧ rootChar a γ = 1 := by
  rcases forall_eq_one_or_exists_isPrimitiveRoot_pow (τ := Tag.E6) (fun _ : Unit => a)
    (fun _ i => h3 i) with h1 | ⟨ω, hω, k, hb⟩
  · refine ⟨Pi.single 0 1, isRoot_single _ 0, ?_⟩
    have : a = 1 := funext fun i => h1 () i
    simp [this, rootChar]
  · obtain ⟨γ, hγ, hk0⟩ := e6Three_exists_root_triPairing_eq_zero (k ())
    refine ⟨γ, hγ, ?_⟩
    rw [rootChar_eq_pow_triPairing hω.pow_eq_one (hb ()) γ, hk0]
    simp

end RootKernel

section Toral


theorem e6Three_exists_perfect_fixed_of_toral
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {w : WeylGroup Tag.E6} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    {g : ModGL Tag.E6 K} {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hga : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) g * g0 =
      rootDiagUnit Tag.E6 a)
    (hT : rootDiagUnit Tag.E6 a ∈ twistedTorusOf
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) (Units.map (entrywiseHom Fr)))
    (ha3 : ∀ i, a i ^ 3 = 1) (ha1 : rootDiagUnit Tag.E6 a ≠ 1)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hχ : rootChar a γ = 1) :
    ∃ P : Subgroup (adjointGroup Tag.E6 K),
      (∀ y ∈ P, g * (y : ModGL Tag.E6 K) * g⁻¹ = y) ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  classical
  set L := AlgebraicClosure K with hL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpK : ¬ 3 ∣ Nat.card K := by
    intro h3
    have : Fintype K := Fintype.ofFinite K
    haveI := ringChar.charP K
    obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hcard] at h3
    exact hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  obtain ⟨S, hS⟩ := exists_langSetup_ofFrobenius (τ := Tag.E6) (Or.inr (Or.inl rfl)) w K hFr hg0C
    hg0 Nat.prime_three hpK (Or.inr hK4)
  have hTS : rootDiagUnit Tag.E6 a ∈ S.D.torus := by rw [hS]; exact hT
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have : a ^ 3 = 1 := funext fun i => by simpa using ha3 i
    rw [this, rootDiagUnit_one]
  have hk : γ ∈ kernelRoots (rootCharHom a) := ⟨hγ, hχ⟩
  set i : KernelComponent (rootCharHom a) := ⟦⟨γ, hk⟩⟧ with hi
  obtain ⟨hRC, -⟩ := langSubnormal_provedT Tag.E6 L 3 S a hTS hTp ha1 i
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  have hbig : ¬ Nat.Coprime 3 (Nat.card R) := threeBigComponents_holds Tag.E6 L S a hTS ha1 i
  have hq : CFSG.IsQuasisimple R := by
    cases hkind : twistKind S.ρ (rootCharHom a) i
    · exact langComponentsQuasisimple_inner_holdsT Tag.E6 L 3 S a hTS hTp ha1 i hkind hbig
    · exact langComponentsQuasisimpleT_suN_proved Tag.E6 L 3 S a hTS hTp ha1 i hkind hbig
    · exact langComponentsQuasisimpleT_twoD_proved Tag.E6 L 3 S a hTS hTp ha1 i hkind hbig
    · exact langComponentsQuasisimple_exc_provedT Tag.E6 L 3 S a hTS hTp ha1 i hkind hbig
  have hRΓ : R ≤ S.Γ := hRC.trans inf_le_left
  have hRcent : R ≤ Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 L)) :=
    hRC.trans inf_le_right
  have hRperf : ⁅R, R⁆ = R := by
    haveI : Group.IsPerfect ↥R := hq.1
    exact Subgroup.commutator_eq_self
  let ψ : adjointGroup Tag.E6 K →* ModGL Tag.E6 L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E6 K).subtype)
  have hψ : ∀ y, ψ y = g0⁻¹ * baseChangeGL (algebraMap K L) (y : ModGL Tag.E6 K) * g0 :=
    fun y => by simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g0⁻¹).injective.comp
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))
  have hΓ : S.Γ = langModel Tag.E6 K L g0 := by
    change S.D.Γ = _
    rw [hS]
    exact Γ_ofFrobenius_eq_langModel_exc (Or.inr (Or.inl rfl)) w K hFr hg0C hg0
  have hrange : ψ.range = langModel Tag.E6 K L g0 := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype, langModel]
  have hRrange : R ≤ ψ.range := by
    rw [hrange, ← hΓ]
    exact hRΓ
  refine ⟨R.comap ψ, ?_, ?_, ?_⟩
  · intro y hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hRcent (Subgroup.mem_comap.1 hy))
    rw [hψ, ← hga] at h1
    have h2 : baseChangeGL (algebraMap K L) (y : ModGL Tag.E6 K) *
        baseChangeGL (algebraMap K L) g =
        baseChangeGL (algebraMap K L) g * baseChangeGL (algebraMap K L) (y : ModGL Tag.E6 K) := by
      have h3 : g0 * (g0⁻¹ * baseChangeGL (algebraMap K L) (y : ModGL Tag.E6 K) * g0 *
          (g0⁻¹ * baseChangeGL (algebraMap K L) g * g0)) * g0⁻¹ =
          g0 * (g0⁻¹ * baseChangeGL (algebraMap K L) g * g0 *
          (g0⁻¹ * baseChangeGL (algebraMap K L) (y : ModGL Tag.E6 K) * g0)) * g0⁻¹ := by rw [h1]
      simpa [mul_assoc] using h3
    apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K L)
    rw [map_mul, map_mul, map_inv, h2.symm]
    group
  · apply Subgroup.map_injective hψinj
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hRrange, hRperf]
  · rw [← Subgroup.card_map_of_injective hψinj (K := R.comap ψ),
      Subgroup.map_comap_eq_self hRrange]
    exact (Nat.Prime.dvd_iff_not_coprime Nat.prime_three).2 hbig

end Toral

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
