module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67AltComb
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup

section Invariance

variable {G G' : Type*} [Group G] [Group G']

@[expose] def CenDerivedPerfect (x : G) : Prop :=
  ⁅⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆,
      ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆⁆ =
    ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ ∧
  ∃ u ∈ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆,
    ∃ v ∈ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆, u * v ≠ v * u

theorem centralizer_singleton_map (ψ : G ≃* G') (x : G) :
    centralizer ({ψ x} : Set G') = (centralizer ({x} : Set G)).map ψ.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine Subgroup.mem_map.2 ⟨ψ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply ψ.injective
    simpa using hy
  · intro hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
    simpa using congrArg ψ hu

theorem CenDerivedPerfect.map (ψ : G ≃* G') {x : G} (h : CenDerivedPerfect x) :
    CenDerivedPerfect (ψ x) := by
  obtain ⟨hperf, u, hu, v, hv, huv⟩ := h
  unfold CenDerivedPerfect
  rw [centralizer_singleton_map ψ x, ← Subgroup.map_commutator]
  refine ⟨?_, ψ u, Subgroup.mem_map_of_mem _ hu, ψ v, Subgroup.mem_map_of_mem _ hv, ?_⟩
  · rw [← Subgroup.map_commutator, hperf]
  · intro h
    exact huv (ψ.injective (by simpa using h))

end Invariance

section Singular


section FromSingular

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Lattice CFSG.RankThree.LocalRank

theorem CenDerivedPerfect.of_singular {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ}
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (h : SingularCentralizerData σ q x) :
    CenDerivedPerfect x := by
  obtain ⟨hq, -⟩ := h
  refine ⟨Subgroup.isPerfect_iff.1 hq.1, ?_⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a'.1, a'.2, b'.1, b'.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)

end FromSingular

section Lines

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem exists_four_singular_lines {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : CFSG.IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) :
    ∃ M : Fin 4 → Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ i, M i ≤ E) ∧ (∀ i, Nat.card (M i) = p) ∧ (∀ i j, i ≠ j → M i ≠ M j) ∧
      ∀ i, ∀ x ∈ M i, x ≠ 1 → CenDerivedPerfect x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hFr : ∀ c : AlgebraicClosure K,
      iterateFrobenius (AlgebraicClosure K) ℓ f c = c ^ (ℓ ^ f) :=
    fun c => by rw [iterateFrobenius_def]
  have hq1 : (1 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_pow _ _ hℓ.pos
  have hd0 : 0 ≤ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 := by
    rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 :=
    ⟨_, Int.toNat_of_nonneg hd0⟩
  have hpd' : p ∣ d := by
    rw [← hd] at hpd
    exact_mod_cast hpd
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, hall⟩ := triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ
    hσ (AlgebraicClosure K) _ hFr hε hd
  obtain ⟨hrange, -, hp'⟩ := hall g hgG hFg
  obtain ⟨-, -, -, -, hlinecard, hdist, -, hkernels, -, hplanes⟩ := hp' p hp hp3 hpd'
  obtain ⟨c, hcE, -⟩ := hplanes E hE hEcard
  have hι := threeSixEmb_injective K (AlgebraicClosure K) σ
  have hTle : threeSixTorsion (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) ε p ≤
      threeSixTorus (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) ε :=
    fun h hh => hh.1
  have hmapT := (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hTle).trans hrange
  have hLT : ∀ i, threeSixLine (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      ε p i ≤ threeSixTorsion (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
        ε p := fun i => inf_le_left
  let M : Fin 4 → Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun i =>
    ((threeSixLine (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) ε p i).map
      (MulAut.conj g).toMonoidHom).comap (threeSixEmb K (AlgebraicClosure K) σ)
  have hMmap : ∀ i, (M i).map (threeSixEmb K (AlgebraicClosure K) σ) =
      (threeSixLine (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) ε p i).map
        (MulAut.conj g).toMonoidHom := fun i =>
    Subgroup.map_comap_eq_self ((Subgroup.map_mono (hLT i)).trans (hmapT))
  have hMle : ∀ i, M i ≤ threeSixFixedTorsion K (AlgebraicClosure K) σ
      (iterateFrobenius (AlgebraicClosure K) ℓ f) ε p g := fun i =>
    Subgroup.comap_mono (Subgroup.map_mono (hLT i))
  refine ⟨fun i => (M i).map (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro i y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
    have hmT := hMle i hm
    rw [← hcE] at hmT
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hmT
    have : (MulAut.conj c⁻¹).toMonoidHom ((MulAut.conj c).toMonoidHom e) = e := by
      show c⁻¹ * (c * e * c⁻¹) * c⁻¹⁻¹ = e
      group
    rw [this]
    exact he
  · intro i
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective,
      ← Subgroup.card_map_of_injective hι, hMmap,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hlinecard i
  · intro i j hij h
    have h1 : M i = M j := Subgroup.map_injective (MulAut.conj c⁻¹).injective h
    have h2 := congrArg (Subgroup.map (threeSixEmb K (AlgebraicClosure K) σ)) h1
    rw [hMmap, hMmap] at h2
    exact hdist hij (Subgroup.map_injective (MulAut.conj g).injective h2)
  · intro i x hx hx1
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hx
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hx1 (map_one _)
    have hmem : threeSixEmb K (AlgebraicClosure K) σ m ∈
        (threeSixLine (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) ε p i).map
          (MulAut.conj g).toMonoidHom := by
      rw [← hMmap]
      exact Subgroup.mem_map_of_mem _ hm
    obtain ⟨h, hhL, hh⟩ := Subgroup.mem_map.1 hmem
    obtain ⟨hhT, hhK⟩ := Subgroup.mem_inf.1 hhL
    obtain ⟨a, ha, hah⟩ := Subgroup.mem_map.1 hhK
    have hh1 : h ≠ 1 := by
      rintro rfl
      apply hm1
      apply hι
      rw [← hh, map_one, map_one]
    have hord : orderOf h = p := orderOf_eq_prime hhT.2 hh1
    have hha : rootDiagUnit TwistTag.D4.tag a = h := hah
    subst hha
    have hsurv := (hkernels a hhT hh1).1 i hhL
    have hne : (survivingRoots a).Nonempty := by
      rw [hsurv]
      exact ⟨threeSixU i, threeSixU_mem i⟩
    have hsing := singularCentralizerData_threeSix hℓ hf K hK σ hσ (AlgebraicClosure K) _ hFr hε hd
      hgG hFg hp hp3 hpd' a hhT.1 hord hne m (by rw [← hh]; rfl)
    exact CenDerivedPerfect.map (MulAut.conj c⁻¹) (CenDerivedPerfect.of_singular hsing)

end Lines

end Singular

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
