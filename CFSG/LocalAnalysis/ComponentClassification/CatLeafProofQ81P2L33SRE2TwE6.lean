module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2Tools
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem twE6_highRoot_ne_one :
    pinnedX TwistTag.E6.tag K e6HighestRoot 1 ≠ 1 := fun h => by
  rw [← pinnedX_zero TwistTag.E6.tag K e6HighestRoot] at h
  exact one_ne_zero (pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot h)

theorem twE6_highRoot_mem_heightSeries
    {h : ℤ} (hh : h ≤ 11) :
    pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ heightSeries TwistTag.E6.tag K h := by
  unfold heightSeries
  refine pinnedX_mem_rootSpan ?_ 1
  exact ⟨isRoot_e6HighestRoot, by rw [height_e6HighestRoot]; norm_num,
    by rw [height_e6HighestRoot]; exact hh⟩

theorem mk_ne_one_of_ne_one {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H)
    (h : x ≠ 1) : (⟨x, hx⟩ : H) ≠ 1 :=
  fun h1 => h (congrArg Subtype.val h1)

theorem twE6_classT_not_isPGroup
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) := by
  have hu : (t : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom := by
    rw [ht]
    exact pinnedX_mem_graphFixedPosUnipotent σ.toRingHom isRoot_e6HighestRoot
      (by rw [height_e6HighestRoot]; norm_num) permLattice_e6HighestRoot (map_one _)
  have h1 : t ≠ 1 := by
    rintro rfl
    exact twE6_highRoot_ne_one (K := K) ht.symm
  rcases Nat.lt_or_ge f 2 with h2 | h2
  · obtain rfl : f = 1 := by omega
    exact not_isPGroup_of_mem_closure_odd (graphFixedPosUnipotent_le_closure_odd_two
      (by rw [hK]; norm_num) (fun c => by rw [hσ, pow_one]) ht hu) h1
  · exact not_isPGroup_of_mem_closure_odd
      (graphFixedPosUnipotent_le_closure_odd h2 hK hσ ht hu) h1

theorem twE6_classCheck_not_isPGroup
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {R : List (Fin TwistTag.E6.tag.rank → ℤ)} {h : ℤ}
    {T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))} {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hchk : twistedE6ClassCheck R h T L = true) (hh : h ≤ 11)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) := by
  have : Fintype K := Fintype.ofFinite K
  have hσσ : ∀ x, σ.toRingHom (σ.toRingHom x) = x := fun x => by
    change σ (σ x) = x
    rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨d₀, hd₀⟩ := exists_twistedE6_sigma_ne hf hK hσ
  have hd₀' : σ.toRingHom d₀ ≠ d₀ := hd₀
  have hτ : d₀ + σ.toRingHom d₀ ≠ 0 := by
    intro hzero
    apply hd₀'
    have e : σ.toRingHom d₀ = -d₀ := by linear_combination hzero
    rw [e, CharTwo.neg_eq]
  have hστ : σ.toRingHom (d₀ + σ.toRingHom d₀) = d₀ + σ.toRingHom d₀ := by
    rw [map_add, hσσ, add_comm]
  have ht₀ : d₀ * (d₀ + σ.toRingHom d₀)⁻¹ + σ.toRingHom (d₀ * (d₀ + σ.toRingHom d₀)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hστ, ← add_mul, mul_inv_cancel₀ hτ]
  exact not_isPGroup_of_mem_closure_odd
    (fixedHeightSeries_le_closure_odd_of_classCheck σ.surjective hσσ ht₀ hchk ht
      ⟨_, pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom 1 (map_one _)⟩
      (twE6_highRoot_mem_heightSeries hh))
    (mk_ne_one_of_ne_one _ (twE6_highRoot_ne_one (K := K)))

theorem twE6_centralizer_not_isPGroup
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hx : orderOf x = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) := by
  have hx2 : x ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by decide)
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction hf hK hσ
    (twistedE6FrameReduction hf hK hσ) hx2 hx1
  refine not_isPGroup_centralizer_of_isConj (a := g * x * g⁻¹)
    (isConj_iff.mpr ⟨g⁻¹, by group⟩) ?_
  rcases hg with h | h | h
  · exact twE6_classT_not_isPGroup hf hK hσ h
  · exact twE6_classCheck_not_isPGroup hf hK hσ twistedE6ClassCheck_U (by norm_num)
      (by rw [h]; simp [twistedE6ClassU, twistedE6ClassURoots])
  · exact twE6_classCheck_not_isPGroup hf hK hσ twistedE6ClassCheck_V (by norm_num)
      (by rw [h]; simp [twistedE6ClassV, twistedE6ClassVRoots, mul_assoc])

end CFSG.ComponentClassification.HarrisLit.L33.SR.E2

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem involutionCentralizerNotTwoGroup_twistedE6
    : InvolutionCentralizerNotTwoGroup .twistedE6 := by
  intro Y _ _ f hY _ c hc
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf hm
  have hK2 : Nat.card K = (2 ^ f) ^ 2 := hK
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK2, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  exact SR.E2.not_isPGroup_of_mulEquiv e c (SR.E2.twE6_centralizer_not_isPGroup hf hK2 hσ
    (by rw [MulEquiv.orderOf_eq]; exact hc))

end CFSG.ComponentClassification.HarrisLit.L33.E2
