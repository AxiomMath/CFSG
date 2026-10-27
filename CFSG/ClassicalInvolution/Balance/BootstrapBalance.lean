module

public import CFSG.ClassicalInvolution.Balance.BootstrapTriple
public import CFSG.ClassicalInvolution.Balance.ToralBalanceFrame
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Member

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem oddQuotMk_centralizes_of_isCentralInvolution {a z : G} {K : Subgroup G} (hKΩ : K ∈ Ω)
    (hKC : K ≤ Subgroup.centralizer ({a} : Set G)) (hz : IsCentralInvolution K z)
    (hzC : z ∈ Subgroup.centralizer ({a} : Set G)) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨z, hzC⟩ * y = y * oddQuotMk a ⟨z, hzC⟩ := by
  have hzmem : oddQuotMk a ⟨z, hzC⟩ ∈ modOdd a K := oddQuotMk_mem_modOdd hz.mem hzC
  rcases hL with hL | ⟨-, hL⟩
  · exact hL K hKΩ hKC _ hzmem y hy
  · rcases hL K hKΩ hKC with h | h
    · rw [← h] at hy
      obtain ⟨k, hkK, rfl⟩ := hy
      have hkK' : (k : G) ∈ K := hkK
      have hzk : z * (k : G) = (k : G) * z := hz.central k hkK'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext hzk)
    · exact h _ hzmem y hy

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

omit [Finite G] in
theorem oddQuotMk_centralizes_of_mem_group (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hΩ₁ : K₁ ∈ Ω)
    (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) {a : G} (ha : a ∈ T.group) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) {f : G} (hf : f ∈ T.group)
    (hfC : f ∈ Subgroup.centralizer ({a} : Set G)) (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨f, hfC⟩ * y = y * oddQuotMk a ⟨f, hfC⟩ := by
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (T.group : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hmem : ∀ {z : G}, z ∈ T.group → z ∈ Subgroup.centralizer ({a} : Set G) := fun hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (T.comm_of_mem hz ha)
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : T.group ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    have hzA : z ∈ T.group := Subgroup.subset_closure hz
    refine ⟨⟨z, hmem hzA⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact (oddQuotMk_centralizes_of_isCentralInvolution hΩ₁ (hcen T.le_centralizer₁)
        ⟨T.mem₁, T.ne_one₁, T.sq₁, fun k hk => (T.central₁ k hk).symm⟩ _ hL y hy).symm
    · exact (oddQuotMk_centralizes_of_isCentralInvolution hΩ₂ (hcen T.le_centralizer₂)
        ⟨T.mem₂, T.ne_one₂, T.sq₂, fun k hk => (T.central₂ k hk).symm⟩ _ hL y hy).symm
    · exact (oddQuotMk_centralizes_of_isCentralInvolution hΩ₃ (hcen T.le_centralizer₃)
        ⟨T.mem₃, T.ne_one₃, T.sq₃, fun k hk => (T.central₃ k hk).symm⟩ _ hL y hy).symm
  obtain ⟨q, hq, hqf⟩ := hsub hf
  have hqe : q = ⟨f, hfC⟩ := Subtype.ext hqf
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm

theorem exists_mem_ne_one_centralizes_of_exactTriple (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) {a : G} (ha : a ∈ T.group) {F₀ : Subgroup G}
    (hF₀ : F₀ ≤ T.group) (h4 : Nat.card F₀ = 4) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) :
    ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f := by
  obtain ⟨f, hfF, hf1⟩ := exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num) (by omega)
  have hfA : f ∈ T.group := hF₀ hfF
  have hfC : f ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (T.comm_of_mem hfA ha)
  refine ⟨oddQuotMk a ⟨f, hfC⟩, oddQuotMk_mem_modOdd hfF hfC, ?_, fun y hy =>
    oddQuotMk_centralizes_of_mem_group T hΩ₁ hΩ₂ hΩ₃ ha hL hfA hfC y hy⟩
  intro h
  have hsq : (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨f, hfC⟩ = 1 :=
    Subtype.ext (by rw [← pow_two]; exact T.isElemAbelian.2 f hfA)
  exact hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))

theorem twoBalancedWrt_of_exactTriple_of_layers (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hloc : ∀ a ∈ T.group, a ≠ 1 → ComponentLayersAt Ω T.group a) : TwoBalancedWrt T.group := by
  have hA := T.isElemAbelian
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hA.1 ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact T.comm_of_mem (hF₀E hf) ha
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => by
    rw [← pow_two]
    exact hA.2 f (hF₀E hf)
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_oddCentralizerFree (pPrimeCore_oddQuot_eq_bot a)
    (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar ?_
  intro L hL hFn hfaith
  rcases hloc a ha ha1 L hL with h | h | hfree
  · obtain ⟨f, hf, hf1, hfc⟩ :=
      exists_mem_ne_one_centralizes_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha hF₀E h4 (Or.inl h)
    exact absurd hfc (hfaith f hf hf1)
  · obtain ⟨f, hf, hf1, hfc⟩ :=
      exists_mem_ne_one_centralizes_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha hF₀E h4 (Or.inr h)
    exact absurd hfc (hfaith f hf hf1)
  · exact hfree F₀ hF₀E h4 hFn hfaith

end CFSG.ClassicalInvolution.Balance.Bootstrap
