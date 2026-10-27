module

public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.Q3CSBase

public section

namespace CFSG.ClassicalInvolution.Q3.Q3C

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Classical

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

omit [Finite G] in
theorem oddQuotMk_centralizes_of_mem_pair (he : IsEdge3 Ω K₁ K₂ z₁ z₂) {a : G}
    (ha : a ∈ Subgroup.closure ({z₁, z₂} : Set G)) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) {f : G}
    (hf : f ∈ Subgroup.closure ({z₁, z₂} : Set G)) (hfC : f ∈ Subgroup.centralizer ({a} : Set G))
    (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨f, hfC⟩ * y = y * oddQuotMk a ⟨f, hfC⟩ := by
  have hcen : ∀ {K : Subgroup G},
      K ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) →
        K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hmem : ∀ {z : G}, z ∈ Subgroup.closure ({z₁, z₂} : Set G) →
      z ∈ Subgroup.centralizer ({a} : Set G) := fun hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (elem_comm he.isElemAbelian_pair hz ha)
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : Subgroup.closure ({z₁, z₂} : Set G) ≤
      Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    have hzA : z ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure hz
    refine ⟨⟨z, hmem hzA⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hz with rfl | hz
    · exact (oddQuotMk_centralizes_of_isCentralInvolution he.mem₁ (hcen he.le_centralizer_pair)
        he.cls₁.isCentralInvolution _ hL y hy).symm
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (oddQuotMk_centralizes_of_isCentralInvolution he.mem₂
        (hcen he.le_centralizer_pair') he.cls₂.isCentralInvolution _ hL y hy).symm
  obtain ⟨q, hq, hqf⟩ := hsub hf
  have hqe : q = ⟨f, hfC⟩ := Subtype.ext hqf
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm

theorem exists_mem_inf_ne_one {A B F₀ : Subgroup G} (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hB : B ≤ A) (hB4 : Nat.card B = 4) (hF : F₀ ≤ A) (hF4 : Nat.card F₀ = 4) :
    ∃ f ∈ F₀, f ∈ B ∧ f ≠ 1 := by
  by_contra h
  push Not at h
  have hdisj : F₀ ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hx1 (h x hx.1 hx.2)
  have hcard := CFSG.SignalizerFunctorTheorem.card_sup_of_le_elemAbelian hA hF hB hdisj
  have hle : Nat.card ↥(F₀ ⊔ B) ≤ Nat.card A := Subgroup.card_le_of_le (sup_le hF hB)
  rw [hcard, hF4, hB4, hA8] at hle
  omega

theorem exists_mem_ne_one_centralizes_of_axis (he : IsEdge3 Ω K₁ K₂ z₁ z₂) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hBA : Subgroup.closure ({z₁, z₂} : Set G) ≤ A) {a : G}
    (ha : a ∈ Subgroup.closure ({z₁, z₂} : Set G)) {F₀ : Subgroup G} (hF₀ : F₀ ≤ A)
    (h4 : Nat.card F₀ = 4) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) :
    ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f := by
  obtain ⟨f, hfF, hfB, hf1⟩ := exists_mem_inf_ne_one hA hA8 hBA he.card_pair hF₀ h4
  have hfC : f ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (elem_comm hA (hBA hfB) (hBA ha))
  refine ⟨oddQuotMk a ⟨f, hfC⟩, oddQuotMk_mem_modOdd hfF hfC, ?_,
    fun y hy => oddQuotMk_centralizes_of_mem_pair he ha hL hfB hfC y hy⟩
  intro h
  have hsq : (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨f, hfC⟩ = 1 :=
    Subtype.ext (elem_sq hA (hF₀ hfF))
  exact hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))

theorem deltaCore_modOdd_eq_bot_of_classical (he : IsEdge3 Ω K₁ K₂ z₁ z₂) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hBA : Subgroup.closure ({z₁, z₂} : Set G) ≤ A) {a : G}
    (ha : a ∈ Subgroup.closure ({z₁, z₂} : Set G)) (hloc : ComponentBalanceAt Ω a)
    {F₀ : Subgroup G} (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A) :
    deltaCore (modOdd a F₀) = ⊥ := by
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have haA : a ∈ A := hBA ha
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact elem_comm hA (hF₀E hf) haA
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => elem_sq hA (hF₀E hf)
  refine deltaCore_eq_bot_of_locallyTwoBalanced (pPrimeCore_oddQuot_eq_bot a) ?_ ?_ ?_
  · rw [card_modOdd_of_exponent_two hFC hF2, h4]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  · intro L hL _ hfaith
    rcases hloc L hL with h | h | h
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_axis he hA hA8 hBA ha hF₀E h4 (Or.inl h)
      exact absurd hfc (hfaith f hf hf1)
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_axis he hA hA8 hBA ha hF₀E h4 (Or.inr h)
      exact absurd hfc (hfaith f hf hf1)
    · exact h

theorem twoBalancedWrt_of_classical_and_datum (hMF : LieSystemOddCentralizer3)
    (he : IsEdge3 Ω K₁ K₂ z₁ z₂) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hA8 : Nat.card A = 8) (hBA : Subgroup.closure ({z₁, z₂} : Set G) ≤ A)
    (hcl : ∀ a ∈ Subgroup.closure ({z₁, z₂} : Set G), a ≠ 1 → ComponentBalanceAt Ω a)
    (hs : ∀ b ∈ A, b ∉ Subgroup.closure ({z₁, z₂} : Set G) → SBaseDatum A b) :
    TwoBalancedWrt A := by
  intro F hF a ha ha1
  have hFC : F ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact elem_comm hA (hF.1 hf) ha
  by_cases haB : a ∈ Subgroup.closure ({z₁, z₂} : Set G)
  · exact deltaCore_inf_centralizer_le_involutionOddCore (IsPGroup.of_card hF.2) hFC
      (deltaCore_modOdd_eq_bot_of_classical he hA hA8 hBA haB (hcl a haB ha1) hF)
  · exact twoBalanced_at_of_datum hMF hA ha ha1 (hs a ha haB) hF.1 (by rw [hF.2]; norm_num)

end Classical

section Balance

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rankThreeBalance_of_axis (hMF : LieSystemOddCentralizer3) (hΩ : ConjInvariant Ω)
    (hO : LocalOddCentralizer3 Ω) (hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ t₁ t₂ t₃ : G}
    (d : AxisData3 Ω K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃)
    (hcl : ∀ a ∈ Subgroup.closure ({z₁, z₂} : Set G), a ≠ 1 → ComponentBalanceAt Ω a)
    (hs : ∀ b ∈ axisOf z₁ z₂ t₁ t₂ t₃, b ∉ Subgroup.closure ({z₁, z₂} : Set G) →
      SBaseDatum (axisOf z₁ z₂ t₁ t₂ t₃) b) :
    RankThreeBalance (axisOf z₁ z₂ t₁ t₂ t₃) where
  elem := d.isElemAbelian_axis
  card := d.card_axis
  weak := weakBalanced_of_classical_of_outside (d.weakBalanced_classical hΩ hO hnc)
    (fun a ha ha1 b hb hbB =>
      weakBalance_at_of_datum hMF d.isElemAbelian_axis hb (hs b hb hbB) a ha ha1)
  two := twoBalancedWrt_of_classical_and_datum hMF d.tri.edge d.isElemAbelian_axis d.card_axis
    (pair_le_axis z₁ z₂ t₁ t₂ t₃) hcl hs

end Balance

end CFSG.ClassicalInvolution.Q3.Q3C
