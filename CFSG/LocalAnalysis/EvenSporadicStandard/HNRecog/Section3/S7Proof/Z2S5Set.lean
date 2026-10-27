module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fischer.LocalZ2S5
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

local notation "Z2" => Multiplicative (ZMod 2)

private theorem s7z_z2_mul_self : ∀ ε : Z2, ε * ε = 1 := by decide

private theorem s7z_z2_cases : ∀ ε : Z2, ε = 1 ∨ ε = Multiplicative.ofAdd 1 := by decide

private theorem s7z_z2_mul_of_ne : ∀ a b : Z2, a ≠ b → a * b = Multiplicative.ofAdd 1 := by decide

private theorem s7z_z2_conj_self : ∀ e y : Z2, e * y * e⁻¹ = y := by decide

private theorem s7z_conj_first_of (x : Z 2 × Sym 5) (e : Z2) (g : Sym 5) :
    (((e, g) : Z 2 × Sym 5) * x * ((e, g) : Z 2 × Sym 5)⁻¹).1 = x.1 := by
  show e * x.1 * e⁻¹ = x.1
  exact s7z_z2_conj_self e x.1

private theorem s7z_conj_first (x : Z 2 × Sym 5) (g : Sym 5) :
    (((1 : Z2), g) * x * ((1 : Z2), g)⁻¹).1 = x.1 :=
  s7z_conj_first_of x 1 g

private theorem s7z_conj_snd (x : Z 2 × Sym 5) (g : Sym 5) :
    (((1 : Z2), g) * x * ((1 : Z2), g)⁻¹).2 = g * x.2 * g⁻¹ := by
  show g * x.2 * g⁻¹ = g * x.2 * g⁻¹
  rfl

private theorem s7z_isConj_of_isSwap {τ τ' : Equiv.Perm (Fin 5)} (h : τ.IsSwap)
    (h' : τ'.IsSwap) : IsConj τ τ' := by
  obtain ⟨a, b, hab, rfl⟩ := h
  obtain ⟨c, d, hcd, rfl⟩ := h'
  exact Equiv.Perm.isConj_swap hab hcd

private theorem s7z_isConj_of_cycleType_two_two {π π' : Equiv.Perm (Fin 5)}
    (h : π.cycleType = ({2, 2} : Multiset ℕ)) (h' : π'.cycleType = ({2, 2} : Multiset ℕ)) :
    IsConj π π' :=
  Equiv.Perm.isConj_iff_cycleType_eq.mpr (h.trans h'.symm)

private theorem s7z_involution_perm5 (σ : Equiv.Perm (Fin 5)) (hσ : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    σ.IsSwap ∨ σ.cycleType = ({2, 2} : Multiset ℕ) := by
  have hcyc : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσ
  have hcard : σ.cycleType.card ≤ 2 := by
    have hsum : (Multiset.replicate σ.cycleType.card 2).sum = σ.support.card := by
      rw [← hcyc]; exact σ.sum_cycleType
    have hsum2 : 2 * σ.cycleType.card = σ.support.card := by
      rw [← hsum, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id]
      ring
    have hle : σ.support.card ≤ 5 := by
      simpa using Finset.card_le_univ σ.support
    omega
  have hcases : σ.cycleType.card = 0 ∨ σ.cycleType.card = 1 ∨ σ.cycleType.card = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at hcyc
    simp at hcyc
    exact absurd hcyc hσ1
  · left
    rw [Equiv.Perm.isSwap_iff_cycleType]
    rw [h1] at hcyc
    simpa using hcyc
  · right
    rw [h2] at hcyc
    simpa using hcyc

private theorem s7z_doubleTransposition_pair :
    ∃ π₁ π₂ : Equiv.Perm (Fin 5),
      π₁.cycleType = ({2, 2} : Multiset ℕ) ∧ π₂.cycleType = ({2, 2} : Multiset ℕ) ∧
        orderOf (π₁ * π₂) = 5 := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 4, ?_, ?_, ?_⟩
  · exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)
  · exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)
  · haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply orderOf_eq_prime
    · decide
    · decide

theorem s7_eq_swapSet {X : Set (Z 2 × Sym 5)} (hne : X.Nonempty)
    (hconj : ∀ g x : Z 2 × Sym 5, x ∈ X → g * x * g⁻¹ ∈ X)
    (hinv : ∀ x ∈ X, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ zetaZ2S5)
    (h3 : ∀ x ∈ insert zetaZ2S5 X, ∀ y ∈ insert zetaZ2S5 X, (x * y) ^ 3 = 1 ∨ (x * y) ^ 2 = 1) :
    ∃ ε : Z 2, X = swapSetZ2S5 ε := by
  have snd_swap : ∀ x ∈ X, x.2.IsSwap := by
    intro x hx
    obtain ⟨hx2, hxne1, hxneζ⟩ := hinv x hx
    have hx2' : x.2 ^ 2 = 1 := by
      have := congrArg Prod.snd hx2
      simpa using this
    have hx2ne : x.2 ≠ 1 := by
      intro h
      rcases s7z_z2_cases x.1 with h1 | h1
      · exact hxne1 (Prod.ext h1 h)
      · exact hxneζ (by simpa [zetaZ2S5] using Prod.ext h1 h)
    rcases s7z_involution_perm5 x.2 hx2' hx2ne with hswap | hdouble
    · exact hswap
    · exfalso
      obtain ⟨π₁, π₂, hπ1, hπ2, hord⟩ := s7z_doubleTransposition_pair
      obtain ⟨g1, hg1⟩ := isConj_iff.mp (s7z_isConj_of_cycleType_two_two hdouble hπ1)
      obtain ⟨g2, hg2⟩ := isConj_iff.mp (s7z_isConj_of_cycleType_two_two hdouble hπ2)
      set x1 : Z 2 × Sym 5 := ((1 : Z2), g1) * x * ((1 : Z2), g1)⁻¹ with x1def
      set x2 : Z 2 × Sym 5 := ((1 : Z2), g2) * x * ((1 : Z2), g2)⁻¹ with x2def
      have hx1X : x1 ∈ X := hconj _ _ hx
      have hx2X : x2 ∈ X := hconj _ _ hx
      have hx1eq : x1 = (x.1, π₁) := by
        rw [x1def]
        apply Prod.ext
        · exact s7z_conj_first x g1
        · rw [s7z_conj_snd]; exact hg1
      have hx2eq : x2 = (x.1, π₂) := by
        rw [x2def]
        apply Prod.ext
        · exact s7z_conj_first x g2
        · rw [s7z_conj_snd]; exact hg2
      have hprod : x1 * x2 = ((1 : Z2), π₁ * π₂) := by
        rw [hx1eq, hx2eq]
        apply Prod.ext
        · exact s7z_z2_mul_self x.1
        · rfl
      rcases h3 x1 (Set.mem_insert_of_mem _ hx1X) x2 (Set.mem_insert_of_mem _ hx2X) with
        h3p | h2p
      · have hpow : (π₁ * π₂) ^ 3 = 1 := by
          have := congrArg Prod.snd h3p
          simpa [hprod] using this
        have hdvd : orderOf (π₁ * π₂) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hpow
        rw [hord] at hdvd
        norm_num at hdvd
      · have hpow : (π₁ * π₂) ^ 2 = 1 := by
          have := congrArg Prod.snd h2p
          simpa [hprod] using this
        have hdvd : orderOf (π₁ * π₂) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
        rw [hord] at hdvd
        norm_num at hdvd
  obtain ⟨x0, hx0⟩ := hne
  refine ⟨x0.1, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    have hy_swap : y.2.IsSwap := snd_swap y hy
    refine ⟨?_, hy_swap⟩
    by_contra hne1
    have hx0_swap : x0.2.IsSwap := snd_swap x0 hx0
    obtain ⟨g1, hg1⟩ := isConj_iff.mp
      (s7z_isConj_of_isSwap hx0_swap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (0 : Fin 5) ≠ 1)))
    obtain ⟨g2, hg2⟩ := isConj_iff.mp
      (s7z_isConj_of_isSwap hy_swap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (1 : Fin 5) ≠ 2)))
    set x1 : Z 2 × Sym 5 := ((1 : Z2), g1) * x0 * ((1 : Z2), g1)⁻¹ with x1def
    set x2 : Z 2 × Sym 5 := ((1 : Z2), g2) * y * ((1 : Z2), g2)⁻¹ with x2def
    have hx1X : x1 ∈ X := hconj _ _ hx0
    have hx2X : x2 ∈ X := hconj _ _ hy
    have hx1eq : x1 = (x0.1, Equiv.swap 0 1) := by
      rw [x1def]
      apply Prod.ext
      · exact s7z_conj_first x0 g1
      · rw [s7z_conj_snd]; exact hg1
    have hx2eq : x2 = (y.1, Equiv.swap 1 2) := by
      rw [x2def]
      apply Prod.ext
      · exact s7z_conj_first y g2
      · rw [s7z_conj_snd]; exact hg2
    have hprod : x1 * x2 =
        (Multiplicative.ofAdd 1, Equiv.swap 0 1 * Equiv.swap 1 2) := by
      rw [hx1eq, hx2eq]
      apply Prod.ext
      · exact s7z_z2_mul_of_ne x0.1 y.1 (Ne.symm hne1)
      · rfl
    rcases h3 x1 (Set.mem_insert_of_mem _ hx1X) x2 (Set.mem_insert_of_mem _ hx2X) with
      h3p | h2p
    · have : (x1 * x2) ^ 3 ≠ 1 := by rw [hprod]; decide
      exact this h3p
    · have : (x1 * x2) ^ 2 ≠ 1 := by rw [hprod]; decide
      exact this h2p
  · intro y hy
    obtain ⟨hy1, hy2swap⟩ := hy
    obtain ⟨g, hg⟩ := isConj_iff.mp (s7z_isConj_of_isSwap (snd_swap x0 hx0) hy2swap)
    have hmem : ((1 : Z2), g) * x0 * ((1 : Z2), g)⁻¹ ∈ X := hconj _ _ hx0
    have heq1 : ((1 : Z2), g) * x0 * ((1 : Z2), g)⁻¹ = (x0.1, y.2) := by
      apply Prod.ext
      · exact s7z_conj_first x0 g
      · rw [s7z_conj_snd]; exact hg
    have heq : ((1 : Z2), g) * x0 * ((1 : Z2), g)⁻¹ = y := by
      rw [heq1]
      exact Prod.ext hy1.symm rfl
    rwa [heq] at hmem

theorem s7_closure_insert_swapSet (ε : Z 2) :
    Subgroup.closure (insert zetaZ2S5 (swapSetZ2S5 ε)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  rintro ⟨e, σ⟩
  let K : Subgroup (Z 2 × Sym 5) := Subgroup.closure (insert zetaZ2S5 (swapSetZ2S5 ε))
  have hζ : zetaZ2S5 ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hε1 : ((ε, (1 : Sym 5)) : Z 2 × Sym 5) ∈ K := by
    rcases s7z_z2_cases ε with h | h
    · rw [h]
      exact one_mem K
    · rw [h]
      simpa [zetaZ2S5] using hζ
  have hswap : ∀ τ : Sym 5, τ.IsSwap → ((1 : Z 2), τ) ∈ K := by
    intro τ hτ
    have hετ : (ε, τ) ∈ K :=
      Subgroup.subset_closure (Set.mem_insert_of_mem zetaZ2S5 ⟨rfl, hτ⟩)
    have := mul_mem hετ hε1
    simpa [s7z_z2_mul_self ε] using this
  have hall : ∀ σ : Sym 5, ((1 : Z 2), σ) ∈ K := by
    intro σ
    have hle : Subgroup.closure {τ : Sym 5 | τ.IsSwap} ≤
        K.comap (MonoidHom.inr (Z 2) (Sym 5)) := by
      rw [Subgroup.closure_le]
      intro τ hτ
      exact hswap τ hτ
    have hσ : σ ∈ Subgroup.closure {τ : Sym 5 | τ.IsSwap} := by
      rw [Equiv.Perm.closure_isSwap]
      exact Subgroup.mem_top σ
    exact hle hσ
  have he1 : ((e, (1 : Sym 5)) : Z 2 × Sym 5) ∈ K := by
    rcases s7z_z2_cases e with h | h
    · rw [h]
      exact one_mem K
    · rw [h]
      simpa [zetaZ2S5] using hζ
  have h1σ : ((1 : Z 2), σ) ∈ K := hall σ
  have := mul_mem he1 h1σ
  show (e, σ) ∈ K
  simpa using this

end CFSG.EvenSporadicStandard.HNRecog.Section3
