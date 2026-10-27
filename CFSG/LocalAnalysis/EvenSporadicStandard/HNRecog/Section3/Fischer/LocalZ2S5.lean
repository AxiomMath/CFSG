module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

local notation "Z2" => Multiplicative (ZMod 2)
local notation "G5" => Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)

@[expose] def zetaZ2S5 : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5) :=
  (Multiplicative.ofAdd 1, 1)

@[expose] def swapSetZ2S5 (ε : Multiplicative (ZMod 2)) :
    Set (Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :=
  {x | x.1 = ε ∧ x.2.IsSwap}

private theorem z2_mul_self : ∀ ε : Z2, ε * ε = 1 := by decide

private theorem z2_cases : ∀ ε : Z2, ε = 1 ∨ ε = Multiplicative.ofAdd 1 := by decide

private theorem z2_mul_of_ne : ∀ a b : Z2, a ≠ b → a * b = Multiplicative.ofAdd 1 := by decide

private theorem isConj_of_isSwap {τ τ' : Equiv.Perm (Fin 5)} (h : τ.IsSwap) (h' : τ'.IsSwap) :
    IsConj τ τ' := by
  obtain ⟨a, b, hab, rfl⟩ := h
  obtain ⟨c, d, hcd, rfl⟩ := h'
  exact Equiv.Perm.isConj_swap hab hcd

private theorem isConj_of_cycleType_two_two {π π' : Equiv.Perm (Fin 5)}
    (h : π.cycleType = ({2, 2} : Multiset ℕ)) (h' : π'.cycleType = ({2, 2} : Multiset ℕ)) :
    IsConj π π' :=
  Equiv.Perm.isConj_iff_cycleType_eq.mpr (h.trans h'.symm)

private theorem involution_perm5 (σ : Equiv.Perm (Fin 5)) (hσ : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
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

private theorem doubleTransposition_pair :
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

theorem eq_swapSet_of_threeTranspositions
    (X : Set (Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)))
    (hconj : ∀ g x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5), x ∈ X → g * x * g⁻¹ ∈ X)
    (hinv : ∀ x ∈ X, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ zetaZ2S5)
    (h3 : ∀ x ∈ insert zetaZ2S5 X, ∀ y ∈ insert zetaZ2S5 X, (x * y) ^ 3 = 1 ∨ (x * y) ^ 2 = 1)
    (hgen : Subgroup.closure (insert zetaZ2S5 X) = ⊤) :
    ∃ ε : Multiplicative (ZMod 2), X = swapSetZ2S5 ε := by
  have snd_swap : ∀ x ∈ X, x.2.IsSwap := by
    intro x hx
    obtain ⟨hx2, hxne1, hxneζ⟩ := hinv x hx
    have hx2' : x.2 ^ 2 = 1 := by
      have := congrArg Prod.snd hx2
      simpa using this
    have hx2ne : x.2 ≠ 1 := by
      intro h
      rcases z2_cases x.1 with h1 | h1
      · exact hxne1 (Prod.ext h1 h)
      · exact hxneζ (by simpa [zetaZ2S5] using Prod.ext h1 h)
    rcases involution_perm5 x.2 hx2' hx2ne with hswap | hdouble
    · exact hswap
    · exfalso
      obtain ⟨π₁, π₂, hπ1, hπ2, hord⟩ := doubleTransposition_pair
      obtain ⟨g1, hg1⟩ := isConj_iff.mp (isConj_of_cycleType_two_two hdouble hπ1)
      obtain ⟨g2, hg2⟩ := isConj_iff.mp (isConj_of_cycleType_two_two hdouble hπ2)
      set x1 : G5 := ((1 : Z2), g1) * x * ((1 : Z2), g1)⁻¹ with x1def
      set x2 : G5 := ((1 : Z2), g2) * x * ((1 : Z2), g2)⁻¹ with x2def
      have hx1X : x1 ∈ X := hconj _ _ hx
      have hx2X : x2 ∈ X := hconj _ _ hx
      have hx1eq : x1 = (x.1, π₁) := by
        apply Prod.ext <;> simp [x1def, hg1]
      have hx2eq : x2 = (x.1, π₂) := by
        apply Prod.ext <;> simp [x2def, hg2]
      have hprod : x1 * x2 = ((1 : Z2), π₁ * π₂) := by
        rw [hx1eq, hx2eq]
        apply Prod.ext <;> simp [z2_mul_self x.1]
      rcases h3 x1 (Set.mem_insert_of_mem _ hx1X) x2 (Set.mem_insert_of_mem _ hx2X) with h3p | h2p
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
  by_cases hne : X.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    refine ⟨x0.1, ?_⟩
    apply Set.Subset.antisymm
    · intro y hy
      have hy_swap : y.2.IsSwap := snd_swap y hy
      refine ⟨?_, hy_swap⟩
      by_contra hne1
      have hx0_swap : x0.2.IsSwap := snd_swap x0 hx0
      obtain ⟨g1, hg1⟩ := isConj_iff.mp
        (isConj_of_isSwap hx0_swap (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (0 : Fin 5) ≠ 1)))
      obtain ⟨g2, hg2⟩ := isConj_iff.mp
        (isConj_of_isSwap hy_swap (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (1 : Fin 5) ≠ 2)))
      set x1 : G5 := ((1 : Z2), g1) * x0 * ((1 : Z2), g1)⁻¹ with x1def
      set x2 : G5 := ((1 : Z2), g2) * y * ((1 : Z2), g2)⁻¹ with x2def
      have hx1X : x1 ∈ X := hconj _ _ hx0
      have hx2X : x2 ∈ X := hconj _ _ hy
      have hx1eq : x1 = (x0.1, Equiv.swap 0 1) := by
        apply Prod.ext <;> simp [x1def, hg1]
      have hx2eq : x2 = (y.1, Equiv.swap 1 2) := by
        apply Prod.ext <;> simp [x2def, hg2]
      have hprod : x1 * x2 =
          (Multiplicative.ofAdd 1, Equiv.swap 0 1 * Equiv.swap 1 2) := by
        rw [hx1eq, hx2eq]
        apply Prod.ext
        · exact z2_mul_of_ne x0.1 y.1 (Ne.symm hne1)
        · rfl
      rcases h3 x1 (Set.mem_insert_of_mem _ hx1X) x2 (Set.mem_insert_of_mem _ hx2X) with h3p | h2p
      · have : (x1 * x2) ^ 3 ≠ 1 := by rw [hprod]; decide
        exact this h3p
      · have : (x1 * x2) ^ 2 ≠ 1 := by rw [hprod]; decide
        exact this h2p
    · intro y hy
      obtain ⟨hy1, hy2swap⟩ := hy
      obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isSwap (snd_swap x0 hx0) hy2swap)
      have hmem : ((1 : Z2), g) * x0 * ((1 : Z2), g)⁻¹ ∈ X := hconj _ _ hx0
      have heq1 : ((1 : Z2), g) * x0 * ((1 : Z2), g)⁻¹ = (x0.1, y.2) := by
        apply Prod.ext <;> simp [hg]
      have heq : ((1 : Z2), g) * x0 * ((1 : Z2), g)⁻¹ = y := by
        rw [heq1]
        exact Prod.ext hy1.symm rfl
      rwa [heq] at hmem
  · exfalso
    have hXempty : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hXempty] at hgen
    have htop : Subgroup.closure ({zetaZ2S5} : Set G5) = ⊤ := by simpa using hgen
    have hmem : ((1 : Z2), Equiv.swap 0 1) ∈ Subgroup.closure ({zetaZ2S5} : Set G5) := by
      rw [htop]
      simp
    rw [Subgroup.mem_closure_singleton] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hsnd : (zetaZ2S5 ^ n).2 = Equiv.swap (0 : Fin 5) 1 := by
      have := congrArg Prod.snd hn
      simpa using this
    have hone : (1 : Equiv.Perm (Fin 5)) = Equiv.swap (0 : Fin 5) 1 := by
      simpa [zetaZ2S5] using hsnd
    exact absurd hone.symm (by decide)

theorem swapSetZ2S5_oneClass (ε : Multiplicative (ZMod 2)) :
    ∀ x ∈ swapSetZ2S5 ε, ∀ y ∈ swapSetZ2S5 ε,
      ∃ g : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5), g * x * g⁻¹ = y := by
  intro x hx y hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isSwap hx2 hy2)
  refine ⟨((1 : Z2), g), ?_⟩
  apply Prod.ext
  · show (1 : Z2) * x.1 * (1 : Z2)⁻¹ = y.1
    rw [hx1, hy1]
    simp
  · simpa using hg

theorem swapSetZ2S5_commuting_pair (ε : Multiplicative (ZMod 2)) :
    ∃ x ∈ swapSetZ2S5 ε, ∃ y ∈ swapSetZ2S5 ε, x ≠ y ∧ x * y = y * x := by
  refine ⟨(ε, Equiv.swap 0 1), ⟨rfl, ?_⟩, (ε, Equiv.swap 2 3), ⟨rfl, ?_⟩, ?_, ?_⟩
  · exact Equiv.Perm.swap_isSwap_iff.mpr (by decide : (0 : Fin 5) ≠ 1)
  · exact Equiv.Perm.swap_isSwap_iff.mpr (by decide : (2 : Fin 5) ≠ 3)
  · intro h
    exact absurd (congrArg Prod.snd h)
      (by decide : Equiv.swap (0 : Fin 5) 1 ≠ Equiv.swap 2 3)
  · apply Prod.ext
    · rfl
    · exact (Equiv.Perm.Disjoint.commute (Equiv.Perm.disjoint_swap_swap (by decide))).eq

private noncomputable def z2OfIntUnits (ε : Z2) : ℤˣ →* Z2 where
  toFun u := if u = 1 then 1 else ε
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or v with hv | hv
    · rw [hu, hv]; simp
    · rw [hu, hv]; simp
    · rw [hu, hv]; simp
    · rw [hu, hv]
      have hneg : (-1 : ℤˣ) ≠ 1 := by
        intro h
        have := congrArg (fun u : ℤˣ => (u : ℤ)) h
        norm_num at this
      have hmul : (-1 : ℤˣ) * (-1) = 1 := by
        ext
        simp
      rw [hmul]
      simp [hneg, z2_mul_self ε]

theorem closure_swapSetZ2S5_equiv (ε : Multiplicative (ZMod 2)) :
    Nonempty (↥(Subgroup.closure (swapSetZ2S5 ε)) ≃* Equiv.Perm (Fin 5)) := by
  let θ : Equiv.Perm (Fin 5) →* G5 :=
    ((z2OfIntUnits ε).comp Equiv.Perm.sign).prod (MonoidHom.id _)
  have hθ_apply : ∀ σ, θ σ = (z2OfIntUnits ε (Equiv.Perm.sign σ), σ) := fun σ => rfl
  have hθ_inj : Function.Injective θ := by
    intro σ τ h
    have := congrArg Prod.snd h
    simpa [hθ_apply] using this
  have h_image : θ '' {σ : Equiv.Perm (Fin 5) | σ.IsSwap} = swapSetZ2S5 ε := by
    ext y
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨?_, hσ⟩
      rw [hθ_apply]
      show z2OfIntUnits ε (Equiv.Perm.sign σ) = ε
      rw [Equiv.Perm.IsSwap.sign_eq hσ]
      simp [z2OfIntUnits]
    · rintro ⟨hy1, hy2⟩
      refine ⟨y.2, hy2, ?_⟩
      rw [hθ_apply]
      apply Prod.ext
      · show z2OfIntUnits ε (Equiv.Perm.sign y.2) = y.1
        rw [hy1, Equiv.Perm.IsSwap.sign_eq hy2]
        simp [z2OfIntUnits]
      · rfl
  have hrange : θ.range = Subgroup.closure (swapSetZ2S5 ε) := by
    rw [MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap,
      MonoidHom.map_closure θ {σ : Equiv.Perm (Fin 5) | σ.IsSwap}, h_image]
  exact ⟨((MonoidHom.ofInjective hθ_inj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
