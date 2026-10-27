module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CHom
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL

variable {K : Type} [Field K]

theorem fixed_of_frame {A P D : GL (Fin 4) K} {μ : Kˣ}
    (hAP : A * P = GeneralLinearGroup.scalar (Fin 4) μ * (P * D))
    (s : SpecialLinearGroup (Fin 4) K)
    (hs : (s : Matrix (Fin 4) (Fin 4) K) * (D : Matrix (Fin 4) (Fin 4) K) =
      (D : Matrix (Fin 4) (Fin 4) K) * s) :
    conjAut 4 K A (conjAut 4 K P (proj 4 K s)) = conjAut 4 K P (proj 4 K s) := by
  have h1 : conjAut 4 K A * conjAut 4 K P = conjAut 4 K P * conjAut 4 K D := by
    rw [← map_mul, hAP, map_mul, conjAut_scalar, one_mul, map_mul]
  have hmat : (D : Matrix (Fin 4) (Fin 4) K) * (s : Matrix (Fin 4) (Fin 4) K) *
      ((D⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = s := by
    rw [← hs, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have h2 : conjAut 4 K D (proj 4 K s) = proj 4 K s := by
    rw [conjAut_proj]
    congr 1
    exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [coe_slConjugation, hmat]
  calc conjAut 4 K A (conjAut 4 K P (proj 4 K s)) =
        (conjAut 4 K A * conjAut 4 K P) (proj 4 K s) := rfl
    _ = (conjAut 4 K P * conjAut 4 K D) (proj 4 K s) := by rw [h1]
    _ = conjAut 4 K P (proj 4 K s) := by rw [MulAut.mul_apply, h2]

theorem barAut_symm_fixed {Y : Type*} [Group Y] (e : Y ⧸ center Y ≃* projectiveSL 4 K)
    (α : MulAut Y) {β : MulAut (projectiveSL 4 K)} (hα' : MulAut.congr e (barAut α) = β)
    {y : projectiveSL 4 K} (hy : β y = y) : barAut α (e.symm y) = e.symm y := by
  have h := congrArg (fun φ : MulAut (projectiveSL 4 K) => φ y) hα'
  simp only [MulAut.congr_apply, MulEquiv.trans_apply] at h
  rw [hy] at h
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  exact h

theorem inner_iff_congr {Y : Type*} [Group Y] (e : Y ⧸ center Y ≃* projectiveSL 4 K)
    (α : MulAut Y) :
    (∃ x, barAut α = MulAut.conj x) ↔
      MulAut.congr e (barAut α) ∈ OuterAutomorphisms.inner (projectiveSL 4 K) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    rw [hx]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    ext x
    have h := congrArg (fun φ : MulAut (projectiveSL 4 K) => φ (e x)) hy
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply,
      MulEquiv.symm_apply_apply] at h
    rw [MulAut.conj_apply]
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h.symm

theorem exists_cover_L4 {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ : Nat.card (center Y) = 2) [Finite K] (hK2 : ringChar K ≠ 2)
    (e : Y ⧸ center Y ≃* projectiveSL 4 K) :
    ∃ σ : SpecialLinearGroup (Fin 4) K →* Y, (∀ s, piZ (σ s) = e.symm (proj 4 K s)) ∧
      (scalars 4 K).map σ = center Y := by
  classical
  have := Fintype.ofFinite K
  set η : Y →* projectiveSL 4 K := e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : IsPGroup 2 (center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SpecialLinearGroup (Fin 4) K),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : SpecialLinearGroup (Fin 4) K →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker h2
    obtain ⟨σ, hσ, -⟩ := LieType.Steinberg.sl_central_two_extension_splitting 3 hK2 hπ hker h2
    exact ⟨σ, hσ⟩
  obtain ⟨σ, hσ, -, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit
    (proj_surjective 4 K) hηs (hηker ▸ le_rfl) (hηker ▸ hZ2)
  refine ⟨σ, fun s => ?_, ?_⟩
  · apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hσ s
  · rw [← hηker, hker, ker_proj]

theorem cover_negOne {Y : Type*} [Group Y] (hZ : Nat.card (center Y) = 2)
    (hm1 : ¬ IsSquare (-1 : K)) {σ : SpecialLinearGroup (Fin 4) K →* Y}
    (hσZ : (scalars 4 K).map σ = center Y) : σ negOne4 ∈ center Y ∧ σ negOne4 ≠ 1 := by
  have hneg : negOne4 ∈ scalars 4 K := by
    rw [mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    change (-1 : Matrix (Fin 4) (Fin 4) K) = scalar (Fin 4) ((-1 : Kˣ) : K)
    rw [Units.val_neg, Units.val_one, scalar_apply, ← smul_one_eq_diagonal, neg_smul, one_smul]
  refine ⟨hσZ ▸ mem_map_of_mem σ hneg, fun h1 => ?_⟩
  have hbot : center Y = ⊥ := by
    rw [← hσZ, eq_bot_iff]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨c, hc4, hc⟩ := mem_scalars.1 hs
    have hc2 : (c : K) ^ 2 = 1 := by
      have h4 : ((c : K) ^ 2) * ((c : K) ^ 2) = 1 := by
        rw [← pow_add, ← Units.val_pow_eq_pow_val, hc4, Units.val_one]
      rcases mul_self_eq_one_iff.mp h4 with h | h
      · exact h
      · exact absurd ⟨(c : K), by rw [← h, sq]⟩ hm1
    have hcc : (c : K) * (c : K) = 1 := by rw [← sq]; exact hc2
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · have : s = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
        have hs' : (s : Matrix (Fin 4) (Fin 4) K) = 1 := by rw [hc, h, map_one]
        rw [hs', Matrix.SpecialLinearGroup.coe_one]
      rw [this, map_one]
      exact one_mem _
    · have : s = negOne4 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
        have hs' : (s : Matrix (Fin 4) (Fin 4) K) = -1 := by
          rw [hc, h, scalar_apply, ← smul_one_eq_diagonal, neg_smul, one_smul]
        rw [hs']
        rfl
      rw [this, h1]
      exact one_mem _
  rw [hbot, Subgroup.card_bot] at hZ
  exact absurd hZ (by norm_num)

section Good

variable [Finite K] {p f : ℕ}

theorem charP_of_card (hp : p.Prime) (hK : Nat.card K = p ^ f) : CharP K p := by
  have := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

theorem exists_finset_four (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h3 : p ^ f ≠ 3) : ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h5 : 4 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    obtain ⟨k, hk⟩ := hodd
    rw [hK, hk] at h1
    omega
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ]; exact h5)
  exact ⟨s, hs⟩

theorem elementary_good (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (n : ℕ) :
    closure (LinearGroups.elementarySet n K) = ⊤ ∧
      ∀ s ∈ LinearGroups.elementarySet n K, Odd (orderOf s) := by
  have := charP_of_card hp hK
  exact ⟨LinearGroups.special_linear_elementary_generation,
    fun s hs => odd_orderOf_of_mem_elementarySet hp hp2 hs⟩

theorem hgood_SL2 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) K) ∨
      (p ^ f = 3 ∧ ∃ S : Set (SpecialLinearGroup (Fin 2) K), closure S = ⊤ ∧
        ∀ s ∈ S, Odd (orderOf s)) := by
  by_cases h3 : p ^ f = 3
  · exact Or.inr ⟨h3, _, elementary_good hp hp2 hK 2⟩
  · exact Or.inl (LinearGroups.special_linear_dimension_two_perfect
      (exists_finset_four hp hp2 hK h3))

theorem hgood_SL2SL2 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) ∨
      (p ^ f = 3 ∧ ∃ S : Set (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K),
        closure S = ⊤ ∧ ∀ s ∈ S, Odd (orderOf s)) := by
  by_cases h3 : p ^ f = 3
  · obtain ⟨hS, hSo⟩ := elementary_good hp hp2 hK 2
    refine Or.inr ⟨h3, _, closure_prod_eq_top hS hS, ?_⟩
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_right]
      exact hSo s hs
    · rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left]
      exact hSo s hs
  · have := LinearGroups.special_linear_dimension_two_perfect (exists_finset_four hp hp2 hK h3)
    exact Or.inl isPerfect_prod

end Good

theorem perfect_SL3 : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
  LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)

end CFSG.ComponentClassification.GSThmB.Cent516
