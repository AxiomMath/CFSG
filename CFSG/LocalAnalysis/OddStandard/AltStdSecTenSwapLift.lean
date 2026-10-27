module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapData
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

@[expose] noncomputable def liftS8 : Perm (Fin 8) →* Perm (Fin 10) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by norm_num : 8 ≤ 10))

theorem liftS8_injective : Function.Injective liftS8 := by
  exact Equiv.Perm.viaEmbeddingHom_injective _

theorem liftS8_apply_eight (ρ : Perm (Fin 8)) : liftS8 ρ 8 = 8 := by
  classical
  haveI : DecidablePred (Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10))) :=
    Classical.decPred _
  have h : (8 : Fin 10) ∉ Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10)) := by
    rintro ⟨x, hx⟩
    have hx' : (x : ℕ) = 8 := by simpa using congrArg Fin.val hx
    have := x.isLt
    omega
  rw [liftS8, Equiv.Perm.viaEmbeddingHom_apply,
    Equiv.Perm.viaEmbedding_apply_of_notMem ρ _ 8 h]

theorem liftS8_apply_nine (ρ : Perm (Fin 8)) : liftS8 ρ 9 = 9 := by
  classical
  haveI : DecidablePred (Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10))) :=
    Classical.decPred _
  have h : (9 : Fin 10) ∉ Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10)) := by
    rintro ⟨x, hx⟩
    have hx' : (x : ℕ) = 9 := by simpa using congrArg Fin.val hx
    have := x.isLt
    omega
  rw [liftS8, Equiv.Perm.viaEmbeddingHom_apply,
    Equiv.Perm.viaEmbedding_apply_of_notMem ρ _ 9 h]

theorem mem_stab2_iff_exists_liftS8 {σ : Perm (Fin 10)} :
    σ ∈ stab2 8 9 ↔ ∃ ρ : Perm (Fin 8), liftS8 ρ = σ := by
  classical
  constructor
  · intro hσ
    obtain ⟨h8, h9⟩ := mem_stab2.1 hσ
    have hlt_of_fix : ∀ τ : Perm (Fin 10), τ 8 = 8 → τ 9 = 9 →
        ∀ j : Fin 10, j.val < 8 → (τ j).val < 8 := by
      intro τ ht8 ht9 j hj
      have hj8 : j ≠ 8 := by rintro rfl; simp at hj
      have hj9 : j ≠ 9 := by rintro rfl; simp at hj
      have hne8 : τ j ≠ 8 := fun h => hj8 (τ.injective (h.trans ht8.symm))
      have hne9 : τ j ≠ 9 := fun h => hj9 (τ.injective (h.trans ht9.symm))
      have hn8 : (τ j).val ≠ 8 := fun h => hne8 (Fin.ext (by simpa using h))
      have hn9 : (τ j).val ≠ 9 := fun h => hne9 (Fin.ext (by simpa using h))
      have := (τ j).isLt
      omega
    have hlt := hlt_of_fix σ h8 h9
    have hinv8 : σ⁻¹ 8 = 8 := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact h8.symm
    have hinv9 : σ⁻¹ 9 = 9 := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact h9.symm
    have hltinv := hlt_of_fix σ⁻¹ hinv8 hinv9
    let g : Fin 8 → Fin 8 := fun x =>
      ⟨(σ (Fin.castLE (by norm_num : 8 ≤ 10) x)).val, hlt _ (by simpa using x.isLt)⟩
    have hg_inj : Function.Injective g := by
      intro x y hxy
      have h1 : (σ (Fin.castLE (by norm_num : 8 ≤ 10) x)).val =
          (σ (Fin.castLE (by norm_num : 8 ≤ 10) y)).val := by
        simpa [g] using congrArg Fin.val hxy
      have h2 : σ (Fin.castLE (by norm_num : 8 ≤ 10) x) =
          σ (Fin.castLE (by norm_num : 8 ≤ 10) y) := Fin.ext h1
      exact (Fin.castLEEmb (by norm_num : 8 ≤ 10)).injective (σ.injective h2)
    have hg : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).2 ⟨hg_inj, rfl⟩
    refine ⟨Equiv.ofBijective g hg, ?_⟩
    refine Equiv.ext fun i => ?_
    by_cases hi : i.val < 8
    · have hx : Fin.castLE (by norm_num : 8 ≤ 10) ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [← hx, liftS8, Equiv.Perm.viaEmbeddingHom_apply, ← Fin.coe_castLEEmb,
        Equiv.Perm.viaEmbedding_apply]
      exact Fin.ext rfl
    · have h8or9 : i.val = 8 ∨ i.val = 9 := by have := i.isLt; omega
      rcases h8or9 with h | h
      · have hi8 : i = 8 := Fin.ext (by simpa using h)
        rw [hi8, liftS8_apply_eight, h8]
      · have hi9 : i = 9 := Fin.ext (by simpa using h)
        rw [hi9, liftS8_apply_nine, h9]
  · rintro ⟨ρ, rfl⟩
    exact mem_stab2.2 ⟨liftS8_apply_eight ρ, liftS8_apply_nine ρ⟩

theorem liftS8_mem_stab2 (ρ : Perm (Fin 8)) : liftS8 ρ ∈ stab2 8 9 :=
  mem_stab2_iff_exists_liftS8.2 ⟨ρ, rfl⟩

theorem liftS8_mul_τ₀ (ρ : Perm (Fin 8)) : liftS8 ρ * τ₀ = τ₀ * liftS8 ρ := by
  ext i
  by_cases h8 : i = 8
  · subst h8
    simp [Equiv.Perm.mul_apply, τ₀, liftS8_apply_eight, liftS8_apply_nine]
  by_cases h9 : i = 9
  · subst h9
    simp [Equiv.Perm.mul_apply, τ₀, liftS8_apply_eight, liftS8_apply_nine]
  have h1 : liftS8 ρ i ≠ 8 :=
    fun h => h8 ((liftS8 ρ).injective (h.trans (liftS8_apply_eight ρ).symm))
  have h2 : liftS8 ρ i ≠ 9 :=
    fun h => h9 ((liftS8 ρ).injective (h.trans (liftS8_apply_nine ρ).symm))
  simp [Equiv.Perm.mul_apply, τ₀, Equiv.swap_apply_of_ne_of_ne, h8, h9, h1, h2]

theorem cycleType_liftS8 (ρ : Perm (Fin 8)) : (liftS8 ρ).cycleType = ρ.cycleType := by
  exact @Equiv.Perm.cycleType_extendDomain (Fin 8) _ _ (Fin 10) _ _
    (Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10))) (Classical.decPred _)
    (Equiv.ofInjective (Fin.castLEEmb (by norm_num : 8 ≤ 10)).1
      (Fin.castLEEmb (by norm_num : 8 ≤ 10)).2) (g := ρ)

theorem sign_liftS8 (ρ : Perm (Fin 8)) : sign (liftS8 ρ) = sign ρ := by
  exact @Equiv.Perm.sign_extendDomain (Fin 8) _ (Fin 10) _ _ _ ρ
    (Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10))) (Classical.decPred _)
    (Equiv.ofInjective (Fin.castLEEmb (by norm_num : 8 ≤ 10)).1
      (Fin.castLEEmb (by norm_num : 8 ≤ 10)).2)

theorem liftS8_swap (a b : Fin 8) :
    liftS8 (swap a b) = swap (Fin.castLE (by norm_num) a) (Fin.castLE (by norm_num) b) := by
  classical
  haveI : DecidablePred (Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10))) :=
    Classical.decPred _
  change liftS8 (swap a b) = swap ((Fin.castLEEmb (by norm_num : 8 ≤ 10)) a)
    ((Fin.castLEEmb (by norm_num : 8 ≤ 10)) b)
  refine Equiv.ext fun i => ?_
  by_cases hi : i ∈ Set.range (Fin.castLEEmb (by norm_num : 8 ≤ 10))
  · obtain ⟨x, rfl⟩ := hi
    rw [liftS8, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply]
    by_cases hxa : x = a
    · subst hxa; simp
    by_cases hxb : x = b
    · subst hxb; simp
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb,
        Equiv.swap_apply_of_ne_of_ne
          (fun h => hxa ((Fin.castLEEmb (by norm_num : 8 ≤ 10)).injective h))
          (fun h => hxb ((Fin.castLEEmb (by norm_num : 8 ≤ 10)).injective h))]
  · have hge : 8 ≤ i.val := by
      by_contra hlt
      simp only [not_le] at hlt
      exact hi ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    rcases (show i.val = 8 ∨ i.val = 9 by have := i.isLt; omega) with h | h
    · have hi8 : i = 8 := Fin.ext (by simpa using h)
      rw [hi8, liftS8_apply_eight]
      exact (Equiv.swap_apply_of_ne_of_ne
        (fun hh => by have ha := a.isLt; have hv := congrArg Fin.val hh; simp at hv; omega)
        (fun hh => by have hb := b.isLt; have hv := congrArg Fin.val hh; simp at hv; omega)).symm
    · have hi9 : i = 9 := Fin.ext (by simpa using h)
      rw [hi9, liftS8_apply_nine]
      exact (Equiv.swap_apply_of_ne_of_ne
        (fun hh => by have ha := a.isLt; have hv := congrArg Fin.val hh; simp at hv; omega)
        (fun hh => by have hb := b.isLt; have hv := congrArg Fin.val hh; simp at hv; omega)).symm

theorem eq_one_or_eq_sign {n : ℕ} (f : Perm (Fin n) →* ℤˣ) : f = 1 ∨ f = sign := by
  by_cases hn : n ≤ 1
  · left
    haveI : Subsingleton (Perm (Fin n)) := by
      rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_perm, Fintype.card_fin]
      interval_cases n <;> simp
    refine MonoidHom.ext fun σ => ?_
    rw [Subsingleton.elim σ 1]
    simp
  · have hn2 : 2 ≤ n := by omega
    have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
    have hswap : ∀ x y : Fin n, x ≠ y →
        f (swap x y) = f (swap ⟨0, by omega⟩ ⟨1, by omega⟩) := by
      intro x y hxy
      exact isConj_iff_eq.mp (f.map_isConj (isConj_swap hxy hab))
    rcases Int.units_eq_one_or (f (swap ⟨0, by omega⟩ ⟨1, by omega⟩)) with hc | hc
    · left
      refine MonoidHom.ext fun σ => ?_
      refine σ.swap_induction_on (by simp) ?_
      intro τ x y hxy ih
      rw [map_mul, hswap x y hxy, hc]
      simp [ih]
    · right
      refine MonoidHom.ext fun σ => ?_
      refine σ.swap_induction_on (by simp) ?_
      intro τ x y hxy ih
      rw [map_mul f, map_mul sign, hswap x y hxy, hc, sign_swap hxy]
      simp [ih]

@[expose] def r₁ : Perm (Fin 10) := swap 0 1

@[expose] def r₂ : Perm (Fin 10) := swap 0 1 * swap 2 3

@[expose] def r₃ : Perm (Fin 10) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def ρ₄' : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

theorem liftS8_ρ₄' : liftS8 ρ₄' = ρ₄ := by
  simp only [ρ₄', ρ₄, map_mul, liftS8_swap]
  decide

@[expose] def r₁' : Perm (Fin 8) := swap 0 1

@[expose] def r₂' : Perm (Fin 8) := swap 0 1 * swap 2 3

@[expose] def r₃' : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5

theorem liftS8_r₁' : liftS8 r₁' = r₁ := by
  simp only [r₁', r₁, liftS8_swap]
  decide

theorem liftS8_r₂' : liftS8 r₂' = r₂ := by
  simp only [r₂', r₂, map_mul, liftS8_swap]
  decide

theorem liftS8_r₃' : liftS8 r₃' = r₃ := by
  simp only [r₃', r₃, map_mul, liftS8_swap]
  decide

theorem exists_sq_r₁_mul_τ₀ : ∃ γ : Perm (Fin 10), γ * γ = r₁ * τ₀ := by
  exact ⟨swap 0 8 * swap 8 1 * swap 1 9, by decide⟩

theorem exists_sq_r₂ : ∃ γ : Perm (Fin 10), γ * γ = r₂ := by
  exact ⟨swap 0 2 * swap 2 1 * swap 1 3, by decide⟩

theorem exists_sq_ρ₄ : ∃ γ : Perm (Fin 10), γ * γ = ρ₄ := by
  exact ⟨(swap 0 2 * swap 2 1 * swap 1 3) * (swap 4 6 * swap 6 5 * swap 5 7), by decide⟩

theorem isConj_of_card_cycleType_eq {σ τ : Perm (Fin 10)} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (h : Multiset.card σ.cycleType = Multiset.card τ.cycleType) : IsConj σ τ := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq, cycleType_eq_replicate_two hσ,
    cycleType_eq_replicate_two hτ, h]

theorem isSwap_of_card_cycleType_eq_one {σ : Perm (Fin 10)} (hσ : σ * σ = 1)
    (h : Multiset.card σ.cycleType = 1) : σ.IsSwap := by
  rw [← Equiv.Perm.card_support_eq_two, card_support_eq_two_mul_card_cycleType hσ, h]

theorem card_cycleType_le_five {σ : Perm (Fin 10)} (hσ : σ * σ = 1) :
    Multiset.card σ.cycleType ≤ 5 := by
  have h := card_support_eq_two_mul_card_cycleType hσ
  have hle : σ.support.card ≤ 10 := by simpa using Finset.card_le_univ σ.support
  omega

theorem card_cycleType_of_isSwap {σ : Perm (Fin 10)} (h : σ.IsSwap) :
    Multiset.card σ.cycleType = 1 := by
  rw [Equiv.Perm.isSwap_iff_cycleType.1 h]
  simp

private theorem card_cycleType_eq_of_support_card {σ : Perm (Fin 10)} (hσ : σ * σ = 1) {k : ℕ}
    (hs : σ.support.card = 2 * k) : Multiset.card σ.cycleType = k := by
  have h := card_support_eq_two_mul_card_cycleType hσ
  omega

private theorem tau0_mul_self : τ₀ * τ₀ = 1 := by decide

private theorem r_two_mul_self : r₂ * r₂ = 1 := by decide

private theorem tau0_mul_r_two_mul_self : (τ₀ * r₂) * (τ₀ * r₂) = 1 := by decide

private theorem rho_four_mul_self : ρ₄ * ρ₄ = 1 := by decide

private theorem tau0_mul_rho_four_mul_self : (τ₀ * ρ₄) * (τ₀ * ρ₄) = 1 := by decide

private theorem card_cycleType_tau0 : Multiset.card τ₀.cycleType = 1 :=
  card_cycleType_eq_of_support_card tau0_mul_self (by decide)

private theorem card_cycleType_r_two : Multiset.card r₂.cycleType = 2 :=
  card_cycleType_eq_of_support_card r_two_mul_self (by decide)

private theorem card_cycleType_tau0_mul_r_two : Multiset.card (τ₀ * r₂).cycleType = 3 :=
  card_cycleType_eq_of_support_card tau0_mul_r_two_mul_self (by decide)

private theorem card_cycleType_rho_four : Multiset.card ρ₄.cycleType = 4 :=
  card_cycleType_eq_of_support_card rho_four_mul_self (by decide)

private theorem card_cycleType_tau0_mul_rho_four : Multiset.card (τ₀ * ρ₄).cycleType = 5 :=
  card_cycleType_eq_of_support_card tau0_mul_rho_four_mul_self (by decide)

theorem isConj_rep_of_card_cycleType {σ : Perm (Fin 10)} (hσ : σ * σ = 1) :
    (Multiset.card σ.cycleType = 1 → IsConj σ τ₀) ∧
    (Multiset.card σ.cycleType = 2 → IsConj σ r₂) ∧
    (Multiset.card σ.cycleType = 3 → IsConj σ (τ₀ * r₂)) ∧
    (Multiset.card σ.cycleType = 4 → IsConj σ ρ₄) ∧
    (Multiset.card σ.cycleType = 5 → IsConj σ (τ₀ * ρ₄)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact isConj_of_card_cycleType_eq hσ tau0_mul_self (h.trans card_cycleType_tau0.symm)
  · intro h
    exact isConj_of_card_cycleType_eq hσ r_two_mul_self (h.trans card_cycleType_r_two.symm)
  · intro h
    exact isConj_of_card_cycleType_eq hσ tau0_mul_r_two_mul_self
      (h.trans card_cycleType_tau0_mul_r_two.symm)
  · intro h
    exact isConj_of_card_cycleType_eq hσ rho_four_mul_self (h.trans card_cycleType_rho_four.symm)
  · intro h
    exact isConj_of_card_cycleType_eq hσ tau0_mul_rho_four_mul_self
      (h.trans card_cycleType_tau0_mul_rho_four.symm)

end CFSG.OddStandard.AltStdSec.SwapPattern
