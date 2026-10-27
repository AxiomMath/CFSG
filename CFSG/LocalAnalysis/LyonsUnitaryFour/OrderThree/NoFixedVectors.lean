module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.InductionGram
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NoninvertingSection

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G]

section Auxiliary

theorem exists_pos_le_of_weighted_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ) (w : ι → ℝ)
    (d : ι → ℕ) (hw : ∀ i ∈ s, 0 ≤ w i) (hd : ∀ i ∈ s, 0 < d i)
    (hsum : ∑ i ∈ s, (a i : ℝ) * w i / d i = 1) (hwsum : ∑ i ∈ s, w i = 63) :
    ∃ i ∈ s, 0 < a i ∧ (d i : ℤ) ≤ 63 * a i := by
  by_contra hall
  push Not at hall
  have hle : ∀ i ∈ s, (a i : ℝ) * w i / d i ≤ w i / 63 := by
    intro i hi
    have hdi : (0 : ℝ) < d i := by exact_mod_cast hd i hi
    rw [div_le_div_iff₀ hdi (by norm_num)]
    by_cases ha : 0 < a i
    · have h1 := hall i hi ha
      have h2 : (63 : ℝ) * a i < d i := by exact_mod_cast h1
      nlinarith [hw i hi]
    · push Not at ha
      have h2 : (a i : ℝ) ≤ 0 := by exact_mod_cast ha
      nlinarith [hw i hi]
  have hpos : ∃ i ∈ s, 0 < w i := by
    by_contra hnone
    push Not at hnone
    have : ∑ i ∈ s, w i ≤ 0 := Finset.sum_nonpos hnone
    linarith
  obtain ⟨j, hj, hwj⟩ := hpos
  have hlt : (a j : ℝ) * w j / d j < w j / 63 := by
    have hdj : (0 : ℝ) < d j := by exact_mod_cast hd j hj
    rw [div_lt_div_iff₀ hdj (by norm_num)]
    by_cases ha : 0 < a j
    · have h1 := hall j hj ha
      have h2 : (63 : ℝ) * a j < d j := by exact_mod_cast h1
      nlinarith
    · push Not at ha
      have h2 : (a j : ℝ) ≤ 0 := by exact_mod_cast ha
      nlinarith
  have hstrict := Finset.sum_lt_sum hle ⟨j, hj, hlt⟩
  rw [hsum, ← Finset.sum_div, hwsum] at hstrict
  norm_num at hstrict

theorem fixed_vector_eq_zero [Fintype G] (S : Subgroup G) {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : CFSG.Section1.scalarProduct S (fun x => ρ.character x) 1 = 0) (v : V)
    (hv : ∀ s ∈ S, ρ s v = v) : v = 0 := by
  have htr : LinearMap.trace ℂ V (subgroupAverage ρ S) = 0 := by
    have h1 := trace_mul_subgroupAverage ρ S 1
    rw [map_one, one_mul] at h1
    rw [h1, ← h, scalarProduct_eq_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hzero : subgroupAverage ρ S = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (subgroupAverage_idempotent ρ S) htr
  have hfix : subgroupAverage ρ S v = v := by
    unfold subgroupAverage
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun (s : S) _ => hv s s.property), Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]
  rw [← hfix, hzero]
  rfl

theorem neg_one_le_of_sq_le_two {t : ℤ} (h : t ^ 2 ≤ 2) : -1 ≤ t := by nlinarith

theorem neg_four_le_of_sq_le_seventeen {t : ℤ} (h : t ^ 2 ≤ 17) : -4 ≤ t := by nlinarith

theorem sq_le_of_blockInduction_norm [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (S : Subgroup G) {θ : S → ℂ} (hθ : θ ∈ CFSG.BlocksVChar S)
    {N : ℕ}
    (hN : CFSG.Section1.scalarProduct G (blockInduction basis B S θ)
      (blockInduction basis B S θ) = N) {ξ : basis.index} (hξ : ξ ∈ B) :
    ∃ k : ℤ, CFSG.Section1.scalarProduct S θ
      (fun x => (basis.representation ξ).character x) = k ∧ k ^ 2 ≤ N := by
  choose k hk using fun ξ => scalarProduct_restrict_integer S hθ (basis.representation ξ)
  refine ⟨k ξ, hk ξ, ?_⟩
  rw [scalarProduct_blockInduction] at hN
  simp_rw [hk] at hN
  have hsq : ((∑ ξ' ∈ B, (k ξ') ^ 2 : ℤ) : ℂ) = N := by
    rw [← hN]
    push_cast
    apply Finset.sum_congr rfl
    intro ξ' _
    rw [pow_two]
    congr 1
    simp
  have hsq' : ∑ ξ' ∈ B, (k ξ') ^ 2 = (N : ℤ) := by exact_mod_cast hsq
  rw [← hsq']
  exact Finset.single_le_sum (f := fun ξ' => (k ξ') ^ 2) (fun i _ => sq_nonneg _) hξ

end Auxiliary

section Coefficients

@[expose] def orbitCoeff (a₀ : ℕ) (b : Fin 5 → ℕ) (c : ℕ) :
    Option (Option (Fin 5) × Fin 3) → ℕ
  | none => a₀
  | some (some i, _) => b i
  | some (none, _) => c

theorem restriction_eq_orbitEnum_sum {S : Subgroup G} {n : G} (lam : Fin 5 → S → ℂ)
    (ψ : S → ℂ) (a₀ : ℕ) (b : Fin 5 → ℕ) (c : ℕ) (f : S → ℂ)
    (hf : ∀ x, f x = a₀ + ∑ i, (b i : ℂ) *
        ∑ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) (lam i) x +
      c * ∑ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ x) :
    f = fun x => ∑ t, (orbitCoeff a₀ b c t : ℂ) * orbitEnum S n lam ψ t x := by
  funext x
  rw [hf, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [orbitCoeff, orbitEnum, Pi.one_apply, mul_one]
  simp_rw [Finset.mul_sum]
  ring

variable {S : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
  {lam : Fin 5 → S → ℂ} {ψ : S → ℂ}
  (hlam : ∀ i, lam i ∈ CFSG.BlocksIrr S ∧ lam i 1 = 1 ∧ lam i ≠ 1)
  (hψ : ψ ∈ CFSG.BlocksIrr S) (hψ4 : ψ 1 = 4)
  (hinjL : ∀ (i i' : Fin 5) (a b : Fin 3), conjugateCharacter S (n ^ (a : ℕ)) (lam i) =
    conjugateCharacter S (n ^ (b : ℕ)) (lam i') → i = i' ∧ a = b)
  (hinjD : ∀ a b : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ =
    conjugateCharacter S (n ^ (b : ℕ)) ψ → a = b)
include hn hlam hψ hψ4 hinjL hinjD

theorem scalarProduct_orbitEnum_coeff_right [Fintype G]
    (coef : Option (Option (Fin 5) × Fin 3) → ℕ) (u : Option (Option (Fin 5) × Fin 3)) :
    CFSG.Section1.scalarProduct S (orbitEnum S n lam ψ u)
      (fun x => ∑ t, (coef t : ℂ) * orbitEnum S n lam ψ t x) = coef u := by
  rw [scalarProduct_finsetSum_right]
  simp_rw [scalarProduct_mul_right, scalarProduct_orbitEnum hn hlam hψ hψ4 hinjL hinjD]
  simp

theorem scalarProduct_orbitEnum_coeff_left [Fintype G]
    (coef : Option (Option (Fin 5) × Fin 3) → ℕ) (u : Option (Option (Fin 5) × Fin 3)) :
    CFSG.Section1.scalarProduct S (fun x => ∑ t, (coef t : ℂ) * orbitEnum S n lam ψ t x)
      (orbitEnum S n lam ψ u) = coef u := by
  rw [scalarProduct_finsetSum_left]
  simp_rw [scalarProduct_mul_left, scalarProduct_orbitEnum hn hlam hψ hψ4 hinjL hinjD]
  simp

end Coefficients

section Node

theorem lyons_order_three_principal_character_without_sylow_fixed_vectors [Fintype G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    ∃ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation label).character ≠ 1 ∧
      ∃ lam : ↥(S : Subgroup G) → ℂ, lam ∈ CFSG.BlocksIrr (S : Subgroup G) ∧ lam 1 = 1 ∧
        lam ≠ 1 ∧
      ∃ a : ℕ, 0 < a ∧
        CFSG.Section1.scalarProduct (S : Subgroup G) (lam - 1)
          (fun x => (basis.representation label).character x) = a ∧
        Module.finrank ℂ (basis.representation label).vector ≤ 63 * a ∧
        CFSG.Section1.scalarProduct (S : Subgroup G)
          (fun x => (basis.representation label).character x) 1 = 0 ∧
        ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
          (ρ : Representation ℂ G V), ρ.character = (basis.representation label).character →
          ∀ v : V, (∀ s ∈ (S : Subgroup G), ρ s v = v) → v = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sg := (S : Subgroup G) with hSg
  obtain ⟨n, hn, lam, ψ, hlam, hψ, hψ4, -, -, hinjL, hinjD, -, -, -, -, hn2, hn3, -, hres,
    -, hcentral⟩ := lyons_order_three_principal_induction_gram hnonab hT S U hSU hd basis ideal
      principal hprincipal
  obtain ⟨-, -, hsq, -, -, -, -, -, -, -, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hirr_vchar : ∀ θ ∈ CFSG.BlocksIrr Sg, θ ∈ CFSG.BlocksVChar Sg :=
    fun θ hθ => AddSubgroup.subset_closure hθ
  have hμ : lam 0 - 1 ∈ CFSG.BlocksVChar Sg :=
    sub_mem (hirr_vchar _ (hlam 0).1) (hirr_vchar _ (one_mem_blocksIrr Sg))
  have hlinZ : ∀ z : Sg, z ∈ Subgroup.center Sg → lam 0 z = 1 := by
    intro z hz
    obtain ⟨hlin, -⟩ := hshape.character_table
    have hmem : lam 0 ∈ {χ | χ ∈ CFSG.BlocksIrr Sg ∧ χ 1 = 1} := ⟨(hlam 0).1, (hlam 0).2.1⟩
    rw [hlin] at hmem
    obtain ⟨l, hl⟩ := hmem
    rw [← hl]
    simp only
    rw [(QuotientGroup.eq_one_iff z).mpr hz]
    simp
  have hμZ : ∀ x : Sg, (x : G) * x = 1 → (lam 0 - 1) x = 0 := by
    intro x hx
    have hx2 : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hx)
    have hxZ : x ∈ Subgroup.center Sg := (hshape.sq_eq_one_iff x).mp hx2
    simp [hlinZ x hxZ]
  obtain ⟨v, hv1⟩ : ∃ v : Subgroup.center Sg, v ≠ 1 := by
    have : Nontrivial (Subgroup.center Sg) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hshape.card_center]
      norm_num
    exact exists_ne 1
  have hvZ : (v : Sg) ∈ Subgroup.center Sg := v.property
  have hv1' : (v : Sg) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvv : ((v : Sg) : G) * (v : Sg) = 1 := by
    have h := congrArg Subtype.val ((hshape.sq_eq_one_iff (v : Sg)).mpr hvZ)
    rw [Subgroup.coe_pow, pow_two] at h
    exact h
  have hP : ∀ x ∈ Sg, x * x = 1 → ∀ y ∈ Sg, x * y = y * x := by
    intro x hx hxx y hy
    have hxZ := (hsq x hx).mp (by rw [pow_two]; exact hxx)
    exact ((mem_map_center_iff.mp hxZ).2 y hy).symm
  have hzero := central_sylow_involutions_weighted_block_zero basis ideal principal S hP
    ((v : Sg) : G) hvv (lam 0 - 1) hμZ
  choose k hk using fun ξ => scalarProduct_restrict_integer Sg hμ (basis.representation ξ)
  have hcoef : ∀ ξ, ((Nat.card S : ℂ)⁻¹ * ∑ x : Sg, (lam 0 - 1) x *
      starRingEnd ℂ ((basis.representation ξ).character x)) = k ξ := by
    intro ξ
    rw [← hk ξ, scalarProduct_eq_sum]
    rfl
  have hzero' : ∑ ξ ∈ B, (k ξ : ℂ) *
      (Complex.normSq ((basis.representation ξ).character (v : Sg)) : ℂ) /
        (basis.representation ξ).character 1 = 0 := by
    refine Eq.trans (Finset.sum_congr rfl fun ξ _ => ?_) hzero
    rw [← hcoef ξ]
  set w : basis.index → ℝ := fun ξ => Complex.normSq ((basis.representation ξ).character (v : Sg))
    with hw
  set d : basis.index → ℕ := fun ξ => Module.finrank ℂ (basis.representation ξ).vector with hd'
  have hreal : ∑ ξ ∈ B, (k ξ : ℝ) * w ξ / d ξ = 0 := by
    have h : ((∑ ξ ∈ B, (k ξ : ℝ) * w ξ / d ξ : ℝ) : ℂ) = 0 := by
      rw [← hzero']
      push_cast
      apply Finset.sum_congr rfl
      intro ξ _
      rw [character_one_eq_finrank]
    exact_mod_cast h
  have hprinc : principal ∈ B := coefficientBlock_self_mem basis _ principal
  have hkp : k principal = -1 := by
    have h := hk principal
    rw [hprincipal] at h
    have h1 : (fun x : Sg => (1 : G → ℂ) x) = 1 := rfl
    rw [h1, scalarProduct_sub_left', scalarProduct_blocksIrr (hlam 0).1 (one_mem_blocksIrr Sg),
      scalarProduct_blocksIrr (one_mem_blocksIrr Sg) (one_mem_blocksIrr Sg),
      ite_eq_right (hlam 0).2.2, ite_eq_left rfl] at h
    have h2 : ((k principal : ℤ) : ℂ) = ((-1 : ℤ) : ℂ) := by rw [← h]; norm_num
    exact_mod_cast h2
  have hwp : w principal = 1 := by simp [w, hprincipal]
  have hdp : d principal = 1 := by
    have h := character_one_eq_finrank (basis.representation principal)
    rw [hprincipal] at h
    have h' : ((1 : ℕ) : ℂ) = (Module.finrank ℂ (basis.representation principal).vector : ℂ) := by
      rw [← h]
      norm_num
    exact_mod_cast h'.symm
  have hsum1 : ∑ ξ ∈ B.erase principal, (k ξ : ℝ) * w ξ / d ξ = 1 := by
    rw [← Finset.add_sum_erase B _ hprinc, hkp, hwp, hdp] at hreal
    push_cast at hreal
    linarith
  have hw64 : ∑ ξ ∈ B, w ξ = 64 := hcentral (v : Sg) hvZ hv1'
  have hwsum : ∑ ξ ∈ B.erase principal, w ξ = 63 := by
    rw [← Finset.add_sum_erase B _ hprinc, hwp] at hw64
    linarith
  have hdpos : ∀ ξ ∈ B.erase principal, 0 < d ξ := by
    intro ξ _
    apply Nat.pos_of_ne_zero
    intro h0
    apply irreducible_character_degree_ne_zero (basis.representation ξ) (basis.irreducible ξ)
    rw [character_one_eq_finrank]
    exact_mod_cast h0
  obtain ⟨ξ, hξ, hkξ, hdξ⟩ := exists_pos_le_of_weighted_sum (B.erase principal) k w d
    (fun i _ => Complex.normSq_nonneg _) hdpos hsum1 hwsum
  obtain ⟨hξp, hξB⟩ := Finset.mem_erase.mp hξ
  have hχξ : (basis.representation ξ).character ≠ 1 := by
    intro h
    apply hξp
    apply basis.distinct
    change (basis.representation ξ).character = (basis.representation principal).character
    rw [h, hprincipal]
  obtain ⟨a₀, b, c, hformula, -, hfin⟩ :=
    hres (basis.representation ξ).vector (basis.representation ξ).representation
  have hRes : (fun x : Sg => (basis.representation ξ).character x) =
      fun x => ∑ t, (orbitCoeff a₀ b c t : ℂ) * orbitEnum Sg n lam ψ t x :=
    restriction_eq_orbitEnum_sum lam ψ a₀ b c _ hformula
  have hcR := scalarProduct_orbitEnum_coeff_right hn hlam hψ hψ4 hinjL hinjD (orbitCoeff a₀ b c)
  have hcL := scalarProduct_orbitEnum_coeff_left hn hlam hψ hψ4 hinjL hinjD (orbitCoeff a₀ b c)
  have hL0 : ∀ i, lam i = orbitEnum Sg n lam ψ (some (some i, 0)) := by
    intro i
    change lam i = conjugateCharacter Sg (n ^ ((0 : Fin 3) : ℕ)) (lam i)
    rw [Fin.val_zero, pow_zero, conjugateCharacter_one]
  have hD0 : ψ = orbitEnum Sg n lam ψ (some (none, 0)) := by
    change ψ = conjugateCharacter Sg (n ^ ((0 : Fin 3) : ℕ)) ψ
    rw [Fin.val_zero, pow_zero, conjugateCharacter_one]
  have h1E : (1 : Sg → ℂ) = orbitEnum Sg n lam ψ none := rfl
  have hkb : (k ξ : ℤ) = b 0 - a₀ := by
    have h := hk ξ
    rw [hRes, scalarProduct_sub_left', hL0 0, h1E, hcR, hcR] at h
    simp only [orbitCoeff] at h
    have h' : ((k ξ : ℤ) : ℂ) = (((b 0 : ℤ) - a₀ : ℤ) : ℂ) := by rw [← h]; push_cast; ring
    exact_mod_cast h'
  have hbound : ∀ i : Fin 5, i ≠ 0 → ((b i : ℤ) - b 0) ^ 2 ≤ 2 := by
    intro i hi
    have hθ : lam i - lam 0 ∈ CFSG.BlocksVChar Sg :=
      sub_mem (hirr_vchar _ (hlam i).1) (hirr_vchar _ (hlam 0).1)
    obtain ⟨k', hk', hk'sq⟩ := sq_le_of_blockInduction_norm basis B Sg hθ (N := 2)
      (by rw [hn2 i hi]; norm_num) hξB
    rw [hRes, scalarProduct_sub_left', hL0 i, hL0 0, hcR, hcR] at hk'
    simp only [orbitCoeff] at hk'
    have h' : ((k' : ℤ) : ℂ) = (((b i : ℤ) - b 0 : ℤ) : ℂ) := by rw [← hk']; push_cast; ring
    have h'' : k' = (b i : ℤ) - b 0 := by exact_mod_cast h'
    rw [← h'']
    exact_mod_cast hk'sq
  have hboundψ : ((c : ℤ) - 4 * b 0) ^ 2 ≤ 17 := by
    have h4 : (4 : ℂ) • lam 0 = (4 : ℕ) • lam 0 := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
      norm_num
    have hθ : ψ - (4 : ℂ) • lam 0 ∈ CFSG.BlocksVChar Sg := by
      rw [h4]
      exact sub_mem (hirr_vchar _ hψ) (AddSubgroup.nsmul_mem _ (hirr_vchar _ (hlam 0).1) 4)
    obtain ⟨k', hk', hk'sq⟩ := sq_le_of_blockInduction_norm basis B Sg hθ (N := 17)
      (by rw [hn3]; norm_num) hξB
    have hsplit : ψ - (4 : ℂ) • lam 0 = orbitEnum Sg n lam ψ (some (none, 0)) -
        (4 : ℂ) • orbitEnum Sg n lam ψ (some (some 0, 0)) := by
      rw [← hL0 0]
      congr 1
    rw [hRes, hsplit, scalarProduct_sub_left', scalarProduct_smul_left', hcR, hcR] at hk'
    simp only [orbitCoeff] at hk'
    have h' : ((k' : ℤ) : ℂ) = (((c : ℤ) - 4 * b 0 : ℤ) : ℂ) := by rw [← hk']; push_cast; ring
    have h'' : k' = (c : ℤ) - 4 * b 0 := by exact_mod_cast h'
    rw [← h'']
    exact_mod_cast hk'sq
  have ha₀ : a₀ = 0 := by
    have hdξ' : (d ξ : ℤ) = a₀ + 3 * ∑ i, (b i : ℤ) + 12 * c := by
      change (Module.finrank ℂ (basis.representation ξ).vector : ℤ) = _
      rw [hfin]
      push_cast
      ring
    rw [Fin.sum_univ_five] at hdξ'
    have h1 := hbound 1 (by decide)
    have h2 := hbound 2 (by decide)
    have h3 := hbound 3 (by decide)
    have h4 := hbound 4 (by decide)
    have e1 := neg_one_le_of_sq_le_two h1
    have e2 := neg_one_le_of_sq_le_two h2
    have e3 := neg_one_le_of_sq_le_two h3
    have e4 := neg_one_le_of_sq_le_two h4
    have eψ := neg_four_le_of_sq_le_seventeen hboundψ
    omega
  have hone_coeff : CFSG.Section1.scalarProduct Sg
      (fun x => (basis.representation ξ).character x) 1 = 0 := by
    rw [hRes, h1E, hcL]
    simp [orbitCoeff, ha₀]
  refine ⟨ξ, hξB, hχξ, lam 0, (hlam 0).1, (hlam 0).2.1, (hlam 0).2.2, (k ξ).toNat,
    by omega, ?_, ?_, hone_coeff, ?_⟩
  · rw [hk ξ]
    exact_mod_cast (Int.toNat_of_nonneg hkξ.le).symm
  · have : (d ξ : ℤ) ≤ 63 * ((k ξ).toNat : ℤ) := by rw [Int.toNat_of_nonneg hkξ.le]; exact hdξ
    exact_mod_cast this
  · intro V _ _ _ ρ hρ v hv
    apply fixed_vector_eq_zero Sg ρ _ v hv
    have : (fun x : Sg => ρ.character x) = fun x : Sg => (basis.representation ξ).character x := by
      rw [hρ]
    rw [this]
    exact hone_coeff

end Node

end CFSG.LyonsUnitaryFour
