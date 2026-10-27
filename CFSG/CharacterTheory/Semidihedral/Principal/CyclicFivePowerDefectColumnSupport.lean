module

public import CFSG.CharacterTheory.Semidihedral.Principal.AbelianFiveKernelDefectBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.BrauerSecondMainBlocks

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace FivePowerColumn

section Augmentation

variable {J : Type u} [Group J] (e : J ≃* alternatingGroup (Fin 5))

include e in
theorem orderOf_cases (j : J) :
    orderOf j = 1 ∨ orderOf j = 2 ∨ orderOf j = 3 ∨ orderOf j = 5 := by
  rw [← MulEquiv.orderOf_eq e]
  have h5 : Nat.Prime 5 := by norm_num
  rcases FiveKernel.pow_eq_one_cases (e j) with h | h | h | h
  · left
    rw [h, orderOf_one]
  · rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
  · rcases (Nat.dvd_prime h5).mp (orderOf_dvd_of_pow_eq_one h) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr h'))

variable [Fintype J]

include e in
theorem sylowAugmentation_eq_of_orderOf_eq {J' : Type u} [Group J'] [Fintype J']
    (e' : J' ≃* alternatingGroup (Fin 5)) {j : J} {j' : J'} (h : orderOf j = orderOf j') :
    FiveKernel.sylowAugmentation J j = FiveKernel.sylowAugmentation J' j' := by
  rcases orderOf_cases e j with h1 | h1 | h1 | h1
  · rw [orderOf_eq_one_iff.mp h1, orderOf_eq_one_iff.mp (h.symm.trans h1),
      FiveKernel.sylowAugmentation_one e, FiveKernel.sylowAugmentation_one e']
  · rw [FiveKernel.sylowAugmentation_of_orderOf_two e h1,
      FiveKernel.sylowAugmentation_of_orderOf_two e' (h.symm.trans h1)]
  · rw [FiveKernel.sylowAugmentation_of_orderOf_three e h1,
      FiveKernel.sylowAugmentation_of_orderOf_three e' (h.symm.trans h1)]
  · rw [FiveKernel.sylowAugmentation_of_orderOf_five e h1,
      FiveKernel.sylowAugmentation_of_orderOf_five e' (h.symm.trans h1)]

include e in
theorem coprime_of_sylowAugmentation_ne_zero {j : J}
    (h : FiveKernel.sylowAugmentation J j ≠ 0) : Nat.Coprime 5 (orderOf j) := by
  rcases orderOf_cases e j with h1 | h1 | h1 | h1 <;> rw [h1]
  · norm_num
  · norm_num
  · norm_num
  · exact absurd (FiveKernel.sylowAugmentation_of_orderOf_five e h1) h

include e in
theorem sum_sylowAugmentation_mul_inv :
    ∑ j : J, FiveKernel.sylowAugmentation J j * FiveKernel.sylowAugmentation J j⁻¹ = 60 := by
  have h := FiveKernel.characterPairing_sylowAugmentation e
  unfold characterPairing at h
  rw [FiveKernel.card_eq_sixty e] at h
  have h60 : ((60 : ℕ) : ℂ) ≠ 0 := by norm_num
  calc ∑ j : J, FiveKernel.sylowAugmentation J j * FiveKernel.sylowAugmentation J j⁻¹
      = ((60 : ℕ) : ℂ) * (((60 : ℕ) : ℂ)⁻¹ * ∑ j : J,
          FiveKernel.sylowAugmentation J j * FiveKernel.sylowAugmentation J j⁻¹) := by
        rw [← mul_assoc, mul_inv_cancel₀ h60, one_mul]
    _ = 60 := by
        rw [h]
        norm_num

end Augmentation

theorem exists_support_of_sum_mul_self_eq_three {X : Type*} [Fintype X] (z : X → ℤ)
    (h : ∑ x, z x * z x = 3) :
    ∃ s : Finset X, s.card = 3 ∧ ∀ x, (x ∈ s → z x = 1 ∨ z x = -1) ∧ (x ∉ s → z x = 0) := by
  have hle : ∀ x, z x * z x ≤ 3 := by
    intro x
    rw [← h]
    exact Finset.single_le_sum (f := fun y => z y * z y) (fun y _ => mul_self_nonneg (z y))
      (Finset.mem_univ x)
  have hcases : ∀ x, z x = -1 ∨ z x = 0 ∨ z x = 1 := by
    intro x
    have h1 := hle x
    have h2 : z x ≤ 1 := by nlinarith
    have h3 : -1 ≤ z x := by nlinarith
    omega
  refine ⟨Finset.univ.filter (fun x => z x ≠ 0), ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have hsum : ∑ x, z x * z x = ∑ x ∈ Finset.univ.filter (fun x => z x ≠ 0), (1 : ℤ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcases x with hx | hx | hx <;> simp [hx]
    rw [h, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    exact_mod_cast hsum.symm
  · rw [Finset.mem_filter] at hx
    rcases hcases x with h' | h' | h'
    · exact Or.inr h'
    · exact absurd h' hx.2
    · exact Or.inl h'
  · by_contra hne
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)

section Product

variable {G : Type u} [Group G] {W J : Subgroup G}
  (hsup : W ⊔ J = Subgroup.centralizer (W : Set G))

include hsup in
theorem left_le_centralizer : W ≤ Subgroup.centralizer (W : Set G) := by
  rw [← hsup]
  exact le_sup_left

include hsup in
theorem right_le_centralizer : J ≤ Subgroup.centralizer (W : Set G) := by
  rw [← hsup]
  exact le_sup_right

include hsup in
theorem commute_of_mem {w j : G} (hw : w ∈ W) (hj : j ∈ J) : Commute w j :=
  Subgroup.mem_centralizer_iff.mp (right_le_centralizer hsup hj) w hw

@[expose] noncomputable def prodHom : W × J →* Subgroup.centralizer (W : Set G) :=
  (MonoidHom.noncommCoprod W.subtype J.subtype fun w j =>
    commute_of_mem hsup w.2 j.2).codRestrict _ fun x =>
      Subgroup.mul_mem _ (left_le_centralizer hsup x.1.2) (right_le_centralizer hsup x.2.2)

theorem prodHom_apply (x : W × J) : (prodHom hsup x : G) = x.1 * x.2 := rfl

theorem prodHom_bijective (hdisj : W ⊓ J = ⊥) : Function.Bijective (prodHom hsup) := by
  constructor
  · intro x y h
    have h' : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val h
    have hmemW : (y.1 : G)⁻¹ * x.1 ∈ W := W.mul_mem (W.inv_mem y.1.2) x.1.2
    have hrel : (y.1 : G)⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
    have hmemJ : (y.1 : G)⁻¹ * x.1 ∈ J := by
      rw [hrel]
      exact J.mul_mem y.2.2 (J.inv_mem x.2.2)
    have hone : (y.1 : G)⁻¹ * x.1 = 1 := by
      have hmem : (y.1 : G)⁻¹ * x.1 ∈ W ⊓ J := ⟨hmemW, hmemJ⟩
      rw [hdisj] at hmem
      exact hmem
    have h1 : (x.1 : G) = y.1 := (inv_mul_eq_one.mp hone).symm
    have h2 : (x.2 : G) = y.2 := by
      rw [h1] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro k
    have hnorm : W ≤ Subgroup.normalizer (J : Set G) := by
      intro w hw
      rw [Subgroup.mem_normalizer_iff]
      intro j
      constructor
      · intro hj
        rw [(commute_of_mem hsup hw hj).eq, mul_inv_cancel_right]
        exact hj
      · intro hj
        have hc := (commute_of_mem hsup hw hj).eq
        rw [inv_mul_cancel_right] at hc
        rw [← mul_left_cancel hc]
        exact hj
    have hk : (k : G) ∈ ((W ⊔ J : Subgroup G) : Set G) := by
      rw [hsup]
      exact k.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W J hnorm] at hk
    obtain ⟨w, hw, j, hj, hwj⟩ := hk
    exact ⟨(⟨w, hw⟩, ⟨j, hj⟩), Subtype.ext hwj⟩

@[expose] noncomputable def prodEquiv (hdisj : W ⊓ J = ⊥) :
    W × J ≃* Subgroup.centralizer (W : Set G) :=
  MulEquiv.ofBijective (prodHom hsup) (prodHom_bijective hsup hdisj)

variable (hdisj : W ⊓ J = ⊥)

theorem prodEquiv_apply (x : W × J) : (prodEquiv hsup hdisj x : G) = x.1 * x.2 := rfl

theorem prodEquiv_symm_apply {k : Subgroup.centralizer (W : Set G)} {w : W} {j : J}
    (h : (k : G) = w * j) : (prodEquiv hsup hdisj).symm k = (w, j) := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext h

include hsup hdisj in
theorem exists_eq_mul (k : Subgroup.centralizer (W : Set G)) :
    ∃ (w : W) (j : J), (k : G) = w * j :=
  ⟨((prodEquiv hsup hdisj).symm k).1, ((prodEquiv hsup hdisj).symm k).2,
    (congrArg Subtype.val ((prodEquiv hsup hdisj).apply_symm_apply k)).symm⟩

include hsup hdisj in
theorem eq_of_mul_eq_mul {w w' : W} {j j' : J} (h : (w : G) * j = w' * j') :
    w = w' ∧ j = j' := by
  have h' := (prodHom_bijective hsup hdisj).1 (a₁ := (w, j)) (a₂ := (w', j')) (Subtype.ext h)
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

theorem coe_prodEquiv_inv (w : W) (j : J) :
    (((prodEquiv hsup hdisj (w, j))⁻¹ : Subgroup.centralizer (W : Set G)) : G) =
      (w : G)⁻¹ * (j : G)⁻¹ := by
  rw [← map_inv]
  rfl

include hsup hdisj in
theorem card_centralizer_eq :
    Nat.card (Subgroup.centralizer (W : Set G)) = Nat.card W * Nat.card J := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (prodEquiv hsup hdisj).toEquiv).symm

theorem sum_centralizer [Fintype G] (f : Subgroup.centralizer (W : Set G) → ℂ) :
    ∑ k, f k = ∑ w : W, ∑ j : J, f (prodEquiv hsup hdisj (w, j)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (prodEquiv hsup hdisj).toEquiv _ _ fun _ => rfl).symm

end Product

theorem subgroupOf_centralizer_normal {G : Type u} [Group G] (W : Subgroup G) :
    (W.subgroupOf (Subgroup.centralizer (W : Set G))).Normal := by
  constructor
  intro n hn k
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : (k : G) * n = n * k := (Subgroup.mem_centralizer_iff.mp k.2 n hn).symm
  change (k : G) * n * (k : G)⁻¹ ∈ W
  rw [hc, mul_inv_cancel_right]
  exact hn

section Linear

variable {G : Type u} [Group G] (W : Subgroup G)

theorem zpowers_eq_of_ne_one [Finite G] [IsCyclic W] (a : ℕ) (hWcard : Nat.card W = 5 ^ a)
    (lam : W →* ℂˣ) (hlam : lam ^ 5 = 1) (w : W) (hw : lam w ≠ 1) :
    Subgroup.zpowers (w : G) = W := by
  have hp : Nat.Prime 5 := by norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  have hgord : orderOf g = 5 ^ a := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hWcard]
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hg w))
  have hpk : ¬ 5 ∣ k := by
    rintro ⟨j, rfl⟩
    apply hw
    rw [← hk, map_pow, pow_mul]
    have hgp : lam g ^ 5 = 1 := by
      rw [← MonoidHom.pow_apply, hlam, MonoidHom.one_apply]
    rw [hgp, one_pow]
  have hcop : Nat.Coprime (orderOf g) k := by
    rw [hgord]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpk)
  have hword : orderOf (w : G) = 5 ^ a := by
    rw [Subgroup.orderOf_coe, ← hk, hcop.orderOf_pow, hgord]
  apply Subgroup.eq_of_le_of_card_ge
  · exact (Subgroup.zpowers_le).mpr w.2
  · rw [Nat.card_zpowers, hword, hWcard]

theorem sum_linear [Fintype G] (nu : W →* ℂˣ) :
    ∑ w : W, (nu w : ℂ) = if nu = 1 then (Nat.card W : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp only [MonoidHom.one_apply, Units.val_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  · apply sum_hom_units_eq_zero ((Units.coeHom ℂ).comp nu)
    intro h1
    apply h
    ext w
    have := congrArg (fun f => f w) h1
    simpa using this

theorem conj_eq_inv (lam : W →* ℂˣ) (hlam : lam ^ 5 = 1) (w : W) :
    starRingEnd ℂ (lam w : ℂ) = (lam w⁻¹ : ℂ) := by
  have hroot : (lam w : ℂ) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hlam, MonoidHom.one_apply,
      Units.val_one]
  rw [CFSG.TwoRankLowerBound.Helpers.complex_root_conjugate_inverse hroot (by norm_num),
    map_inv, Units.val_inv_eq_inv_val]

end Linear

section SecondMain

variable {G : Type u} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
  (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] [Fact (Nat.Prime 5)]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) 5]

theorem character_eq_projection (W : Subgroup G) (hW : IsPGroup 5 W) {u : G}
    (hu : Subgroup.zpowers u = W)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (label : basis.index) (c₀ : localBasis.index)
    (hfiber : ∀ c : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal 5 W hW (Subgroup.centralizer (W : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis c =
        centralCharacterResidueHom basis ideal label ↔
      c ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀)
    {χ : basis.index} (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (ρ k : Subgroup.centralizer (W : Set G)) (hρ : Nat.Coprime 5 (orderOf ρ))
    (hk : (k : G) = u * ρ) :
    (basis.representation χ).character k =
      characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀)
        (fun h => (basis.representation χ).character h) k := by
  subst hu
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  have hord : orderOf u ∣ 5 ^ n := by rw [← Nat.card_zpowers, hn]
  obtain ⟨-, hsum⟩ :=
    brauer_second_main_theorem basis ideal 5 u n hord hW localBasis label χ hχ ρ hρ
  have himage : ((Finset.univ.filter fun θ : localBasis.index =>
      brauerNormalizerCharacterResidueHom ideal 5 (Subgroup.zpowers u) hW
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal label).image
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal))) =
      {coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀} := by
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact coefficientBlock_eq_of_mem _ _ ((hfiber θ).mp hθ)
    · rintro rfl
      exact ⟨c₀, (hfiber c₀).mpr (coefficientBlock_self_mem _ _ _), rfl⟩
  rw [himage, Finset.sum_singleton] at hsum
  rw [hk, hsum, show k = ⟨u, element_mem_centralizer_zpowers u⟩ * ρ from Subtype.ext hk]

theorem projection_eq_zero (W : Subgroup G) (hW : IsPGroup 5 W) {u : G}
    (hu : Subgroup.zpowers u = W)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (label : basis.index) (c₀ : localBasis.index)
    (hc₀ : brauerNormalizerCharacterResidueHom ideal 5 W hW (Subgroup.centralizer (W : Set G))
        le_rfl (Subgroup.centralizer_le_normalizer _) localBasis c₀ =
      centralCharacterResidueHom basis ideal label)
    {χ : basis.index} (hχ : χ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (ρ k : Subgroup.centralizer (W : Set G)) (hρ : Nat.Coprime 5 (orderOf ρ))
    (hk : (k : G) = u * ρ) :
    characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀)
        (fun h => (basis.representation χ).character h) k = 0 := by
  subst hu
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  have hord : orderOf u ∣ 5 ^ n := by rw [← Nat.card_zpowers, hn]
  obtain ⟨hzero, -⟩ := brauer_second_main_theorem basis ideal 5 u n hord hW localBasis χ χ
    (coefficientBlock_self_mem _ _ _) ρ hρ
  rw [show k = ⟨u, element_mem_centralizer_zpowers u⟩ * ρ from Subtype.ext hk]
  apply hzero
  rw [hc₀]
  intro h
  apply hχ
  exact (coefficientBlock_mem_iff _ _ _ _).mpr
    ((sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label χ).mpr h)

theorem mem_block_of_brauer_eq (W : Subgroup G) (hW : IsPGroup 5 W)
    (hWK : W ≤ Subgroup.centralizer (W : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (c₀ : localBasis.index)
    (huniq : ∀ l : localBasis.index, coefficientBlockDefect localBasis ideal 5 l
        (W.subgroupOf (Subgroup.centralizer (W : Set G))) →
      l ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀)
    {label : basis.index} (hlabel : coefficientBlockDefect basis ideal 5 label W)
    {c : localBasis.index}
    (hc : brauerNormalizerCharacterResidueHom ideal 5 W hW (Subgroup.centralizer (W : Set G))
        le_rfl (Subgroup.centralizer_le_normalizer _) localBasis c =
      centralCharacterResidueHom basis ideal label) :
    c ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀ := by
  obtain ⟨D', hD'⟩ := coefficientBlockDefect_exists localBasis ideal 5 c
  have := subgroupOf_centralizer_normal W
  have hWD' : W.subgroupOf (Subgroup.centralizer (W : Set G)) ≤ D' :=
    normal_p_le_coefficientBlockDefect localBasis ideal 5
      (W.subgroupOf (Subgroup.centralizer (W : Set G))) hW.comap_subtype hD'
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = D'.map (Subgroup.centralizer (W : Set G)).subtype :=
    ⟨_, rfl⟩
  have hDsub : D.subgroupOf (Subgroup.centralizer (W : Set G)) = D' := by
    rw [hD]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) D'
  have hDp : IsPGroup 5 D := by
    rw [hD]
    exact (coefficientBlockDefect_isPGroup localBasis ideal hD').map _
  have hWD : W ≤ D := by
    intro w hw
    rw [hD]
    exact ⟨⟨w, hWK hw⟩, hWD' (by rw [Subgroup.mem_subgroupOf]; exact hw), rfl⟩
  have hDK : D ≤ Subgroup.centralizer (W : Set G) := by
    rw [hD]
    exact Subgroup.map_subtype_le D'
  have hlocal : coefficientBlockDefect localBasis ideal 5 c
      (D.subgroupOf (Subgroup.centralizer (W : Set G))) := by
    rw [hDsub]
    exact hD'
  obtain ⟨hall, -⟩ := centralizer_brauer_image_defect_contains_local_defect basis ideal 5 W hW D
    hDp hWD hDK localBasis c hlocal label hc
  have hDW : W = D := Subgroup.eq_of_le_of_card_ge hWD
    (CFSG.TwoRankLowerBound.Helpers.subgroupSubconjugate_card_le (hall W hlabel))
  apply huniq
  rw [(congrArg (fun H : Subgroup G => H.subgroupOf (Subgroup.centralizer (W : Set G))) hDW).trans
    hDsub]
  exact hD'

theorem brauer_fiber_eq (W : Subgroup G) (hW : IsPGroup 5 W)
    (hWK : W ≤ Subgroup.centralizer (W : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (c₀ : localBasis.index)
    (huniq : ∀ l : localBasis.index, coefficientBlockDefect localBasis ideal 5 l
        (W.subgroupOf (Subgroup.centralizer (W : Set G))) →
      l ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀)
    {label : basis.index} (hlabel : coefficientBlockDefect basis ideal 5 label W) :
    (∀ c : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal 5 W hW (Subgroup.centralizer (W : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis c =
        centralCharacterResidueHom basis ideal label ↔
      c ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀) ∧
    ∀ other : basis.index, coefficientBlockDefect basis ideal 5 other W →
      other ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label := by
  have hexists : ∀ {other : basis.index}, coefficientBlockDefect basis ideal 5 other W →
      ∃ c : localBasis.index, brauerNormalizerCharacterResidueHom ideal 5 W hW
          (Subgroup.centralizer (W : Set G)) le_rfl (Subgroup.centralizer_le_normalizer _)
          localBasis c = centralCharacterResidueHom basis ideal other := fun hother =>
    brauerNormalizer_local_block_exists_of_subconjugate basis ideal 5 W hW _ le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis hother
      (CFSG.TwoRankLowerBound.Helpers.subgroupSubconjugate_refl W)
  have hsame : ∀ c : localBasis.index,
      c ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀ →
      brauerNormalizerCharacterResidueHom ideal 5 W hW (Subgroup.centralizer (W : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis c =
        brauerNormalizerCharacterResidueHom ideal 5 W hW (Subgroup.centralizer (W : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis c₀ := by
    intro c hc
    apply RingHom.ext
    intro z
    change centralCharacterResidueHom localBasis ideal c _ =
      centralCharacterResidueHom localBasis ideal c₀ _
    rw [(sameCoefficientBlock_iff_centralCharacterResidueHom_eq localBasis ideal c c₀).mp
      (sameCoefficientBlock_symm _ _ ((coefficientBlock_mem_iff _ _ _ _).mp hc))]
  obtain ⟨c₁, hc₁⟩ := hexists hlabel
  have hc₀ := (hsame c₁ (mem_block_of_brauer_eq basis ideal W hW hWK localBasis c₀ huniq hlabel
    hc₁)).symm.trans hc₁
  refine ⟨fun c => ⟨fun hc => mem_block_of_brauer_eq basis ideal W hW hWK localBasis c₀ huniq
    hlabel hc, fun hc => (hsame c hc).trans hc₀⟩, fun other hother => ?_⟩
  obtain ⟨c', hc'⟩ := hexists hother
  have hc'₀ := mem_block_of_brauer_eq basis ideal W hW hWK localBasis c₀ huniq hother hc'
  have heq : centralCharacterResidueHom basis ideal label =
      centralCharacterResidueHom basis ideal other :=
    hc₀.symm.trans ((hsame c' hc'₀).symm.trans hc')
  exact (coefficientBlock_mem_iff _ _ _ _).mpr
    ((sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label other).mpr heq)

end SecondMain

section Mackey

variable {G : Type u} [Group G] [Fintype G] {W J : Subgroup G}
  (hsup : W ⊔ J = Subgroup.centralizer (W : Set G)) (hdisj : W ⊓ J = ⊥)

omit [Fintype G] in
theorem orderOf_conj (c x : G) : orderOf (c⁻¹ * x * c) = orderOf x := by
  have h := (MulAut.conj c⁻¹).orderOf_eq x
  rwa [MulAut.conj_apply, inv_inv] at h

include hsup hdisj in
theorem induced_apply_generator (a : ℕ) (hWcard : Nat.card W = 5 ^ a)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hJH : ∀ h ∈ Subgroup.normalizer (W : Set G), ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (hinv : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (θ : J → ℂ) (hθ : ∀ j j' : J, orderOf j = orderOf j' → θ j = θ j')
    (hθ5 : ∀ j : J, θ j ≠ 0 → Nat.Coprime 5 (orderOf j))
    (lam : W →* ℂˣ) (hgen : ∀ w : W, lam w ≠ 1 → Subgroup.zpowers (w : G) = W)
    (ψ : Subgroup.centralizer (W : Set G) → ℂ)
    (hψ : ∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J), (k : G) = w * j →
      ψ k = θ j * ((lam w : ℂ) - 1))
    {w : W} (hw : Subgroup.zpowers (w : G) = W) {j : J} (hj : Nat.Coprime 5 (orderOf j)) :
    inducedFunction (Subgroup.centralizer (W : Set G)) ψ ((w : G) * j) =
      θ j * ((lam w : ℂ) - 1) + θ j * ((lam w⁻¹ : ℂ) - 1) := by
  have hWK := left_le_centralizer hsup
  have hJK := right_le_centralizer hsup
  have hWord : ∀ x : W, orderOf (x : G) ∣ 5 ^ a := fun x => by
    rw [Subgroup.orderOf_coe, ← hWcard]
    exact orderOf_dvd_natCard x
  have hθconj : ∀ (c : G) (hc : c⁻¹ * (j : G) * c ∈ J), θ ⟨c⁻¹ * j * c, hc⟩ = θ j := by
    intro c hc
    apply hθ
    rw [Subgroup.orderOf_mk, orderOf_conj, Subgroup.orderOf_coe]
  have hvalue : ∀ c : G,
      (if hmem : c⁻¹ * ((w : G) * j) * c ∈ Subgroup.centralizer (W : Set G) then
        ψ ⟨c⁻¹ * ((w : G) * j) * c, hmem⟩ else 0) =
      (if c ∈ Subgroup.centralizer (W : Set G) then θ j * ((lam w : ℂ) - 1) else 0) +
        (if c ∈ Subgroup.normalizer (W : Set G) ∧ c ∉ Subgroup.centralizer (W : Set G) then
          θ j * ((lam w⁻¹ : ℂ) - 1) else 0) := by
    intro c
    have hsplit : c⁻¹ * ((w : G) * j) * c = (c⁻¹ * w * c) * (c⁻¹ * j * c) := by group
    by_cases hcK : c ∈ Subgroup.centralizer (W : Set G)
    · have hcw : c⁻¹ * (w : G) * c = w := by
        have hc : (w : G) * c = c * w := Subgroup.mem_centralizer_iff.mp hcK w w.2
        rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
      have hcj : c⁻¹ * (j : G) * c ∈ J := by
        have h := hJH c⁻¹ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hcK)) j j.2
        rwa [inv_inv] at h
      have hmem : c⁻¹ * ((w : G) * j) * c ∈ Subgroup.centralizer (W : Set G) := by
        rw [hsplit, hcw]
        exact Subgroup.mul_mem _ (hWK w.2) (hJK hcj)
      rw [dite_eq_left hmem, ite_eq_left hcK, ite_eq_right (fun h => h.2 hcK), add_zero,
        hψ ⟨_, hmem⟩ w ⟨_, hcj⟩ (by
          show c⁻¹ * ((w : G) * j) * c = (w : G) * (c⁻¹ * j * c)
          rw [hsplit, hcw]), hθconj c hcj]
    · by_cases hcH : c ∈ Subgroup.normalizer (W : Set G)
      · have hcinvH : c⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hcH
        have hcinvK : c⁻¹ ∉ Subgroup.centralizer (W : Set G) := fun h =>
          hcK (by simpa using Subgroup.inv_mem _ h)
        have hcw : c⁻¹ * (w : G) * c = (w : G)⁻¹ := by
          have h := hinv c⁻¹ hcinvH hcinvK w w.2
          rwa [inv_inv] at h
        have hcj : c⁻¹ * (j : G) * c ∈ J := by
          have h := hJH c⁻¹ hcinvH j j.2
          rwa [inv_inv] at h
        have hmem : c⁻¹ * ((w : G) * j) * c ∈ Subgroup.centralizer (W : Set G) := by
          rw [hsplit, hcw]
          exact Subgroup.mul_mem _ (hWK (W.inv_mem w.2)) (hJK hcj)
        rw [dite_eq_left hmem, ite_eq_right hcK, ite_eq_left ⟨hcH, hcK⟩, zero_add,
          hψ ⟨_, hmem⟩ w⁻¹ ⟨_, hcj⟩ (by
            show c⁻¹ * ((w : G) * j) * c = ((w⁻¹ : W) : G) * (c⁻¹ * j * c)
            rw [hsplit, hcw]
            rfl), hθconj c hcj]
      · rw [ite_eq_right hcK, ite_eq_right (fun h => hcH h.1), add_zero]
        by_cases hmem : c⁻¹ * ((w : G) * j) * c ∈ Subgroup.centralizer (W : Set G)
        · rw [dite_eq_left hmem]
          by_contra hne
          obtain ⟨w', j', hk⟩ := exists_eq_mul hsup hdisj ⟨_, hmem⟩
          rw [hψ ⟨_, hmem⟩ w' j' hk] at hne
          have hθ' : θ j' ≠ 0 := left_ne_zero_of_mul hne
          have hlam' : lam w' ≠ 1 := fun h =>
            right_ne_zero_of_mul hne (by rw [h, Units.val_one, sub_self])
          have h1 : orderOf (c⁻¹ * (w : G) * c) ∣ 5 ^ a := by
            rw [orderOf_conj]
            exact hWord w
          have h2 : Nat.Coprime 5 (orderOf (c⁻¹ * (j : G) * c)) := by
            rw [orderOf_conj, Subgroup.orderOf_coe]
            exact hj
          have h3 : Commute (c⁻¹ * (w : G) * c) (c⁻¹ * (j : G) * c) := by
            have h := (commute_of_mem hsup w.2 j.2).map (MulAut.conj c⁻¹).toMonoidHom
            simpa using h
          have h5 : Nat.Coprime 5 (orderOf (j' : G)) := by
            rw [Subgroup.orderOf_coe]
            exact hθ5 j' hθ'
          have hprod : (c⁻¹ * (w : G) * c) * (c⁻¹ * (j : G) * c) = (w' : G) * j' := by
            rw [← hsplit]
            exact hk
          obtain ⟨hpart, -⟩ := CFSG.LyonsUnitaryFour.primary_factorization_unique h1 h2 h3
            (hWord w') h5 (commute_of_mem hsup w'.2 j'.2) hprod
          exact hcH (CyclicInversion.mem_normalizer_of_conj_generator W hw (hgen w' hlam') hpart)
        · rw [dite_eq_right hmem]
  unfold inducedFunction
  rw [Finset.sum_congr rfl fun c _ => hvalue c, Finset.sum_add_distrib]
  have hs1 : ∑ c : G, (if c ∈ Subgroup.centralizer (W : Set G) then
      θ j * ((lam w : ℂ) - 1) else 0) =
      (Nat.card (Subgroup.centralizer (W : Set G)) : ℂ) * (θ j * ((lam w : ℂ) - 1)) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hs2 : ∑ c : G, (if c ∈ Subgroup.normalizer (W : Set G) ∧
      c ∉ Subgroup.centralizer (W : Set G) then θ j * ((lam w⁻¹ : ℂ) - 1) else 0) =
      (Nat.card (Subgroup.centralizer (W : Set G)) : ℂ) * (θ j * ((lam w⁻¹ : ℂ) - 1)) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard := CyclicInversion.card_normalizer_sdiff W hindex
    exact_mod_cast (by convert hcard using 2 :
      (Finset.univ.filter (fun c : G => c ∈ Subgroup.normalizer (W : Set G) ∧
        c ∉ Subgroup.centralizer (W : Set G))).card = Nat.card (Subgroup.centralizer (W : Set G)))
  rw [hs1, hs2, ← mul_add, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

end Mackey

theorem apply_eq_of_mem_span {G : Type u} [Group G] [Fintype G] {W J : Subgroup G}
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (S : Finset localBasis.index) (θ : J → ℂ) (t : J) (ht : θ t = 1)
    (hS : ∀ c ∈ S, ∃ μ : W →* ℂˣ, ∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J),
      (k : G) = w * j → (localBasis.representation c).character k = μ w * θ j)
    {F : Subgroup.centralizer (W : Set G) → ℂ} (hF : F ∈ coefficientCharacterSpace localBasis S)
    {k k' : Subgroup.centralizer (W : Set G)} {w : W} {j : J} (hk : (k : G) = w * j)
    (hk' : (k' : G) = w * t) : F k = θ j * F k' := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hc, rfl⟩ := hf
    obtain ⟨μ, hμ⟩ := hS c hc
    beta_reduce
    rw [hμ k w j hk, hμ k' w t hk', ht, mul_one, mul_comm]
  | zero => simp
  | add f g _ _ hf hg => rw [Pi.add_apply, Pi.add_apply, hf, hg, mul_add]
  | smul r f _ hf =>
    rw [Pi.smul_apply, Pi.smul_apply, hf, smul_eq_mul, smul_eq_mul]
    ring

theorem kernelBlock_eq {G : Type u} [Group G] [Fintype G] {W J : Subgroup G}
    (hsup : W ⊔ J = Subgroup.centralizer (W : Set G)) (e : J ≃* alternatingGroup (Fin 5))
    (hWab : ∀ x ∈ W.subgroupOf (Subgroup.centralizer (W : Set G)),
      ∀ y ∈ W.subgroupOf (Subgroup.centralizer (W : Set G)), Commute x y)
    (basisW : FiniteIrreducibleCharacterBasis (W.subgroupOf (Subgroup.centralizer (W : Set G)))) :
    {ψ : Subgroup.centralizer (W : Set G) → ℂ | ∃ lam : basisW.index,
      ∀ (w : W.subgroupOf (Subgroup.centralizer (W : Set G)))
        (j : J.subgroupOf (Subgroup.centralizer (W : Set G))),
        ψ ((w : Subgroup.centralizer (W : Set G)) * j) =
          (basisW.representation lam).character w *
            FiveKernel.sylowAugmentation (J.subgroupOf (Subgroup.centralizer (W : Set G))) j} =
    {f | ∃ μ : W →* ℂˣ, ∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J),
      (k : G) = w * j → f k = μ w * FiveKernel.sylowAugmentation J j} := by
  have hWK := left_le_centralizer hsup
  have hJK := right_le_centralizer hsup
  have hθ : ∀ j : J.subgroupOf (Subgroup.centralizer (W : Set G)),
      FiveKernel.sylowAugmentation (J.subgroupOf (Subgroup.centralizer (W : Set G))) j =
        FiveKernel.sylowAugmentation J (Subgroup.subgroupOfEquivOfLe hJK j) := fun j =>
    sylowAugmentation_eq_of_orderOf_eq ((Subgroup.subgroupOfEquivOfLe hJK).trans e) e
      (MulEquiv.orderOf_eq (Subgroup.subgroupOfEquivOfLe hJK) j).symm
  ext f
  constructor
  · rintro ⟨lam, hlam⟩
    refine ⟨(degreeOneCharacterUnits (basisW.representation lam)
      (FiveKernel.character_one_eq_one basisW hWab lam)).comp
        (Subgroup.subgroupOfEquivOfLe hWK).symm.toMonoidHom, ?_⟩
    intro k w j hk
    have hk' : k = (((Subgroup.subgroupOfEquivOfLe hWK).symm w :
        W.subgroupOf (Subgroup.centralizer (W : Set G))) : Subgroup.centralizer (W : Set G)) *
        (((Subgroup.subgroupOfEquivOfLe hJK).symm j :
          J.subgroupOf (Subgroup.centralizer (W : Set G))) :
            Subgroup.centralizer (W : Set G)) := by
      apply Subtype.ext
      rw [hk, Subgroup.coe_mul, Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe,
        Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe]
    rw [hk', hlam, hθ, MulEquiv.apply_symm_apply]
    rfl
  · rintro ⟨μ, hμ⟩
    obtain ⟨lam, hlam⟩ := CyclicInversion.exists_label_of_linear basisW
      (μ.comp (Subgroup.subgroupOfEquivOfLe hWK).toMonoidHom)
    refine ⟨lam, fun w j => ?_⟩
    rw [hμ _ (Subgroup.subgroupOfEquivOfLe hWK w) (Subgroup.subgroupOfEquivOfLe hJK j) (by
      rw [Subgroup.coe_mul, Subgroup.subgroupOfEquivOfLe_apply_coe,
        Subgroup.subgroupOfEquivOfLe_apply_coe]), hlam, hθ]
    rfl

end FivePowerColumn

end CFSG.Semidihedral.Principal
