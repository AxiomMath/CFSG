module

public import CFSG.CharacterTheory.Semidihedral.Principal.DefectKleinFourSectionColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistComplementBlocks
public import CFSG.CharacterTheory.Blocks.NormTwo
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ProductCharacterFormula

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

@[expose] def translatedOddSection {C : Type*} [Group C] (t : C) : Set C :=
  {x | ∃ z : C, x = t * z ∧ Odd (orderOf z)}

namespace TwoLinearLocal

variable {C : Type*} [Group C]

theorem mem_closure_pair {t s : C} (hts : t * s = s * t) (ht2 : t * t = 1) (hs2 : s * s = 1)
    {v : C} (hv : v ∈ Subgroup.closure ({t, s} : Set C)) :
    v = 1 ∨ v = t ∨ v = s ∨ v = t * s := by
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul a b _ _ ha hb =>
    have h1 : t * (t * s) = s := by rw [← mul_assoc, ht2, one_mul]
    have h2 : s * (t * s) = t := by rw [← mul_assoc, ← hts, mul_assoc, hs2, mul_one]
    have h3 : t * s * t = s := by rw [mul_assoc, ← hts, ← mul_assoc, ht2, one_mul]
    have h4 : t * s * s = t := by rw [mul_assoc, hs2, mul_one]
    have h5 : t * s * (t * s) = 1 := by rw [mul_assoc, h2, ht2]
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ht2, hs2, h1, h2, h3, h4, h5, ← hts, true_or, or_true]
  | inv a _ ha =>
    have hinv : ∀ z : C, z * z = 1 → z⁻¹ = z := fun z hz => inv_eq_of_mul_eq_one_left hz
    have h5 : t * s * (t * s) = 1 := by
      rw [mul_assoc, ← mul_assoc s, ← hts, mul_assoc, hs2, mul_one, ht2]
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (hinv _ ht2))
    · exact Or.inr (Or.inr (Or.inl (hinv _ hs2)))
    · exact Or.inr (Or.inr (Or.inr (hinv _ h5)))

theorem oddSectionMatrix_column_ne_zero {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (label : basis.index)
    (P : Subgroup G) (hP : coefficientBlockDefect basis ideal 2 label P) (hP4 : Nat.card P = 4)
    (ρ : basis.index) (hρ : ρ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (z : ℤ) (hz : Odd z) (hρρ : oddSectionMatrix basis ρ ρ = z)
    (χ : basis.index) (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label) :
    oddSectionMatrix basis χ ρ ≠ 0 := by
  obtain ⟨-, -, hdeg⟩ := block_class_defect_witness_character_degree_dvd basis ideal 2 label P hP
  obtain ⟨ha2, hdiv⟩ := hdeg 2 (by rw [hP4]; norm_num)
  obtain ⟨N, hN⟩ := pow_padicValNat_dvd (p := 2) (n := Nat.card G)
  have hNodd : ¬ 2 ∣ N := by
    rintro ⟨M, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := 2) (Nat.card_pos (α := G)).ne'
    refine ⟨M, ?_⟩
    rw [pow_succ]
    conv_lhs => rw [hN]
    ring
  have hd : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∃ dχ : ℕ, 0 < dχ ∧ Module.finrank ℂ (basis.representation χ).vector =
        2 ^ (padicValNat 2 (Nat.card G) - 2) * dχ := by
    intro χ hχ
    obtain ⟨dχ, hdχ⟩ := hdiv χ hχ
    refine ⟨dχ, Nat.pos_of_ne_zero fun h0 => ?_, hdχ⟩
    apply irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one, hdχ, h0, mul_zero,
      Nat.cast_zero]
  choose! d hdpos hdeq using hd
  generalize padicValNat 2 (Nat.card G) = a at hN ha2 hdeq
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hN
      exact (Nat.card_pos (α := G)).ne' hN
    exact_mod_cast this
  have hval : ∀ (ψ : basis.index) (K : ConjClasses G),
      (basis.representation ψ).character (Classical.choose (ConjClasses.exists_rep K))⁻¹ ∈
        localizedComplexIntegerRing ideal := fun ψ K =>
    complexAlgebraicInteger_mem_localized_ring ideal
      (algebraicCharacterValue (basis.representation ψ) _)
  obtain ⟨S, hS⟩ : ∃ S : basis.index → basis.index → localizedComplexIntegerRing ideal,
      S = fun χ ψ => ∑ K ∈ (Finset.univ.filter (fun x : G => Odd (orderOf x))).image
        ConjClasses.mk, localCentralCharacterHom basis ideal χ
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) * ⟨_, hval ψ K⟩ :=
    ⟨_, rfl⟩
  have hScoe : ∀ χ ψ, (S χ ψ : ℂ) =
      ∑ K ∈ (Finset.univ.filter (fun x : G => Odd (orderOf x))).image ConjClasses.mk,
        (localCentralCharacterHom basis ideal χ
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) : ℂ) *
        (basis.representation ψ).character (Classical.choose (ConjClasses.exists_rep K))⁻¹ := by
    intro χ ψ
    rw [hS]
    push_cast
    rfl
  have hSres : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label, ∀ ψ,
      localizedComplexIntegerResidue ideal (S χ ψ) =
        localizedComplexIntegerResidue ideal (S label ψ) := by
    intro χ hχ ψ
    have hsame : centralCharacterResidueHom basis ideal label =
        centralCharacterResidueHom basis ideal χ :=
      (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label χ).mp
        ((coefficientBlock_mem_iff _ _ _ _).mp hχ)
    rw [hS]
    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun K _ => ?_
    congr 1
    exact (congrFun (congrArg DFunLike.coe hsame) _).symm
  have hrel : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label, ∀ ψ,
      (N : ℂ) * oddSectionMatrix basis χ ψ = (d χ : ℂ) * (S χ ψ : ℂ) := by
    intro χ hχ ψ
    unfold oddSectionMatrix
    rw [DefectFourOdd.sum_odd_eq_degree_mul_classSum basis ideal χ ψ, ← hScoe,
      FiniteComplexRepresentation.character, Representation.char_one, hdeq χ hχ, hN]
    have h2a : (2 : ℂ) ^ a = 2 ^ (a - 2) * 4 := by
      rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel ha2]
    push_cast
    rw [h2a]
    field_simp
  have hσ : localizedComplexIntegerResidue ideal (S label ρ) ≠ 0 := by
    intro h0
    have hR : (((N : ℤ) * z : ℤ) : localizedComplexIntegerRing ideal) =
        (d ρ : localizedComplexIntegerRing ideal) * S ρ ρ := by
      apply Subtype.ext
      push_cast
      rw [← hρρ]
      exact hrel ρ hρ ρ
    have h := congrArg (localizedComplexIntegerResidue ideal) hR
    rw [map_mul, map_intCast, map_natCast, hSres ρ hρ ρ, h0, mul_zero] at h
    have hdvd := (CharP.intCast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) 2 _).mp h
    have hN2 : ¬ (2 : ℤ) ∣ (N : ℤ) := by exact_mod_cast hNodd
    rcases Int.prime_two.dvd_mul.mp hdvd with h' | h'
    · exact hN2 h'
    · exact (Int.not_even_iff_odd.mpr hz) (even_iff_two_dvd.mpr h')
  intro h0
  have h := hrel χ hχ ρ
  rw [h0, mul_zero] at h
  have hd0 : (d χ : ℂ) ≠ 0 := by exact_mod_cast (hdpos χ hχ).ne'
  have hS0 : S χ ρ = 0 := by
    apply Subtype.ext
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact absurd h1 hd0
    · exact h1
  apply hσ
  rw [← hSres χ hχ ρ, hS0, map_zero]

theorem two_part_eq_of_mul {x a b u v : C} (ha : a * a = 1) (hab : Commute a b)
    (hb : Odd (orderOf b)) (hx : x = a * b) {e : ℕ} (hu : orderOf u ∣ 2 ^ e)
    (hv : Nat.Coprime 2 (orderOf v)) (huv : Commute u v) (hxuv : x = u * v) : u = a := by
  have hvodd : Odd (orderOf v) := Nat.coprime_two_left.mp hv
  have hm : Odd (orderOf b * orderOf v) := hb.mul hvodd
  have hu2 : u ^ 2 = 1 := by
    have hpow : u ^ (2 * (orderOf b * orderOf v)) = 1 := by
      have h1 : x ^ (2 * (orderOf b * orderOf v)) = u ^ (2 * (orderOf b * orderOf v)) := by
        rw [hxuv, huv.mul_pow, orderOf_dvd_iff_pow_eq_one.mp
          (dvd_mul_of_dvd_right (dvd_mul_left _ _) 2), mul_one]
      have h2 : x ^ (2 * (orderOf b * orderOf v)) = 1 := by
        rw [hx, hab.mul_pow, pow_mul a 2, pow_two a, ha, one_pow, one_mul,
          orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_of_dvd_right (dvd_mul_right _ _) 2)]
      rw [← h1, h2]
    have hdvd : orderOf u ∣ 2 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
      have h2m := orderOf_dvd_of_pow_eq_one hpow
      rw [hj] at h2m ⊢
      have hcop : Nat.Coprime (2 ^ j) (orderOf b * orderOf v) :=
        Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
      exact hcop.dvd_of_dvd_mul_right h2m
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have ha2 : a ^ 2 = 1 := by rw [pow_two, ha]
  exact BrauerFiberSection.involution_part_unique huv hu2 hvodd hab ha2 hb (hxuv.symm.trans hx)

theorem odd_iff_two_part_eq_one {u v : C} {e : ℕ} (hu : orderOf u ∣ 2 ^ e)
    (hv : Nat.Coprime 2 (orderOf v)) (huv : Commute u v) : Odd (orderOf (u * v)) ↔ u = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
  have hcop : Nat.Coprime (orderOf u) (orderOf v) := by
    rw [hj]
    exact Nat.Coprime.pow_left j hv
  rw [huv.orderOf_mul_eq_mul_orderOf_of_coprime hcop, Nat.odd_mul]
  constructor
  · rintro ⟨hodd, -⟩
    rw [hj] at hodd
    have hj0 : j = 0 := by
      by_contra hne
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [pow_succ] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rintro rfl
    exact ⟨by rw [orderOf_one]; exact odd_one, Nat.coprime_two_left.mp hv⟩

theorem mem_translatedOddSection_iff {t : C} (htcent : ∀ g : C, g * t = t * g)
    (ht2 : t * t = 1) {u v : C} {e : ℕ} (hu : orderOf u ∣ 2 ^ e)
    (hv : Nat.Coprime 2 (orderOf v)) (huv : Commute u v) :
    u * v ∈ translatedOddSection t ↔ u = t := by
  constructor
  · rintro ⟨z, hz, hzodd⟩
    exact two_part_eq_of_mul ht2 (htcent z).symm hzodd hz hu hv huv rfl
  · rintro rfl
    exact ⟨v, rfl, Nat.coprime_two_left.mp hv⟩

theorem mem_involutionSectionUnion_iff {s : C} (hs2 : s * s = 1) {u v : C} {e : ℕ}
    (hu : orderOf u ∣ 2 ^ e) (hv : Nat.Coprime 2 (orderOf v)) (huv : Commute u v) :
    u * v ∈ involutionSectionUnion s ↔ IsConj u s := by
  constructor
  · rintro ⟨g, q, ⟨z, rfl, hzodd⟩, hq⟩
    have hsz : Commute s (z : C) :=
      Subtype.ext_iff.mp (BrauerFiberSection.commute_centralizerSelf s z)
    have hconj : Commute (g * s * g⁻¹) (g * (z : C) * g⁻¹) := by
      have := hsz.map (MulAut.conj g).toMonoidHom
      simpa [MulAut.conj_apply] using this
    have hsq : g * s * g⁻¹ * (g * s * g⁻¹) = 1 := by
      rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group, hs2]
      group
    have hzo : Odd (orderOf (g * (z : C) * g⁻¹)) := by
      have h := (MulAut.conj g).orderOf_eq (z : C)
      rw [MulAut.conj_apply] at h
      rw [h, Subgroup.orderOf_coe]
      exact hzodd
    have hx : u * v = g * s * g⁻¹ * (g * (z : C) * g⁻¹) := by
      rw [hq, Subgroup.coe_mul]
      group
    have hueq := two_part_eq_of_mul hsq hconj hzo hx hu hv huv rfl
    rw [hueq]
    exact isConj_iff.mpr ⟨g⁻¹, by group⟩
  · intro hus
    obtain ⟨g, hg⟩ := isConj_iff.mp hus
    have hmem : g * v * g⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← hg]
      have huv' : Commute (g * u * g⁻¹) (g * v * g⁻¹) := by
        have := huv.map (MulAut.conj g).toMonoidHom
        simpa [MulAut.conj_apply] using this
      exact (huv'.zpow_left k).eq
    have hodd : Odd (orderOf (⟨g * v * g⁻¹, hmem⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C))) := by
      rw [← Subgroup.orderOf_coe]
      have h := (MulAut.conj g).orderOf_eq v
      rw [MulAut.conj_apply] at h
      simp only
      rw [h]
      exact Nat.coprime_two_left.mp hv
    refine ⟨g⁻¹, ⟨s, element_mem_centralizer_zpowers s⟩ * ⟨g * v * g⁻¹, hmem⟩,
      ⟨_, rfl, hodd⟩, ?_⟩
    rw [Subgroup.coe_mul]
    change u * v = g⁻¹ * (s * (g * v * g⁻¹)) * g⁻¹⁻¹
    rw [← hg]
    group

theorem central_involution_sign {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (t : G) (htcent : ∀ g : G, g * t = t * g)
    (ht2 : t * t = 1) (χ : basis.index) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ x : G,
      (basis.representation χ).character (t * x) = σ * (basis.representation χ).character x := by
  have hA : CFSG.LyonsUnitaryFour.ConjInvariant ({t} : Finset G) := by
    intro g x
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      rw [htcent g, mul_inv_cancel_right]
    · intro h
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * t * g := by rw [h]
        _ = t := by rw [mul_assoc, ← htcent g, ← mul_assoc, inv_mul_cancel, one_mul]
  have hsc := CFSG.LyonsUnitaryFour.irreducible_invariant_sum_eq_smul (basis.representation χ)
    (basis.irreducible χ) {t} hA
  rw [Finset.sum_singleton, Finset.sum_singleton] at hsc
  set c := (basis.representation χ).character t / (basis.representation χ).character 1 with hc
  have hdeg := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
  have hval : ∀ x, (basis.representation χ).character (t * x) =
      c * (basis.representation χ).character x := by
    intro x
    change LinearMap.trace ℂ _ ((basis.representation χ).representation (t * x)) =
      c * LinearMap.trace ℂ _ ((basis.representation χ).representation x)
    rw [map_mul, hsc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  have hc2 : c * c = 1 := by
    have h1 := hval t
    rw [ht2] at h1
    have h2 := hval 1
    rw [mul_one] at h2
    rw [h2] at h1
    have : (c * c - 1) * (basis.representation χ).character 1 = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hdeg)
  have hc' : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hc' with h | h
  · exact ⟨1, Or.inl rfl, fun x => by rw [hval x, h, Int.cast_one]⟩
  · exact ⟨-1, Or.inr rfl, fun x => by rw [hval x, h]; push_cast; ring⟩

theorem card_filter_mk_eq {H : Type*} [Group H] [Fintype H] (N : Subgroup H) [N.Normal] (g : H) :
    (Finset.univ.filter (fun x : H => (x : H ⧸ N) = (g : H ⧸ N))).card = Nat.card N := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := N)]
  symm
  apply Finset.card_bij (fun (n : N) _ => g * n)
  · intro n _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [QuotientGroup.eq]
    simp
  · intro n _ n' _ h
    exact Subtype.ext (mul_left_cancel h)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hmem : g⁻¹ * x ∈ N := QuotientGroup.eq.mp hx.symm
    exact ⟨⟨g⁻¹ * x, hmem⟩, Finset.mem_univ _, by simp⟩

theorem pairing_add_smul_left {H : Type*} [Group H] [Fintype H] (a b : ℂ) (F₀ F₁ g : H → ℂ) :
    characterPairing (a • F₀ + b • F₁) g =
      a * characterPairing F₀ g + b * characterPairing F₁ g := by
  unfold characterPairing
  have h : ∑ x : H, (a • F₀ + b • F₁) x * g x⁻¹ =
      a * ∑ x : H, F₀ x * g x⁻¹ + b * ∑ x : H, F₁ x * g x⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  ring

theorem vec_four_injective {α : Type*} {a b c d : α} (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d)
    (h12 : b ≠ c) (h13 : b ≠ d) (h23 : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem image_vec_four {α : Type*} [DecidableEq α] (a b c d : α) :
    Finset.univ.image ![a, b, c, d] = {a, b, c, d} := by
  ext x
  simp [Fin.exists_fin_succ, eq_comm]

end TwoLinearLocal

open TwoLinearLocal

theorem central_involution_two_linear_local_blocks_four_characters_and_section_line
    {C : Type} [Group C] [Fintype C] (basis : FiniteIrreducibleCharacterBasis C)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (t s : C) (htcent : ∀ g : C, g * t = t * g) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hst : s ≠ t) (hgroup : IsPGroup 2 (Subgroup.zpowers s))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers s : Set C)))
    (E : Subgroup C) (hEodd : Odd (Nat.card E))
    (hED : E ≤ Subgroup.centralizer (Subgroup.zpowers s : Set C))
    (hDVE : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C),
      ∃ v ∈ Subgroup.closure ({t, s} : Set C), ∃ e ∈ E, x = v * e)
    (hVE : Subgroup.closure ({t, s} : Set C) ⊓ E = ⊥)
    (y : C) (hyV : y ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set C) : Set C))
    (hys : y * s * y⁻¹ = t * s)
    (μ μ₁ : E →* ℂˣ) (hμ₁ : ∀ e e' : E, (e' : C) = y⁻¹ * e * y → μ₁ e = μ e')
    (hμne : μ₁ ≠ μ)
    (ν₀ ν₁ : Subgroup.centralizer (Subgroup.zpowers s : Set C) →* ℂˣ)
    (hν₀ : ∀ (x : Subgroup.centralizer (Subgroup.zpowers s : Set C)) (v : C) (e : E),
      v ∈ Subgroup.closure ({t, s} : Set C) → (x : C) = v * e → ν₀ x = μ e)
    (hν₁ : ∀ (x : Subgroup.centralizer (Subgroup.zpowers s : Set C)) (v : C) (e : E),
      v ∈ Subgroup.closure ({t, s} : Set C) → (x : C) = v * e → ν₁ x = μ₁ e)
    (n₀ n₁ : localBasis.index)
    (hn₀ : ∀ x, (localBasis.representation n₀).character x = ν₀ x)
    (hn₁ : ∀ x, (localBasis.representation n₁).character x = ν₁ x)
    (label : basis.index)
    (hD : coefficientBlockDefect basis ideal 2 label (Subgroup.closure ({t, s} : Set C)))
    (hfiber : brauerFiberBlocks basis ideal 2 s hgroup localBasis label =
      {coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀,
        coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁}) :
    ∃ (θ : Fin 4 → basis.index) (f : ℕ),
      Function.Injective θ ∧
      coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ.image θ ∧
      0 < f ∧ (∀ i, Module.finrank ℂ (basis.representation (θ i)).vector = f) ∧
      (basis.representation (θ 0)).character t = f ∧
      (basis.representation (θ 1)).character t = f ∧
      (basis.representation (θ 2)).character t = -(f : ℂ) ∧
      (basis.representation (θ 3)).character t = -(f : ℂ) ∧
      (basis.representation (θ 0)).character s = 2 ∧
      (basis.representation (θ 1)).character s = -2 ∧
      (basis.representation (θ 2)).character s = 0 ∧
      (basis.representation (θ 3)).character s = 0 ∧
      (∀ x : C, Odd (orderOf x) → ∀ i i',
        (basis.representation (θ i)).character x = (basis.representation (θ i')).character x) ∧
      (∀ x : C, 4 ∣ orderOf x → ∀ i, (basis.representation (θ i)).character x = 0) ∧
      (∀ x, x ∉ translatedOddSection t →
        ((basis.representation (θ 0)).character + (basis.representation (θ 1)).character -
          (basis.representation (θ 2)).character - (basis.representation (θ 3)).character) x =
            0) ∧
      BlocksInnerProduct ((basis.representation (θ 0)).character +
          (basis.representation (θ 1)).character - (basis.representation (θ 2)).character -
            (basis.representation (θ 3)).character)
        ((basis.representation (θ 0)).character + (basis.representation (θ 1)).character -
          (basis.representation (θ 2)).character - (basis.representation (θ 3)).character) = 4 ∧
      ((basis.representation (θ 0)).character + (basis.representation (θ 1)).character -
          (basis.representation (θ 2)).character - (basis.representation (θ 3)).character) t =
        4 * f ∧
      coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (translatedOddSection t) =
        Submodule.span ℂ {(basis.representation (θ 0)).character +
          (basis.representation (θ 1)).character - (basis.representation (θ 2)).character -
            (basis.representation (θ 3)).character} ∧
      Module.finrank ℂ ↥(coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (translatedOddSection t)) = 1 ∧
      Module.finrank ℂ ↥(coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported {x : C | Odd (orderOf x)}) = 1 := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hts : t * s = s * t := (htcent s).symm
  have hVmem : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v = 1 ∨ v = t ∨ v = s ∨ v = t * s :=
    fun v hv => mem_closure_pair hts ht2 hs2 hv
  have hV2 : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v * v = 1 := by
    intro v hv
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ht2
    · exact hs2
    · rw [mul_assoc, ← mul_assoc s, ← hts, mul_assoc, hs2, mul_one, ht2]
  have hsD : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), s * x = x * s := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx s (Subgroup.mem_zpowers s))
  have hVcomm : ∀ v ∈ Subgroup.closure ({t, s} : Set C),
      ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), v * x = x * v := by
    intro v hv x hx
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact (htcent x).symm
    · exact hsD x hx
    · rw [mul_assoc, hsD x hx, ← mul_assoc, ← htcent x, mul_assoc]
  have hoddEord : ∀ e ∈ E, Odd (orderOf e) := by
    intro e he
    have h := Subgroup.orderOf_dvd_natCard E he
    exact Odd.of_dvd_nat hEodd h
  have hoddE : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), Odd (orderOf x) →
      x ∈ E := by
    intro x hx hodd
    obtain ⟨v, hv, e, he, rfl⟩ := hDVE x hx
    have hcomm : Commute v e := hVcomm v hv e (hED he)
    have hv2 : orderOf v ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hV2 v hv])
    have he' : Nat.Coprime 2 (orderOf e) := Nat.coprime_two_left.mpr (hoddEord e he)
    have h1 := (odd_iff_two_part_eq_one hv2 he' hcomm).mp hodd
    rw [h1, one_mul]
    exact he
  have hys' : y⁻¹ * (t * s) * y = s := by rw [← hys]; group
  have hyt : y⁻¹ * t * y = t := by rw [mul_assoc, ← htcent y, ← mul_assoc, inv_mul_cancel, one_mul]
  have hyE : ∀ e ∈ E, y⁻¹ * e * y ∈ E := by
    intro e he
    apply hoddE
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hcs : s * (y⁻¹ * e * y) = y⁻¹ * e * y * s := by
        have he1 : e * (t * s) = (t * s) * e := by
          rw [← mul_assoc, htcent e, mul_assoc, ← hsD e (hED he), ← mul_assoc]
        calc s * (y⁻¹ * e * y) = y⁻¹ * (t * s) * y * (y⁻¹ * e * y) := by rw [hys']
          _ = y⁻¹ * ((t * s) * e) * y := by group
          _ = y⁻¹ * (e * (t * s)) * y := by rw [he1]
          _ = y⁻¹ * e * y * (y⁻¹ * (t * s) * y) := by group
          _ = y⁻¹ * e * y * s := by rw [hys']
      exact (Commute.zpow_left hcs k).eq
    · have h := (MulAut.conj y⁻¹).orderOf_eq e
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h]
      exact hoddEord e he
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    norm_num at hs
  have hts1 : t * s ≠ 1 := by
    intro h
    apply hst
    have : s = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_left ht2]
  have hVset : (Subgroup.closure ({t, s} : Set C) : Set C) =
      ((({1, t, s, t * s} : Finset C)) : Set C) := by
    ext v
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · exact hVmem v
    · rintro (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hV4 : Nat.card (Subgroup.closure ({t, s} : Set C)) = 4 := by
    have h : Nat.card (Subgroup.closure ({t, s} : Set C)) =
        Nat.card ((({1, t, s, t * s} : Finset C)) : Set C) := Nat.card_congr (Set.equivOfEq hVset)
    rw [h, Nat.card_eq_card_toFinset, Finset.toFinset_coe]
    have hne1 : (1 : C) ∉ ({t, s, t * s} : Finset C) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ht1, Ne.symm hs1, Ne.symm hts1⟩
    have hnet : t ∉ ({s, t * s} : Finset C) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨Ne.symm hst, fun h => hs1 ?_⟩
      calc s = t⁻¹ * (t * s) := by group
        _ = 1 := by rw [← h, inv_mul_cancel]
    have hnes : s ∉ ({t * s} : Finset C) := by
      simp only [Finset.mem_singleton]
      intro h
      apply ht1
      calc t = t * s * s⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel]
    rw [Finset.card_insert_of_notMem hne1, Finset.card_insert_of_notMem hnet,
      Finset.card_insert_of_notMem hnes, Finset.card_singleton]
  have hVD : ∀ v ∈ Subgroup.closure ({t, s} : Set C),
      v ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : s * v = v * s := by
      rcases hVmem v hv with rfl | rfl | rfl | rfl
      · rw [one_mul, mul_one]
      · exact hts.symm
      · rfl
      · rw [← mul_assoc, ← hts]
    exact (Commute.zpow_left hc k).eq
  have hcardD : Nat.card (Subgroup.centralizer (Subgroup.zpowers s : Set C)) =
      4 * Nat.card E := by
    let φ : Subgroup.closure ({t, s} : Set C) × E →
        Subgroup.centralizer (Subgroup.zpowers s : Set C) :=
      fun p => ⟨(p.1 : C) * p.2, Subgroup.mul_mem _ (hVD _ p.1.2) (hED p.2.2)⟩
    have hφ : Function.Bijective φ := by
      constructor
      · rintro ⟨v, e⟩ ⟨v', e'⟩ h
        have h' : (v : C) * e = v' * e' := congrArg Subtype.val h
        have hmem : (v' : C)⁻¹ * v = e' * (e : C)⁻¹ := by
          calc (v' : C)⁻¹ * v = (v' : C)⁻¹ * (v * e) * (e : C)⁻¹ := by group
            _ = (v' : C)⁻¹ * (v' * e') * (e : C)⁻¹ := by rw [h']
            _ = e' * (e : C)⁻¹ := by group
        have hinter : (v' : C)⁻¹ * v ∈ Subgroup.closure ({t, s} : Set C) ⊓ E :=
          ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ v'.2) v.2, by
            rw [hmem]; exact Subgroup.mul_mem _ e'.2 (Subgroup.inv_mem _ e.2)⟩
        rw [hVE, Subgroup.mem_bot] at hinter
        have hvv : (v : C) = v' := by
          calc (v : C) = v' * ((v' : C)⁻¹ * v) := by group
            _ = v' := by rw [hinter, mul_one]
        have hee : (e : C) = e' := by
          calc (e : C) = (v : C)⁻¹ * (v * e) := by group
            _ = (v' : C)⁻¹ * (v' * e') := by rw [h', hvv]
            _ = e' := by group
        exact Prod.ext (Subtype.ext hvv) (Subtype.ext hee)
      · rintro ⟨x, hx⟩
        obtain ⟨v, hv, e, he, rfl⟩ := hDVE x hx
        exact ⟨(⟨v, hv⟩, ⟨e, he⟩), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, hV4]
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup (Subgroup.centralizer (Subgroup.zpowers s : Set C)),
      E' = E.subgroupOf (Subgroup.centralizer (Subgroup.zpowers s : Set C)) := ⟨_, rfl⟩
  have hE'mem : ∀ x : Subgroup.centralizer (Subgroup.zpowers s : Set C), x ∈ E' ↔ (x : C) ∈ E :=
    fun x => by rw [hE', Subgroup.mem_subgroupOf]
  have hE'N : E'.Normal := by
    constructor
    intro n hn g
    rw [hE'mem] at hn ⊢
    apply hoddE _ (g * n * g⁻¹).2
    have h := (MulAut.conj (g : C)).orderOf_eq (n : C)
    rw [MulAut.conj_apply] at h
    change Odd (orderOf ((g : C) * n * (g : C)⁻¹))
    rw [h]
    exact hoddEord _ hn
  have hcardE' : Nat.card E' = Nat.card E := by
    rw [hE']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv
  have hcardQ : Nat.card (Subgroup.centralizer (Subgroup.zpowers s : Set C) ⧸ E') = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup E'
    rw [hcardD, hcardE'] at h
    have hE0 : 0 < Nat.card E := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hE0 h).symm
  have hcopE' : Nat.Coprime 2 (Nat.card E') := by
    rw [hcardE']
    exact Nat.coprime_two_left.mpr hEodd
  have hsqQ : ∀ q : Subgroup.centralizer (Subgroup.zpowers s : Set C) ⧸ E', q * q = 1 := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hE'mem]
    obtain ⟨v, hv, e, he, hde⟩ := hDVE d d.2
    have hdd : ((d * d : Subgroup.centralizer (Subgroup.zpowers s : Set C)) : C) = e * e := by
      rw [Subgroup.coe_mul, hde]
      calc v * e * (v * e) = v * (e * v) * e := by group
        _ = v * (v * e) * e := by rw [hVcomm v hv e (hED he)]
        _ = (v * v) * (e * e) := by group
        _ = e * e := by rw [hV2 v hv, one_mul]
    rw [hdd]
    exact Subgroup.mul_mem _ he he
  have hQp : IsPGroup 2 (Subgroup.centralizer (Subgroup.zpowers s : Set C) ⧸ E') := by
    intro q
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact hsqQ q
  have hcentD : ∀ x : Subgroup.centralizer (Subgroup.zpowers s : Set C),
      x * ⟨s, element_mem_centralizer_zpowers s⟩ = ⟨s, element_mem_centralizer_zpowers s⟩ * x :=
    fun x => Subtype.ext (hsD x x.2).symm
  obtain ⟨Fs, hFs⟩ : ∃ Fs : Subgroup.centralizer (Subgroup.zpowers s : Set C) ⧸ E' → ℂ,
      Fs = fun q => if q = ((⟨s, element_mem_centralizer_zpowers s⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') then 4 else 0 :=
    ⟨_, rfl⟩
  have hsQcent : ∀ q : Subgroup.centralizer (Subgroup.zpowers s : Set C) ⧸ E',
      q * ((⟨s, element_mem_centralizer_zpowers s⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') =
      ((⟨s, element_mem_centralizer_zpowers s⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') * q := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcentD d]
  have hFsclass : ∀ x y : Subgroup.centralizer (Subgroup.zpowers s : Set C) ⧸ E',
      Fs (y * x * y⁻¹) = Fs x := by
    intro x y
    rw [hFs]
    have hiff : y * x * y⁻¹ = ((⟨s, element_mem_centralizer_zpowers s⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') ↔
        x = ((⟨s, element_mem_centralizer_zpowers s⟩ :
          Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') := by
      constructor
      · intro h
        calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
          _ = _ := by rw [h, mul_assoc, ← hsQcent y, ← mul_assoc, inv_mul_cancel, one_mul]
      · rintro rfl
        rw [hsQcent y, mul_inv_cancel_right]
    simp only [hiff]
  have hQs : ∀ x : Subgroup.centralizer (Subgroup.zpowers s : Set C),
      x ∈ involutionLocalSection s ↔ (x : _ ⧸ E') = ((⟨s, element_mem_centralizer_zpowers s⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') := by
    intro x
    rw [eq_comm, QuotientGroup.eq, hE'mem]
    constructor
    · rintro ⟨z, rfl, hz⟩
      have hz' : ((⟨s, element_mem_centralizer_zpowers s⟩ :
          Subgroup.centralizer (Subgroup.zpowers s : Set C))⁻¹ *
            (⟨s, element_mem_centralizer_zpowers s⟩ * z) :
          Subgroup.centralizer (Subgroup.zpowers s : Set C)) = z := by group
      rw [hz']
      exact hoddE _ z.2 (by rw [Subgroup.orderOf_coe]; exact hz)
    · intro hmem
      refine ⟨(⟨s, element_mem_centralizer_zpowers s⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C))⁻¹ * x, by group, ?_⟩
      rw [← Subgroup.orderOf_coe]
      exact hoddEord _ hmem
  have hloc : ∀ (ν : Subgroup.centralizer (Subgroup.zpowers s : Set C) →* ℂˣ) (μ' : E →* ℂˣ)
      (n : localBasis.index), (∀ x, (localBasis.representation n).character x = ν x) →
      (∀ (x : Subgroup.centralizer (Subgroup.zpowers s : Set C)) (v : C) (e : E),
        v ∈ Subgroup.closure ({t, s} : Set C) → (x : C) = v * e → ν x = μ' e) →
      (fun x => (ν x : ℂ) * Fs (x : _ ⧸ E')) ∈
          coefficientVirtualLattice localBasis
            (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) ∧
        coefficientCharacterSpace localBasis
            (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) ⊓
          sectionSupported (involutionLocalSection s) =
            Submodule.span ℂ {fun x => (ν x : ℂ) * Fs (x : _ ⧸ E')} ∧
        BlocksInnerProduct (fun x => (ν x : ℂ) * Fs (x : _ ⧸ E'))
          (fun x => (ν x : ℂ) * Fs (x : _ ⧸ E')) = 4 ∧
        ∀ e : E, (fun x => (ν x : ℂ) * Fs (x : _ ⧸ E'))
          ((⟨s, element_mem_centralizer_zpowers s⟩ :
            Subgroup.centralizer (Subgroup.zpowers s : Set C)) * ⟨e, hED e.2⟩) = 4 * μ' e := by
    intro ν μ' n hn hν
    obtain ⟨-, hex, hspan⟩ := linear_twist_prime_complement_block_and_class_functions localBasis
      ideal 2 E' hcopE' hQp ν n hn
    have hmemspan : (fun x => (ν x : ℂ) * Fs (x : _ ⧸ E')) ∈ coefficientCharacterSpace localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) :=
      (hspan _).mpr ⟨Fs, hFsclass, fun c => rfl⟩
    have hsupp : ∀ x, x ∉ involutionLocalSection s → (ν x : ℂ) * Fs (x : _ ⧸ E') = 0 := by
      intro x hx
      rw [hFs]
      dsimp only
      rw [ite_eq_right (fun h => hx ((hQs x).mpr h)), mul_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      obtain ⟨qb⟩ := finiteIrreducibleCharacterBasis_exists
        (G := Subgroup.centralizer (Subgroup.zpowers s : Set C) ⧸ E')
      choose ψ hψ hψval using fun lam : qb.index => hex (qb.representation lam) (qb.irreducible lam)
      have hsq : ((⟨s, element_mem_centralizer_zpowers s⟩ :
          Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') ^ 2 = 1 := by
        rw [pow_two]
        exact hsqQ _
      have hint : ∀ lam : qb.index, ∃ z : ℤ, (qb.representation lam).character
          ((⟨s, element_mem_centralizer_zpowers s⟩ :
            Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') = z := by
        intro lam
        obtain ⟨m, m', hmm, -⟩ := KleinFourColumns.involution_character_split
          (qb.representation lam) _ hsq
        exact ⟨(m : ℤ) - m', by push_cast; exact hmm⟩
      choose z hz using hint
      have hinv : ((⟨s, element_mem_centralizer_zpowers s⟩ :
          Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E')⁻¹ =
          ((⟨s, element_mem_centralizer_zpowers s⟩ :
            Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') :=
        inv_eq_of_mul_eq_one_left (hsqQ _)
      have hcoef : ∀ lam : qb.index, characterPairing Fs (qb.representation lam).character =
          (qb.representation lam).character ((⟨s, element_mem_centralizer_zpowers s⟩ :
            Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') := by
        intro lam
        unfold characterPairing
        rw [hFs]
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hinv,
          hcardQ]
        ring
      have hexpand : (fun x => (ν x : ℂ) * Fs (x : _ ⧸ E')) =
          ∑ lam : qb.index, (z lam) • (localBasis.representation (ψ lam)).character := by
        funext x
        rw [Finset.sum_apply, finiteIrreducibleCharacterBasis_reconstruction qb Fs
          (fun a b => hFsclass a b) (x : _ ⧸ E'), Finset.mul_sum]
        refine Finset.sum_congr rfl fun lam _ => ?_
        rw [Pi.smul_apply, zsmul_eq_mul, hcoef, hz, hψval lam x]
        simp only [QuotientGroup.mk'_apply]
        ring
      rw [hexpand]
      exact Submodule.sum_mem _ fun lam _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨ψ lam, hψ lam, rfl⟩)
    ·
      apply le_antisymm
      · intro f hf
        obtain ⟨hfspan, hfsupp⟩ := Submodule.mem_inf.mp hf
        obtain ⟨F, -, hfF⟩ := (hspan f).mp hfspan
        rw [Submodule.mem_span_singleton]
        refine ⟨F ((⟨s, element_mem_centralizer_zpowers s⟩ :
          Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') / 4, ?_⟩
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        by_cases hx : (x : _ ⧸ E') = ((⟨s, element_mem_centralizer_zpowers s⟩ :
            Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E')
        · rw [hfF x, hFs]
          change _ * ((ν x : ℂ) * (if (x : _ ⧸ E') = _ then 4 else 0)) =
            (ν x : ℂ) * F (x : _ ⧸ E')
          rw [ite_eq_left hx, hx]
          ring
        · have hx' : x ∉ involutionLocalSection s := fun h => hx ((hQs x).mp h)
          rw [hfsupp x hx', hsupp x hx', mul_zero]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.mem_inf.mpr ⟨hmemspan, hsupp⟩
    ·
      unfold BlocksInnerProduct
      have hterm : ∀ x : Subgroup.centralizer (Subgroup.zpowers s : Set C),
          (ν x : ℂ) * Fs (x : _ ⧸ E') * starRingEnd ℂ ((ν x : ℂ) * Fs (x : _ ⧸ E')) =
            if (x : _ ⧸ E') = ((⟨s, element_mem_centralizer_zpowers s⟩ :
              Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') then 16 else 0 := by
        intro x
        rw [hFs]
        dsimp only
        split_ifs with hx
        · have hroot : ((ν x : ℂˣ) : ℂ) ^ Nat.card (Subgroup.centralizer
              (Subgroup.zpowers s : Set C)) = 1 := by
            rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
          rw [map_mul, complex_root_conjugate_inverse hroot Nat.card_pos.ne']
          have hν0 : ((ν x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
          field_simp
          simp only [map_ofNat]
          norm_num
        · simp
      rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_filter, Finset.sum_const,
        card_filter_mk_eq, nsmul_eq_mul, hcardE', hcardD]
      have hE0 : (Nat.card E : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := E)).ne'
      push_cast
      field_simp
      norm_num
    ·
      intro e
      dsimp only
      have hval := hν (⟨s, element_mem_centralizer_zpowers s⟩ * ⟨e, hED e.2⟩) s e
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) rfl
      rw [hval, hFs]
      dsimp only
      have hmk : ((((⟨s, element_mem_centralizer_zpowers s⟩ :
          Subgroup.centralizer (Subgroup.zpowers s : Set C)) * ⟨e, hED e.2⟩ :
            Subgroup.centralizer (Subgroup.zpowers s : Set C))) : _ ⧸ E') =
          ((⟨s, element_mem_centralizer_zpowers s⟩ :
            Subgroup.centralizer (Subgroup.zpowers s : Set C)) : _ ⧸ E') := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr ((hE'mem ⟨e, hED e.2⟩).mpr e.2),
          mul_one]
      rw [ite_eq_left hmk]
      ring
  obtain ⟨a₀, ha₀⟩ : ∃ a : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ,
      a = fun x => (ν₀ x : ℂ) * Fs (x : _ ⧸ E') := ⟨_, rfl⟩
  obtain ⟨a₁, ha₁⟩ : ∃ a : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ,
      a = fun x => (ν₁ x : ℂ) * Fs (x : _ ⧸ E') := ⟨_, rfl⟩
  obtain ⟨hint₀, hspan₀, hnorm₀, hval₀⟩ := hloc ν₀ μ n₀ hn₀ hν₀
  obtain ⟨hint₁, hspan₁, hnorm₁, hval₁⟩ := hloc ν₁ μ₁ n₁ hn₁ hν₁
  rw [← ha₀] at hint₀ hspan₀ hnorm₀ hval₀
  rw [← ha₁] at hint₁ hspan₁ hnorm₁ hval₁
  have hβne : coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀ ≠
      coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁ := by
    intro h
    obtain ⟨hdesc₁, -, -⟩ := linear_twist_prime_complement_block_and_class_functions localBasis
      ideal 2 E' hcopE' hQp ν₁ n₁ hn₁
    have hmem : n₀ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁ := by
      rw [← h]
      exact coefficientBlock_self_mem _ _ n₀
    obtain ⟨lam, -, hlamval⟩ := (hdesc₁ n₀).mp hmem
    have h1 := hlamval 1
    rw [hn₀, map_one, map_one, Units.val_one, one_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk_one] at h1
    apply hμne
    ext e
    have hx := hlamval ⟨e, hED e.2⟩
    have hEx : QuotientGroup.mk' E' (⟨e, hED e.2⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hE'mem]
      exact e.2
    rw [hn₀, hν₀ _ 1 e (Subgroup.one_mem _) (by simp), hν₁ _ 1 e (Subgroup.one_mem _) (by simp),
      hEx, ← h1, mul_one] at hx
    exact hx.symm
  obtain ⟨-, horth, eX, heX, heXsymm, hisoX⟩ :=
    brauer_fiber_involution_section_induction_decomposition basis ideal s hs hgroup localBasis
      label
  have hβ₀T : coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀ ∈
      brauerFiberBlocks basis ideal 2 s hgroup localBasis label := by
    rw [hfiber]
    exact Finset.mem_insert_self _ _
  have hβ₁T : coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁ ∈
      brauerFiberBlocks basis ideal 2 s hgroup localBasis label := by
    rw [hfiber]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have ha₀V : a₀ ∈ coefficientCharacterSpace localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₀) ⊓
        sectionSupported (involutionLocalSection s) := by
    rw [hspan₀]
    exact Submodule.mem_span_singleton_self _
  have ha₁V : a₁ ∈ coefficientCharacterSpace localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n₁) ⊓
        sectionSupported (involutionLocalSection s) := by
    rw [hspan₁]
    exact Submodule.mem_span_singleton_self _
  have ha₀M : a₀ ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)) :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hβ₀T ha₀V)
  have ha₁M : a₁ ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)) :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hβ₁T ha₁V)
  have hMspan : ∀ F ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)),
      ∃ c₀ c₁ : ℂ, c₀ • a₀ + c₁ • a₁ = F := by
    intro F hF
    have hle : (⨆ b' ∈ brauerFiberBlocks basis ideal 2 s hgroup localBasis label,
        coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection s)) ≤
        Submodule.span ℂ {a₀, a₁} := by
      refine iSup₂_le fun b' hb' => ?_
      rw [hfiber, Finset.mem_insert, Finset.mem_singleton] at hb'
      rcases hb' with rfl | rfl
      · rw [hspan₀]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      · rw [hspan₁]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact Submodule.mem_span_pair.mp (hle hF)
  obtain ⟨Θ₀, hΘ₀⟩ : ∃ Θ : C → ℂ,
      Θ = inducedFunction (Subgroup.centralizer (Subgroup.zpowers s : Set C)) a₀ := ⟨_, rfl⟩
  obtain ⟨Θ₁, hΘ₁⟩ : ∃ Θ : C → ℂ,
      Θ = inducedFunction (Subgroup.centralizer (Subgroup.zpowers s : Set C)) a₁ := ⟨_, rfl⟩
  have hΘ₀e : (eX ⟨a₀, ha₀M⟩ : C → ℂ) = Θ₀ := by rw [heX, hΘ₀]
  have hΘ₁e : (eX ⟨a₁, ha₁M⟩ : C → ℂ) = Θ₁ := by rw [heX, hΘ₁]
  have hΘ₀W : Θ₀ ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion s) := by
    rw [← hΘ₀e]
    exact (eX _).2
  have hΘ₁W : Θ₁ ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion s) := by
    rw [← hΘ₁e]
    exact (eX _).2
  have hΘQ : ∀ x ∈ involutionLocalSection s, Θ₀ x = a₀ x ∧ Θ₁ x = a₁ x := by
    intro x hx
    have h0 := congrFun (congrArg Subtype.val (eX.symm_apply_apply ⟨a₀, ha₀M⟩)) x
    have h1 := congrFun (congrArg Subtype.val (eX.symm_apply_apply ⟨a₁, ha₁M⟩)) x
    rw [heXsymm, hΘ₀e] at h0
    rw [heXsymm, hΘ₁e] at h1
    unfold characterFunctionMask at h0 h1
    rw [ite_eq_left hx] at h0 h1
    exact ⟨h0, h1⟩
  have hΘvirt : Θ₀ ∈ virtualCharacters C ∧ Θ₁ ∈ virtualCharacters C := by
    rw [hΘ₀, hΘ₁]
    exact ⟨inducedFunction_mem_virtualCharacters _
      (coefficientVirtualLattice_le_virtual localBasis _ hint₀),
      inducedFunction_mem_virtualCharacters _
        (coefficientVirtualLattice_le_virtual localBasis _ hint₁)⟩
  have hvchar : ∀ F ∈ virtualCharacters C, F ∈ BlocksVChar C := fun F hF => by
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
    exact hF
  have hgram00 : characterPairing Θ₀ Θ₀ = 4 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (hvchar _ hΘvirt.1), ← hΘ₀e, hisoX]
    exact hnorm₀
  have hgram11 : characterPairing Θ₁ Θ₁ = 4 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (hvchar _ hΘvirt.2), ← hΘ₁e, hisoX]
    exact hnorm₁
  have hgram01 : characterPairing Θ₀ Θ₁ = 0 := by
    rw [← blocksInnerProduct_eq_characterPairing _ (hvchar _ hΘvirt.2), ← hΘ₀e, ← hΘ₁e, hisoX]
    exact horth _ hβ₀T _ hβ₁T hβne a₀ ha₀V a₁ ha₁V
  have hXspan : ∀ F ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion s),
      ∃ c₀ c₁ : ℂ, F = c₀ • Θ₀ + c₁ • Θ₁ := by
    intro F hF
    obtain ⟨c₀, c₁, hc⟩ := hMspan _ (eX.symm ⟨F, hF⟩).2
    refine ⟨c₀, c₁, ?_⟩
    have h1 : inducedFunction (Subgroup.centralizer (Subgroup.zpowers s : Set C))
        (eX.symm ⟨F, hF⟩ : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ) = F := by
      have h0 := congrArg Subtype.val (eX.apply_symm_apply ⟨F, hF⟩)
      rw [heX] at h0
      exact h0
    rw [← h1, ← hc, hΘ₀, hΘ₁]
    exact (inducedFunctionComplexLinearMap _).map_add _ _ |>.trans (by
      rw [(inducedFunctionComplexLinearMap _).map_smul,
        (inducedFunctionComplexLinearMap _).map_smul]
      rfl)
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) label with hB
  have hint : ∀ χ : basis.index,
      ∃ n : ℤ, characterPairing Θ₀ (basis.representation χ).character = n :=
    fun χ => characterPairing_virtual_integer _ _ hΘvirt.1 (character_mem_virtualCharacters _)
  choose u hu using hint
  have hΘ₀exp : ∀ x, Θ₀ x = ∑ χ ∈ B, (u χ : ℂ) * (basis.representation χ).character x := by
    intro x
    have h := characterSubsetProjection_identity basis _ Θ₀ (Submodule.mem_inf.mp hΘ₀W).1
    rw [← h, BrauerSecondMain.characterSubsetProjection_apply_sum]
    exact Finset.sum_congr rfl fun χ _ => by rw [hu χ]
  choose σ hσ hσval using fun χ => central_involution_sign basis t htcent ht2 χ
  have hXt : ∀ x, x ∈ involutionSectionUnion s → t * x ∈ involutionSectionUnion s := by
    rintro x ⟨g, q, ⟨z, rfl, hzodd⟩, rfl⟩
    have hzE : (z : C) ∈ E := hoddE _ z.2 (by rw [Subgroup.orderOf_coe]; exact hzodd)
    have hz'D : y⁻¹ * (z : C) * y ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C) :=
      hED (hyE _ hzE)
    have hz'odd : Odd (orderOf (⟨y⁻¹ * (z : C) * y, hz'D⟩ :
        Subgroup.centralizer (Subgroup.zpowers s : Set C))) := by
      rw [← Subgroup.orderOf_coe]
      have h := (MulAut.conj y⁻¹).orderOf_eq (z : C)
      rw [MulAut.conj_apply, inv_inv] at h
      change Odd (orderOf (y⁻¹ * (z : C) * y))
      rw [h, Subgroup.orderOf_coe]
      exact hzodd
    refine ⟨g * y, ⟨s, element_mem_centralizer_zpowers s⟩ * ⟨y⁻¹ * (z : C) * y, hz'D⟩,
      ⟨_, rfl, hz'odd⟩, ?_⟩
    change t * (g * (s * (z : C)) * g⁻¹) = g * y * (s * (y⁻¹ * (z : C) * y)) * (g * y)⁻¹
    have e1 : t * (g * (s * (z : C)) * g⁻¹) = (t * g) * (s * (z : C)) * g⁻¹ := by group
    have e2 : g * y * (s * (y⁻¹ * (z : C) * y)) * (g * y)⁻¹ =
        g * (y * s * y⁻¹) * (z : C) * g⁻¹ := by group
    rw [e1, e2, ← htcent g, hys]
    group
  have hXt' : ∀ x, t * x ∈ involutionSectionUnion s → x ∈ involutionSectionUnion s := by
    intro x hx
    have h := hXt _ hx
    rwa [← mul_assoc, ht2, one_mul] at h
  have hTW : (fun x => Θ₀ (t * x)) ∈ coefficientCharacterSpace basis B ⊓
      sectionSupported (involutionSectionUnion s) := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have heq : (fun x => Θ₀ (t * x)) = ∑ χ ∈ B,
          ((u χ : ℂ) * σ χ) • (basis.representation χ).character := by
        funext x
        rw [hΘ₀exp, Finset.sum_apply]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [hσval χ x, Pi.smul_apply, smul_eq_mul]
        ring
      rw [heq]
      exact Submodule.sum_mem _ fun χ hχ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, hχ, rfl⟩)
    · intro x hx
      exact (Submodule.mem_inf.mp hΘ₀W).2 _ (fun h => hx (hXt' x h))
  obtain ⟨c₀, c₁, hc⟩ := hXspan _ hTW
  have hsE : ∀ e : E, (⟨s, element_mem_centralizer_zpowers s⟩ * ⟨e, hED e.2⟩ :
      Subgroup.centralizer (Subgroup.zpowers s : Set C)) ∈ involutionLocalSection s :=
    fun e => ⟨⟨e, hED e.2⟩, rfl, by rw [← Subgroup.orderOf_coe]; exact hoddEord e e.2⟩
  have hΘsE : ∀ e : E, Θ₀ (s * e) = 4 * μ e ∧ Θ₁ (s * e) = 4 * μ₁ e := by
    intro e
    obtain ⟨h0, h1⟩ := hΘQ _ (hsE e)
    exact ⟨h0.trans (hval₀ e), h1.trans (hval₁ e)⟩
  have hcμ : ∀ e : E, 4 * (μ₁ e : ℂ) = c₀ * (4 * μ e) + c₁ * (4 * μ₁ e) := by
    intro e
    have h := congrFun hc (s * e)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [(hΘsE e).1, (hΘsE e).2] at h
    rw [← h]
    have hconj : Θ₀ (y⁻¹ * (t * (s * e)) * y⁻¹⁻¹) = Θ₀ (t * (s * e)) := by
      rw [hΘ₀]
      exact inducedFunction_conjugate _ _ _ _
    rw [← hconj]
    have he' : y⁻¹ * (e : C) * y ∈ E := hyE e e.2
    have heq : y⁻¹ * (t * (s * e)) * y⁻¹⁻¹ = s * ((⟨y⁻¹ * e * y, he'⟩ : E) : C) := by
      rw [inv_inv]
      calc y⁻¹ * (t * (s * e)) * y = (y⁻¹ * (t * s) * y) * (y⁻¹ * e * y) := by group
        _ = s * (y⁻¹ * e * y) := by rw [hys']
    rw [heq, (hΘsE ⟨_, he'⟩).1, hμ₁ e ⟨_, he'⟩ rfl]
  have hc1 : c₀ + c₁ = 1 := by
    have h := hcμ 1
    rw [map_one, map_one, Units.val_one] at h
    linear_combination -h / 4
  obtain ⟨e₀, he₀⟩ : ∃ e : E, (μ e : ℂ) ≠ μ₁ e := by
    by_contra hall
    push Not at hall
    exact hμne (MonoidHom.ext fun e => Units.ext (hall e).symm)
  have hc0 : c₀ = 0 := by
    have h := hcμ e₀
    have h' : c₀ * (4 * ((μ e₀ : ℂ) - μ₁ e₀)) = 0 := by
      linear_combination -h - 4 * (μ₁ e₀ : ℂ) * hc1
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h''
    · exact absurd (sub_eq_zero.mp ((mul_eq_zero.mp h'').resolve_left (by norm_num))) he₀
  have hc1' : c₁ = 1 := by rw [hc0, zero_add] at hc1; exact hc1
  have hT : ∀ x, Θ₀ (t * x) = Θ₁ x := by
    intro x
    have h := congrFun hc x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h, hc0, hc1', zero_mul, zero_add, one_mul]
  have hΘ₁exp : ∀ x, Θ₁ x = ∑ χ ∈ B,
      ((u χ : ℂ) * σ χ) * (basis.representation χ).character x := by
    intro x
    rw [← hT x, hΘ₀exp]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hσval χ x]
    ring
  have hΘ₀fun : Θ₀ = fun x => ∑ χ ∈ B, (u χ : ℂ) * (basis.representation χ).character x :=
    funext hΘ₀exp
  have hΘ₁fun : Θ₁ = fun x => ∑ χ ∈ B,
      ((u χ : ℂ) * σ χ) * (basis.representation χ).character x :=
    funext hΘ₁exp
  have hpair0 : ∀ ρ, characterPairing (basis.representation ρ).character Θ₀ = u ρ := fun ρ => by
    rw [characterPairing_comm, hu ρ]
  have hpair1 : ∀ ρ ∈ B, characterPairing Θ₁ (basis.representation ρ).character =
      (u ρ : ℂ) * σ ρ := by
    intro ρ hρ
    rw [hΘ₁fun, KleinFourColumns.pairing_finset_sum_left]
    simp only [KleinFourColumns.pairing_basis, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' B ρ, ite_eq_left hρ]
  have hpair1' : ∀ ρ ∈ B, characterPairing (basis.representation ρ).character Θ₁ =
      (u ρ : ℂ) * σ ρ := fun ρ hρ => by rw [characterPairing_comm, hpair1 ρ hρ]
  have hG1 : ∑ χ ∈ B, u χ * u χ = 4 := by
    have h : characterPairing (fun x => ∑ χ ∈ B,
        (u χ : ℂ) * (basis.representation χ).character x) Θ₀ = 4 := by
      rw [← hΘ₀fun]
      exact hgram00
    rw [KleinFourColumns.pairing_finset_sum_left] at h
    simp only [hpair0] at h
    exact_mod_cast h
  have hG2 : ∑ χ ∈ B, u χ * (u χ * σ χ) = 0 := by
    have h : characterPairing (fun x => ∑ χ ∈ B,
        (u χ : ℂ) * (basis.representation χ).character x) Θ₁ = 0 := by
      rw [← hΘ₀fun]
      exact hgram01
    rw [KleinFourColumns.pairing_finset_sum_left] at h
    have h' : ∑ χ ∈ B, (u χ : ℂ) * ((u χ : ℂ) * σ χ) = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun χ hχ => by rw [hpair1' χ hχ]
    exact_mod_cast h'
  have h1X : (1 : C) ∉ involutionSectionUnion s := fun h => by
    have h' := KleinFourColumns.even_orderOf_of_mem_involutionSectionUnion hs 1 h
    rw [orderOf_one] at h'
    exact Nat.not_even_one h'
  have hchar1 : ∀ χ, (basis.representation χ).character 1 =
      (Module.finrank ℂ (basis.representation χ).vector : ℂ) := fun χ => by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  have hG3 : ∑ χ ∈ B, u χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
    have h := hΘ₀exp 1
    rw [(Submodule.mem_inf.mp hΘ₀W).2 1 h1X] at h
    simp only [hchar1] at h
    exact_mod_cast h.symm
  have hG4 : ∑ χ ∈ B, u χ * σ χ *
      (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
    have h := hΘ₁exp 1
    rw [(Submodule.mem_inf.mp hΘ₁W).2 1 h1X] at h
    simp only [hchar1] at h
    exact_mod_cast h.symm
  have hdeg : ∀ χ, 0 < Module.finrank ℂ (basis.representation χ).vector := fun χ => by
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [hchar1] at h
    exact Nat.pos_of_ne_zero (by exact_mod_cast h)
  have hpair : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ∃ χ₁ χ₂ : basis.index,
      χ₁ ∈ B ∧ χ₂ ∈ B ∧ σ χ₁ = ε ∧ σ χ₂ = ε ∧ u χ₁ = 1 ∧ u χ₂ = -1 ∧
      Module.finrank ℂ (basis.representation χ₁).vector =
        Module.finrank ℂ (basis.representation χ₂).vector ∧
      ∀ χ ∈ B, σ χ = ε → χ ≠ χ₁ → χ ≠ χ₂ → u χ = 0 := by
    intro ε hε
    obtain ⟨w, hw⟩ : ∃ w : basis.index → ℤ,
        w = fun χ => if χ ∈ B ∧ σ χ = ε then u χ else 0 := ⟨_, rfl⟩
    have hwsq : ∀ χ, 2 * w χ ^ 2 =
        if χ ∈ B then u χ * u χ + ε * (u χ * (u χ * σ χ)) else 0 := by
      intro χ
      rw [hw]
      dsimp only
      by_cases hχ : χ ∈ B
      · rcases hσ χ with h | h <;> rcases hε with h' | h' <;> simp [hχ, h, h'] <;> ring
      · simp [hχ]
    have hwdeg : ∀ χ, 2 * (w χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ)) =
        if χ ∈ B then u χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ) +
          ε * (u χ * σ χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ)) else 0 := by
      intro χ
      rw [hw]
      dsimp only
      by_cases hχ : χ ∈ B
      · rcases hσ χ with h | h <;> rcases hε with h' | h' <;> simp [hχ, h, h'] <;> ring
      · simp [hχ]
    have hnorm : ∑ χ, w χ ^ 2 = 2 := by
      have h : ∑ χ, 2 * w χ ^ 2 = 4 := by
        rw [Finset.sum_congr rfl fun χ _ => hwsq χ, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_add_distrib, ← Finset.mul_sum, hG1, hG2]
        ring
      rw [← Finset.mul_sum] at h
      linarith
    have hdsum : ∑ χ, w χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
      have h : ∑ χ, 2 * (w χ * (Module.finrank ℂ (basis.representation χ).vector : ℤ)) = 0 := by
        rw [Finset.sum_congr rfl fun χ _ => hwdeg χ, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_add_distrib, ← Finset.mul_sum, hG3, hG4]
        ring
      rw [← Finset.mul_sum] at h
      linarith
    obtain ⟨χ₁, χ₂, h12, h1, h2, hother⟩ := integer_norm_two_two_coefficients w hnorm
    have hsum2 : w χ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
        w χ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) = 0 := by
      rw [← hdsum, ← Finset.sum_subset (Finset.subset_univ {χ₁, χ₂}) ?_]
      · exact (Finset.sum_pair (f := fun χ => w χ *
          (Module.finrank ℂ (basis.representation χ).vector : ℤ)) h12).symm
      · intro χ _ hχ
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hχ
        rw [hother χ hχ.1 hχ.2, zero_mul]
    have hmem : ∀ χ, w χ ≠ 0 → χ ∈ B ∧ σ χ = ε ∧ w χ = u χ := by
      intro χ hχ
      rw [hw] at hχ ⊢
      dsimp only at hχ ⊢
      split_ifs at hχ ⊢ with hc
      · exact ⟨hc.1, hc.2, rfl⟩
      · exact absurd rfl hχ
    have hzero : ∀ χ ∈ B, σ χ = ε → χ ≠ χ₁ → χ ≠ χ₂ → u χ = 0 := by
      intro χ hχ hσχ hne1 hne2
      have h := hother χ hne1 hne2
      rw [hw] at h
      dsimp only at h
      rwa [ite_eq_left ⟨hχ, hσχ⟩] at h
    have hd1 := hdeg χ₁
    have hd2 := hdeg χ₂
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      rw [h1, h2] at hsum2
      omega
    · obtain ⟨hB1, hσ1, hw1⟩ := hmem χ₁ (by rw [h1]; norm_num)
      obtain ⟨hB2, hσ2, hw2⟩ := hmem χ₂ (by rw [h2]; norm_num)
      refine ⟨χ₁, χ₂, hB1, hB2, hσ1, hσ2, by rw [← hw1, h1], by rw [← hw2, h2], ?_,
        fun χ hχ hσχ hne1 hne2 => hzero χ hχ hσχ hne1 hne2⟩
      rw [h1, h2] at hsum2
      omega
    · obtain ⟨hB1, hσ1, hw1⟩ := hmem χ₁ (by rw [h1]; norm_num)
      obtain ⟨hB2, hσ2, hw2⟩ := hmem χ₂ (by rw [h2]; norm_num)
      refine ⟨χ₂, χ₁, hB2, hB1, hσ2, hσ1, by rw [← hw2, h2], by rw [← hw1, h1], ?_,
        fun χ hχ hσχ hne2 hne1 => hzero χ hχ hσχ hne1 hne2⟩
      rw [h1, h2] at hsum2
      omega
    · exfalso
      rw [h1, h2] at hsum2
      omega
  obtain ⟨θ₀, θ₁, hθ₀B, hθ₁B, hσθ₀, hσθ₁, huθ₀, huθ₁, hdeg01, hzeroP⟩ := hpair 1 (Or.inl rfl)
  obtain ⟨θ₂, θ₃, hθ₂B, hθ₃B, hσθ₂, hσθ₃, huθ₂, huθ₃, hdeg23, hzeroM⟩ := hpair (-1) (Or.inr rfl)
  have hXsec : primeSectionUnion 2 (involutionSectionUnion s) := by
    intro u₁ u₂ v₁ v₂ e₁ e₂ hu₁ hu₂ hv₁ hv₂ hc₁ hc₂ hconj
    rw [mem_involutionSectionUnion_iff hs2 hu₁ hv₁ hc₁,
      mem_involutionSectionUnion_iff hs2 hu₂ hv₂ hc₂]
    exact ⟨fun h => hconj.symm.trans h, fun h => hconj.trans h⟩
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  have hXinv : ∀ x, x ∈ involutionSectionUnion s → x⁻¹ ∈ involutionSectionUnion s := by
    rintro x ⟨g, q, ⟨z, rfl, hzodd⟩, rfl⟩
    refine ⟨g, ⟨s, element_mem_centralizer_zpowers s⟩ * z⁻¹,
      ⟨z⁻¹, rfl, by rw [orderOf_inv]; exact hzodd⟩, ?_⟩
    have hcomm : Commute (z : C) s := (hsD z z.2).symm
    change (g * (s * (z : C)) * g⁻¹)⁻¹ = g * (s * (z : C)⁻¹) * g⁻¹
    calc (g * (s * (z : C)) * g⁻¹)⁻¹ = g * ((z : C)⁻¹ * s⁻¹) * g⁻¹ := by group
      _ = g * (s * (z : C)⁻¹) * g⁻¹ := by rw [hsinv, hcomm.inv_left.eq]
  have hXinv' : ∀ x, x ∉ involutionSectionUnion s → x⁻¹ ∉ involutionSectionUnion s :=
    fun x hx h => hx (by simpa using hXinv _ h)
  have hgram10 : characterPairing Θ₁ Θ₀ = 0 := by rw [characterPairing_comm]; exact hgram01
  have hmaskX : ∀ χ ∈ B, characterFunctionMask (involutionSectionUnion s)
      (basis.representation χ).character =
        ((u χ : ℂ) / 4) • Θ₀ + ((u χ : ℂ) * σ χ / 4) • Θ₁ := by
    intro χ hχ
    have hFW : characterFunctionMask (involutionSectionUnion s)
        (basis.representation χ).character ∈
          coefficientCharacterSpace basis B ⊓ sectionSupported (involutionSectionUnion s) := by
      refine Submodule.mem_inf.mpr ⟨coefficientBlock_section_mask_mem basis ideal 2 label _
        hXsec _ (Submodule.subset_span ⟨χ, hχ, rfl⟩), ?_⟩
      intro x hx
      unfold characterFunctionMask
      rw [ite_eq_right hx]
    obtain ⟨c₀', c₁', hc'⟩ := hXspan _ hFW
    have hmp : ∀ F : C → ℂ, F ∈ sectionSupported (involutionSectionUnion s) →
        characterPairing (characterFunctionMask (involutionSectionUnion s)
          (basis.representation χ).character) F =
            characterPairing (basis.representation χ).character F := by
      intro F hF
      unfold characterPairing characterFunctionMask
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ involutionSectionUnion s
      · rw [ite_eq_left hx]
      · rw [ite_eq_right hx, zero_mul, hF x⁻¹ (hXinv' x hx), mul_zero]
    have h0 := hmp Θ₀ (Submodule.mem_inf.mp hΘ₀W).2
    have h1 := hmp Θ₁ (Submodule.mem_inf.mp hΘ₁W).2
    rw [hc', pairing_add_smul_left, hgram00, hgram10, hpair0 χ] at h0
    rw [hc', pairing_add_smul_left, hgram01, hgram11, hpair1' χ hχ] at h1
    have hc0' : c₀' = (u χ : ℂ) / 4 := by linear_combination h0 / 4
    have hc1' : c₁' = (u χ : ℂ) * σ χ / 4 := by linear_combination h1 / 4
    rw [hc', hc0', hc1']
  have hXval : ∀ χ ∈ B, ∀ x ∈ involutionSectionUnion s, (basis.representation χ).character x =
      (u χ : ℂ) / 4 * Θ₀ x + (u χ : ℂ) * σ χ / 4 * Θ₁ x := by
    intro χ hχ x hx
    have h := congrFun (hmaskX χ hχ) x
    unfold characterFunctionMask at h
    rw [ite_eq_left hx] at h
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hnotconj1s : ¬ IsConj (1 : C) s := fun h => hs1 (isConj_one_right.mp h)
  have hnotconjts : ¬ IsConj t s := by
    intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply hst
    rw [← hc, htcent c, mul_inv_cancel_right]
  have hpart : ∀ χ ∈ B, ∀ x : C, (basis.representation χ).character x =
      characterFunctionMask {x : C | Odd (orderOf x)} (basis.representation χ).character x +
      characterFunctionMask (translatedOddSection t) (basis.representation χ).character x +
      characterFunctionMask (involutionSectionUnion s) (basis.representation χ).character x := by
    intro χ hχ x
    obtain ⟨a, v, k, -, -, hav, hprod, ha, hv⟩ :=
      finite_prime_primary_factorization x 2 Nat.prime_two
    subst hprod
    have hodd := odd_iff_two_part_eq_one ha hv hav
    have htO := mem_translatedOddSection_iff htcent ht2 ha hv hav
    have hX := mem_involutionSectionUnion_iff hs2 ha hv hav
    unfold characterFunctionMask
    by_cases h1 : a = 1
    · have hO : a * v ∈ {x : C | Odd (orderOf x)} := hodd.mpr h1
      have hT' : a * v ∉ translatedOddSection t := fun h => ht1 ((htO.mp h).symm.trans h1)
      have hX' : a * v ∉ involutionSectionUnion s := fun h => hnotconj1s (h1 ▸ hX.mp h)
      rw [ite_eq_left hO, ite_eq_right hT', ite_eq_right hX', add_zero, add_zero]
    by_cases h2 : a = t
    · have hO : a * v ∉ {x : C | Odd (orderOf x)} := fun h => h1 (hodd.mp h)
      have hT' : a * v ∈ translatedOddSection t := htO.mpr h2
      have hX' : a * v ∉ involutionSectionUnion s := fun h => hnotconjts (h2 ▸ hX.mp h)
      rw [ite_eq_right hO, ite_eq_left hT', ite_eq_right hX', zero_add, add_zero]
    by_cases h3 : IsConj a s
    · have hO : a * v ∉ {x : C | Odd (orderOf x)} := fun h => h1 (hodd.mp h)
      have hT' : a * v ∉ translatedOddSection t := fun h => h2 (htO.mp h)
      have hX' : a * v ∈ involutionSectionUnion s := hX.mpr h3
      rw [ite_eq_right hO, ite_eq_right hT', ite_eq_left hX', zero_add, zero_add]
    have hnot : ¬ subgroupSubconjugate (Subgroup.zpowers a)
        (Subgroup.closure ({t, s} : Set C)) := by
      rintro ⟨c, hc⟩
      have hmem : (MulAut.conj c) a ∈ Subgroup.closure ({t, s} : Set C) :=
        hc (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers a))
      rw [MulAut.conj_apply] at hmem
      rcases hVmem _ hmem with h | h | h | h
      · apply h1
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = 1 := by rw [h]; group
      · apply h2
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = t := by rw [h, mul_assoc, ← htcent c, ← mul_assoc, inv_mul_cancel, one_mul]
      · exact h3 (isConj_iff.mpr ⟨c, h⟩)
      · apply h3
        refine isConj_iff.mpr ⟨y⁻¹ * c, ?_⟩
        calc y⁻¹ * c * a * (y⁻¹ * c)⁻¹ = y⁻¹ * (c * a * c⁻¹) * y := by group
          _ = s := by rw [h, hys']
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
    have hzero := (block_characters_vanish_outside_defect_primary basis ideal 2 label _ hD
      (a * v) a v rfl hav ⟨j, hj⟩ hv).1 hnot χ hχ
    rw [hzero]
    simp only [ite_self, add_zero]
  have hpairsplit : ∀ χ ∈ B, ∀ ρ : basis.index,
      characterPairing (basis.representation χ).character (basis.representation ρ).character =
        characterPairing (characterFunctionMask {x : C | Odd (orderOf x)}
          (basis.representation χ).character) (basis.representation ρ).character +
        characterPairing (characterFunctionMask (translatedOddSection t)
          (basis.representation χ).character) (basis.representation ρ).character +
        characterPairing (characterFunctionMask (involutionSectionUnion s)
          (basis.representation χ).character) (basis.representation ρ).character := by
    intro χ hχ ρ
    unfold characterPairing
    rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← add_mul, ← add_mul, ← hpart χ hχ x]
  have htOdd_iff : ∀ z : C, t * z ∈ translatedOddSection t ↔ Odd (orderOf z) := by
    intro z
    constructor
    · rintro ⟨z', hz', hodd⟩
      rw [mul_left_cancel hz']
      exact hodd
    · intro hz
      exact ⟨z, rfl, hz⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hpairT : ∀ χ ρ : basis.index,
      characterPairing (characterFunctionMask (translatedOddSection t)
        (basis.representation χ).character) (basis.representation ρ).character =
        (σ χ * σ ρ : ℂ) * characterPairing (characterFunctionMask {x : C | Odd (orderOf x)}
          (basis.representation χ).character) (basis.representation ρ).character := by
    intro χ ρ
    unfold characterPairing characterFunctionMask
    have h : ∑ x : C, (if x ∈ translatedOddSection t then (basis.representation χ).character x
        else 0) * (basis.representation ρ).character x⁻¹ =
        ∑ z : C, (σ χ * σ ρ : ℂ) * ((if z ∈ {x : C | Odd (orderOf x)} then
          (basis.representation χ).character z else 0) *
            (basis.representation ρ).character z⁻¹) := by
      calc ∑ x : C, (if x ∈ translatedOddSection t then (basis.representation χ).character x
            else 0) * (basis.representation ρ).character x⁻¹
          = ∑ z : C, (if t * z ∈ translatedOddSection t then
              (basis.representation χ).character (t * z) else 0) *
                (basis.representation ρ).character (t * z)⁻¹ :=
            (Fintype.sum_equiv (Equiv.mulLeft t) _ _ (fun _ => rfl)).symm
        _ = _ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          have hinv : (t * z)⁻¹ = t * z⁻¹ := by rw [mul_inv_rev, htinv, htcent]
          by_cases hz : Odd (orderOf z)
          · rw [ite_eq_left ((htOdd_iff z).mpr hz),
              ite_eq_left (show z ∈ {x : C | Odd (orderOf x)} from hz), hinv, hσval χ z,
              hσval ρ z⁻¹]
            ring
          · rw [ite_eq_right (fun h => hz ((htOdd_iff z).mp h)),
              ite_eq_right (show z ∉ {x : C | Odd (orderOf x)} from hz)]
            ring
    rw [h, ← Finset.mul_sum]
    ring_nf
  have hA : ∀ χ ∈ B, ∀ ρ ∈ B, σ χ = σ ρ →
      oddSectionMatrix basis χ ρ = 2 * (if χ = ρ then 1 else 0) - (u χ : ℂ) * u ρ := by
    intro χ hχ ρ hρ hσχρ
    have h := hpairsplit χ hχ ρ
    rw [hpairT, hmaskX χ hχ, pairing_add_smul_left, hu ρ, hpair1 ρ hρ,
      KleinFourColumns.pairing_basis] at h
    rw [DefectFourOdd.oddSectionMatrix_eq_pairing]
    have hσ2 : (σ χ : ℂ) * σ ρ = 1 := by
      rw [hσχρ]
      rcases hσ ρ with h' | h' <;> rw [h'] <;> norm_num
    set P := characterPairing (characterFunctionMask {x : C | Odd (orderOf x)}
      (basis.representation χ).character) (basis.representation ρ).character with hP
    linear_combination (-2 : ℂ) * h - (2 * P + (u χ : ℂ) * u ρ / 2) * hσ2
  have hcover : ∀ χ ∈ B, χ = θ₀ ∨ χ = θ₁ ∨ χ = θ₂ ∨ χ = θ₃ := by
    intro χ hχ
    by_contra hne
    push Not at hne
    obtain ⟨hn0, hn1, hn2, hn3⟩ := hne
    rcases hσ χ with h | h
    · have hu0 : u χ = 0 := hzeroP χ hχ h hn0 hn1
      have hAχ := hA χ hχ θ₀ hθ₀B (h.trans hσθ₀.symm)
      rw [ite_eq_right hn0, hu0] at hAχ
      have hA00 := hA θ₀ hθ₀B θ₀ hθ₀B rfl
      rw [ite_eq_left rfl, huθ₀] at hA00
      exact oddSectionMatrix_column_ne_zero basis ideal label _ hD hV4 θ₀ hθ₀B 1 odd_one
        (by rw [hA00]; norm_num) χ hχ (by rw [hAχ]; norm_num)
    · have hu0 : u χ = 0 := hzeroM χ hχ h hn2 hn3
      have hAχ := hA χ hχ θ₂ hθ₂B (h.trans hσθ₂.symm)
      rw [ite_eq_right hn2, hu0] at hAχ
      have hA22 := hA θ₂ hθ₂B θ₂ hθ₂B rfl
      rw [ite_eq_left rfl, huθ₂] at hA22
      exact oddSectionMatrix_column_ne_zero basis ideal label _ hD hV4 θ₂ hθ₂B 1 odd_one
        (by rw [hA22]; norm_num) χ hχ (by rw [hAχ]; norm_num)
  have hθ01 : θ₀ ≠ θ₁ := fun h => by rw [h, huθ₁] at huθ₀; norm_num at huθ₀
  have hθ23 : θ₂ ≠ θ₃ := fun h => by rw [h, huθ₃] at huθ₂; norm_num at huθ₂
  have hθ02 : θ₀ ≠ θ₂ := fun h => by rw [h, hσθ₂] at hσθ₀; norm_num at hσθ₀
  have hθ03 : θ₀ ≠ θ₃ := fun h => by rw [h, hσθ₃] at hσθ₀; norm_num at hσθ₀
  have hθ12 : θ₁ ≠ θ₂ := fun h => by rw [h, hσθ₂] at hσθ₁; norm_num at hσθ₁
  have hθ13 : θ₁ ≠ θ₃ := fun h => by rw [h, hσθ₃] at hσθ₁; norm_num at hσθ₁
  have hBeq : B = {θ₀, θ₁, θ₂, θ₃} := by
    ext χ
    constructor
    · intro hχ
      rcases hcover χ hχ with rfl | rfl | rfl | rfl <;> simp
    · intro hχ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
      rcases hχ with rfl | rfl | rfl | rfl <;> assumption
  have hsumB : ∀ g : basis.index → ℂ, ∑ χ ∈ B, g χ = g θ₀ + g θ₁ + g θ₂ + g θ₃ := by
    intro g
    rw [hBeq, Finset.sum_insert (by simp [hθ01, hθ02, hθ03]),
      Finset.sum_insert (by simp [hθ12, hθ13]), Finset.sum_pair hθ23]
    ring
  have htval : ∀ χ, (basis.representation χ).character t =
      (σ χ : ℂ) * (Module.finrank ℂ (basis.representation χ).vector : ℂ) := by
    intro χ
    have h := hσval χ 1
    rw [mul_one, hchar1] at h
    exact h
  have hnotconj1t : ¬ IsConj (1 : C) t := fun h => ht1 (isConj_one_right.mp h)
  have hf02 : Module.finrank ℂ (basis.representation θ₀).vector =
      Module.finrank ℂ (basis.representation θ₂).vector := by
    have h := admissible_character_section_column_orthogonality basis ideal 2 B
      (coefficientBlock_admissible basis _ label) 1 t 1 1 0 1
      (by rw [orderOf_one]; exact one_dvd _) (by rw [ht, pow_one])
      (by rw [orderOf_one]; exact Nat.coprime_one_right 2)
      (by rw [orderOf_one]; exact Nat.coprime_one_right 2) (Commute.one_right 1)
      (Commute.one_right t) hnotconj1t
    simp only [mul_one, htinv] at h
    rw [hsumB, htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃, hchar1, hchar1,
      hchar1, hchar1, ← hdeg01, ← hdeg23] at h
    push_cast at h
    have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) ^ 2 =
        ((Module.finrank ℂ (basis.representation θ₂).vector : ℕ) : ℂ) ^ 2 := by
      linear_combination h / 2
    have h'' : (Module.finrank ℂ (basis.representation θ₀).vector) ^ 2 =
        (Module.finrank ℂ (basis.representation θ₂).vector) ^ 2 := by
      exact_mod_cast h'
    exact Nat.pow_left_injective two_ne_zero h''
  have hsX : s ∈ involutionSectionUnion s := by
    refine ⟨1, ⟨s, element_mem_centralizer_zpowers s⟩,
      ⟨1, (mul_one _).symm, by rw [orderOf_one]; exact odd_one⟩, ?_⟩
    rw [one_mul, inv_one, mul_one]
  have hΘs : Θ₀ s = 4 ∧ Θ₁ s = 4 := by
    have h := hΘsE 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one] at h
    exact h
  have hsval : ∀ χ ∈ B, (basis.representation χ).character s = (u χ : ℂ) * (1 + σ χ) := by
    intro χ hχ
    rw [hXval χ hχ s hsX, hΘs.1, hΘs.2]
    ring
  have hsEX : ∀ e : E, s * (e : C) ∈ involutionSectionUnion s := by
    intro e
    refine ⟨1, _, hsE e, ?_⟩
    rw [one_mul, inv_one, mul_one]
    rfl
  have hsEval : ∀ χ ∈ B, ∀ e : E, (basis.representation χ).character (s * e) =
      (u χ : ℂ) * ((μ e : ℂ) + σ χ * μ₁ e) := by
    intro χ hχ e
    rw [hXval χ hχ _ (hsEX e), (hΘsE e).1, (hΘsE e).2]
    ring
  have hcol : ∀ x : C, Odd (orderOf x) → ∀ (a w : C) (k : ℕ), orderOf a ∣ 2 ^ k →
      ¬ IsConj 1 a → Nat.Coprime 2 (orderOf w) → Commute a w →
      ∑ χ ∈ B, (basis.representation χ).character x *
        (basis.representation χ).character (a * w)⁻¹ = 0 := by
    intro x hx a w k ha hna hw haw
    have h := admissible_character_section_column_orthogonality basis ideal 2 B
      (coefficientBlock_admissible basis _ label) 1 a x w 0 k
      (by rw [orderOf_one]; exact one_dvd _) ha (Nat.coprime_two_left.mpr hx) hw
      (Commute.one_left x) haw hna
    simpa only [one_mul] using h
  have hoddagree : ∀ x : C, Odd (orderOf x) →
      (basis.representation θ₁).character x = (basis.representation θ₀).character x ∧
      (basis.representation θ₂).character x = (basis.representation θ₀).character x ∧
      (basis.representation θ₃).character x = (basis.representation θ₀).character x := by
    intro x hx
    have hse : ∀ e : E, (basis.representation θ₀).character x * ((μ e : ℂ) + μ₁ e) -
        (basis.representation θ₁).character x * ((μ e : ℂ) + μ₁ e) +
        (basis.representation θ₂).character x * ((μ e : ℂ) - μ₁ e) -
        (basis.representation θ₃).character x * ((μ e : ℂ) - μ₁ e) = 0 := by
      intro e
      have hcse : Commute s (e : C) := hsD e (hED e.2)
      have hinvse : (s * (e : C)⁻¹)⁻¹ = s * e := by
        rw [mul_inv_rev, inv_inv, hsinv]
        exact hcse.eq.symm
      have h := hcol x hx s (e : C)⁻¹ 1 (by rw [hs, pow_one]) hnotconj1s
        (by rw [orderOf_inv]; exact Nat.coprime_two_left.mpr (hoddEord e e.2)) hcse.inv_right
      rw [hinvse, hsumB, hsEval θ₀ hθ₀B, hsEval θ₁ hθ₁B, hsEval θ₂ hθ₂B, hsEval θ₃ hθ₃B,
        huθ₀, huθ₁, huθ₂, huθ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃] at h
      push_cast at h
      linear_combination h
    have h1 := hse 1
    rw [map_one, map_one, Units.val_one] at h1
    have h01 : (basis.representation θ₁).character x = (basis.representation θ₀).character x := by
      linear_combination -h1 / 2
    have h23 : (basis.representation θ₂).character x = (basis.representation θ₃).character x := by
      have h' : ((basis.representation θ₂).character x - (basis.representation θ₃).character x) *
          ((μ e₀ : ℂ) - μ₁ e₀) = 0 := by
        linear_combination hse e₀ + ((μ e₀ : ℂ) + μ₁ e₀) * h01
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr he₀))
    have ht' := hcol x hx t 1 1 (by rw [ht, pow_one]) hnotconj1t
      (by rw [orderOf_one]; exact Nat.coprime_one_right 2) (Commute.one_right t)
    rw [mul_one, htinv, hsumB, htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃,
      ← hdeg01, ← hdeg23, ← hf02] at ht'
    push_cast at ht'
    have hf0 : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (hdeg θ₀).ne'
    have h02 : (basis.representation θ₂).character x = (basis.representation θ₀).character x := by
      have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) *
          ((basis.representation θ₂).character x - (basis.representation θ₀).character x) = 0 := by
        linear_combination -ht' / 2 + ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) :
          ℂ) / 2 * h01 + ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) / 2 * h23
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hf0)
    exact ⟨h01, h02, by rw [← h23, h02]⟩
  have hexpV : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v ≠ 1 → orderOf v = 2 := fun v hv hv1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hV2 v hv) hv1
  have hvan4 : ∀ χ ∈ B, ∀ x : C, 4 ∣ orderOf x → (basis.representation χ).character x = 0 :=
    fun χ hχ x hx => block_characters_vanish_of_defect_exponent_prime basis ideal 2 label _ hD
      hexpV x (by norm_num; exact hx) χ hχ
  have hrest : ∀ χ ∈ B, ∀ x : C, ¬ Odd (orderOf x) → x ∉ translatedOddSection t →
      x ∉ involutionSectionUnion s → (basis.representation χ).character x = 0 := by
    intro χ hχ x hodd htx hxX
    rw [hpart χ hχ x]
    unfold characterFunctionMask
    rw [ite_eq_right (show x ∉ {x : C | Odd (orderOf x)} from hodd), ite_eq_right htx,
      ite_eq_right hxX]
    ring
  have hoddX : ∀ x : C, Odd (orderOf x) → x ∉ involutionSectionUnion s := fun x hx hX =>
    Nat.not_even_iff_odd.mpr hx
      (KleinFourColumns.even_orderOf_of_mem_involutionSectionUnion hs x hX)
  have htOddX : ∀ x ∈ translatedOddSection t, x ∉ involutionSectionUnion s := by
    rintro x ⟨z, rfl, hz⟩ hX
    exact hnotconjts ((mem_involutionSectionUnion_iff hs2 (e := 1) (by rw [ht, pow_one])
      (Nat.coprime_two_left.mpr hz) (htcent z).symm).mp hX)
  have h1tOdd : (1 : C) ∉ translatedOddSection t := by
    rintro ⟨z, hz, hodd⟩
    have hzt : z = t := by
      calc z = t⁻¹ * (t * z) := by group
        _ = t := by rw [← hz, mul_one, htinv]
    rw [hzt, ht] at hodd
    exact Nat.not_even_iff_odd.mpr hodd even_two
  have htodd : ¬ Odd (orderOf t) := by
    rw [ht]
    exact Nat.not_odd_iff_even.mpr even_two
  have hαB : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character ∈
        coefficientCharacterSpace basis B :=
    Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
      (Submodule.subset_span ⟨θ₀, hθ₀B, rfl⟩) (Submodule.subset_span ⟨θ₁, hθ₁B, rfl⟩))
        (Submodule.subset_span ⟨θ₂, hθ₂B, rfl⟩)) (Submodule.subset_span ⟨θ₃, hθ₃B, rfl⟩)
  have hαsupp : ∀ x, x ∉ translatedOddSection t →
      ((basis.representation θ₀).character + (basis.representation θ₁).character -
        (basis.representation θ₂).character - (basis.representation θ₃).character) x = 0 := by
    intro x hx
    simp only [Pi.add_apply, Pi.sub_apply]
    by_cases hodd : Odd (orderOf x)
    · obtain ⟨h1, h2, h3⟩ := hoddagree x hodd
      rw [h1, h2, h3]
      ring
    by_cases hxX : x ∈ involutionSectionUnion s
    · rw [hXval θ₀ hθ₀B x hxX, hXval θ₁ hθ₁B x hxX, hXval θ₂ hθ₂B x hxX, hXval θ₃ hθ₃B x hxX,
        huθ₀, huθ₁, huθ₂, huθ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
      push_cast
      ring
    · rw [hrest θ₀ hθ₀B x hodd hx hxX, hrest θ₁ hθ₁B x hodd hx hxX, hrest θ₂ hθ₂B x hodd hx hxX,
        hrest θ₃ hθ₃B x hodd hx hxX]
      ring
  have hαfun : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character =
      fun x => ∑ χ ∈ B, (σ χ : ℂ) * (basis.representation χ).character x := by
    funext x
    rw [hsumB, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
    simp only [Pi.add_apply, Pi.sub_apply]
    push_cast
    ring
  have hpairα : ∀ ρ ∈ B, characterPairing (fun x => ∑ χ ∈ B,
      (σ χ : ℂ) * (basis.representation χ).character x) (basis.representation ρ).character =
        σ ρ := by
    intro ρ hρ
    rw [KleinFourColumns.pairing_finset_sum_left]
    simp only [KleinFourColumns.pairing_basis, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' B ρ, ite_eq_left hρ]
  have hαvirt : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character ∈
        virtualCharacters C :=
    Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
      (character_mem_virtualCharacters _) (character_mem_virtualCharacters _))
        (character_mem_virtualCharacters _)) (character_mem_virtualCharacters _)
  have hαnorm : BlocksInnerProduct ((basis.representation θ₀).character +
      (basis.representation θ₁).character - (basis.representation θ₂).character -
        (basis.representation θ₃).character) ((basis.representation θ₀).character +
      (basis.representation θ₁).character - (basis.representation θ₂).character -
        (basis.representation θ₃).character) = 4 := by
    rw [blocksInnerProduct_eq_characterPairing _ (hvchar _ hαvirt), hαfun,
      KleinFourColumns.pairing_finset_sum_left]
    have h : ∀ χ ∈ B, (σ χ : ℂ) * characterPairing (basis.representation χ).character
        (fun x => ∑ χ ∈ B, (σ χ : ℂ) * (basis.representation χ).character x) =
          (σ χ : ℂ) * σ χ := fun χ hχ => by rw [characterPairing_comm, hpairα χ hχ]
    rw [Finset.sum_congr rfl h, hsumB, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
    norm_num
  have hαt : ((basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character) t =
        4 * (Module.finrank ℂ (basis.representation θ₀).vector : ℂ) := by
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃, ← hdeg01, ← hdeg23,
      ← hf02]
    push_cast
    ring
  have hf0 : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (hdeg θ₀).ne'
  have hα0 : (basis.representation θ₀).character + (basis.representation θ₁).character -
      (basis.representation θ₂).character - (basis.representation θ₃).character ≠ 0 := by
    intro h
    have h' := hαt
    rw [h, Pi.zero_apply] at h'
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hf0 h'.symm
  have hFexp : ∀ F ∈ coefficientCharacterSpace basis B, ∀ x, F x =
      characterPairing F (basis.representation θ₀).character *
        (basis.representation θ₀).character x +
      characterPairing F (basis.representation θ₁).character *
        (basis.representation θ₁).character x +
      characterPairing F (basis.representation θ₂).character *
        (basis.representation θ₂).character x +
      characterPairing F (basis.representation θ₃).character *
        (basis.representation θ₃).character x := by
    intro F hF x
    have h := congrFun (characterSubsetProjection_identity basis _ F hF) x
    rw [BrauerSecondMain.characterSubsetProjection_apply_sum, hsumB] at h
    exact h.symm
  have hFsum : ∀ F ∈ coefficientCharacterSpace basis B, F = fun x => ∑ χ ∈ B,
      characterPairing F (basis.representation χ).character *
        (basis.representation χ).character x := by
    intro F hF
    funext x
    have h := congrFun (characterSubsetProjection_identity basis _ F hF) x
    rw [BrauerSecondMain.characterSubsetProjection_apply_sum] at h
    exact h.symm
  have hcoefX : ∀ F ∈ coefficientCharacterSpace basis B,
      (∀ x ∈ involutionSectionUnion s, F x = 0) →
      characterPairing F (basis.representation θ₁).character =
        characterPairing F (basis.representation θ₀).character ∧
      characterPairing F (basis.representation θ₃).character =
        characterPairing F (basis.representation θ₂).character := by
    intro F hF hFX
    have key : ∀ Θ : C → ℂ, Θ ∈ sectionSupported (involutionSectionUnion s) →
        characterPairing F Θ = 0 := by
      intro Θ hΘ
      unfold characterPairing
      rw [Finset.sum_eq_zero (fun x _ => ?_), mul_zero]
      by_cases hx : x ∈ involutionSectionUnion s
      · rw [hFX x hx, zero_mul]
      · rw [hΘ x⁻¹ (hXinv' x hx), mul_zero]
    have h0 := key Θ₀ (Submodule.mem_inf.mp hΘ₀W).2
    have h1 := key Θ₁ (Submodule.mem_inf.mp hΘ₁W).2
    have hF' := hFsum F hF
    rw [hF', KleinFourColumns.pairing_finset_sum_left, hsumB] at h0 h1
    simp only [hpair0] at h0
    rw [hpair1' θ₀ hθ₀B, hpair1' θ₁ hθ₁B, hpair1' θ₂ hθ₂B, hpair1' θ₃ hθ₃B] at h1
    rw [huθ₀, huθ₁, huθ₂, huθ₃] at h0 h1
    rw [hσθ₀, hσθ₁, hσθ₂, hσθ₃] at h1
    push_cast at h0 h1
    exact ⟨by linear_combination (-(h0 + h1)) / 2, by linear_combination (-(h0 - h1)) / 2⟩
  have hspanα : coefficientCharacterSpace basis B ⊓ sectionSupported (translatedOddSection t) =
      Submodule.span ℂ {(basis.representation θ₀).character +
        (basis.representation θ₁).character - (basis.representation θ₂).character -
          (basis.representation θ₃).character} := by
    apply le_antisymm
    · intro F hF
      obtain ⟨hFB, hFsupp⟩ := Submodule.mem_inf.mp hF
      obtain ⟨h10, h32⟩ := hcoefX F hFB (fun x hx => hFsupp x (fun h => htOddX x h hx))
      have h1 : F 1 = 0 := hFsupp 1 h1tOdd
      rw [hFexp F hFB 1, hchar1, hchar1, hchar1, hchar1, ← hdeg01, ← hdeg23, ← hf02, h10,
        h32] at h1
      have hc2 : characterPairing F (basis.representation θ₂).character =
          -characterPairing F (basis.representation θ₀).character := by
        have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) *
            (characterPairing F (basis.representation θ₂).character +
              characterPairing F (basis.representation θ₀).character) = 0 := by
          linear_combination h1 / 2
        exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h').resolve_left hf0)
      rw [Submodule.mem_span_singleton]
      refine ⟨characterPairing F (basis.representation θ₀).character, ?_⟩
      funext x
      rw [hFexp F hFB x, h10, h32, hc2]
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.mem_inf.mpr ⟨hαB, hαsupp⟩
  have hωB : (basis.representation θ₀).character + (basis.representation θ₁).character +
      (basis.representation θ₂).character + (basis.representation θ₃).character ∈
        coefficientCharacterSpace basis B :=
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.subset_span ⟨θ₀, hθ₀B, rfl⟩) (Submodule.subset_span ⟨θ₁, hθ₁B, rfl⟩))
        (Submodule.subset_span ⟨θ₂, hθ₂B, rfl⟩)) (Submodule.subset_span ⟨θ₃, hθ₃B, rfl⟩)
  have hωsupp : ∀ x, x ∉ {x : C | Odd (orderOf x)} →
      ((basis.representation θ₀).character + (basis.representation θ₁).character +
        (basis.representation θ₂).character + (basis.representation θ₃).character) x = 0 := by
    intro x hx
    simp only [Pi.add_apply]
    by_cases htx : x ∈ translatedOddSection t
    · obtain ⟨z, rfl, hz⟩ := htx
      rw [hσval θ₀ z, hσval θ₁ z, hσval θ₂ z, hσval θ₃ z, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
      obtain ⟨h1, h2, h3⟩ := hoddagree z hz
      rw [h1, h2, h3]
      push_cast
      ring
    by_cases hxX : x ∈ involutionSectionUnion s
    · rw [hXval θ₀ hθ₀B x hxX, hXval θ₁ hθ₁B x hxX, hXval θ₂ hθ₂B x hxX, hXval θ₃ hθ₃B x hxX,
        huθ₀, huθ₁, huθ₂, huθ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃]
      push_cast
      ring
    · rw [hrest θ₀ hθ₀B x hx htx hxX, hrest θ₁ hθ₁B x hx htx hxX, hrest θ₂ hθ₂B x hx htx hxX,
        hrest θ₃ hθ₃B x hx htx hxX]
      ring
  have hω0 : (basis.representation θ₀).character + (basis.representation θ₁).character +
      (basis.representation θ₂).character + (basis.representation θ₃).character ≠ 0 := by
    intro h
    have h' := congrFun h 1
    simp only [Pi.add_apply, Pi.zero_apply] at h'
    rw [hchar1, hchar1, hchar1, hchar1, ← hdeg01, ← hdeg23, ← hf02] at h'
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hf0 (by linear_combination h')
  have hspanω : coefficientCharacterSpace basis B ⊓ sectionSupported {x : C | Odd (orderOf x)} =
      Submodule.span ℂ {(basis.representation θ₀).character +
        (basis.representation θ₁).character + (basis.representation θ₂).character +
          (basis.representation θ₃).character} := by
    apply le_antisymm
    · intro F hF
      obtain ⟨hFB, hFsupp⟩ := Submodule.mem_inf.mp hF
      obtain ⟨h10, h32⟩ := hcoefX F hFB (fun x hx => hFsupp x (fun h => hoddX x h hx))
      have ht0 : F t = 0 := hFsupp t htodd
      rw [hFexp F hFB t, htval θ₀, htval θ₁, htval θ₂, htval θ₃, hσθ₀, hσθ₁, hσθ₂, hσθ₃,
        ← hdeg01, ← hdeg23, ← hf02, h10, h32] at ht0
      push_cast at ht0
      have hc2 : characterPairing F (basis.representation θ₂).character =
          characterPairing F (basis.representation θ₀).character := by
        have h' : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) *
            (characterPairing F (basis.representation θ₂).character -
              characterPairing F (basis.representation θ₀).character) = 0 := by
          linear_combination -ht0 / 2
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hf0)
      rw [Submodule.mem_span_singleton]
      refine ⟨characterPairing F (basis.representation θ₀).character, ?_⟩
      funext x
      rw [hFexp F hFB x, h10, h32, hc2]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.mem_inf.mpr ⟨hωB, hωsupp⟩
  have hinj : Function.Injective ![θ₀, θ₁, θ₂, θ₃] :=
    vec_four_injective hθ01 hθ02 hθ03 hθ12 hθ13 hθ23
  have himg : B = Finset.univ.image ![θ₀, θ₁, θ₂, θ₃] := by
    rw [hBeq, image_vec_four]
  refine ⟨![θ₀, θ₁, θ₂, θ₃], Module.finrank ℂ (basis.representation θ₀).vector, hinj, himg,
    hdeg θ₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hαsupp, hαnorm, hαt, hspanα, ?_, ?_⟩
  · intro i
    fin_cases i
    · rfl
    · exact hdeg01.symm
    · exact hf02.symm
    · exact hdeg23.symm.trans hf02.symm
  · change (basis.representation θ₀).character t = _
    rw [htval θ₀, hσθ₀]
    push_cast
    ring
  · change (basis.representation θ₁).character t = _
    rw [htval θ₁, hσθ₁, ← hdeg01]
    push_cast
    ring
  · change (basis.representation θ₂).character t = _
    rw [htval θ₂, hσθ₂, ← hf02]
    push_cast
    ring
  · change (basis.representation θ₃).character t = _
    rw [htval θ₃, hσθ₃, ← hdeg23, ← hf02]
    push_cast
    ring
  · change (basis.representation θ₀).character s = _
    rw [hsval θ₀ hθ₀B, huθ₀, hσθ₀]
    norm_num
  · change (basis.representation θ₁).character s = _
    rw [hsval θ₁ hθ₁B, huθ₁, hσθ₁]
    norm_num
  · change (basis.representation θ₂).character s = _
    rw [hsval θ₂ hθ₂B, huθ₂, hσθ₂]
    norm_num
  · change (basis.representation θ₃).character s = _
    rw [hsval θ₃ hθ₃B, huθ₃, hσθ₃]
    norm_num
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := hoddagree x hx
    have hall : ∀ i, (basis.representation (![θ₀, θ₁, θ₂, θ₃] i)).character x =
        (basis.representation θ₀).character x := by
      intro i
      fin_cases i
      · rfl
      · exact h1
      · exact h2
      · exact h3
    intro i i'
    rw [hall i, hall i']
  · intro x hx i
    have hmem : ![θ₀, θ₁, θ₂, θ₃] i ∈ B := by
      rw [himg]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    exact hvan4 _ hmem x hx
  · rw [hspanα]
    exact finrank_span_singleton hα0
  · rw [hspanω]
    exact finrank_span_singleton hω0

end CFSG.Semidihedral.Principal
