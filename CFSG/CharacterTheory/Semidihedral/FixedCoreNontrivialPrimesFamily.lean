module

public import CFSG.CharacterTheory.CyclicBlocks.AbelianFamily
public import CFSG.CharacterTheory.CyclicBlocks.LabelReality

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FixedCoreNontrivialPrimes

open CFSG.TwoRankLowerBound.Helpers CFSG.CyclicBlocks CFSG.Semidihedral.Principal

structure InvertedFamily {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (B : Finset basis.index)
    (principal : basis.index) (p : ℕ) (P : Subgroup G)
    (basisP : FiniteIrreducibleCharacterBasis P) (principalP : basisP.index)
    (T : Finset basisP.index) (a : basis.index) (b : T → basis.index) (δ : ℤ) : Prop where
  sign : δ = 1 ∨ δ = -1
  T_nonempty : T.Nonempty
  T_nontrivial : principalP ∉ T
  mem_a : a ∈ B
  a_ne : a ≠ principal
  b_inj : Function.Injective b
  mem_b : ∀ k, b k ∈ B
  b_ne_principal : ∀ k, b k ≠ principal
  b_ne_a : ∀ k, b k ≠ a
  deg_b : ∀ k, (Module.finrank ℂ (basis.representation (b k)).vector : ℤ) =
    Module.finrank ℂ (basis.representation a).vector + δ
  regular : ∀ k (x : G), ¬ p ∣ orderOf x →
    (basis.representation (b k)).character x = (basis.representation a).character x + δ
  value_a : ∀ z : P, z ≠ 1 → (basis.representation a).character z = δ
  value_b : ∀ k (z : P), z ≠ 1 → (basis.representation (b k)).character z =
    δ * ((basisP.representation k).character z + (basisP.representation k).character z⁻¹)
  vanish : ∀ θ ∈ B, θ ≠ principal → θ ≠ a → (∀ k, θ ≠ b k) → ∀ z : P, z ≠ 1 →
    (basis.representation θ).character z = 0
  real_a : ∀ g, starRingEnd ℂ ((basis.representation a).character g) =
    (basis.representation a).character g
  real_b : ∀ k g, starRingEnd ℂ ((basis.representation (b k)).character g) =
    (basis.representation (b k)).character g
  transversal_sum : ∀ z : P, z ≠ 1 →
    ∑ k : T, ((basisP.representation k).character z +
      (basisP.representation k).character z⁻¹) = -1

theorem transversal_sums {A : Type*} [Group A] [Fintype A] [IsMulCommutative A]
    (basisA : FiniteIrreducibleCharacterBasis A) (principalA : basisA.index)
    (hprincipalA : (basisA.representation principalA).character = 1) {T : Finset basisA.index}
    (hT0 : principalA ∉ T) (hT1 : ∀ φ ∈ T, conjugateLabel basisA φ ∉ T)
    (hT2 : ∀ φ, φ ≠ principalA → φ ∈ T ∨ conjugateLabel basisA φ ∈ T)
    (hTcard : 2 * T.card + 1 = Nat.card A) {z : A} (hz : z ≠ 1) (hz2 : z ^ 2 ≠ 1) :
    ∑ k : T, ((basisA.representation k).character z +
        (basisA.representation k).character z⁻¹) = -1 ∧
      ∑ k : T, ((basisA.representation k).character z +
        (basisA.representation k).character z⁻¹) ^ 2 = (Nat.card A : ℂ) - 2 := by
  constructor
  · rw [Finset.sum_coe_sort T (fun φ => (basisA.representation φ).character z +
      (basisA.representation φ).character z⁻¹)]
    simp_rw [← conjugateLabel_character_eq_inv]
    rw [sum_conj_transversal basisA principalA hprincipalA hT0 hT1 hT2
      (fun φ => (basisA.representation φ).character z),
      sum_label_character_eq_zero_of_ne_one basisA hz, hprincipalA, Pi.one_apply]
    ring
  · have hsq : ∀ k : T, ((basisA.representation k).character z +
        (basisA.representation k).character z⁻¹) ^ 2 =
        2 + ((basisA.representation k).character (z ^ 2) +
          (basisA.representation (conjugateLabel basisA k)).character (z ^ 2)) := by
      intro k
      have h1 := label_character_mul_inv_of_comm basisA (k : basisA.index) z
      rw [conjugateLabel_character_eq_inv, label_character_pow_of_comm, ← inv_pow,
        label_character_pow_of_comm]
      linear_combination 2 * h1
    rw [Finset.sum_congr rfl fun k _ => hsq k, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      Finset.sum_coe_sort T (fun φ => (basisA.representation φ).character (z ^ 2) +
        (basisA.representation (conjugateLabel basisA φ)).character (z ^ 2)),
      sum_conj_transversal basisA principalA hprincipalA hT0 hT1 hT2
        (fun φ => (basisA.representation φ).character (z ^ 2)),
      sum_label_character_eq_zero_of_ne_one basisA hz2, hprincipalA, Pi.one_apply]
    have hcast : (2 : ℂ) * T.card + 1 = Nat.card A := by exact_mod_cast hTcard
    linear_combination hcast

theorem character_add_inv_im {A : Type*} [Group A] [Fintype A]
    (basisA : FiniteIrreducibleCharacterBasis A) (k : basisA.index) (z : A) :
    ((basisA.representation k).character z + (basisA.representation k).character z⁻¹).im =
      0 := by
  have hconj : starRingEnd ℂ ((basisA.representation k).character z +
      (basisA.representation k).character z⁻¹) =
      (basisA.representation k).character z + (basisA.representation k).character z⁻¹ := by
    simp only [map_add, finite_character_conjugate_inverse, inv_inv]
    ring
  exact Complex.conj_eq_iff_im.mp hconj

theorem normSq_sign_mul_of_im {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) {w : ℂ} (hw : w.im = 0) :
    Complex.normSq ((δ : ℂ) * w) = w.re ^ 2 := by
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by rcases hδ with rfl | rfl <;> simp
  rw [Complex.normSq_mul, hδnorm, one_mul, Complex.normSq_apply, hw]
  ring

theorem inverted_family_exists {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G) (τ : G) (hP : InvertedAbelianSylow P τ)
    (basisP : FiniteIrreducibleCharacterBasis (P : Subgroup G)) (principalP : basisP.index)
    (hprincipalP : (basisP.representation principalP).character = 1) :
    ∃ (T : Finset basisP.index) (a : basis.index) (b : T → basis.index) (δ : ℤ),
      InvertedFamily basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
        principal p P basisP principalP T a b δ := by
  classical
  have hpp : p.Prime := Fact.out
  have := hP.isMulCommutative
  obtain ⟨hodd, h3⟩ := card_sylow_odd_three_le_of_relIndex hp P hP.index
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hprinB : principal ∈ B := coefficientBlock_self_mem _ _ _
  obtain ⟨T, hT0, hT1, hT2, hTcard⟩ := exists_conj_transversal basisP hodd principalP hprincipalP
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨a, b, δ, haB, hao, hbinj, hb, hδ, hbdeg, hTdec⟩ :=
    hP.abelian_inversion_family_decomposition basis ideal hp principal hprincipal basisP
      principalP hprincipalP hTne hT0 hT1
  have hδsq : (δ : ℂ) * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hval := fun (z : (P : Subgroup G)) (hz : z ≠ 1) =>
    hP.abelian_inversion_values basis ideal hp principal hprincipal basisP principalP hprincipalP
      hT0 hT1 hT2 hTcard a b δ haB hao hbinj hb hδ hTdec z hz
  have hz2 : ∀ z : (P : Subgroup G), z ≠ 1 → z ^ 2 ≠ 1 := by
    intro z hz h
    have hz1 : (z : G) ≠ 1 := fun h' => hz (Subtype.ext h')
    apply hz1
    refine eq_one_of_inv_eq_self_of_odd
      (odd_orderOf_of_dvd_prime_pow hpp hp (orderOf_dvd_of_mem_sylow P z.2)) ?_
    have h' : (z : G) ^ 2 = 1 := by rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
    rw [inv_eq_iff_mul_eq_one, ← pow_two, h']
  have hsums := fun (z : (P : Subgroup G)) (hz : z ≠ 1) =>
    transversal_sums basisP principalP hprincipalP hT0 hT1 hT2 hTcard hz (hz2 z hz)
  have hreg : ∀ (k : T) (x : G), ¬ p ∣ orderOf x →
      (basis.representation (b k)).character x = (basis.representation a).character x + δ := by
    intro k x hx
    have h0 := subgroupProjection_eq_zero_of_coprime basis ideal p principal
      (fun y hy => orderOf_dvd_of_mem_sylow P hy)
      (fun w => 1 - (basisP.representation (k : basisP.index)).character w)
      (by simp only [label_character_one_of_comm, sub_self]) hx
    rw [hTdec k x] at h0
    linear_combination (-(δ : ℂ)) * h0 +
      ((basis.representation a).character x - (basis.representation (b k)).character x) * hδsq
  have hvan : ∀ θ ∈ B, θ ≠ principal → θ ≠ a → (∀ k, θ ≠ b k) → ∀ z : (P : Subgroup G),
      z ≠ 1 → (basis.representation θ).character z = 0 := by
    intro θ hθ hθp hθa hθb z hz
    obtain ⟨hza, hzb⟩ := hval z hz
    obtain ⟨-, hsq⟩ := hsums z hz
    have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
    have hcol := hP.principal_column_norm basis ideal hp principal hprincipal z.2 hz1
    have hcolR : ∑ θ ∈ B, Complex.normSq ((basis.representation θ).character z) =
        Nat.card P := by
      have h : ∑ θ ∈ B, ((Complex.normSq ((basis.representation θ).character z) : ℝ) : ℂ) =
          (Nat.card P : ℂ) := by
        rw [← hcol]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [Complex.mul_conj]
      exact_mod_cast h
    set S : Finset basis.index := insert principal (insert a (Finset.univ.image b)) with hSdef
    have hSB : S ⊆ B := by
      intro x hx
      simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with rfl | rfl | ⟨k, rfl⟩
      · exact hprinB
      · exact haB
      · exact (hb k).1
    have hpa : principal ∉ insert a (Finset.univ.image b) := by
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
        not_exists]
      exact ⟨fun h => hao h.symm, fun k hk => (hb k).2.1 hk⟩
    have ha : a ∉ Finset.univ.image b := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun k hk => (hb k).2.2 hk
    have hsqR : ∑ k : T, ((basisP.representation k).character z +
        (basisP.representation k).character z⁻¹).re ^ 2 = (Nat.card P : ℝ) - 2 := by
      have h : ∀ k : T, (((basisP.representation k).character z +
          (basisP.representation k).character z⁻¹) ^ 2).re =
          ((basisP.representation k).character z +
            (basisP.representation k).character z⁻¹).re ^ 2 := fun k => by
        rw [sq, Complex.mul_re, character_add_inv_im basisP k z]
        ring
      rw [← Finset.sum_congr rfl fun k _ => h k, ← Complex.re_sum, hsq]
      simp
    have hsumS : ∑ θ ∈ S, Complex.normSq ((basis.representation θ).character z) =
        Nat.card P := by
      rw [Finset.sum_insert hpa, Finset.sum_insert ha,
        Finset.sum_image (fun x _ y _ h => hbinj h)]
      rw [hprincipal, Pi.one_apply, Complex.normSq_one, hza]
      have hδn : Complex.normSq (δ : ℂ) = 1 := by rcases hδ with rfl | rfl <;> simp
      rw [hδn, Finset.sum_congr rfl fun k _ => by
        rw [hzb k, normSq_sign_mul_of_im hδ (character_add_inv_im basisP k z)], hsqR]
      ring
    have hsplit := Finset.sum_sdiff hSB (f := fun θ =>
      Complex.normSq ((basis.representation θ).character z))
    rw [hsumS, hcolR] at hsplit
    have hrest : ∑ θ ∈ B \ S, Complex.normSq ((basis.representation θ).character z) = 0 := by
      linarith
    have hθS : θ ∈ B \ S := by
      refine Finset.mem_sdiff.mpr ⟨hθ, ?_⟩
      simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
        not_exists]
      exact ⟨hθp, hθa, fun k hk => hθb k hk.symm⟩
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun θ _ => Complex.normSq_nonneg
      ((basis.representation θ).character z)).mp hrest θ hθS
    exact Complex.normSq_eq_zero.mp h
  have hTreal : ∀ (k : T) (g : G),
      starRingEnd ℂ (subgroupProjection basis B P
        (fun w => 1 - (basisP.representation k).character w) g) =
        subgroupProjection basis B P (fun w => 1 - (basisP.representation k).character w) g := by
    intro k g
    by_cases hg : p ∣ orderOf g
    · obtain ⟨x, hx, hx1, y, hxy, hy, hconj⟩ := exists_isConj_mul_of_dvd_orderOf_of_sylow P hg
      have hz1 : (⟨x, hx⟩ : (P : Subgroup G)) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
      have h := hP.subgroupProjection_section basis ideal hp principal hprincipal
        (fun w => 1 - (basisP.representation k).character w) ⟨x, hx⟩ hz1 hxy hy
      rw [subgroupProjection_isConj basis B P _ hconj, h]
      simp only [map_add, map_sub, map_one, finite_character_conjugate_inverse, inv_inv]
      ring
    · rw [subgroupProjection_eq_zero_of_coprime basis ideal p principal
        (fun x hx => orderOf_dvd_of_mem_sylow P hx) _
        (by simp only [label_character_one_of_comm, sub_self]) hg, map_zero]
  have hreal : ∀ k : T,
      (∀ g, starRingEnd ℂ ((basis.representation a).character g) =
        (basis.representation a).character g) ∧
      ∀ g, starRingEnd ℂ ((basis.representation (b k)).character g) =
        (basis.representation (b k)).character g := fun k =>
    real_of_one_add_sub_real basis (hb k).2.2 hδ fun g => by rw [← hTdec k g, hTreal k g]
  obtain ⟨k₀, hk₀⟩ := hTne
  exact ⟨T, a, b, δ,
    { sign := hδ
      T_nonempty := ⟨k₀, hk₀⟩
      T_nontrivial := hT0
      mem_a := haB
      a_ne := hao
      b_inj := hbinj
      mem_b := fun k => (hb k).1
      b_ne_principal := fun k => (hb k).2.1
      b_ne_a := fun k => (hb k).2.2
      deg_b := hbdeg
      regular := hreg
      value_a := fun z hz => (hval z hz).1
      value_b := fun k z hz => (hval z hz).2 k
      vanish := hvan
      real_a := (hreal ⟨k₀, hk₀⟩).1
      real_b := fun k => (hreal k).2
      transversal_sum := fun z hz => (hsums z hz).1 }⟩

namespace InvertedFamily

variable {G : Type*} [Group G] [Fintype G]
  {basis : FiniteIrreducibleCharacterBasis G} {B : Finset basis.index}
  {principal : basis.index} {p : ℕ} {P : Subgroup G}
  {basisP : FiniteIrreducibleCharacterBasis P} {principalP : basisP.index}
  {T : Finset basisP.index} {a : basis.index} {b : T → basis.index} {δ : ℤ}

theorem character_one_b (hF : InvertedFamily basis B principal p P basisP principalP T a b δ)
    (hp : p.Prime) (k : T) :
    (basis.representation (b k)).character 1 = (basis.representation a).character 1 + δ :=
  hF.regular k 1 (by rw [orderOf_one]; exact hp.not_dvd_one)

theorem character_one_add_ne_zero
    (hF : InvertedFamily basis B principal p P basisP principalP T a b δ) (hp : p.Prime) :
    (basis.representation a).character 1 + δ ≠ 0 := by
  obtain ⟨k, hk⟩ := hF.T_nonempty
  rw [← hF.character_one_b hp ⟨k, hk⟩, (label_character_one basis _).1]
  exact Nat.cast_ne_zero.mpr (label_character_one basis _).2.ne'

theorem weighted_sum (hF : InvertedFamily basis B principal p P basisP principalP T a b δ)
    (hp : p.Prime) (hprincipal : (basis.representation principal).character = 1)
    (hpB : principal ∈ B) {x₁ x₂ : G} (hx₁ : ¬ p ∣ orderOf x₁) (hx₂ : ¬ p ∣ orderOf x₂)
    (z : P) (hz : z ≠ 1) :
    ∑ θ ∈ B, (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
        (basis.representation θ).character z / (basis.representation θ).character 1 =
      ((basis.representation a).character 1 - (basis.representation a).character x₁) *
        ((basis.representation a).character 1 - (basis.representation a).character x₂) /
          ((basis.representation a).character 1 *
            ((basis.representation a).character 1 + δ)) := by
  classical
  set S : Finset basis.index := insert principal (insert a (Finset.univ.image b)) with hSdef
  have hSB : S ⊆ B := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨k, rfl⟩
    · exact hpB
    · exact hF.mem_a
    · exact hF.mem_b k
  have hpa : principal ∉ insert a (Finset.univ.image b) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists]
    exact ⟨fun h => hF.a_ne h.symm, fun k hk => hF.b_ne_principal k hk⟩
  have ha : a ∉ Finset.univ.image b := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun k hk => hF.b_ne_a k hk
  have hrest : ∑ θ ∈ B \ S, (basis.representation θ).character x₁ *
      (basis.representation θ).character x₂ * (basis.representation θ).character z /
        (basis.representation θ).character 1 = 0 := by
    refine Finset.sum_eq_zero fun θ hθ => ?_
    obtain ⟨hθB, hθS⟩ := Finset.mem_sdiff.mp hθ
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists] at hθS
    obtain ⟨hθp, hθa, hθb⟩ := hθS
    rw [hF.vanish θ hθB hθp hθa (fun k hk => hθb k hk.symm) z hz]
    simp
  rw [← Finset.sum_sdiff hSB, hrest, zero_add, Finset.sum_insert hpa, Finset.sum_insert ha,
    Finset.sum_image (fun x _ y _ h => hF.b_inj h)]
  rw [hprincipal, hF.value_a z hz]
  simp only [Pi.one_apply, mul_one, div_one]
  have hsumk : ∑ k : T, (basis.representation (b k)).character x₁ *
      (basis.representation (b k)).character x₂ * (basis.representation (b k)).character z /
        (basis.representation (b k)).character 1 =
      ((basis.representation a).character x₁ + δ) * ((basis.representation a).character x₂ + δ) *
        δ / ((basis.representation a).character 1 + δ) * (-1) := by
    rw [← hF.transversal_sum z hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hF.value_b k z hz, hF.regular k x₁ hx₁, hF.regular k x₂ hx₂, hF.character_one_b hp k]
    ring
  rw [hsumk]
  have hf : (basis.representation a).character 1 ≠ 0 := by
    rw [(label_character_one basis a).1]
    exact Nat.cast_ne_zero.mpr (label_character_one basis a).2.ne'
  have hδ' : (δ : ℂ) = 1 ∨ (δ : ℂ) = -1 := by
    rcases hF.sign with h | h
    · left
      rw [h]
      norm_num
    · right
      rw [h]
      norm_num
  have hid := prime_inversion_weighted_identity ((basis.representation a).character 1)
    ((basis.representation a).character x₁) ((basis.representation a).character x₂) δ hδ' hf
    (hF.character_one_add_ne_zero hp)
  rw [← hid]
  ring

end InvertedFamily

end CFSG.Semidihedral.FixedCoreNontrivialPrimes
