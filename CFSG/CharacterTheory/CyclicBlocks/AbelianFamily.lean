module

public import CFSG.CharacterTheory.CyclicBlocks.AbelianSections
public import CFSG.CharacterTheory.CyclicBlocks.AbelianDual
public import CFSG.CharacterTheory.CyclicBlocks.Gram

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Semidihedral.Principal

theorem characterPairing_one_sub_right {H : Type*} [Group H] [Fintype H] (f g : H → ℂ) :
    characterPairing f (fun z => 1 - g z) = characterPairing f 1 - characterPairing f g := by
  unfold characterPairing
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.one_apply]
  ring

theorem characterPairing_two_sub_sub_one_sub {H : Type*} [Group H] [Fintype H]
    (F₁ F₂ G : H → ℂ) :
    characterPairing (fun z => 2 - F₁ z - F₂ z) (fun z => 1 - G z) =
      2 * characterPairing (1 : H → ℂ) 1 - 2 * characterPairing (1 : H → ℂ) G -
        characterPairing F₁ 1 + characterPairing F₁ G - characterPairing F₂ 1 +
          characterPairing F₂ G := by
  unfold characterPairing
  have h : ∀ z : H, (2 - F₁ z - F₂ z) * (1 - G z⁻¹) =
      2 * ((1 : H → ℂ) z * (1 : H → ℂ) z⁻¹) - 2 * ((1 : H → ℂ) z * G z⁻¹) -
        F₁ z * (1 : H → ℂ) z⁻¹ + F₁ z * G z⁻¹ - F₂ z * (1 : H → ℂ) z⁻¹ + F₂ z * G z⁻¹ := by
    intro z
    simp only [Pi.one_apply]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem characterPairing_two_sub_sub_one_sub_label {H : Type*} [Group H] [Fintype H]
    (basisH : FiniteIrreducibleCharacterBasis H) (o : basisH.index)
    (ho : (basisH.representation o).character = 1) (φ φ' ψ : basisH.index) :
    characterPairing (fun z => 2 - (basisH.representation φ).character z -
        (basisH.representation φ').character z)
      (fun z => 1 - (basisH.representation ψ).character z) =
      2 - 2 * (if o = ψ then 1 else 0) - (if φ = o then 1 else 0) + (if φ = ψ then 1 else 0) -
        (if φ' = o then 1 else 0) + (if φ' = ψ then 1 else 0) := by
  rw [characterPairing_two_sub_sub_one_sub, ← ho]
  simp only [characterPairing_label_label, ↓reduceIte, mul_one]

variable {G : Type*} [Group G] [Fintype G]

namespace InvertedAbelianSylow

variable (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
  {P : Sylow p G} {τ : G}

theorem subgroupProjection_one_sub_apply (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (basisP : FiniteIrreducibleCharacterBasis (P : Subgroup G)) (φ : basisP.index)
    (z : (P : Subgroup G)) :
    subgroupProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal) P (fun w => 1 - (basisP.representation φ).character w) (z : G) =
      2 - (basisP.representation φ).character z - (basisP.representation φ).character z⁻¹ := by
  have hpp : p.Prime := Fact.out
  have := hP.isMulCommutative
  by_cases hz : z = 1
  · subst hz
    rw [Subgroup.coe_one, subgroupProjection_eq_zero_of_coprime basis ideal p principal
      (fun x hx => orderOf_dvd_of_mem_sylow P hx) _
      (by simp only [label_character_one_of_comm, sub_self])
      (by rw [orderOf_one]; exact hpp.not_dvd_one), inv_one, label_character_one_of_comm]
    norm_num
  · have h := hP.subgroupProjection_section basis ideal hp2 principal hprincipal
      (fun w => 1 - (basisP.representation φ).character w) z hz (y := 1) (Commute.one_right _)
      (by rw [orderOf_one]; exact hpp.not_dvd_one)
    rw [mul_one] at h
    rw [h]
    ring

theorem abelian_inversion_family_decomposition (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (basisP : FiniteIrreducibleCharacterBasis (P : Subgroup G)) (principalP : basisP.index)
    (hprincipalP : (basisP.representation principalP).character = 1) {T : Finset basisP.index}
    (hT : T.Nonempty) (hT0 : principalP ∉ T) (hT1 : ∀ φ ∈ T, conjugateLabel basisP φ ∉ T) :
    ∃ (a : basis.index) (b : T → basis.index) (δ : ℤ),
      a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      a ≠ principal ∧ Function.Injective b ∧
      (∀ k, b k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
        b k ≠ principal ∧ b k ≠ a) ∧
      (δ = 1 ∨ δ = -1) ∧
      (∀ k, (Module.finrank ℂ (basis.representation (b k)).vector : ℤ) =
        Module.finrank ℂ (basis.representation a).vector + δ) ∧
      ∀ (k : T) (g : G),
        subgroupProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
          principal) P (fun w => 1 - (basisP.representation k).character w) g =
          1 + δ * (basis.representation a).character g -
            δ * (basis.representation (b k)).character g := by
  classical
  have hpp : p.Prime := Fact.out
  have := hP.isMulCommutative
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hprinB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hσp := conjugateLabel_principal basisP principalP hprincipalP
  choose m hm using fun (x : basis.index) (φ : basisP.index) =>
    restriction_pairing_nat basis basisP x φ
  have hc : ∀ (x : basis.index) (φ : basisP.index),
      characterPairing (fun y : (P : Subgroup G) => (basis.representation x).character y)
        (fun w => 1 - (basisP.representation φ).character w) =
        (((m x principalP : ℤ) - m x φ : ℤ) : ℂ) := by
    intro x φ
    rw [characterPairing_one_sub_right, ← hprincipalP, hm, hm]
    push_cast
    ring
  have hTsum : ∀ (φ : basisP.index) (g : G), subgroupProjection basis B P
      (fun w => 1 - (basisP.representation φ).character w) g =
      ∑ x ∈ B, (((m x principalP : ℤ) - m x φ : ℤ) : ℂ) * (basis.representation x).character g := by
    intro φ g
    unfold subgroupProjection
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hc]
  have hmprin : ∀ φ : basisP.index, (m principal φ : ℂ) = if principalP = φ then 1 else 0 := by
    intro φ
    have h := hm principal φ
    have h1 : (fun h : (P : Subgroup G) => (basis.representation principal).character (h : G)) =
        (basisP.representation principalP).character := by
      funext h
      rw [hprincipal, hprincipalP]
      rfl
    rw [h1, characterPairing_label_label] at h
    exact h.symm
  have hgram : ∀ φ ψ : basisP.index, φ ∈ T → ψ ∈ T →
      ((∑ x ∈ B, ((m x principalP : ℤ) - m x φ) * ((m x principalP : ℤ) - m x ψ) : ℤ) : ℂ) =
        2 + (if φ = ψ then 1 else 0) := by
    intro φ ψ hφ hψ
    have h1 := characterPairing_sum_left B (fun x => (((m x principalP : ℤ) - m x φ : ℤ) : ℂ))
      (fun x (y : (P : Subgroup G)) => (basis.representation x).character y)
      (fun w => 1 - (basisP.representation ψ).character w)
    have h2 : (fun y : (P : Subgroup G) => ∑ x ∈ B, (((m x principalP : ℤ) - m x φ : ℤ) : ℂ) *
        (basis.representation x).character y) =
        fun y => 2 - (basisP.representation φ).character y -
          (basisP.representation (conjugateLabel basisP φ)).character y := by
      funext y
      rw [← hTsum, subgroupProjection_one_sub_apply basis ideal hp2 hP principal hprincipal basisP
        φ y, conjugateLabel_character_eq_inv]
    rw [h2, characterPairing_two_sub_sub_one_sub_label basisP principalP hprincipalP] at h1
    simp_rw [hc] at h1
    have hoψ : principalP ≠ ψ := fun h => hT0 (h ▸ hψ)
    have hφo : φ ≠ principalP := fun h => hT0 (h ▸ hφ)
    have hσφo : conjugateLabel basisP φ ≠ principalP := fun h =>
      hφo (by rw [← conjugateLabel_conjugateLabel basisP φ, h, hσp])
    have hσφψ : conjugateLabel basisP φ ≠ ψ := fun h => hT1 φ hφ (h ▸ hψ)
    simp only [hoψ, hφo, hσφo, hσφψ, ↓reduceIte] at h1
    push_cast at h1 ⊢
    linear_combination -h1
  have hIcard : 1 ≤ Fintype.card T := by
    rw [Fintype.card_coe]
    exact hT.card_pos
  let v : T → basis.index → ℤ := fun k x =>
    if x ∈ B then (m x principalP : ℤ) - m x (k : basisP.index) else 0
  let d : basis.index → ℤ := fun x => Module.finrank ℂ (basis.representation x).vector
  have hd : ∀ x, 0 < d x := fun x => by
    show (0 : ℤ) < (Module.finrank ℂ (basis.representation x).vector : ℤ)
    exact_mod_cast (label_character_one basis x).2
  have hdo : d principal = 1 := by
    have h := (label_character_one basis principal).1
    rw [hprincipal, Pi.one_apply] at h
    have h' : (Module.finrank ℂ (basis.representation principal).vector : ℂ) = 1 := h.symm
    show (Module.finrank ℂ (basis.representation principal).vector : ℤ) = 1
    exact_mod_cast h'
  have hvo : ∀ k, v k principal = 1 := by
    intro k
    have hko : principalP ≠ (k : basisP.index) := fun h => hT0 (h ▸ k.2)
    have h0 := hmprin principalP
    have hk := hmprin (k : basisP.index)
    simp only [↓reduceIte, hko] at h0 hk
    have h0' : m principal principalP = 1 := by exact_mod_cast h0
    have hk' : m principal (k : basisP.index) = 0 := by exact_mod_cast hk
    simp only [v, hprinB, ↓reduceIte, h0', hk']
    norm_num
  have hsumB : ∀ F : basis.index → ℤ, ∑ x, (if x ∈ B then F x else 0) = ∑ x ∈ B, F x := by
    intro F
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hnorm : ∀ k, ∑ x, v k x ^ 2 = 3 := by
    intro k
    have h := hgram _ _ k.2 k.2
    simp only [↓reduceIte] at h
    have h' : ((∑ x ∈ B, ((m x principalP : ℤ) - m x (k : basisP.index)) *
        ((m x principalP : ℤ) - m x (k : basisP.index)) : ℤ) : ℂ) = ((3 : ℤ) : ℂ) := by
      rw [h]
      norm_num
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v]
    split_ifs <;> ring
  have hdeg : ∀ k, ∑ x, d x * v k x = 0 := by
    intro k
    have hT1' := subgroupProjection_eq_zero_of_coprime basis ideal p principal
      (fun x hx => orderOf_dvd_of_mem_sylow P hx)
      (fun w => 1 - (basisP.representation (k : basisP.index)).character w)
      (by simp only [label_character_one_of_comm, sub_self]) (g := 1)
      (by rw [orderOf_one]; exact hpp.not_dvd_one)
    rw [hTsum] at hT1'
    have h' : ((∑ x ∈ B, (Module.finrank ℂ (basis.representation x).vector : ℤ) *
        ((m x principalP : ℤ) - m x (k : basisP.index)) : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
      push_cast
      rw [← hT1']
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [(label_character_one basis x).1]
      push_cast
      ring
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v, d]
    split_ifs <;> ring
  have hgram' : ∀ k k', k ≠ k' → ∑ x, v k x * v k' x = 2 := by
    intro k k' hkk
    have h := hgram _ _ k.2 k'.2
    have hne : (k : basisP.index) ≠ k' := fun h' => hkk (Subtype.ext h')
    simp only [hne, ↓reduceIte, add_zero] at h
    have h' : ((∑ x ∈ B, ((m x principalP : ℤ) - m x (k : basisP.index)) *
        ((m x principalP : ℤ) - m x (k' : basisP.index)) : ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by
      rw [h]
      norm_num
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v]
    split_ifs <;> ring
  obtain ⟨a, hao, b, hbinj, hbne, δ, hδ, hv⟩ :=
    integral_norm_three_degree_zero_gram_family_of_pos hIcard principal d hd hdo v hvo hnorm hdeg
      hgram'
  have hvB : ∀ k x, v k x ≠ 0 → x ∈ B := by
    intro k x hx
    by_contra hxB
    exact hx (by simp only [v, hxB, ↓reduceIte])
  obtain ⟨k₀, hk₀⟩ := hT
  have haB : a ∈ B := hvB ⟨k₀, hk₀⟩ a (((hv ⟨k₀, hk₀⟩).2.2.2 a).mpr (Or.inr (Or.inl rfl)))
  have hbB : ∀ k, b k ∈ B := fun k => hvB k (b k) (((hv k).2.2.2 (b k)).mpr (Or.inr (Or.inr rfl)))
  refine ⟨a, b, δ, haB, hao, hbinj, fun k => ⟨hbB k, (hbne k).1, (hbne k).2⟩, hδ,
    fun k => (hv k).2.1, fun k g => ?_⟩
  rw [hTsum]
  have hext : ∑ x ∈ B, (((m x principalP : ℤ) - m x (k : basisP.index) : ℤ) : ℂ) *
      (basis.representation x).character g =
      ∑ x, (v k x : ℂ) * (basis.representation x).character g := by
    rw [← Finset.sum_subset (Finset.subset_univ B)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      simp only [v, hx, ↓reduceIte]
    · intro x _ hx
      simp only [v, hx, ↓reduceIte]
      push_cast
      ring
  rw [hext, (hv k).1]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  push_cast
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hprincipal, Pi.one_apply]

theorem abelian_inversion_values (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (basisP : FiniteIrreducibleCharacterBasis (P : Subgroup G)) (principalP : basisP.index)
    (hprincipalP : (basisP.representation principalP).character = 1) {T : Finset basisP.index}
    (hT0 : principalP ∉ T) (hT1 : ∀ φ ∈ T, conjugateLabel basisP φ ∉ T)
    (hT2 : ∀ φ, φ ≠ principalP → φ ∈ T ∨ conjugateLabel basisP φ ∈ T)
    (hTcard : 2 * T.card + 1 = Nat.card P)
    (a : basis.index) (b : T → basis.index) (δ : ℤ)
    (haB : a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hao : a ≠ principal) (hbinj : Function.Injective b)
    (hb : ∀ k, b k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      b k ≠ principal ∧ b k ≠ a) (hδ : δ = 1 ∨ δ = -1)
    (hTdec : ∀ (k : T) (g : G),
      subgroupProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        principal) P (fun w => 1 - (basisP.representation k).character w) g =
        1 + δ * (basis.representation a).character g -
          δ * (basis.representation (b k)).character g)
    (z : (P : Subgroup G)) (hz : z ≠ 1) :
    (basis.representation a).character z = δ ∧
      ∀ k : T, (basis.representation (b k)).character z =
        δ * ((basisP.representation k).character z + (basisP.representation k).character z⁻¹) := by
  classical
  have hpp : p.Prime := Fact.out
  have := hP.isMulCommutative
  have hδsq : (δ : ℂ) * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by rcases hδ with rfl | rfl <;> simp
  have hprinB : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem _ _ _
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
  have hz2 : z ^ 2 ≠ 1 := by
    intro h
    apply hz1
    refine eq_one_of_inv_eq_self_of_odd
      (odd_orderOf_of_dvd_prime_pow hpp hp2 (orderOf_dvd_of_mem_sylow P z.2)) ?_
    have h' : (z : G) ^ 2 = 1 := by rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
    rw [inv_eq_iff_mul_eq_one, ← pow_two, h']
  let α : T → ℂ := fun k =>
    (basisP.representation k).character z + (basisP.representation k).character z⁻¹
  have hαreal : ∀ k, (α k).im = 0 := by
    intro k
    have hconj : starRingEnd ℂ (α k) = α k := by
      simp only [α, map_add, finite_character_conjugate_inverse, inv_inv]
      ring
    exact Complex.conj_eq_iff_im.mp hconj
  have hαsum : ∑ k, α k = -1 := by
    rw [Finset.sum_coe_sort T (fun φ => (basisP.representation φ).character z +
      (basisP.representation φ).character z⁻¹)]
    simp_rw [← conjugateLabel_character_eq_inv]
    rw [sum_conj_transversal basisP principalP hprincipalP hT0 hT1 hT2
      (fun φ => (basisP.representation φ).character z),
      sum_label_character_eq_zero_of_ne_one basisP hz, hprincipalP, Pi.one_apply]
    ring
  have hαsq : ∑ k, α k ^ 2 = (Nat.card P : ℂ) - 2 := by
    have hsq : ∀ k : T, α k ^ 2 = 2 + ((basisP.representation k).character (z ^ 2) +
        (basisP.representation (conjugateLabel basisP k)).character (z ^ 2)) := by
      intro k
      have h1 := label_character_mul_inv_of_comm basisP (k : basisP.index) z
      rw [conjugateLabel_character_eq_inv, label_character_pow_of_comm, ← inv_pow,
        label_character_pow_of_comm]
      simp only [α]
      linear_combination 2 * h1
    rw [Finset.sum_congr rfl fun k _ => hsq k, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      Finset.sum_coe_sort T (fun φ => (basisP.representation φ).character (z ^ 2) +
        (basisP.representation (conjugateLabel basisP φ)).character (z ^ 2)),
      sum_conj_transversal basisP principalP hprincipalP hT0 hT1 hT2
        (fun φ => (basisP.representation φ).character (z ^ 2)),
      sum_label_character_eq_zero_of_ne_one basisP hz2, hprincipalP, Pi.one_apply]
    have hcast : (2 : ℂ) * T.card + 1 = Nat.card P := by exact_mod_cast hTcard
    linear_combination hcast
  have hαsumR : ∑ k, (α k).re = -1 := by
    rw [← Complex.re_sum, hαsum]
    simp
  have hαsqR : ∑ k, (α k).re ^ 2 = (Nat.card P : ℝ) - 2 := by
    have h : ∀ k, (α k ^ 2).re = (α k).re ^ 2 := fun k => by
      rw [sq, Complex.mul_re, hαreal k]
      ring
    rw [← Finset.sum_congr rfl fun k _ => h k, ← Complex.re_sum, hαsq]
    simp
  have hTz : ∀ k, 1 + δ * (basis.representation a).character z -
      δ * (basis.representation (b k)).character z = 2 - α k := by
    intro k
    rw [← hTdec k, subgroupProjection_one_sub_apply basis ideal hp2 hP principal hprincipal]
    simp only [α]
    ring
  set A := (basis.representation a).character z with hA
  have hBk : ∀ k, (basis.representation (b k)).character z = δ * ((δ * A - 1) + α k) := by
    intro k
    linear_combination (-(δ : ℂ)) * hTz k - (basis.representation (b k)).character z * hδsq
  have hAβ : A = δ * ((δ * A - 1) + 1) := by linear_combination (-A) * hδsq
  have hcol := hP.principal_column_norm basis ideal hp2 principal hprincipal z.2 hz1
  have hcolR : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      Complex.normSq ((basis.representation θ).character z) = Nat.card P := by
    have h : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ((Complex.normSq ((basis.representation θ).character z) : ℝ) : ℂ) =
          (Nat.card P : ℂ) := by
      rw [← hcol]
      refine Finset.sum_congr rfl fun θ _ => ?_
      rw [Complex.mul_conj]
    exact_mod_cast h
  let S : Finset basis.index := insert principal (insert a (Finset.univ.image b))
  have hSB : S ⊆ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
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
  have hnormsq : ∀ w : ℂ, w.im = 0 → Complex.normSq ((δ * A - 1) + w) =
      Complex.normSq (δ * A - 1) + w.re ^ 2 + 2 * (δ * A - 1).re * w.re := by
    intro w hw
    have hw2 : Complex.normSq w = w.re ^ 2 := by
      rw [Complex.normSq_apply, hw]
      ring
    rw [Complex.normSq_add, hw2, Complex.mul_re, Complex.conj_re, Complex.conj_im, hw]
    ring
  have hsumS : ∑ θ ∈ S, Complex.normSq ((basis.representation θ).character z) =
      Nat.card P + ((T.card : ℝ) + 1) * Complex.normSq (δ * A - 1) := by
    rw [Finset.sum_insert hpa, Finset.sum_insert ha,
      Finset.sum_image (fun x _ y _ h => hbinj h)]
    rw [hprincipal, Pi.one_apply, Complex.normSq_one]
    have h1 : Complex.normSq A = Complex.normSq (δ * A - 1) + 1 + 2 * (δ * A - 1).re := by
      conv_lhs => rw [hAβ]
      rw [Complex.normSq_mul, hδnorm, one_mul, hnormsq 1 Complex.one_im, Complex.one_re]
      ring
    have h2 : ∀ k, Complex.normSq ((basis.representation (b k)).character z) =
        Complex.normSq (δ * A - 1) + (α k).re ^ 2 + 2 * (δ * A - 1).re * (α k).re := by
      intro k
      rw [hBk k, Complex.normSq_mul, hδnorm, one_mul, hnormsq (α k) (hαreal k)]
    rw [h1, Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, ← Finset.mul_sum, hαsumR, hαsqR, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    ring
  have hsplit := Finset.sum_sdiff hSB (f := fun θ =>
    Complex.normSq ((basis.representation θ).character z))
  rw [hsumS, hcolR] at hsplit
  have hrest_nonneg : 0 ≤ ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal \ S, Complex.normSq ((basis.representation θ).character z) :=
    Finset.sum_nonneg fun θ _ => Complex.normSq_nonneg _
  have hβ0 : Complex.normSq (δ * A - 1) = 0 := by
    have hnn := Complex.normSq_nonneg (δ * A - 1)
    have hrpos : (0 : ℝ) < (T.card : ℝ) + 1 := by
      have := (Nat.cast_nonneg T.card : (0 : ℝ) ≤ T.card)
      linarith
    nlinarith
  have hβ : δ * A - 1 = 0 := Complex.normSq_eq_zero.mp hβ0
  refine ⟨?_, fun k => ?_⟩
  · rw [hAβ, hβ, zero_add, mul_one]
  · rw [hBk k, hβ, zero_add]

end InvertedAbelianSylow

end CFSG.CyclicBlocks
