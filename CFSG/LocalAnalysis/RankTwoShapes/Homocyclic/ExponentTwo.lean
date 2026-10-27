module

public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ColumnGram
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.IntegralGram
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.Noninversion

public section

namespace CFSG.RankTwoShapes

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem exists_maximal_ideal_residue_two :
    ∃ ideal : Ideal ComplexAlgebraicIntegers, ideal.IsMaximal ∧
      CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := by
  let : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
  let P : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  have hPbot : P ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have hPmax : P.IsMaximal := hPprime.isMaximal hPbot
  have hker : RingHom.ker (algebraMap ℤ ComplexAlgebraicIntegers) ≤ P := by
    intro z hz
    rw [RingHom.mem_ker] at hz
    have hz' : (z : ℂ) = 0 := by
      have := congrArg Subtype.val hz
      simpa using this
    have : z = 0 := by exact_mod_cast hz'
    rw [this]
    exact P.zero_mem
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
  obtain ⟨p, hp, hchar, hmem⟩ := complexAlgebraicIntegers_maximal_residue_characteristic Q
  have h2 : ((2 : ℤ) : ComplexAlgebraicIntegers) ∈ Q := by
    have h2P : (2 : ℤ) ∈ P := Ideal.subset_span rfl
    rw [← hQ] at h2P
    simpa using h2P
  have hdvd : (p : ℤ) ∣ 2 := (hmem 2).mp h2
  have hp2 : p = 2 := by
    have hdvd' : p ∣ 2 := by exact_mod_cast hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd'
  subst hp2
  exact ⟨Q, hQmax, hchar⟩

theorem simple_degree_one_eq_principal {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (label : basis.index) (hdeg : Module.finrank ℂ (basis.representation label).vector = 1) :
    label = principal := by
  set ρ := (basis.representation label).representation
  have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
    intro a b
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdeg (ρ a)
    obtain ⟨c', hc', -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdeg (ρ b)
    rw [hc, hc']
    ext v
    simp [smul_smul, mul_comm]
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.ker ρ) with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hbot
    apply hinj
    rw [map_mul, map_mul, hcomm]
  · apply basis.distinct
    change (basis.representation label).character = (basis.representation principal).character
    rw [hprincipal]
    ext g
    have hg : g ∈ MonoidHom.ker ρ := by rw [htop]; trivial
    rw [MonoidHom.mem_ker] at hg
    change LinearMap.trace ℂ _ (ρ g) = 1
    rw [hg, LinearMap.trace_one, hdeg, Nat.cast_one]

theorem sylow_abelian_no_inversion {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a)
    {x : G} (hx : x ∈ (S : Subgroup G)) (hxo : 2 < orderOf x) {t : G} (ht : t * t = 1) :
    t * x * t⁻¹ ≠ x⁻¹ := by
  intro hinv
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have htp : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two, ht])
  have hconj : ∀ k : ℤ, t * x ^ k * t⁻¹ = (x ^ k)⁻¹ := by
    intro k
    rw [← conj_zpow, hinv, inv_zpow]
  have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hconj]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers x k)
    · intro hy
      have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
        rw [htinv]
        calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
          _ = y := by rw [ht]; group
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← h2, ← hk, hconj]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers x k)
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    Subgroup.zpowers_le.mpr htN
  have hsup := IsPGroup.to_sup_of_normal_right' htp hxp hle
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hsup
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hmemP : ∀ y : G, y ∈ (P : Subgroup G) → g⁻¹ * y * g ∈ (S : Subgroup G) := by
    intro y hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa [MulAut.smul_def, MulAut.conj_apply] using hy
  have htP : t ∈ (P : Subgroup G) := hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hxP : x ∈ (P : Subgroup G) := hP (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hcomm : t * x = x * t := by
    have h := hS _ (hmemP t htP) _ (hmemP x hxP)
    calc t * x = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
      _ = x * t := by group
  have hx2 : x * x = 1 := by
    have h' : t * x * t⁻¹ = x := by rw [hcomm, mul_inv_cancel_right]
    rw [h'] at hinv
    calc x * x = x * x⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel x
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx2])
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

@[expose] noncomputable def zmodTwoSignChar : AddChar (ZMod 2) ℂ where
  toFun x := (-1 : ℂ) ^ x.val
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

section Parity

variable {n : ℕ}

@[expose] noncomputable def homocyclicParityChar (hn : 1 ≤ n) : AddChar (HomocyclicVector n) ℂ :=
  zmodTwoSignChar.compAddMonoidHom
    ((ZMod.castHom (dvd_pow_self 2 (by omega : n ≠ 0)) (ZMod 2)).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _))

theorem homocyclicParityChar_apply (hn : 1 ≤ n) (v : HomocyclicVector n) :
    homocyclicParityChar hn v =
      (-1 : ℂ) ^ (ZMod.castHom (dvd_pow_self 2 (by omega : n ≠ 0)) (ZMod 2) v.1).val :=
  rfl

theorem homocyclicParityChar_ne_zero (hn : 1 ≤ n) : homocyclicParityChar hn ≠ 0 := by
  intro h
  have h1 := congrArg (fun χ : AddChar (HomocyclicVector n) ℂ => χ (1, 0)) h
  simp only [homocyclicParityChar_apply, map_one, AddChar.zero_apply] at h1
  have hval : (1 : ZMod 2).val = 1 := rfl
  rw [hval, pow_one] at h1
  norm_num at h1

theorem homocyclicParityChar_eq_one (hn : 1 ≤ n) (v : HomocyclicVector n)
    (hv : (2 ^ (n - 1) : ℕ) • v = 0) : homocyclicParityChar hn v = 1 := by
  rw [homocyclicParityChar_apply]
  suffices hzero : ZMod.castHom (dvd_pow_self 2 (by omega : n ≠ 0)) (ZMod 2) v.1 = 0 by
    rw [hzero, ZMod.val_zero, pow_zero]
  have h1 : (2 ^ (n - 1) : ℕ) • v.1 = 0 := congrArg Prod.fst hv
  rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val v.1, ← Nat.cast_mul,
    CharP.cast_eq_zero_iff (ZMod (2 ^ n)) (2 ^ n)] at h1
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have h1' : 2 ^ (n - 1) * 2 ∣ 2 ^ (n - 1) * v.1.val := by rw [← hpow]; exact h1
  have h2 : 2 ∣ v.1.val := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1'
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_zero_iff _ 2).mpr h2

end Parity

theorem homocyclic_restriction_constant_multiplicity {G : Type} [Group G] [Fintype G] {n : ℕ}
    {S : Subgroup G} (e : S ≃* HomocyclicGroup n) (basis : FiniteIrreducibleCharacterBasis G)
    (label : basis.index) (m δ : ℂ) (hm0 : homocyclicMultiplicity e basis 0 label = m)
    (hmult : ∀ φ : AddChar (HomocyclicVector n) ℂ, φ ≠ 0 →
      homocyclicMultiplicity e basis φ label = m + δ)
    (v : HomocyclicVector n) :
    (basis.representation label).character (homocyclicEmbed e v) =
      (m + δ) * (if v = 0 then (Fintype.card (HomocyclicVector n) : ℂ) else 0) - δ := by
  rw [homocyclic_restriction_fourier e basis label v]
  have hsplit : ∀ φ : AddChar (HomocyclicVector n) ℂ,
      homocyclicMultiplicity e basis φ label * φ v =
        (m + δ) * φ v - (if φ = 0 then δ else 0) * φ v := by
    intro φ
    by_cases hφ : φ = 0
    · subst hφ
      rw [hm0, ite_eq_left rfl]
      ring
    · rw [hmult φ hφ, ite_eq_right hφ]
      ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, AddChar.sum_apply_eq_ite]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    AddChar.zero_apply, mul_one]

theorem column_form_sum {α : Type*} [DecidableEq α] (B : Finset α) (o i₁ i₂ k : α)
    (ho : o ∈ B) (h1 : i₁ ∈ B) (h2 : i₂ ∈ B) (hk : k ∈ B) (b : α → ℤ) (δ₁ δ₂ ε : ℤ)
    (hform : ∀ i ∈ B, b i = -(if i = o then 1 else 0) + δ₁ * (if i = i₁ then 1 else 0) +
      δ₂ * (if i = i₂ then 1 else 0) + ε * (if i = k then 1 else 0)) (F : α → ℂ) :
    ∑ i ∈ B, (b i : ℂ) * F i = -F o + δ₁ * F i₁ + δ₂ * F i₂ + ε * F k := by
  rw [Finset.sum_congr rfl (fun i hi => by rw [hform i hi])]
  push_cast
  simp only [add_mul, neg_mul, mul_assoc, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', ho, h1, h2, hk, ite_true]

theorem homocyclic_degree_numerics (q d₁ d₂ e m₁ m₂ δ₁ δ₂ ε : ℤ) (hq : 16 ≤ q)
    (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hε : ε = 1 ∨ ε = -1)
    (hd₁ : d₁ = (m₁ + δ₁) * q - δ₁) (hd₂ : d₂ = (m₂ + δ₂) * q - δ₂)
    (hd₁pos : 1 ≤ d₁) (hd₂pos : 1 ≤ d₂) (he : 1 ≤ e)
    (h1 : -1 + δ₁ * d₁ + δ₂ * d₂ + ε * e = 0)
    (h3 : -(d₁ * d₂ * e) + δ₁ * d₂ * e + δ₂ * d₁ * e + 9 * ε * d₁ * d₂ = 0) :
    d₁ = 1 ∨ d₂ = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hd₁ne, hd₂ne⟩ := hcon
  have hsq : ∀ δ : ℤ, (δ = 1 ∨ δ = -1) → δ * δ = 1 := by
    rintro δ (rfl | rfl) <;> norm_num
  have hbound : ∀ (d m δ : ℤ), (δ = 1 ∨ δ = -1) → d = (m + δ) * q - δ → 1 ≤ d → d ≠ 1 →
      q - 1 ≤ d := by
    rintro d m δ (rfl | rfl) hd hpos hne
    · have hm : 1 ≤ m + 1 := by
        by_contra h
        have : (m + 1) * q ≤ 0 := by nlinarith
        omega
      nlinarith
    · have hm : 1 ≤ m + -1 := by
        by_contra h
        have h' : m + -1 ≤ 0 := by omega
        rcases lt_or_eq_of_le h' with hlt | heq
        · have : (m + -1) * q ≤ -q := by nlinarith
          omega
        · rw [heq] at hd
          omega
      nlinarith
  have hD₁ := hbound d₁ m₁ δ₁ hδ₁ hd₁ hd₁pos hd₁ne
  have hD₂ := hbound d₂ m₂ δ₂ hδ₂ hd₂ hd₂pos hd₂ne
  have hd₁15 : 15 ≤ d₁ := by omega
  have hd₂15 : 15 ≤ d₂ := by omega
  have hP : 13 * (d₁ * d₂) ≤ 15 * (d₁ * d₂ - δ₁ * d₂ - δ₂ * d₁) := by
    have hδ₁d : δ₁ * d₂ ≤ d₂ := by rcases hδ₁ with rfl | rfl <;> omega
    have hδ₂d : δ₂ * d₁ ≤ d₁ := by rcases hδ₂ with rfl | rfl <;> omega
    nlinarith
  have hPpos : 0 < d₁ * d₂ - δ₁ * d₂ - δ₂ * d₁ := by nlinarith
  have hEP : e * (d₁ * d₂ - δ₁ * d₂ - δ₂ * d₁) = 9 * ε * (d₁ * d₂) := by linarith
  have hε1 : ε = 1 := by
    rcases hε with h | h
    · exact h
    · exfalso
      rw [h] at hEP
      have : 0 < e * (d₁ * d₂ - δ₁ * d₂ - δ₂ * d₁) := by positivity
      nlinarith
  rw [hε1] at hEP h1
  have he10 : e ≤ 10 := by
    by_contra h
    have h11 : 11 ≤ e := by omega
    nlinarith
  have hM : e - 3 = -(q * (δ₁ * (m₁ + δ₁) + δ₂ * (m₂ + δ₂))) := by
    have hs₁ := hsq δ₁ hδ₁
    have hs₂ := hsq δ₂ hδ₂
    rw [hd₁, hd₂] at h1
    linear_combination h1 + hs₁ + hs₂
  have he3 : e = 3 := by
    set M := δ₁ * (m₁ + δ₁) + δ₂ * (m₂ + δ₂)
    rcases lt_trichotomy M 0 with hlt | heq | hgt
    · have : q ≤ -(q * M) := by nlinarith
      omega
    · rw [heq] at hM
      omega
    · have : q ≤ q * M := by nlinarith
      omega
  rw [he3] at hEP
  have hδ₁d : -(δ₁ * d₂) ≤ d₂ := by rcases hδ₁ with rfl | rfl <;> omega
  have hδ₂d : -(δ₂ * d₁) ≤ d₁ := by rcases hδ₂ with rfl | rfl <;> omega
  nlinarith

theorem homocyclic_coord_of_orderOf_ne {G : Type*} [Group G] {n : ℕ} (hn : 1 ≤ n)
    {S : Subgroup G} (e : S ≃* HomocyclicGroup n) (s : S) (hs : orderOf (s : G) ≠ 2 ^ n) :
    (2 ^ (n - 1) : ℕ) • homocyclicCoord e s = 0 := by
  have hpow : (s : G) ^ (2 ^ n) = 1 := by
    rw [← homocyclicEmbed_coord e s, ← homocyclicEmbed_nsmul, vector_two_pow_nsmul,
      homocyclicEmbed_zero]
  have hdvd : orderOf (s : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hkn : k ≠ n := fun h => hs (by rw [hkeq, h])
  have hdvd' : orderOf (s : G) ∣ 2 ^ (n - 1) := by
    rw [hkeq]
    exact Nat.pow_dvd_pow 2 (by omega)
  apply homocyclicEmbed_injective e
  rw [homocyclicEmbed_nsmul, homocyclicEmbed_coord, homocyclicEmbed_zero]
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd'

theorem homocyclic_sylow_simple_exponent_two {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) (n : ℕ) (hn : 1 ≤ n)
    (hS : Nonempty ((S : Subgroup G) ≃*
      Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) : n = 1 := by
  by_contra hn1
  have hn2 : 2 ≤ n := by omega
  obtain ⟨e⟩ := hS
  let : Fintype G := Fintype.ofFinite G
  have hNC := homocyclic_normalizer_ne_centralizer_of_simple S e hn hnonab
  obtain ⟨ideal, hmax, hchar⟩ := exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hoB : principal ∈ B := coefficientBlock_self_mem basis _ principal
  obtain ⟨-, -, hint, hprin, hdegsum, hgram, -⟩ :=
    homocyclic_principal_restriction_column_gram S e ideal basis principal hn hNC hprincipal
  obtain ⟨ι, hι, ψ, hψ0, hpair, hcover⟩ := exists_homocyclic_orbit_representatives S e
  have hcard := homocyclic_orbit_representatives_card S e hn hNC ψ hψ0 hpair hcover
  have hS4 : Nat.card S = 4 ^ n := homocyclic_card e
  have hq16 : 16 ≤ 4 ^ n :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hι5 : 5 ≤ Fintype.card ι := by omega
  choose bInt hbInt using hint
  let b : ι → basis.index → ℤ := fun i χ => bInt (ψ i) χ
  have hb : ∀ i χ, homocyclicColumn e basis (ψ i) χ = (b i χ : ℂ) := fun i χ => hbInt (ψ i) χ
  have hbo : ∀ i, b i principal = -1 := by
    intro i
    have h := hprin (ψ i) (hψ0 i)
    rw [hb] at h
    exact_mod_cast h
  have hgramZ : ∀ i j, ∑ χ ∈ B, b i χ * b j χ = 3 + if i = j then 1 else 0 := by
    intro i j
    have h := hgram (ψ i) (ψ j) (hψ0 i) (hψ0 j)
    simp_rw [hb] at h
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left (homocyclicOrbitRel_refl e _)] at h
      rw [ite_eq_left rfl]
      exact_mod_cast h
    · rw [ite_eq_right (fun h' => hij (hpair j i h').symm)] at h
      rw [ite_eq_right hij]
      exact_mod_cast h
  let deg : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
  have hdegchar : ∀ χ, (basis.representation χ).character 1 = (deg χ : ℂ) := by
    intro χ
    simp only [deg, FiniteComplexRepresentation.character, Representation.char_one]
  have hdegpos : ∀ χ, 0 < deg χ := by
    intro χ
    apply Nat.pos_of_ne_zero
    intro h
    apply irreducible_character_degree_ne_zero _ (basis.irreducible χ)
    rw [hdegchar, h, Nat.cast_zero]
  have hann : ∀ i, ∑ χ ∈ B, (b i χ : ℝ) * (deg χ : ℝ) = 0 := by
    intro i
    have h := hdegsum (ψ i)
    simp_rw [hb, hdegchar] at h
    have hZ : ∑ χ ∈ B, b i χ * (deg χ : ℤ) = 0 := by exact_mod_cast h
    exact_mod_cast hZ
  obtain ⟨i₁, i₂, k, δ₁, δ₂, ε, hi₁, hi₂, hk, hδ₁, hδ₂, hε, hi₁o, hi₂o, hi₁₂, -, hkdist, hform,
    -⟩ := integral_gram_three_common_rows B principal hoB hι5 b hbo hgramZ
      (fun χ => (deg χ : ℝ)) (fun χ _ => by exact_mod_cast hdegpos χ) hann
  have hbi₁ : ∀ i, b i i₁ = δ₁ := by
    intro i
    rw [hform i i₁ hi₁, ite_eq_right hi₁o, ite_eq_left rfl, ite_eq_right hi₁₂,
      ite_eq_right (Ne.symm (hkdist i).2.1)]
    ring
  have hbi₂ : ∀ i, b i i₂ = δ₂ := by
    intro i
    rw [hform i i₂ hi₂, ite_eq_right hi₂o, ite_eq_right (Ne.symm hi₁₂), ite_eq_left rfl,
      ite_eq_right (Ne.symm (hkdist i).2.2)]
    ring
  have hvalues : ∀ (χ : basis.index) (δ : ℤ), (∀ i, b i χ = δ) →
      ∃ m : ℤ, ∀ v : HomocyclicVector n,
        (basis.representation χ).character (homocyclicEmbed e v) =
          ((m : ℂ) + δ) * (if v = 0 then (Fintype.card (HomocyclicVector n) : ℂ) else 0) - δ := by
    intro χ δ hδ
    obtain ⟨m, hm⟩ := homocyclicMultiplicity_integer e basis 0 χ
    refine ⟨m, fun v => homocyclic_restriction_constant_multiplicity e basis χ m δ hm ?_ v⟩
    intro φ hφ
    obtain ⟨i, hi⟩ := hcover φ hφ
    rw [homocyclicMultiplicity_orbit e basis (ψ i) φ hi χ, ← hm]
    have h := homocyclicColumn_eq_sub e basis (ψ i) χ
    rw [hb, hδ] at h
    rw [h]
    ring
  obtain ⟨m₁, hm₁⟩ := hvalues i₁ δ₁ hbi₁
  obtain ⟨m₂, hm₂⟩ := hvalues i₂ δ₂ hbi₂
  have hqC : (Fintype.card (HomocyclicVector n) : ℂ) = ((4 ^ n : ℕ) : ℂ) := by
    rw [← card_homocyclic_eq_card_vector e, hS4]
  set a : HomocyclicVector n := (2 ^ (n - 1), 0)
  obtain ⟨ha2, ha0⟩ := homocyclic_half_vector (n := n) hn
  set J := homocyclicEmbed e a
  have hJ1 : J ≠ 1 := fun h => ha0 ((homocyclicEmbed_eq_one_iff e a).mp h)
  have hJ2 : J ^ 2 = 1 := by
    rw [pow_two, ← homocyclicEmbed_add, ha2, homocyclicEmbed_zero]
  have hJ : orderOf J = 2 := orderOf_eq_prime hJ2 hJ1
  have hd₁ : (deg i₁ : ℂ) = ((m₁ : ℂ) + δ₁) * ((4 ^ n : ℕ) : ℂ) - δ₁ := by
    rw [← hdegchar, ← homocyclicEmbed_zero e, hm₁, ite_eq_left rfl, hqC]
  have hd₂ : (deg i₂ : ℂ) = ((m₂ : ℂ) + δ₂) * ((4 ^ n : ℕ) : ℂ) - δ₂ := by
    rw [← hdegchar, ← homocyclicEmbed_zero e, hm₂, ite_eq_left rfl, hqC]
  have hJ₁ : (basis.representation i₁).character J = -δ₁ := by
    rw [hm₁, ite_eq_right ha0]
    ring
  have hJ₂ : (basis.representation i₂).character J = -δ₂ := by
    rw [hm₂, ite_eq_right ha0]
    ring
  set ψ₁ := homocyclicParityChar hn
  obtain ⟨t₀, ht₀⟩ := hcover ψ₁ (homocyclicParityChar_ne_zero hn)
  let U : Set G := {x | x ∈ (S : Subgroup G) ∧ orderOf x = 2 ^ n}
  have hUQ : U ⊆ ((S : Subgroup G) : Set G) := fun x hx => hx.1
  have hU : ∀ x ∈ U, ∀ t : G, IsConj J t → t * x * t⁻¹ ≠ x⁻¹ := by
    intro x hx t ht
    have htt : t * t = 1 := by
      obtain ⟨c, rfl⟩ := isConj_iff.mp ht
      calc c * J * c⁻¹ * (c * J * c⁻¹) = c * (J * J) * c⁻¹ := by group
        _ = 1 := by rw [← pow_two, hJ2]; group
    have hxo : 2 < orderOf x := by
      rw [hx.2]
      calc 2 < 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact sylow_abelian_no_inversion S (fun a ha b hb => homocyclic_mul_comm e a b ha hb) hx.1
      hxo htt
  let θ : ↥(S : Subgroup G) → ℂ := fun s => ψ₁ (homocyclicCoord e s) - 1
  have hθ : θ ∈ virtualCharacters (S : Subgroup G) :=
    Submodule.sub_mem _ (homocyclicChar_mem_virtualCharacters e ψ₁)
      (one_mem_virtualCharacters' (S := (S : Subgroup G)))
  have hθU : ∀ x : (S : Subgroup G), (x : G) ∉ U → θ x = 0 := by
    intro x hx
    have hxo : orderOf (x : G) ≠ 2 ^ n := fun h => hx ⟨x.property, h⟩
    simp only [θ, ψ₁]
    rw [homocyclicParityChar_eq_one hn _ (homocyclic_coord_of_orderOf_ne hn e x hxo), sub_self]
  obtain ⟨-, hI1, hI2, hI3⟩ := principal_noninversion_restriction_identities basis ideal 2
    principal (S : Subgroup G) S.isPGroup' J hJ U hUQ hU θ hθ hθU
  have hacol : ∀ χ, characterPairing
      (fun x : (S : Subgroup G) => (basis.representation χ).character x.val) θ = (b t₀ χ : ℂ) := by
    intro χ
    rw [← hb]
    exact homocyclicColumn_orbit e basis (ψ t₀) ψ₁ ht₀ χ
  simp_rw [hacol] at hI1 hI2 hI3
  rw [column_form_sum B principal i₁ i₂ (k t₀) hoB hi₁ hi₂ (hk t₀) (b t₀) δ₁ δ₂ ε (hform t₀)]
    at hI1 hI2 hI3
  set η := k t₀
  have hprinJ : (basis.representation principal).character J = 1 := by rw [hprincipal]; rfl
  have hprin1 : (basis.representation principal).character 1 = 1 := by rw [hprincipal]; rfl
  rw [hprin1] at hI1
  rw [hprinJ, hJ₁, hJ₂] at hI2
  rw [hprinJ, hprin1, hJ₁, hJ₂] at hI3
  have hsq : ∀ δ : ℤ, (δ = 1 ∨ δ = -1) → ((δ : ℂ)) ^ 2 = 1 := by
    rintro δ (rfl | rfl) <;> norm_num
  have hηJ : (ε : ℂ) * (basis.representation η).character J = 3 := by
    have h1 := hsq δ₁ hδ₁
    have h2 := hsq δ₂ hδ₂
    linear_combination hI2 + h1 + h2
  have hηJ2 : (basis.representation η).character J ^ 2 = 9 := by
    have hε2 := hsq ε hε
    have hsq9 : ((ε : ℂ) * (basis.representation η).character J) ^ 2 = 9 := by
      rw [hηJ]
      norm_num
    calc (basis.representation η).character J ^ 2 =
        (ε : ℂ) ^ 2 * (basis.representation η).character J ^ 2 := by rw [hε2, one_mul]
      _ = ((ε : ℂ) * (basis.representation η).character J) ^ 2 := by ring
      _ = 9 := hsq9
  rw [hdegchar, hdegchar, hdegchar] at hI1
  rw [hdegchar, hdegchar, hdegchar] at hI3
  have hd₁ne : (deg i₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hdegpos i₁).ne'
  have hd₂ne : (deg i₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hdegpos i₂).ne'
  have hene : (deg η : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hdegpos η).ne'
  have hI3' : -((deg i₁ : ℂ) * deg i₂ * deg η) + δ₁ * deg i₂ * deg η + δ₂ * deg i₁ * deg η +
      9 * ε * deg i₁ * deg i₂ = 0 := by
    have h1 := hsq δ₁ hδ₁
    have h2 := hsq δ₂ hδ₂
    rw [neg_sq, neg_sq, h1, h2, hηJ2] at hI3
    field_simp at hI3
    linear_combination hI3
  have hI1Z : -1 + δ₁ * (deg i₁ : ℤ) + δ₂ * (deg i₂ : ℤ) + ε * (deg η : ℤ) = 0 := by
    have : (-1 + δ₁ * (deg i₁ : ℤ) + δ₂ * (deg i₂ : ℤ) + ε * (deg η : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hI1
    exact_mod_cast this
  have hI3Z : -((deg i₁ : ℤ) * deg i₂ * deg η) + δ₁ * deg i₂ * deg η + δ₂ * deg i₁ * deg η +
      9 * ε * deg i₁ * deg i₂ = 0 := by
    exact_mod_cast hI3'
  have hd₁Z : (deg i₁ : ℤ) = (m₁ + δ₁) * ((4 ^ n : ℕ) : ℤ) - δ₁ := by exact_mod_cast hd₁
  have hd₂Z : (deg i₂ : ℤ) = (m₂ + δ₂) * ((4 ^ n : ℕ) : ℤ) - δ₂ := by exact_mod_cast hd₂
  have hnum := homocyclic_degree_numerics ((4 ^ n : ℕ) : ℤ) (deg i₁) (deg i₂) (deg η) m₁ m₂ δ₁ δ₂
    ε (by exact_mod_cast hq16) hδ₁ hδ₂ hε hd₁Z hd₂Z (by exact_mod_cast hdegpos i₁)
    (by exact_mod_cast hdegpos i₂) (by exact_mod_cast hdegpos η) hI1Z hI3Z
  rcases hnum with h | h
  · exact hi₁o (simple_degree_one_eq_principal hnonab basis principal hprincipal i₁
      (by exact_mod_cast h))
  · exact hi₂o (simple_degree_one_eq_principal hnonab basis principal hprincipal i₂
      (by exact_mod_cast h))

end CFSG.RankTwoShapes
