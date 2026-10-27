module

public import CFSG.CharacterTheory.Semidihedral.Principal.BrauerSecondMainBlocks
public import CFSG.CharacterTheory.Blocks.InnerProduct
public import CFSG.CharacterTheory.TwoRankLowerBound.SupportedPrincipalInduction

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

@[expose] def involutionLocalSection {G : Type*} [Group G] (t : G) :
    Set (Subgroup.centralizer (Subgroup.zpowers t : Set G)) :=
  {x | ∃ y : Subgroup.centralizer (Subgroup.zpowers t : Set G),
    x = ⟨t, element_mem_centralizer_zpowers t⟩ * y ∧ Odd (orderOf y)}

@[expose] def involutionSectionUnion {G : Type*} [Group G] (t : G) : Set G :=
  {x | ∃ g : G, ∃ q ∈ involutionLocalSection t, x = g * (q : G) * g⁻¹}

@[expose] def sectionSupported {X : Type*} (S : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | ∀ x, x ∉ S → f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx]
  zero_mem' x _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]

@[expose] noncomputable def brauerFiberBlocks {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (u : G) (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (label : basis.index) : Finset (Finset localBasis.index) :=
  (Finset.univ.filter fun θ : localBasis.index =>
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal label).image
    (coefficientBlock localBasis (localizedComplexIntegerRing ideal))

namespace BrauerFiberSection

theorem involution_part_unique {G : Type*} [Group G] {a b a' b' : G} (hab : Commute a b)
    (ha : a ^ 2 = 1) (hb : Odd (orderOf b)) (hab' : Commute a' b') (ha' : a' ^ 2 = 1)
    (hb' : Odd (orderOf b')) (h : a * b = a' * b') : a = a' := by
  have hm : Odd (orderOf b * orderOf b') := hb.mul hb'
  obtain ⟨k, hk⟩ := hm
  have hpow : ∀ {x y : G}, Commute x y → x ^ 2 = 1 → orderOf y ∣ orderOf b * orderOf b' →
      (x * y) ^ (orderOf b * orderOf b') = x := by
    intro x y hxy hx hy
    rw [hxy.mul_pow, orderOf_dvd_iff_pow_eq_one.mp hy, mul_one, hk, pow_succ, pow_mul, hx,
      one_pow, one_mul]
  rw [← hpow hab ha (dvd_mul_right _ _), ← hpow hab' ha' (dvd_mul_left _ _), h]

theorem involutionLocalSection_conj {G : Type*} [Group G] (t : G)
    (x c : Subgroup.centralizer (Subgroup.zpowers t : Set G))
    (hx : x ∈ involutionLocalSection t) : c * x * c⁻¹ ∈ involutionLocalSection t := by
  obtain ⟨y, rfl, hy⟩ := hx
  refine ⟨c * y * c⁻¹, ?_, ?_⟩
  · have hcomm : c * ⟨t, element_mem_centralizer_zpowers t⟩ =
        ⟨t, element_mem_centralizer_zpowers t⟩ * c := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp c.2 t (Subgroup.mem_zpowers t)).symm
    calc c * (⟨t, element_mem_centralizer_zpowers t⟩ * y) * c⁻¹ =
        (c * ⟨t, element_mem_centralizer_zpowers t⟩) * y * c⁻¹ := by group
      _ = ⟨t, element_mem_centralizer_zpowers t⟩ * (c * y * c⁻¹) := by rw [hcomm]; group
  · have h := (MulAut.conj c).orderOf_eq y
    rw [MulAut.conj_apply] at h
    rwa [h]

theorem commute_centralizerSelf {G : Type*} [Group G] (t : G)
    (y : Subgroup.centralizer (Subgroup.zpowers t : Set G)) :
    Commute (⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) y := by
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp y.2 t (Subgroup.mem_zpowers t))

theorem mem_involutionLocalSection_iff {G : Type*} [Group G] {t : G} (ht : orderOf t = 2)
    (u v : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (e : ℕ) (hu : orderOf u ∣ 2 ^ e)
    (hv : Nat.Coprime 2 (orderOf v)) (huv : Commute u v) :
    u * v ∈ involutionLocalSection t ↔
      u = (⟨t, element_mem_centralizer_zpowers t⟩ :
        Subgroup.centralizer (Subgroup.zpowers t : Set G)) := by
  have ht2 : (⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
  have hvodd : Odd (orderOf v) := Nat.coprime_two_left.mp hv
  constructor
  · rintro ⟨y, hxy, hy⟩
    have hu2 : u ^ 2 = 1 := by
      have hm : Odd (orderOf v * orderOf y) := hvodd.mul hy
      have hpow : u ^ (2 * (orderOf v * orderOf y)) = 1 := by
        have h1 : (u * v) ^ (2 * (orderOf v * orderOf y)) = u ^ (2 * (orderOf v * orderOf y)) := by
          rw [huv.mul_pow, orderOf_dvd_iff_pow_eq_one.mp
            (dvd_mul_of_dvd_right (dvd_mul_right _ _) 2), mul_one]
        have h2 : (⟨t, element_mem_centralizer_zpowers t⟩ * y :
            Subgroup.centralizer (Subgroup.zpowers t : Set G)) ^ (2 * (orderOf v * orderOf y)) =
              1 := by
          rw [(commute_centralizerSelf t y).mul_pow, pow_mul, ht2, one_pow, one_mul,
            orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_of_dvd_right (dvd_mul_left _ _) 2)]
        rw [← h1, hxy, h2]
      have hdvd : orderOf u ∣ 2 := by
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
        have h2m := orderOf_dvd_of_pow_eq_one hpow
        rw [hj] at h2m ⊢
        have hcop : Nat.Coprime (2 ^ j) (orderOf v * orderOf y) :=
          Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
        exact hcop.dvd_of_dvd_mul_right h2m
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact involution_part_unique huv hu2 hvodd (commute_centralizerSelf t y) ht2 hy hxy
  · rintro rfl
    exact ⟨v, rfl, hvodd⟩

theorem involutionLocalSection_primeSectionUnion {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) : primeSectionUnion 2 (involutionLocalSection t) := by
  intro u₁ u₂ v₁ v₂ e₁ e₂ hu₁ hu₂ hv₁ hv₂ hc₁ hc₂ hconj
  rw [mem_involutionLocalSection_iff ht u₁ v₁ e₁ hu₁ hv₁ hc₁,
    mem_involutionLocalSection_iff ht u₂ v₂ e₂ hu₂ hv₂ hc₂]
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hcentral : ∀ c : Subgroup.centralizer (Subgroup.zpowers t : Set G),
      c * (⟨t, element_mem_centralizer_zpowers t⟩ :
        Subgroup.centralizer (Subgroup.zpowers t : Set G)) * c⁻¹ =
          ⟨t, element_mem_centralizer_zpowers t⟩ := by
    intro c
    rw [((commute_centralizerSelf t c).symm).eq, mul_inv_cancel_right]
  constructor
  · rintro rfl
    rw [← hc, hcentral]
  · intro h2
    rw [h2] at hc
    have h := hcentral c⁻¹
    rw [inv_inv] at h
    have hu : u₁ = c⁻¹ * ⟨t, element_mem_centralizer_zpowers t⟩ * c := by
      rw [← hc]
      group
    rw [hu, h]

theorem mem_centralizer_of_conj_mem_involutionLocalSection {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) (x : G) (hx : x ∈ Subtype.val '' involutionLocalSection t) (c : G)
    (hc : c⁻¹ * x * c ∈ Subtype.val '' involutionLocalSection t) :
    c ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
  obtain ⟨_, ⟨y, rfl, hy⟩, rfl⟩ := hx
  obtain ⟨_, ⟨y', rfl, hy'⟩, hxc⟩ := hc
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hty : Commute t (y : G) := Subtype.ext_iff.mp (commute_centralizerSelf t y)
  have hty' : Commute t (y' : G) := Subtype.ext_iff.mp (commute_centralizerSelf t y')
  have hconj : (c⁻¹ * t * c) * (c⁻¹ * y * c) = t * y' := by
    rw [show (c⁻¹ * t * c) * (c⁻¹ * y * c) = c⁻¹ * (t * y) * c by group]
    exact hxc.symm
  have hcomm : Commute (c⁻¹ * t * c) (c⁻¹ * y * c) := by
    have h := hty.map (MulAut.conj c⁻¹).toMonoidHom
    simpa [MulAut.conj_apply] using h
  have hsq : (c⁻¹ * t * c) ^ 2 = 1 := by
    have h := conj_pow (a := c⁻¹) (b := t) (i := 2)
    rw [inv_inv] at h
    rw [h, ht2, mul_one, inv_mul_cancel]
  have hord : Odd (orderOf (c⁻¹ * (y : G) * c)) := by
    have h := (MulAut.conj c⁻¹).orderOf_eq (y : G)
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, Subgroup.orderOf_coe]
    exact hy
  have hy'odd : Odd (orderOf (y' : G)) := by rwa [Subgroup.orderOf_coe]
  have heq := involution_part_unique hcomm hsq hord hty' ht2 hy'odd hconj
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have htc : t * c = c * t := by
    have := congrArg (fun z => c * z) heq
    simp only [mul_assoc, mul_inv_cancel_left] at this
    exact this
  exact ((Commute.zpow_left htc k).eq)

theorem sum_image_coefficientBlock_projection {H : Type*} [Group H] [Fintype H]
    (localBasis : FiniteIrreducibleCharacterBasis H) (R : Subring ℂ)
    (F : Finset localBasis.index) (hF : ∀ θ ∈ F, coefficientBlock localBasis R θ ⊆ F)
    (f : H → ℂ) :
    ∑ b ∈ F.image (coefficientBlock localBasis R), characterSubsetProjection localBasis b f =
      characterSubsetProjection localBasis F f := by
  have hunion : (F.image (coefficientBlock localBasis R)).biUnion id = F := by
    ext θ
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨β, ⟨θ', hθ', rfl⟩, hθβ⟩
      exact hF θ' hθ' hθβ
    · intro hθ
      exact ⟨_, ⟨θ, hθ, rfl⟩, coefficientBlock_self_mem localBasis R θ⟩
  have hdisj : ((F.image (coefficientBlock localBasis R) : Finset (Finset localBasis.index)) :
      Set (Finset localBasis.index)).PairwiseDisjoint id := by
    intro β hβ β' hβ' hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hβ hβ'
    obtain ⟨θ, -, rfl⟩ := hβ
    obtain ⟨θ', -, rfl⟩ := hβ'
    rcases coefficientBlock_disjoint_or_eq localBasis R θ θ' with h | h
    · exact h
    · exact absurd h hne
  funext x
  rw [Finset.sum_apply]
  conv_rhs => rw [← hunion]
  rw [BrauerSecondMain.characterSubsetProjection_apply_sum, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [BrauerSecondMain.characterSubsetProjection_apply_sum]
  rfl

variable {G : Type*} [Group G] [Fintype G]

theorem mem_coefficientBlock_of_residue_eq (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] {label χ : basis.index}
    (h : centralCharacterResidueHom basis ideal label = centralCharacterResidueHom basis ideal χ) :
    χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label :=
  (coefficientBlock_mem_iff _ _ _ _).mpr
    ((sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label χ).mpr h)

theorem brauerFiber_labels_closed (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (label : basis.index) :
    ∀ θ ∈ (Finset.univ.filter fun θ : localBasis.index =>
        brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
          (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis θ =
            centralCharacterResidueHom basis ideal label),
      coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ ⊆
        (Finset.univ.filter fun θ : localBasis.index =>
          brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
            (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) localBasis θ =
              centralCharacterResidueHom basis ideal label) := by
  intro θ hθ θ' hθ'
  have hsame := BrauerSecondMain.brauerNormalizerCharacterResidueHom_eq_of_mem_coefficientBlock
    ideal p u hgroup localBasis hθ'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
  exact hsame.trans hθ

theorem section_sum_fiber_of_mem (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G) (ht : orderOf t = 2)
    (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (x : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hx : x ∈ involutionLocalSection t) :
    (basis.representation χ).character x =
      ∑ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
        characterSubsetProjection localBasis b
          (fun h => (basis.representation χ).character h) x := by
  obtain ⟨y, rfl, hy⟩ := hx
  exact (brauer_second_main_theorem basis ideal 2 t 1 (by rw [ht, pow_one]) hgroup localBasis
    label χ hχ y (Nat.coprime_two_left.mpr hy)).2

theorem section_fiber_projection_zero_of_not_mem (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G) (ht : orderOf t = 2)
    (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label χ : basis.index)
    (hχ : χ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (b : Finset localBasis.index)
    (hb : b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label)
    (x : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hx : x ∈ involutionLocalSection t) :
    characterSubsetProjection localBasis b
      (fun h => (basis.representation χ).character h) x = 0 := by
  obtain ⟨y, rfl, hy⟩ := hx
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  apply (brauer_second_main_theorem basis ideal 2 t 1 (by rw [ht, pow_one]) hgroup localBasis χ χ
    (coefficientBlock_self_mem basis _ χ) y (Nat.coprime_two_left.mpr hy)).1 θ
  intro heq
  exact hχ (mem_coefficientBlock_of_residue_eq basis ideal (hθ.symm.trans heq))

theorem section_projection_zero_of_not_fiber (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G) (ht : orderOf t = 2)
    (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (θ : localBasis.index)
    (hθ : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) hgroup
      (Subgroup.centralizer (Subgroup.zpowers t : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ ≠
        centralCharacterResidueHom basis ideal label)
    (x : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hx : x ∈ involutionLocalSection t) :
    characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ)
      (fun h => (basis.representation χ).character h) x = 0 := by
  obtain ⟨y, rfl, hy⟩ := hx
  exact (brauer_second_main_theorem basis ideal 2 t 1 (by rw [ht, pow_one]) hgroup localBasis
    label χ hχ y (Nat.coprime_two_left.mpr hy)).1 θ hθ

theorem fiber_projection_inv_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G) (ht : orderOf t = 2)
    (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label χ : basis.index)
    (hχ : χ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (x : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hx : x ∈ involutionLocalSection t) :
    characterSubsetProjection localBasis
      (Finset.univ.filter fun θ : localBasis.index =>
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) hgroup
          (Subgroup.centralizer (Subgroup.zpowers t : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis θ =
            centralCharacterResidueHom basis ideal label)
      (fun h => (basis.representation χ).character h) x⁻¹ = 0 := by
  obtain ⟨y, rfl, hy⟩ := hx
  apply BrauerSecondMain.mismatch_projection_zero_inv basis ideal 2 t 1 (by rw [ht, pow_one])
    hgroup localBasis χ χ (coefficientBlock_self_mem basis _ χ) _
    ((characterSubsetAdmissible_iff_union_blocks localBasis _ _).mpr
      (brauerFiber_labels_closed basis ideal 2 t hgroup localBasis label)) _ y
    (Nat.coprime_two_left.mpr hy)
  intro θ hθ heq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  exact hχ (mem_coefficientBlock_of_residue_eq basis ideal (hθ.symm.trans heq))

theorem compl_fiber_projection_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G) (ht : orderOf t = 2)
    (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (x : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hx : x ∈ involutionLocalSection t) :
    characterSubsetProjection localBasis
      (Finset.univ.filter fun θ : localBasis.index =>
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) hgroup
          (Subgroup.centralizer (Subgroup.zpowers t : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis θ =
            centralCharacterResidueHom basis ideal label)ᶜ
      (fun h => (basis.representation χ).character h) x = 0 := by
  obtain ⟨y, rfl, hy⟩ := hx
  have hzero := BrauerSecondMain.mismatch_projection_zero_inv basis ideal 2 t 1
    (by rw [ht, pow_one]) hgroup localBasis label χ hχ _
    (characterSubsetAdmissible_compl localBasis _ _
      ((characterSubsetAdmissible_iff_union_blocks localBasis _ _).mpr
        (brauerFiber_labels_closed basis ideal 2 t hgroup localBasis label)))
    (fun θ hθ => by simpa using hθ) y (Nat.coprime_two_left.mpr hy)
  have h := BrauerSecondMain.characterSubsetProjection_restrict_inv basis χ _ localBasis
    (Finset.univ.filter fun θ : localBasis.index =>
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) hgroup
          (Subgroup.centralizer (Subgroup.zpowers t : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis θ =
            centralCharacterResidueHom basis ideal label)ᶜ
    ((⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) * y)⁻¹
  rw [inv_inv] at h
  rw [h, hzero, map_zero]

theorem blocksInnerProduct_eq_zero_of_disjoint {H : Type} [Group H] [Fintype H]
    (localBasis : FiniteIrreducibleCharacterBasis H) (S S' : Finset localBasis.index)
    (hdisj : Disjoint S S') (α β : H → ℂ) (hα : α ∈ coefficientCharacterSpace localBasis S)
    (hβ : β ∈ coefficientCharacterSpace localBasis S') : BlocksInnerProduct α β = 0 := by
  induction hβ using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨θ', hθ', rfl⟩ := hg
    have hv : (localBasis.representation θ').character ∈ BlocksVChar H :=
      AddSubgroup.subset_closure ⟨_, inferInstance, inferInstance, inferInstance,
        (localBasis.representation θ').representation, localBasis.irreducible θ', rfl⟩
    rw [blocksInnerProduct_eq_characterPairing α hv]
    exact coefficientCharacterSpace_pairing_zero_outside localBasis S α hα θ'
      (Finset.disjoint_right.mp hdisj hθ')
  | zero => simp [BlocksInnerProduct]
  | add f g _ _ hf hg =>
    simp only [BlocksInnerProduct, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      at hf hg ⊢
    rw [hf, hg, add_zero]
  | smul c f _ hf =>
    unfold BlocksInnerProduct at hf ⊢
    have h : ∑ x, α x * starRingEnd ℂ ((c • f) x) =
        starRingEnd ℂ c * ∑ x, α x * starRingEnd ℂ (f x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    rw [h, mul_left_comm, hf, mul_zero]

theorem section_projection_identity_character (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G) (ht : orderOf t = 2)
    (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label χ : basis.index)
    (x : Subgroup.centralizer (Subgroup.zpowers t : Set G)) (hx : x ∈ involutionLocalSection t) :
    characterSubsetProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        label) (basis.representation χ).character x =
      ∑ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
        characterSubsetProjection localBasis b
          (fun h => (basis.representation χ).character h) x := by
  by_cases hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label
  · rw [characterSubsetProjection_character basis _ χ hχ]
    exact section_sum_fiber_of_mem basis ideal t ht hgroup localBasis label χ hχ x hx
  · rw [characterSubsetProjection_character_not_mem basis _ χ hχ, Pi.zero_apply]
    exact (Finset.sum_eq_zero fun b hb => section_fiber_projection_zero_of_not_mem basis ideal t ht
      hgroup localBasis label χ hχ b hb x hx).symm

end BrauerFiberSection

open BrauerFiberSection

theorem brauer_fiber_involution_section_induction_decomposition {G : Type} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G) (ht : orderOf t = 2)
    (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label : basis.index) :
    (∀ f : G → ℂ, (∀ x g : G, f (g * x * g⁻¹) = f x) →
      characterFunctionMask (involutionLocalSection t)
          (fun h => characterSubsetProjection basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) label) f h) =
        characterFunctionMask (involutionLocalSection t)
          (∑ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
            characterSubsetProjection localBasis b (fun h => f h))) ∧
    (∀ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      ∀ b' ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label, b ≠ b' →
        ∀ α ∈ coefficientCharacterSpace localBasis b ⊓
          sectionSupported (involutionLocalSection t),
        ∀ β ∈ coefficientCharacterSpace localBasis b' ⊓
          sectionSupported (involutionLocalSection t),
          BlocksInnerProduct α β = 0) ∧
    ∃ e : ↥(⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
          coefficientCharacterSpace localBasis b ⊓
            sectionSupported (involutionLocalSection t)) ≃ₗ[ℂ]
        ↥(coefficientCharacterSpace basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (involutionSectionUnion t)),
      (∀ α, (e α : G → ℂ) =
        inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) α) ∧
      (∀ F, (e.symm F : Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ) =
        characterFunctionMask (involutionLocalSection t) (fun h => (F : G → ℂ) h)) ∧
      (∀ α β, BlocksInnerProduct (e α : G → ℂ) (e β) =
        BlocksInnerProduct (α : Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ) β) := by
  have hQ := involutionLocalSection_primeSectionUnion ht
  set Fib := Finset.univ.filter fun θ : localBasis.index =>
    brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t) hgroup
      (Subgroup.centralizer (Subgroup.zpowers t : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ =
        centralCharacterResidueHom basis ideal label with hFib
  have hclosed := brauerFiber_labels_closed basis ideal 2 t hgroup localBasis label
  have hFibadm : characterSubsetAdmissible localBasis (localizedComplexIntegerRing ideal) Fib :=
    (characterSubsetAdmissible_iff_union_blocks localBasis _ _).mpr hclosed
  have hT : brauerFiberBlocks basis ideal 2 t hgroup localBasis label =
      Fib.image (coefficientBlock localBasis (localizedComplexIntegerRing ideal)) := rfl
  have hproj : ∀ f : G → ℂ, (∀ x g : G, f (g * x * g⁻¹) = f x) →
      characterFunctionMask (involutionLocalSection t)
          (fun h => characterSubsetProjection basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) label) f h) =
        characterFunctionMask (involutionLocalSection t)
          (∑ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
            characterSubsetProjection localBasis b (fun h => f h)) := by
    intro f hclass
    funext x
    unfold characterFunctionMask
    split_ifs with hx
    · have hexp : f = ∑ χ, characterPairing f (basis.representation χ).character •
          (basis.representation χ).character := by
        funext element
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
          finiteIrreducibleCharacterBasis_reconstruction basis f
            (fun element conjugator => hclass element conjugator) element
      let restriction : (G → ℂ) →ₗ[ℂ] (Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ) :=
        LinearMap.pi fun member => LinearMap.proj member.val
      let E₁ : (G → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj (x : G)).comp
        (characterSubsetProjection basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label))
      let E₂ : (G → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj x).comp
        ((∑ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
          characterSubsetProjection localBasis b).comp restriction)
      have h₁ : characterSubsetProjection basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) f x = E₁ f := rfl
      have h₂ : (∑ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
          characterSubsetProjection localBasis b (fun h => f h)) x = E₂ f := by
        simp only [E₂, restriction, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, LinearMap.sum_apply, Finset.sum_apply]
        rfl
      dsimp only
      rw [h₁, h₂, hexp, map_sum, map_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [map_smul, map_smul]
      congr 1
      have hχ := section_projection_identity_character basis ideal t ht hgroup localBasis label χ
        x hx
      simp only [E₁, E₂, restriction, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, LinearMap.sum_apply, Finset.sum_apply]
      exact hχ
    · rfl
  have horth : ∀ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      ∀ b' ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label, b ≠ b' →
        ∀ α ∈ coefficientCharacterSpace localBasis b ⊓
          sectionSupported (involutionLocalSection t),
        ∀ β ∈ coefficientCharacterSpace localBasis b' ⊓
          sectionSupported (involutionLocalSection t),
          BlocksInnerProduct α β = 0 := by
    intro b hb b' hb' hne α hα β hβ
    rw [hT] at hb hb'
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨θ', -, rfl⟩ := Finset.mem_image.mp hb'
    have hdisj := (coefficientBlock_disjoint_or_eq localBasis
      (localizedComplexIntegerRing ideal) θ θ').resolve_right hne
    exact blocksInnerProduct_eq_zero_of_disjoint localBasis _ _ hdisj α β
      (Submodule.mem_inf.mp hα).1 (Submodule.mem_inf.mp hβ).1
  refine ⟨hproj, horth, ?_⟩
  have hMle : (⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      coefficientCharacterSpace localBasis b ⊓ sectionSupported (involutionLocalSection t)) ≤
      coefficientCharacterSpace localBasis Fib ⊓ sectionSupported (involutionLocalSection t) := by
    refine iSup₂_le fun b hb => ?_
    rw [hT] at hb
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hb
    refine inf_le_inf_right _ (Submodule.span_mono (Set.image_mono ?_))
    exact Finset.coe_subset.mpr (hclosed θ hθ)
  have hclassC : ∀ α ∈ coefficientCharacterSpace localBasis Fib,
      ∀ element conjugator : Subgroup.centralizer (Subgroup.zpowers t : Set G),
        α (conjugator * element * conjugator⁻¹) = α element := fun α hα =>
    ((coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside localBasis Fib α).mp hα).1
  have hTI : ∀ x ∈ Subtype.val '' involutionLocalSection t, ∀ c : G,
      c ∉ Subgroup.centralizer (Subgroup.zpowers t : Set G) →
        c⁻¹ * x * c ∉ Subtype.val '' involutionLocalSection t :=
    fun x hx c hc hmem => hc (mem_centralizer_of_conj_mem_involutionLocalSection ht x hx c hmem)
  have hsuppG : ∀ α ∈ sectionSupported (involutionLocalSection t),
      ∀ element : Subgroup.centralizer (Subgroup.zpowers t : Set G),
        (element : G) ∉ Subtype.val '' involutionLocalSection t → α element = 0 :=
    fun α hα element he => hα element (fun hmem => he ⟨element, hmem, rfl⟩)
  have hIndOn : ∀ α ∈ coefficientCharacterSpace localBasis Fib ⊓
      sectionSupported (involutionLocalSection t), ∀ x ∈ involutionLocalSection t,
        inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) α x = α x := by
    intro α hα x hx
    obtain ⟨hspan, hsupp⟩ := Submodule.mem_inf.mp hα
    exact inducedFunction_eq_on_trivial_intersection_support _
      (Subtype.val '' involutionLocalSection t) α (hclassC α hspan) (hsuppG α hsupp) hTI x
      ⟨x, hx, rfl⟩
  have hIndW : ∀ α ∈ (⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      coefficientCharacterSpace localBasis b ⊓ sectionSupported (involutionLocalSection t)),
      inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) α ∈
        coefficientCharacterSpace basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (involutionSectionUnion t) := by
    intro α hα
    obtain ⟨hspan, hsupp⟩ := Submodule.mem_inf.mp (hMle hα)
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact supported_inducedFunction_mem_coefficientCharacterSpace _ basis _ localBasis Fib
        (involutionLocalSection t) α hspan hsupp
        (fun χ hχ x hx => fiber_projection_inv_zero basis ideal t ht hgroup localBasis label χ hχ x
          hx)
    · intro x hx
      apply inducedFunction_eq_zero_of_support_avoids_conjugates _
        (Subtype.val '' involutionLocalSection t) α (hsuppG α hsupp) x
      rintro c ⟨q, hq, hqx⟩
      exact hx ⟨c, q, hq, by rw [hqx]; group⟩
  have hiso : ∀ α ∈ (⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      coefficientCharacterSpace localBasis b ⊓ sectionSupported (involutionLocalSection t)),
      ∀ β ∈ (⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
        coefficientCharacterSpace localBasis b ⊓ sectionSupported (involutionLocalSection t)),
      BlocksInnerProduct (inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) α)
          (inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) β) =
        BlocksInnerProduct α β := by
    intro α hα β hβ
    rw [blocksInnerProduct_inducedFunction_left _ α _
      (fun element conjugator => inducedFunction_conjugate _ β element conjugator)]
    unfold BlocksInnerProduct
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    by_cases hx : x ∈ involutionLocalSection t
    · rw [hIndOn β (hMle hβ) x hx]
    · rw [(Submodule.mem_inf.mp (hMle hα)).2 x hx, zero_mul, zero_mul]
  have hleft : ∀ α ∈ (⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      coefficientCharacterSpace localBasis b ⊓ sectionSupported (involutionLocalSection t)),
      characterFunctionMask (involutionLocalSection t) (fun h =>
        inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) α h) = α := by
    intro α hα
    funext x
    unfold characterFunctionMask
    split_ifs with hx
    · exact hIndOn α (hMle hα) x hx
    · exact ((Submodule.mem_inf.mp (hMle hα)).2 x hx).symm
  have hcomplF : ∀ F ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label),
      ∀ x ∈ involutionLocalSection t,
        characterSubsetProjection localBasis Fibᶜ (fun h => F h) x = 0 := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨χ, hχ, rfl⟩ := hg
      exact fun x hx => compl_fiber_projection_zero basis ideal t ht hgroup localBasis label χ hχ
        x hx
    | zero =>
      intro x _
      have h0 : (fun h : Subgroup.centralizer (Subgroup.zpowers t : Set G) => (0 : G → ℂ) h) = 0 :=
        rfl
      rw [h0, map_zero, Pi.zero_apply]
    | add f g _ _ hf hg =>
      intro x hx
      have hsum : (fun h : Subgroup.centralizer (Subgroup.zpowers t : Set G) => (f + g) h) =
          (fun h : Subgroup.centralizer (Subgroup.zpowers t : Set G) => f h) +
            (fun h : Subgroup.centralizer (Subgroup.zpowers t : Set G) => g h) := rfl
      rw [hsum, map_add, Pi.add_apply, hf x hx, hg x hx, add_zero]
    | smul c f _ hf =>
      intro x hx
      have hsmul : (fun h : Subgroup.centralizer (Subgroup.zpowers t : Set G) => (c • f) h) =
          c • (fun h : Subgroup.centralizer (Subgroup.zpowers t : Set G) => f h) := rfl
      rw [hsmul, map_smul, Pi.smul_apply, hf x hx, smul_zero]
  have hresM : ∀ F ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion t),
      characterFunctionMask (involutionLocalSection t) (fun h => F h) ∈
        (⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
          coefficientCharacterSpace localBasis b ⊓
            sectionSupported (involutionLocalSection t)) := by
    intro F hF
    obtain ⟨hFspan, -⟩ := Submodule.mem_inf.mp hF
    have hFclass := ((coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside basis _
      F).mp hFspan).1
    have hfclass : ∀ element conjugator : Subgroup.centralizer (Subgroup.zpowers t : Set G),
        characterFunctionMask (involutionLocalSection t) (fun h => F h)
            (conjugator * element * conjugator⁻¹) =
          characterFunctionMask (involutionLocalSection t) (fun h => F h) element := by
      intro x c
      have hiff : c * x * c⁻¹ ∈ involutionLocalSection t ↔ x ∈ involutionLocalSection t := by
        constructor
        · intro h
          have h' := involutionLocalSection_conj t _ c⁻¹ h
          simpa [mul_assoc] using h'
        · exact involutionLocalSection_conj t x c
      unfold characterFunctionMask
      by_cases hx : x ∈ involutionLocalSection t
      · rw [ite_eq_left (hiff.mpr hx), ite_eq_left hx]
        exact hFclass x c
      · rw [ite_eq_right (mt hiff.mp hx), ite_eq_right hx]
    have hcompl : characterSubsetProjection localBasis Fibᶜ
        (characterFunctionMask (involutionLocalSection t) (fun h => F h)) = 0 := by
      rw [admissible_characterSubsetProjection_section_mask_commute localBasis ideal 2 Fibᶜ
        (characterSubsetAdmissible_compl localBasis _ _ hFibadm) _ hQ]
      funext x
      unfold characterFunctionMask
      split_ifs with hx
      · exact hcomplF F hFspan x hx
      · rfl
    have hdecomp := characterSubsetProjection_add_compl localBasis Fib
      (characterFunctionMask (involutionLocalSection t) (fun h => F h)) hfclass
    rw [hcompl, add_zero] at hdecomp
    rw [← hdecomp, ← sum_image_coefficientBlock_projection localBasis _ Fib hclosed, ← hT]
    refine Submodule.sum_mem _ fun b hb => ?_
    refine Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb ?_)
    refine Submodule.mem_inf.mpr ⟨characterSubsetProjection_mem localBasis b _, ?_⟩
    rw [hT] at hb
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hb
    intro x hx
    rw [coefficientBlock_section_mask_commute localBasis ideal 2 θ _ hQ]
    unfold characterFunctionMask
    rw [ite_eq_right hx]
  have hright : ∀ F ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion t),
      inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G))
        (characterFunctionMask (involutionLocalSection t) (fun h => F h)) = F := by
    intro F hF
    obtain ⟨hFspan, hFsupp⟩ := Submodule.mem_inf.mp hF
    have hFclass := ((coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside basis _
      F).mp hFspan).1
    have hfM := hMle (hresM F hF)
    funext x
    by_cases hx : x ∈ involutionSectionUnion t
    · obtain ⟨g, q, hq, rfl⟩ := hx
      rw [inducedFunction_conjugate, hIndOn _ hfM q hq, hFclass]
      unfold characterFunctionMask
      rw [ite_eq_left hq]
    · rw [hFsupp x hx]
      apply inducedFunction_eq_zero_of_support_avoids_conjugates _
        (Subtype.val '' involutionLocalSection t) _ (hsuppG _ (Submodule.mem_inf.mp hfM).2) x
      rintro c ⟨q, hq, hqx⟩
      exact hx ⟨c, q, hq, by rw [hqx]; group⟩
  let e : ↥(⨆ b ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
        coefficientCharacterSpace localBasis b ⊓ sectionSupported (involutionLocalSection t)) ≃ₗ[ℂ]
      ↥(coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion t)) :=
    { toFun := fun α => ⟨inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) α,
        hIndW α α.2⟩
      map_add' := fun α β => Subtype.ext
        ((inducedFunctionComplexLinearMap
          (Subgroup.centralizer (Subgroup.zpowers t : Set G))).map_add α β)
      map_smul' := fun c α => Subtype.ext
        ((inducedFunctionComplexLinearMap
          (Subgroup.centralizer (Subgroup.zpowers t : Set G))).map_smul c α)
      invFun := fun F => ⟨characterFunctionMask (involutionLocalSection t)
        (fun h => (F : G → ℂ) h), hresM F F.2⟩
      left_inv := fun α => Subtype.ext (hleft α α.2)
      right_inv := fun F => Subtype.ext (hright F F.2) }
  exact ⟨e, fun α => rfl, fun F => rfl, fun α β => hiso α α.2 β β.2⟩

end CFSG.Semidihedral.Principal

