module

public import CFSG.CharacterTheory.Wreathed.UniqueLocalBlockProjection
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionIntegralColumns

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes

variable {G : Type*} [Group G] [Fintype G]

theorem unique_local_block_primary_section_integral_columns
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [hp : Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    {u : G} {r : ℕ} (_hr : 1 ≤ r) (hu : orderOf u = p ^ r)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (block : basis.index) (localBlock : localBasis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ r))
    (ℓ : ℕ) (_hℓ : 1 ≤ ℓ)
    (b : Fin ℓ → Subgroup.centralizer (Subgroup.zpowers u : Set G) → ℂ)
    (_hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, ¬ p ∣ orderOf y →
      b j y = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock,
        c θ * (localBasis.representation θ).character y)
    (hbindep : ∀ c : Fin ℓ → ℂ, (∀ y, ¬ p ∣ orderOf y → ∑ j, c j * b j y = 0) → c = 0)
    (d : localBasis.index → Fin ℓ → ℤ)
    (hd : ∀ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock,
      ∀ y, ¬ p ∣ orderOf y →
        (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b j y) :
    ∃ (U : basis.index → Fin ℓ → ℂ) (m : basis.index → localBasis.index → ℕ)
      (lam : localBasis.index → ℂ),
      (∀ χ θ, characterPairing
          (fun c : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
            (basis.representation χ).character c)
          (localBasis.representation θ).character = m χ θ) ∧
      (∀ θ, (∃ k : ℕ, lam θ = ζ ^ k) ∧
        (localBasis.representation θ).representation (centralizerSelf u) = lam θ • 1) ∧
      (∀ χ j, U χ j = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
        localBlock, (m χ θ : ℂ) * lam θ * d θ j) ∧
      (∀ χ j, U χ j ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
        ∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G), ¬ p ∣ orderOf y →
          (basis.representation χ).character (u * y) = ∑ j, U χ j * b j y) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
        ∀ v : Fin ℓ → ℂ, (∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G),
          ¬ p ∣ orderOf y →
            (basis.representation χ).character (u * y) = ∑ j, v j * b j y) → v = U χ) ∧
      (∀ j k, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
          starRingEnd ℂ (U χ j) * U χ k =
        ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock,
          ((d θ j * d θ k : ℤ) : ℂ)) ∧
      (∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = p ^ e) →
          ¬ p ∣ orderOf c → ¬ IsConj a u) →
        ∀ j, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
          U χ j * starRingEnd ℂ ((basis.representation χ).character g) = 0) := by
  have hpp := hp.out
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have huord : orderOf u ∣ p ^ r := by rw [hu]
  have hreg : ∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G), ¬ p ∣ orderOf y →
      Nat.Coprime p (orderOf y) := fun y hy => (Nat.Prime.coprime_iff_not_dvd hpp).mpr hy
  have hcentral := centralizerSelf_mem_center u
  have hpow : centralizerSelf u ^ (p ^ r) = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← hu]; exact pow_orderOf_eq_one u)
  choose s hs using fun θ : localBasis.index =>
    irreducible_central_scalar_root (localBasis.representation θ) (localBasis.irreducible θ)
      (centralizerSelf u) hcentral (p ^ r) (pow_pos hpp.pos r) hpow
  set lam : localBasis.index → ℂ := fun θ => (s θ : ℂ) with hlamdef
  have hlam : ∀ θ, (localBasis.representation θ).representation (centralizerSelf u) =
      lam θ • 1 := fun θ => (hs θ).2
  have hlampow : ∀ θ, lam θ ^ (p ^ r) = 1 := fun θ => by
    have h := congrArg Subtype.val (hs θ).1
    simpa [hlamdef] using h
  have hlamζ : ∀ θ, ∃ k : ℕ, lam θ = ζ ^ k := fun θ => by
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (hlampow θ)
    exact ⟨k, hk.symm⟩
  have hlamnorm : ∀ θ, lam θ * starRingEnd ℂ (lam θ) = 1 := by
    intro θ
    have hn : ‖lam θ‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (hlampow θ) (pow_ne_zero _ hpp.ne_zero)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have hlamval : ∀ θ (c : Subgroup.centralizer (Subgroup.zpowers u : Set G)),
      (localBasis.representation θ).character (c * centralizerSelf u) =
        lam θ * (localBasis.representation θ).character c := by
    intro θ c
    rw [FiniteComplexRepresentation.character, Representation.character, map_mul, hlam θ,
      mul_smul_comm, mul_one, map_smul, smul_eq_mul]
    rfl
  have hucomm : ∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      (u * (y : G)) =
        ((y * centralizerSelf u : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G) :=
    fun y => by
    rw [Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.mp y.2 u (Subgroup.mem_zpowers u)
  choose m hm using fun (χ : basis.index) (θ : localBasis.index) =>
    CFSG.Semidihedral.Principal.restriction_pairing_nat basis localBasis χ θ
  set B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) block with hB₀
  set b₀ := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock
    with hb₀
  have hlocal : ∀ θ ∈ b₀, ∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      ¬ p ∣ orderOf y →
        (localBasis.representation θ).character (y * centralizerSelf u) =
          lam θ * ∑ j, (d θ j : ℂ) * b j y := fun θ hθ y hy => by
    rw [hlamval θ y, hd θ hθ y hy]
  have hproj : ∀ χ ∈ B₀, ∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      ¬ p ∣ orderOf y →
        (basis.representation χ).character (u * y) =
          ∑ θ ∈ b₀, (m χ θ : ℂ) *
            (localBasis.representation θ).character (y * centralizerSelf u) := by
    intro χ hχ y hy
    have h := unique_local_block_projection_character basis ideal p u r huord hgroup localBasis
      block localBlock hbrauer hunique y (by rw [Subgroup.orderOf_coe]; exact hreg y hy) χ
    have hpt : ((⟨u, element_mem_centralizer_zpowers u⟩ :
        Subgroup.centralizer (Subgroup.zpowers u : Set G)) * y) = y * centralizerSelf u :=
      (centralizerSelf_commute u y).eq
    rw [hpt, characterSubsetProjection_character basis B₀ χ hχ,
      characterSubsetProjection_apply'] at h
    have h' := congrArg (starRingEnd ℂ) h
    rw [map_sum, Subgroup.coe_inv, ← finite_character_conjugate_inverse, Complex.conj_conj] at h'
    rw [hucomm y, ← h']
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [map_mul, finite_character_conjugate_inverse, inv_inv, hm χ θ, Complex.conj_natCast]
  let U : basis.index → Fin ℓ → ℂ := fun χ j => ∑ θ ∈ b₀, (m χ θ : ℂ) * lam θ * d θ j
  have hrow : ∀ χ ∈ B₀, ∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      ¬ p ∣ orderOf y → (basis.representation χ).character (u * y) = ∑ j, U χ j * b j y := by
    intro χ hχ y hy
    rw [hproj χ hχ y hy]
    simp only [U, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [hlocal θ hθ y hy, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcoeff : ∀ c : Fin ℓ → ℂ, (∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      ¬ p ∣ orderOf y → ∑ j, c j * b j y = 0) → ∀ j, c j = 0 :=
    fun c hc j => congrFun (hbindep c hc) j
  have huniq : ∀ (v w : Fin ℓ → ℂ), (∀ y : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      ¬ p ∣ orderOf y → ∑ j, v j * b j y = ∑ j, w j * b j y) → v = w := by
    intro v w hvw
    funext j
    have h := hcoeff (fun j => v j - w j) (fun y hy => by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [hvw y hy, sub_self]) j
    exact sub_eq_zero.mp h
  refine ⟨U, m, lam, hm, fun θ => ⟨hlamζ θ, hlam θ⟩, fun χ j => rfl, ?_, hrow,
    fun χ hχ v hv => huniq v (U χ) fun y hy => by rw [← hv y hy, hrow χ hχ y hy], ?_, ?_⟩
  ·
    intro χ j
    have hζmem : ζ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := Algebra.subset_adjoin (Set.mem_singleton ζ)
    show (∑ θ ∈ b₀, (m χ θ : ℂ) * lam θ * d θ j) ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)
    refine Subalgebra.sum_mem _ fun θ _ => ?_
    obtain ⟨k, hk⟩ := hlamζ θ
    have hlk : lam θ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
      rw [hk]; exact Subalgebra.pow_mem _ hζmem k
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ (m χ θ)) hlk)
      (Subalgebra.intCast_mem _ (d θ j))
  ·
    have hker : ∀ y y' : Subgroup.centralizer (Subgroup.zpowers u : Set G),
        ¬ p ∣ orderOf y → ¬ p ∣ orderOf y' →
        ∑ χ ∈ B₀, (basis.representation χ).character (u * y) *
            starRingEnd ℂ ((basis.representation χ).character (u * y')) =
          ∑ θ ∈ b₀, (∑ j, (d θ j : ℂ) * b j y) * starRingEnd ℂ (∑ k, (d θ k : ℂ) * b k y') := by
      intro y y' hy hy'
      have h := unique_local_block_section_kernel basis ideal p u r huord hgroup localBasis block
        localBlock hbrauer hunique (y * centralizerSelf u) (y' * centralizerSelf u)
        ⟨y, (centralizerSelf_commute u y).eq.symm, hreg y hy⟩
        ⟨y', (centralizerSelf_commute u y').eq.symm, hreg y' hy'⟩
      rw [← hucomm y, ← hucomm y'] at h
      rw [h]
      refine Finset.sum_congr rfl fun θ hθ => ?_
      rw [hlocal θ hθ y hy, hlocal θ hθ y' hy', map_mul]
      linear_combination (∑ j, (d θ j : ℂ) * b j y) *
        starRingEnd ℂ (∑ k, (d θ k : ℂ) * b k y') * (hlamnorm θ)
    set Δ : Fin ℓ → Fin ℓ → ℂ := fun j k =>
      ∑ χ ∈ B₀, U χ j * starRingEnd ℂ (U χ k) - ∑ θ ∈ b₀, ((d θ j * d θ k : ℤ) : ℂ) with hΔ
    have hexp : ∀ y y' : Subgroup.centralizer (Subgroup.zpowers u : Set G),
        ¬ p ∣ orderOf y → ¬ p ∣ orderOf y' →
        ∑ j, (∑ k, Δ j k * starRingEnd ℂ (b k y')) * b j y = 0 := by
      intro y y' hy hy'
      have hl : ∑ χ ∈ B₀, (basis.representation χ).character (u * y) *
          starRingEnd ℂ ((basis.representation χ).character (u * y')) =
          ∑ j, ∑ k, (∑ χ ∈ B₀, U χ j * starRingEnd ℂ (U χ k)) * b j y *
            starRingEnd ℂ (b k y') := by
        rw [Finset.sum_congr rfl fun χ hχ => by
          rw [hrow χ hχ y hy, hrow χ hχ y' hy', map_sum, Finset.sum_mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_mul]
        ring
      have hr : ∑ θ ∈ b₀, (∑ j, (d θ j : ℂ) * b j y) *
          starRingEnd ℂ (∑ k, (d θ k : ℂ) * b k y') =
          ∑ j, ∑ k, (∑ θ ∈ b₀, ((d θ j * d θ k : ℤ) : ℂ)) * b j y * starRingEnd ℂ (b k y') := by
        rw [Finset.sum_congr rfl fun θ _ => by rw [map_sum, Finset.sum_mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [map_mul, map_intCast]
        push_cast
        ring
      have hkey := (hl.symm.trans (hker y y' hy hy')).trans hr
      have : ∀ j, (∑ k, Δ j k * starRingEnd ℂ (b k y')) * b j y =
          ∑ k, (∑ χ ∈ B₀, U χ j * starRingEnd ℂ (U χ k)) * b j y * starRingEnd ℂ (b k y') -
            ∑ k, (∑ θ ∈ b₀, ((d θ j * d θ k : ℤ) : ℂ)) * b j y * starRingEnd ℂ (b k y') := by
        intro j
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hΔ]
        ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, hkey, sub_self]
    have hrowzero : ∀ y' : Subgroup.centralizer (Subgroup.zpowers u : Set G),
        ¬ p ∣ orderOf y' → ∀ j, ∑ k, Δ j k * starRingEnd ℂ (b k y') = 0 := fun y' hy' =>
      hcoeff _ fun y hy => by rw [← hexp y y' hy hy']
    have hzero : ∀ j k, Δ j k = 0 := by
      intro j k
      have h := hcoeff (fun k => starRingEnd ℂ (Δ j k)) (fun y' hy' => by
        have h0 := congrArg (starRingEnd ℂ) (hrowzero y' hy' j)
        simp only [map_sum, map_mul, Complex.conj_conj, map_zero] at h0
        exact h0) k
      simpa using h
    intro j k
    have h := hzero k j
    simp only [hΔ, sub_eq_zero] at h
    rw [Finset.sum_congr rfl fun χ _ => mul_comm _ _, h]
    exact Finset.sum_congr rfl fun θ _ => by push_cast; ring
  ·
    intro g hg j
    obtain ⟨a, c, e, -, -, hac, hacg, ha, hc⟩ := finite_prime_primary_factorization g p hpp
    have hnot : ¬ IsConj u a := fun h => hg a c hacg hac (by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hpp).mp ha
      exact ⟨k, hk⟩) ((Nat.Prime.coprime_iff_not_dvd hpp).mp hc) h.symm
    refine hcoeff (fun j => ∑ χ ∈ B₀, U χ j *
      starRingEnd ℂ ((basis.representation χ).character g)) (fun y hy => ?_) j
    have h := coefficientBlock_section_column_orthogonality basis ideal p block u a (y : G) c r
      e huord ha (by rw [Subgroup.orderOf_coe]; exact hreg y hy) hc
      (Subgroup.mem_centralizer_iff.mp y.2 u (Subgroup.mem_zpowers u)) hac hnot
    rw [hacg] at h
    rw [← h]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [← finite_character_conjugate_inverse, hrow χ hχ y hy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

end CFSG.Wreathed
