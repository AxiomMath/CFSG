module

public import CFSG.CharacterTheory.BlockBasics.Sections
public import CFSG.CharacterTheory.Wreathed.ConditionalCentralPowerRegularBases

public section

open scoped Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers

section Sections

variable {E : Type*} [Group E]

theorem pPart_eq_one_of_odd_orderOf {g a : E} (hg : Odd (orderOf g))
    (ha : BlocksIsPPart 2 g a) : a = 1 := by
  obtain ⟨b, hab, hba, ⟨k, hk⟩, -, hcop⟩ := ha
  have hcomm : Commute a b := hab.trans hba.symm
  have hco : Nat.Coprime (orderOf a) (orderOf b) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_comm.mp hcop)
  have horder := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco
  rw [hab, hk] at horder
  rw [horder] at hg
  have h2 : Odd (2 ^ k) := Nat.Odd.of_mul_left hg
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr h2) ((Nat.even_pow' hk0).mpr even_two)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem odd_orderOf_of_isConj_pPart {g h gp hp : E} (hg : Odd (orderOf g))
    (hgp : BlocksIsPPart 2 g gp) (hhp : BlocksIsPPart 2 h hp) (hconj : IsConj gp hp) :
    Odd (orderOf h) := by
  rw [pPart_eq_one_of_odd_orderOf hg hgp, isConj_one_right] at hconj
  obtain ⟨b, hab, -, -, -, hcop⟩ := hhp
  rw [hconj, one_mul] at hab
  rw [← hab]
  exact Nat.Coprime.odd_of_right hcop

end Sections

section PrincipalBlock

variable {E : Type} [Group E] [Fintype E]

theorem mem_coefficientBlock_iff_mem_blockOf (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal l : basis.index) :
    l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      (basis.representation l).character ∈
        BlocksBlockOf ideal E (basis.representation principal).character := by
  rw [coefficientBlock_mem_iff, CFSG.BlockBasics.sameCoefficientBlock_iff]

theorem mem_coefficientBlock_of_odd_eq (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {χ θ : basis.index}
    (hθ : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hχθ : ∀ y : E, Odd (orderOf y) →
      (basis.representation χ).character y = (basis.representation θ).character y) :
    χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
  by_contra hχ
  set D : Set E := {y | Odd (orderOf y)} with hDdef
  have hD : ∀ g h gp hp : E, g ∈ D → BlocksIsPPart 2 g gp → BlocksIsPPart 2 h hp →
      IsConj gp hp → h ∈ D := fun g h gp hp hg hgp hhp hconj =>
    odd_orderOf_of_isConj_pPart hg hgp hhp hconj
  have hχirr := CFSG.BlockBasics.basis_character_mem_irr basis χ
  set B := BlocksBlockOf ideal E (basis.representation χ).character with hBdef
  set C := BlocksBlockOf ideal E (basis.representation principal).character with hCdef
  have hB : BlocksIsBlock ideal E B := ⟨_, hχirr, rfl⟩
  have hC : BlocksIsBlock ideal E C :=
    ⟨_, CFSG.BlockBasics.basis_character_mem_irr basis principal, rfl⟩
  have hBC : B ≠ C := by
    intro h
    apply hχ
    rw [mem_coefficientBlock_iff_mem_blockOf, ← hCdef, ← h]
    exact mem_blockOf_self ideal hχirr
  have hθC : (basis.representation θ).character ∈ C :=
    (mem_coefficientBlock_iff_mem_blockOf basis ideal principal θ).mp hθ
  obtain ⟨-, -, horth⟩ := CFSG.BlockBasics.block_section_restriction_stability 2 Nat.prime_two
    ideal inferInstance E B hB D hD
  have h0 := horth C hC hBC _ (Submodule.subset_span (mem_blockOf_self ideal hχirr)) _
    (Submodule.subset_span hθC)
  have hind : D.indicator (basis.representation χ).character =
      D.indicator (basis.representation θ).character := by
    funext y
    by_cases hy : y ∈ D
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hχθ y hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  rw [hind] at h0
  have h1 : (1 : E) ∈ D := by
    change Odd (orderOf (1 : E))
    rw [orderOf_one]
    exact odd_one
  have hzero := congrFun (CFSG.blocksInnerProduct_self_zero _ h0) 1
  rw [Set.indicator_of_mem h1, Pi.zero_apply] at hzero
  have hpos := CFSG.blocksIrr_identity_re_pos
    ⟨_, CFSG.BlockBasics.basis_character_mem_irr basis θ⟩
  change 0 < ((basis.representation θ).character 1).re at hpos
  rw [hzero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

theorem principal_linear_augmentation_iff (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {Φ : E → ℂ} {ε : ℤ} {q : ℕ}
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdata : PrincipalRegularIntegralBasisData basis ideal principal Φ ε q M) (hq : q ≠ 0)
    {m d : ℕ} {ζd : ℂ} (hζd : IsPrimitiveRoot ζd d) {lam Ξ : Fin m → Fin d → E → ℂ}
    (hlam : ∀ r v, lam r v ∈ BlocksIrr E ∧ lam r v 1 = 1) (hΞirr : ∀ r v, Ξ r v ∈ BlocksIrr E)
    (hΞ : ∀ r v y, Ξ r v y = lam r v y * Φ y)
    (hodd : ∀ r v, v.val = 0 → ∀ y : E, Odd (orderOf y) → lam r v y = 1)
    {u z : E} (hu : Odd (orderOf u)) (hΦu : Φ u = 0) (hlamu : ∀ r v, lam r v u = 1)
    (hz : Odd (orderOf z)) (hΦz : Φ z ≠ 0) (hlamz : ∀ r v, lam r v z = ζd ^ v.val) :
    (∀ r v, (∃ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation l).character = lam r v) ↔ v.val = 0) ∧
      ∀ r v, (∃ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation l).character = Ξ r v) ↔ v.val = 0 := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hv0 : ∀ v : Fin d, ζd ^ v.val = 1 → v.val = 0 := by
    intro v hv
    exact Nat.eq_zero_of_dvd_of_lt ((hζd.pow_eq_one_iff_dvd _).mp hv) v.isLt
  have h1odd : Odd (orderOf (1 : E)) := by rw [orderOf_one]; exact odd_one
  refine ⟨fun r v => ⟨?_, fun hv => ?_⟩, fun r v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨l, hl, hchar⟩
    obtain ⟨a, c, hac, -, -, h1, -⟩ := hdata.coefficients l hl
    have hua := hac u hu
    rw [hchar, hlamu, hΦu, mul_zero, add_zero] at hua
    rw [hchar, (hlam r v).2, ← hua] at h1
    have hc : (c : ℂ) = 0 := by
      have : (c : ℂ) * q = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp this).resolve_right hqC
    have hza := hac z hz
    rw [hchar, hlamz, hc, zero_mul, add_zero, ← hua] at hza
    exact hv0 v hza
  · obtain ⟨l, hl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis (hlam r v).1
    refine ⟨l, mem_coefficientBlock_of_odd_eq basis ideal principal
      (coefficientBlock_self_mem _ _ principal) fun y hy => ?_, hl⟩
    rw [hl, hprincipal, hodd r v hv y hy]
    rfl
  · rintro ⟨l, hl, hchar⟩
    obtain ⟨a, c, hac, -, -, h1, -⟩ := hdata.coefficients l hl
    have hua := hac u hu
    rw [hchar, hΞ, hlamu, hΦu, mul_zero, mul_zero, add_zero] at hua
    rw [hchar, hΞ, (hlam r v).2, one_mul, hdata.degree, ← hua, zero_add] at h1
    have hc : (c : ℂ) = 1 := by
      have : ((c : ℂ) - 1) * q = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hqC)
    have hza := hac z hz
    rw [hchar, hΞ, hlamz, hc, one_mul, ← hua, zero_add] at hza
    have : (ζd ^ v.val - 1) * Φ z = 0 := by linear_combination hza
    exact hv0 v (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hΦz))
  · obtain ⟨l, hl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis (hΞirr r v)
    obtain ⟨l', hl', hl'Φ⟩ := hdata.irreducible
    refine ⟨l, mem_coefficientBlock_of_odd_eq basis ideal principal hl' fun y hy => ?_, hl⟩
    rw [hl, hl'Φ, hΞ, hodd r v hv y hy, one_mul]

end PrincipalBlock

end CFSG.Wreathed
