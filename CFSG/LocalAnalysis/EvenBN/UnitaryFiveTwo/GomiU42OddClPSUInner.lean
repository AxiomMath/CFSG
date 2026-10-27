module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSUDet
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClArithC
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLInner
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUInner

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p f n : ℕ} {K : Type} [Field K]

theorem u42GU_cast (q k : ℕ) (hq : 1 ≤ q) :
    ((u42GU q k : ℕ) : ℤ) =
      (q : ℤ) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 1 k, ((q : ℤ) ^ i - (-1) ^ i) := by
  unfold u42GU
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i % 2 = 1
  · rw [if_pos hi]
    have : Odd i := Nat.odd_iff.mpr hi
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [if_neg hi]
    have : Even i := Nat.even_iff.mpr (by omega)
    rw [this.neg_one_pow, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast
    ring

theorem u42_card_GL_subspace {P : Type} [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    [Finite K] :
    Nat.card (LinearMap.GeneralLinearGroup K P) = u42GL (Nat.card K) (finrank K P) := by
  let b := Module.finBasis K P
  let e : LinearMap.GeneralLinearGroup K P ≃* GL (Fin (finrank K P)) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  rw [Nat.card_congr e.toEquiv, u42_card_GL]


theorem u42_card_centralizer_toLinU (h : UnitaryFieldData p f K)
    (A : ↥(primeFormUnitary h (idGram K n)))
    (T : ↥(sesqUnitaryGroup (idForm h n)))
    (hT : (T : LinearMap.GeneralLinearGroup K (Fin n → K)) = toLinU h n A) :
    Nat.card ↥(Subgroup.centralizer ({A} : Set ↥(primeFormUnitary h (idGram K n)))) =
      Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(sesqUnitaryGroup (idForm h n)))) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨⟨toLinU h n x.1, toLinU_mem x.1⟩, ?_⟩) ⟨?_, ?_⟩)
  · have h1 : x.1 * A = A * x.1 := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change toLinU h n x.1 * (T : LinearMap.GeneralLinearGroup K (Fin n → K)) =
      (T : LinearMap.GeneralLinearGroup K (Fin n → K)) * toLinU h n x.1
    rw [hT, ← map_mul, ← map_mul, h1]
  · intro x y hxy
    have := congrArg (fun z => (z.1 : LinearMap.GeneralLinearGroup K (Fin n → K))) hxy
    exact Subtype.ext (toLinU_injective this)
  · rintro ⟨y, hy⟩
    obtain ⟨A', hA'⟩ := exists_toLinU y.2
    have h1 : y * T = T * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have h2 : (y : LinearMap.GeneralLinearGroup K (Fin n → K)) *
        (T : LinearMap.GeneralLinearGroup K (Fin n → K)) =
        (T : LinearMap.GeneralLinearGroup K (Fin n → K)) *
          (y : LinearMap.GeneralLinearGroup K (Fin n → K)) := congrArg Subtype.val h1
    refine ⟨⟨A', ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply toLinU_injective
      rw [map_mul, map_mul, hA', ← hT]
      exact h2
    · exact Subtype.ext (Subtype.ext hA')


theorem u42_card_sesqU (h : UnitaryFieldData p f K) {r : ℕ} {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hdim : finrank K V = r) (hr : 1 ≤ r) :
    Nat.card ↥(sesqUnitaryGroup B) = u42GU (p ^ f) r := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h1 := (CFSG.LinearGroups.unitary_full_group_order h hB hBl hdim hr).1
  have h2 := u42GU_cast (p ^ f) r (Nat.one_le_pow _ _ h.prime.pos)
  exact_mod_cast h1.trans h2.symm


theorem u42_psu_inner {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 f K) (hn : 3 ≤ n)
    (A : ↥(primeFormUnitary h (idGram K n)))
    (hA : orderOf (primeFormConjHom h (idGram K n) A) = 2)
    {J : Subgroup ↥(fixedSubgroup (primeFormConjHom h (idGram K n) A))}
    (hJ : U42Hyp (primeFormConjHom h (idGram K n) A) J) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  have hf := h.one_le
  obtain ⟨T, hT, hT2⟩ := CFSG.ComponentClassification.CatFC.psu_exists_involution_lift h hn A hA
  have hA1 : primeFormConjHom h (idGram K n) A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn
    (A := A * A) (by rw [map_mul, hA2])
  have hAA : ∃ c : Kˣ, (A : GL (Fin n) K) * A = GeneralLinearGroup.scalar (Fin n) c :=
    ⟨c, by rw [← Subgroup.coe_mul]; exact hc⟩
  obtain ⟨ε, k, hε, hk, heq⟩ := u42_psu_inner_eq h hn A hAA
  rw [u42_card_centralizer_toLinU h A T hT] at heq
  have hdimV : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hnV : 2 ≤ finrank K (Fin n → K) := by omega
  obtain ⟨l, -, -, hN, hP, hM, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h (by norm_num : (3 : ℕ) ≠ 2) hnV
      (idForm_isSymm h n) (idForm_separatingLeft h n) hT2
  have hC₀ := hJ.card_mem
  have hsymm : ∀ Pm : Submodule K (Fin n → K), ((idForm h n).domRestrict₁₂ Pm Pm).IsSymm :=
    fun Pm => ⟨fun x y => (idForm_isSymm h n).eq (x : Fin n → K) (y : Fin n → K)⟩
  rcases hN with hN | hN
  · obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    have hr := Submodule.finrank_add_eq_of_isCompl hcompl
    have hr1 : 1 ≤ finrank K (eigenPlus l (unitaryOp T)) := Submodule.one_le_finrank_iff.mpr hP
    have hs1 : 1 ≤ finrank K (eigenMinus l (unitaryOp T)) := Submodule.one_le_finrank_iff.mpr hM
    have hcardM : Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(sesqUnitaryGroup (idForm h n)))) =
        u42GU (3 ^ f) (finrank K (eigenPlus l (unitaryOp T))) *
          u42GU (3 ^ f) (finrank K (eigenMinus l (unitaryOp T))) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod,
        u42_card_sesqU h (hsymm _) hlP rfl hr1, u42_card_sesqU h (hsymm _) hlM rfl hs1]
    rw [hcardM] at heq
    have hk' : k ∣ Nat.gcd (finrank K (eigenPlus l (unitaryOp T)) +
        finrank K (eigenMinus l (unitaryOp T))) (3 ^ f + 1) := by
      rw [hr, hdimV]
      exact hk
    rcases hC₀ with h0 | h0 <;> rw [h0] at heq
    · exact u42_arith_psu_split hf hr1 hs1 (by omega) hε (Or.inl rfl) hk' heq
    · exact u42_arith_psu_split hf hr1 hs1 (by omega) hε (Or.inr rfl) hk' heq
  · obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    have hl2 : 2 ≤ finrank K (eigenPlus l (unitaryOp T)) := by omega
    have hcardM : Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(sesqUnitaryGroup (idForm h n)))) =
        u42GL ((3 ^ f) ^ 2) (finrank K (eigenPlus l (unitaryOp T))) := by
      rw [Nat.card_congr e.toEquiv, u42_card_GL_subspace, h.card_eq_sq]
    rw [hcardM] at heq
    have hk' : k ∣ Nat.gcd (2 * finrank K (eigenPlus l (unitaryOp T))) (3 ^ f + 1) := by
      rw [hdim2, hdimV]
      exact hk
    rcases hC₀ with h0 | h0 <;> rw [h0] at heq
    · exact u42_arith_psu_quad hf hl2 hε (Or.inl rfl) hk' heq
    · exact u42_arith_psu_quad hf hl2 hε (Or.inr rfl) hk' heq

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
