module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsUpper
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryFamily
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f p : ℕ} {K : Type} [Field K]

section Basic

variable (h : UnitaryFieldData ℓ f K)

theorem bar_fix_neg_one : h.bar (-1 : K) = -1 := by rw [map_neg, map_one]

theorem diagHom_mem_unitary {n : ℕ} (c : Fin n → Kˣ)
    (hc : ∀ i, h.bar (c i : K) * (c i : K) = 1) :
    (Torus.diagHom c : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary]
  rw [Torus.diagHom_apply, Torus.coe_diagGL, diagonal_map (map_zero h.bar), diagonal_transpose]
  simp only [idGram, Units.val_one, Matrix.mul_one, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hc i]
  · simp [hij]

theorem swapGL_mem_unitary {n : ℕ} (a b : Fin n) :
    (Torus.swapGL a b : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary, Torus.coe_swapGL, Matrix.map_swap, Matrix.transpose_swap]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  exact Matrix.swap_mul_self a b

end Basic

section Lower

variable (h : UnitaryFieldData ℓ f K)

theorem sgnSwap_mem_unitary {n : ℕ} (a b : Fin n) :
    (Torus.sgnSwap a b : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) := by
  refine mul_mem (swapGL_mem_unitary h a b) (diagHom_mem_unitary h _ fun i => ?_)
  simp only [Torus.signVec, Function.update_apply, Pi.one_apply]
  split_ifs
  · simp [bar_fix_neg_one h]
  · simp

theorem tvec_mem_unitary {n : ℕ} {ζ : Kˣ} (hζ : h.bar (ζ : K) * (ζ : K) = 1) (i j : Fin n) :
    (Torus.diagHom (Torus.tvec ζ i j) : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) := by
  refine diagHom_mem_unitary h _ fun m => ?_
  simp only [Torus.tvec, Function.update_apply, Pi.one_apply]
  split_ifs
  · simp only [Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_mul_eq_one₀ ?_]
    · exact eq_inv_of_mul_eq_one_left hζ
    · exact fun h0 => by simp [h0] at hζ
  · exact hζ
  · simp

theorem uniLowerData (hp : p.Prime) (hn : 7 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    Nonempty (LowerData p (primeFormP h (idGram K p))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := h.finite
  have hcardK : Nat.card Kˣ = ℓ ^ (2 * f) - 1 := by
    rw [Nat.card_units, h.card]
  have hdvd : p ∣ Nat.card Kˣ := by
    have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have h2 : Nat.card Kˣ = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have e : ℓ ^ (2 * f) = ℓ ^ f * ℓ ^ f := by rw [two_mul, pow_add]
      have h3 : 1 ≤ ℓ ^ f * ℓ ^ f := Nat.mul_le_mul h1 h1
      rw [hcardK, e]
      zify [h1, h3]
      ring
    rw [h2]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζ : IsPrimitiveRoot z p := hz ▸ IsPrimitiveRoot.orderOf z
  have hzq : z ^ (ℓ ^ f + 1) = 1 := (hζ.pow_eq_one_iff_dvd _).2 hpq
  have hbar : h.bar (z : K) * (z : K) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hzq
    simpa [Units.val_pow_eq_pow_val, h.bar_apply, pow_succ] using this
  have hmem : ∀ g : GL (Fin p) K, g ∈ primeFormUnitary h (idGram K p) →
      (g : Matrix (Fin p) (Fin p) K).det = 1 →
      g ∈ ((gramSU h (idGram K p)).subtype).range := by
    intro g hg hdet
    rw [Subgroup.range_subtype]
    exact (mem_gramSU_iff_unitary h).2 ⟨hg, hdet⟩
  refine Torus.lowerDataOfModel hζ hn (gramSU h (idGram K p)).subtype
    (Subgroup.subtype_injective _) (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K p)) p))
    ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff g).1 hg
    exact ⟨c, hc⟩
  · exact fun k => hmem _ (tvec_mem_unitary h hbar _ _) (Torus.det_Xg z hn k)
  · exact fun k => hmem _ (sgnSwap_mem_unitary h _ _) (Torus.det_Swg hn k)
  · exact hmem _ (sgnSwap_mem_unitary h _ _) (Torus.det_Tg hn)

end Lower

section Upper

variable (h : UnitaryFieldData ℓ f K)

theorem bar_mul_self_of_scalar_mem {n : ℕ} [NeZero n] {c : Kˣ}
    (hc : (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n)) :
    h.bar (c : K) * (c : K) = 1 := by
  rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_map (map_zero h.bar), diagonal_transpose] at hc
  simp only [idGram, Units.val_one, Matrix.mul_one, diagonal_mul_diagonal] at hc
  have := congrArg (fun m : Matrix (Fin n) (Fin n) K => m ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) hc
  simpa using this

noncomputable def uniUpperModel (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    UpperModel p (primeFormP h (idGram K p)) K :=
  have hp2 : p ≠ 2 := by omega
  have hn : 3 ≤ p := by omega
  have hne : ¬(p = 3 ∧ ℓ ^ f = 2) := fun hh => by omega
  have hq0 : ¬(p = 3 ∧ ℓ ^ (f / p) = 2) := fun hh => by omega
  have hq3 : 3 < ℓ ^ f := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  { M := primeFormUnitary h (idGram K p)
    ι := (primeFormUnitary h (idGram K p)).subtype
    ι_inj := Subgroup.subtype_injective _
    ρ := primeFormConjHom h (idGram K p)
    ker_ρ := fun g hg => by
      obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne g).1 hg
      exact ⟨c, hc⟩
    scalar_ρ := fun g c hg => by
      have hg' : (g : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) c := hg
      refine (primeFormConjHom_eq_one_iff_of_ne hn hne g).2 ⟨c, ?_, hg'⟩
      have hb := bar_mul_self_of_scalar_mem h (hg' ▸ g.2)
      refine (pow_succ_eq_one_iff_norm h c).mpr ?_
      rw [UnitaryFieldData.norm, mul_comm]
      exact hb
    plane := fun A B hAB hAp hBp hA1 hBA H hH _ =>
      localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq hAB hAp hBp hA1 hBA hH
    outer_bal := fun D hD hDl H hH =>
      localDeltaIn_eq_bot_of_not_le_primeFormD h hn hne hp hp2 hpq hq0 hD hDl hH
    cyc := fun A hA hfin => by
      have hcyc : IsCyclic (K ≃+* K) :=
        CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
      refine ⟨K ≃+* K, inferInstance, hcyc,
        (primeFormFieldFactor h isPrimeFormGram_one hn hne).comp A.subtype, fun x hx => ?_⟩
      have hx' : (x : MulAut (primeFormP h (idGram K p))) ∈
          (primeFormFieldFactor h isPrimeFormGram_one hn hne).ker := hx
      rw [ker_primeFormFieldFactor] at hx'
      exact hx' }

end Upper

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
