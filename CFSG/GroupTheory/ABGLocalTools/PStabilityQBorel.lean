module

public import CFSG.GroupTheory.ABGLocalTools.PStabilitySL2Props
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternatingFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.IntegralDomain
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.RingTheory.ZMod.Torsion

public section

open Subgroup Matrix

namespace CFSG.ABGLocalTools

open SL2Facts

section Borel

variable (F : Type*) [Field F]

@[expose] def borelSL2 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {A | A 1 0 = 0}
  mul_mem' {A B} hA hB := by
    change A 1 0 = 0 at hA
    change B 1 0 = 0 at hB
    change (A * B : Matrix.SpecialLinearGroup (Fin 2) F) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
    ring
  one_mem' := by
    change (1 : Matrix.SpecialLinearGroup (Fin 2) F) 1 0 = 0
    simp
  inv_mem' {A} hA := by
    change A 1 0 = 0 at hA
    change (A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hA]

variable {F}

theorem mem_borelSL2 {A : Matrix.SpecialLinearGroup (Fin 2) F} : A ∈ borelSL2 F ↔ A 1 0 = 0 :=
  Iff.rfl

theorem uT_mem_borelSL2 (t : F) : uT t ∈ borelSL2 F := by
  rw [mem_borelSL2, coe_uT]
  simp

@[expose] def borelDiag : borelSL2 F →* F where
  toFun A := (A : Matrix.SpecialLinearGroup (Fin 2) F) 0 0
  map_one' := by simp
  map_mul' A B := by
    have hB : (B : Matrix.SpecialLinearGroup (Fin 2) F) 1 0 = 0 := B.2
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hB, mul_zero, add_zero]

theorem borelDiag_apply (A : borelSL2 F) :
    borelDiag A = (A : Matrix.SpecialLinearGroup (Fin 2) F) 0 0 := rfl

theorem eq_uT_of_borelDiag_eq_one {A : borelSL2 F} (h : borelDiag A = 1) :
    (A : Matrix.SpecialLinearGroup (Fin 2) F) =
      uT ((A : Matrix.SpecialLinearGroup (Fin 2) F) 0 1) := by
  have h10 : (A : Matrix.SpecialLinearGroup (Fin 2) F) 1 0 = 0 := A.2
  have h00 : (A : Matrix.SpecialLinearGroup (Fin 2) F) 0 0 = 1 := h
  have hdet := det_eq (A : Matrix.SpecialLinearGroup (Fin 2) F)
  rw [h00, h10, one_mul, mul_zero, sub_zero] at hdet
  apply Subtype.ext
  rw [coe_uT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, hdet]

theorem borel_mul_uT_mul_inv {A : Matrix.SpecialLinearGroup (Fin 2) F} (hA : A 1 0 = 0) (t : F) :
    A * uT t * A⁻¹ = uT (A 0 0 ^ 2 * t) := by
  have hdet := det_eq A
  rw [hA, mul_zero, sub_zero] at hdet
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_uT, coe_uT,
    Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F), hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | ring1 | linear_combination hdet

variable [Finite F]

theorem uT_pow_card (t : F) : uT t ^ Nat.card F = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [uT_pow, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero, zero_mul]
  apply Subtype.ext
  rw [coe_uT, Matrix.SpecialLinearGroup.coe_one]
  simp [Matrix.one_fin_two]

theorem eq_one_of_pow_coprime {G : Type*} [Group G] {x : G} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : x ^ m = 1) (hn : x ^ n = 1) : x = 1 := by
  have := pow_gcd_eq_one.mpr ⟨hm, hn⟩
  rwa [hmn.gcd_eq_one, pow_one] at this

theorem twoSubgroupsCyclic_borelSL2 (hodd : Odd (Nat.card F)) :
    TwoSubgroupsCyclic (borelSL2 F) := by
  intro T hTB hT
  let f : T →* F := borelDiag.comp (Subgroup.inclusion hTB)
  have hker : ∀ t : T, f t = 1 → t = 1 := by
    intro t ht
    have hu := eq_uT_of_borelDiag_eq_one (A := Subgroup.inclusion hTB t) ht
    obtain ⟨k, hk⟩ := hT t
    have h1 : (t : Matrix.SpecialLinearGroup (Fin 2) F) ^ Nat.card F = 1 := by
      change ((Subgroup.inclusion hTB t : borelSL2 F) : Matrix.SpecialLinearGroup (Fin 2) F) ^
        Nat.card F = 1
      rw [hu, uT_pow_card]
    have h2 : (t : Matrix.SpecialLinearGroup (Fin 2) F) ^ 2 ^ k = 1 := by
      rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
    have hcop : Nat.Coprime (Nat.card F) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    exact Subtype.ext (eq_one_of_pow_coprime hcop h1 h2)
  have hinj : Function.Injective f := by
    intro a b hab
    have : f (a * b⁻¹) = 1 := by
      rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
    exact mul_inv_eq_one.mp (hker _ this)
  exact isCyclic_of_injective_ringHom f hinj

theorem pCore_borelSL2_eq_bot {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card F) : CFSG.pCore p (borelSL2 F) = ⊥ := by
  have hpp : p.Prime := Fact.out
  set PC := CFSG.pCore p (borelSL2 F) with hPC
  have hPCn : PC.Normal := CFSG.pCore_normal
  have hPCp : IsPGroup p PC := CFSG.pCore_isPGroup
  have hcopq : ∀ k : ℕ, Nat.Coprime (Nat.card F) (p ^ k) := fun k =>
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpq).symm
  rw [eq_bot_iff]
  intro π hπ
  obtain ⟨k, hk⟩ := hPCp ⟨π, hπ⟩
  have hπk : π ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  let u : borelSL2 F := ⟨uT 1, uT_mem_borelSL2 1⟩
  set c := π * u * π⁻¹ * u⁻¹ with hc
  have hcPC : c ∈ PC := by
    have h1 : u * π⁻¹ * u⁻¹ ∈ PC := hPCn.conj_mem _ (inv_mem hπ) u
    rw [hc, show π * u * π⁻¹ * u⁻¹ = π * (u * π⁻¹ * u⁻¹) by group]
    exact mul_mem hπ h1
  have hcdiag : borelDiag c = 1 := by
    have hπinv : borelDiag π * borelDiag π⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have huinv : borelDiag u * borelDiag u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hu1 : borelDiag u = 1 := by rw [borelDiag_apply]; simp [u, coe_uT]
    rw [hc, map_mul, map_mul, map_mul]
    rw [hu1, one_mul] at huinv
    rw [hu1, huinv, mul_one, mul_one, hπinv]
  have hc1 : c = 1 := by
    obtain ⟨m, hm⟩ := hPCp ⟨c, hcPC⟩
    have hcm : c ^ p ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hcq : c ^ Nat.card F = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, eq_uT_of_borelDiag_eq_one hcdiag, uT_pow_card, Subgroup.coe_one]
    exact eq_one_of_pow_coprime (hcopq m) hcq hcm
  have hcomm : ((π : borelSL2 F) : Matrix.SpecialLinearGroup (Fin 2) F) * uT 1 *
      ((π : borelSL2 F) : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ = uT 1 := by
    have h := congrArg (fun x : borelSL2 F => ((x * u : borelSL2 F) :
      Matrix.SpecialLinearGroup (Fin 2) F)) hc1
    simp only [hc, inv_mul_cancel_right, one_mul] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hπ10 : ((π : borelSL2 F) : Matrix.SpecialLinearGroup (Fin 2) F) 1 0 = 0 := π.2
  rw [borel_mul_uT_mul_inv hπ10, mul_one] at hcomm
  have hsq : ((π : borelSL2 F) : Matrix.SpecialLinearGroup (Fin 2) F) 0 0 ^ 2 = 1 := by
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A 0 1) hcomm
    simpa [coe_uT] using this
  have hπ2 : borelDiag (π ^ 2) = 1 := by rw [map_pow, borelDiag_apply]; exact hsq
  have hπ2q : π ^ (2 * Nat.card F) = 1 := by
    apply Subtype.ext
    rw [pow_mul, Subgroup.coe_pow, Subgroup.coe_pow, ← Subgroup.coe_pow,
      eq_uT_of_borelDiag_eq_one hπ2, uT_pow_card, Subgroup.coe_one]
  have hcop2 : Nat.Coprime (2 * Nat.card F) (p ^ k) := by
    refine Nat.Coprime.mul_left ?_ (hcopq k)
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hpp).mpr hp.symm)
  exact (eq_one_of_pow_coprime hcop2 hπ2q hπk).symm ▸ Subgroup.mem_bot.mpr rfl

end Borel

section Eigen

variable {F : Type*} [Field F]

theorem exists_eigenvector_of_pow_eq_one {g : Matrix.SpecialLinearGroup (Fin 2) F} {n : ℕ}
    (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n) (hg : g ^ n = 1) :
    ∃ μ : F, μ ^ n = 1 ∧ ∃ v : Fin 2 → F, v ≠ 0 ∧
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = μ • v := by
  classical
  by_contra hcon
  push Not at hcon
  have hunit : ∀ μ ∈ Polynomial.nthRootsFinset n (1 : F),
      IsUnit ((g : Matrix (Fin 2) (Fin 2) F) - μ • 1) := by
    intro μ hμ
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hcon μ ((Polynomial.mem_nthRootsFinset hn 1).mp hμ) v hv0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have h0 : Polynomial.aeval (g : Matrix (Fin 2) (Fin 2) F)
      (Polynomial.X ^ n - 1 : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, ← Matrix.SpecialLinearGroup.coe_pow, hg,
      Matrix.SpecialLinearGroup.coe_one, sub_self]
  rw [Polynomial.X_pow_sub_one_eq_prod hn hζ, ← Finset.prod_map_toList, map_list_prod,
    List.map_map] at h0
  have hu : IsUnit (((Polynomial.nthRootsFinset n (1 : F)).toList.map
      ((Polynomial.aeval (g : Matrix (Fin 2) (Fin 2) F)) ∘
        fun μ => Polynomial.X - Polynomial.C μ)).prod) := by
    apply List.prod_isUnit
    intro m hm
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hm
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
    exact hunit μ (Finset.mem_toList.mp hμ)
  rw [h0] at hu
  exact not_isUnit_zero hu

theorem exists_sl2_first_column {v : Fin 2 → F} (hv : v ≠ 0) :
    ∃ P : Matrix.SpecialLinearGroup (Fin 2) F, P 0 0 = v 0 ∧ P 1 0 = v 1 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_two]
      simp [h1]
    · simp [h0]
    · simp
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_two]
      simp [h0]
    · simp
    · simp

theorem inv_mul_mul_apply_of_eigenvector {g P : Matrix.SpecialLinearGroup (Fin 2) F}
    {μ : F} (hv : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![P 0 0, P 1 0] = μ • ![P 0 0, P 1 0]) :
    (P⁻¹ * g * P) 1 0 = 0 ∧ (P⁻¹ * g * P) 0 0 = μ := by
  have hdet := det_eq P
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · linear_combination (-(P 1 0)) * h0 + P 0 0 * h1
  · linear_combination P 1 1 * h0 - P 0 1 * h1 + μ * hdet

end Eigen

section Transport

variable {G : Type*} [Group G]

theorem TwoSubgroupsCyclic.map_mulAut {B : Subgroup G} (hB : TwoSubgroupsCyclic B)
    (φ : MulAut G) : TwoSubgroupsCyclic (B.map φ.toMonoidHom) := by
  intro T hT hT2
  have hT' : T.map φ⁻¹.toMonoidHom ≤ B := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hT ht
    simpa using hb
  have hcyc : IsCyclic (T.map φ⁻¹.toMonoidHom) :=
    hB _ hT' (hT2.map φ⁻¹.toMonoidHom)
  have e : T.map φ⁻¹.toMonoidHom ≃* T :=
    (T.equivMapOfInjective φ⁻¹.toMonoidHom (MulEquiv.injective _)).symm
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem pCore_map_mulAut_eq_bot {B : Subgroup G} {p : ℕ} (hB : CFSG.pCore p B = ⊥)
    (φ : MulAut G) : CFSG.pCore p (B.map φ.toMonoidHom) = ⊥ := by
  let e : B ≃* B.map φ.toMonoidHom := B.equivMapOfInjective _ (MulEquiv.injective _)
  rw [← CFSG.pCore_map_iso p e, hB, Subgroup.map_bot]

end Transport

theorem sl2BorelOfSplitElement : SL2BorelOfSplitElement := by
  intro F _ _ p _ hp hodd hpq hpq1 g hg
  classical
  have : Fintype F := Fintype.ofFinite F
  have hpp : p.Prime := Fact.out
  set q := Nat.card F with hqdef
  have hq1 : 1 ≤ q := Nat.card_pos
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  have hpq' : p ∣ q - 1 := by
    have h1 : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [← hg]; exact orderOf_dvd_natCard g
    rw [CFSG.GorensteinWalter.sl2_card_formula, ← hqdef, hsq] at h1
    rcases (Nat.Prime.dvd_mul hpp).mp h1 with h | h
    · exact absurd h hpq
    rcases (Nat.Prime.dvd_mul hpp).mp h with h | h
    · exact h
    · exact absurd h hpq1
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card]; exact hpq')
  have hζ : IsPrimitiveRoot (u : F) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hu]
    exact IsPrimitiveRoot.orderOf u
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  obtain ⟨μ, hμp, v, hv0, hv⟩ := exists_eigenvector_of_pow_eq_one hpp.pos hζ hgp
  obtain ⟨P, hP0, hP1⟩ := exists_sl2_first_column hv0
  have hvP : v = ![P 0 0, P 1 0] := by
    ext i; fin_cases i <;> simp [hP0, hP1]
  rw [hvP] at hv
  obtain ⟨hg10, hg00⟩ := inv_mul_mul_apply_of_eigenvector hv
  set g' := P⁻¹ * g * P with hg'
  have hg'B : g' ∈ borelSL2 F := hg10
  have hgg' : g = MulAut.conj P g' := by
    rw [MulAut.conj_apply, hg']; group
  have hμ2 : μ ^ 2 ≠ 1 := by
    intro hμ2
    have hμ : μ = 1 ∨ μ = -1 := by
      have : (μ - 1) * (μ + 1) = 0 := by linear_combination hμ2
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hμ with rfl | rfl
    ·
      have hu' : g' = uT (g' 0 1) := by
        have := eq_uT_of_borelDiag_eq_one (A := ⟨g', hg'B⟩) hg00
        exact this
      have hgq : g ^ q = 1 := by
        rw [hgg', ← map_pow, hu', uT_pow_card, map_one]
      have := orderOf_dvd_of_pow_eq_one hgq
      rw [hg] at this
      exact hpq this
    ·
      have hodd' : Odd p := hpp.odd_of_ne_two hp
      rw [hodd'.neg_one_pow] at hμp
      have h2 : (2 : F) = 0 := by linear_combination -hμp
      have hchar : ringChar F = 2 := by
        have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp (by exact_mod_cast h2)
        have hp2 : (ringChar F).Prime := by
          obtain ⟨n, hn⟩ := FiniteField.card F (ringChar F)
          exact hn.1
        exact (Nat.prime_dvd_prime_iff_eq hp2 Nat.prime_two).mp hdvd
      have heven := FiniteField.even_card_of_char_two hchar
      rw [← Nat.card_eq_fintype_card, ← hqdef] at heven
      have := Nat.odd_iff.mp hodd
      omega
  refine ⟨(borelSL2 F).map (MulAut.conj P).toMonoidHom, ⟨g', hg'B, hgg'.symm⟩,
    (twoSubgroupsCyclic_borelSL2 hodd).map_mulAut _,
    pCore_map_mulAut_eq_bot (pCore_borelSL2_eq_bot hp hpq) _,
    MulAut.conj P (uT 1), ⟨uT 1, uT_mem_borelSL2 1, rfl⟩, ?_⟩
  intro hcomm
  rw [hgg', ← map_mul, ← map_mul] at hcomm
  have hc := (MulAut.conj P).injective hcomm
  have h1 : g' * uT 1 * g'⁻¹ = uT 1 := by rw [hc]; group
  rw [borel_mul_uT_mul_inv hg10, hg00, mul_one] at h1
  apply hμ2
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A 0 1) h1
  simpa [coe_uT] using this

theorem exists_noncentral_sq_central (K : Type*) [Field K] :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) K,
      w ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) ∧
        w ^ 2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  let w : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  have hw : (w : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl
  refine ⟨w, ?_, ?_⟩
  · intro hw'
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hw'
    have := congrFun (congrFun hr 0) 1
    rw [hw] at this
    simp at this
  · rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq]

theorem sl2OddNormal : SL2OddNormal := by
  intro K _ _ hKodd N hN hNodd
  classical
  have : Fintype K := Fintype.ofFinite K
  set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)
  set π := QuotientGroup.mk' Z
  have hNn : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective Z)
  have hodd' : Odd (Nat.card (N.map π)) := Odd.of_dvd_nat hNodd (Subgroup.card_map_dvd N π)
  have hNbar : N.map π = ⊥ := by
    have hK3 : 3 ≤ Nat.card K := by
      have h2 : 2 ≤ Nat.card K := by
        have := Fintype.one_lt_card (α := K)
        rw [Nat.card_eq_fintype_card]; omega
      rcases hKodd with ⟨m, hm⟩
      omega
    by_cases hcard3 : Nat.card K = 3
    · have hFcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hcard3
      let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
      let ePSL : CFSG.GorensteinWalter.PSL2 K ≃* alternatingGroup (Fin 4) :=
        (CFSG.GorensteinWalter.psl2RingEquiv eK).symm.trans
          CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup
      have h12 : Nat.card (CFSG.GorensteinWalter.PSL2 K) = 12 := by
        rw [Nat.card_congr ePSL.toEquiv, nat_card_alternatingGroup]
        simp [Nat.factorial]
      have hdvd : Nat.card (N.map π) ∣ 12 := h12 ▸ Subgroup.card_subgroup_dvd_card _
      have h3 : Nat.card (N.map π) ∣ 3 := by
        have hcop : Nat.Coprime (Nat.card (N.map π)) 4 :=
          Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd')
        exact hcop.dvd_of_dvd_mul_left (show Nat.card (N.map π) ∣ 4 * 3 from hdvd)
      have hp3 : IsPGroup 3 (N.map π) := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
        · exact IsPGroup.of_card (n := 0) (by rw [h]; rfl)
        · exact IsPGroup.of_card (n := 1) (by rw [h]; rfl)
      exact CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
        ⟨ePSL⟩ 3 Nat.prime_three (by decide) _ hNn hp3
    · have hcard4 : 4 ≤ Nat.card K := by
        rcases hKodd with ⟨m, hm⟩
        omega
      have hsimple : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 K) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4
      rcases (haveI := hNn; hsimple.eq_bot_or_eq_top_of_normal (N.map π)) with h | h
      · exact h
      · exfalso
        obtain ⟨w, hw, hw2⟩ := exists_noncentral_sq_central K
        have hπw : orderOf (π w) = 2 := by
          apply orderOf_eq_prime
          · rw [← map_pow]
            exact (QuotientGroup.eq_one_iff _).mpr hw2
          · intro h1
            exact hw ((QuotientGroup.eq_one_iff _).mp h1)
        have h2 : 2 ∣ Nat.card (CFSG.GorensteinWalter.PSL2 K) :=
          hπw ▸ orderOf_dvd_natCard (π w)
        have hcard : Nat.card (N.map π) = Nat.card (CFSG.GorensteinWalter.PSL2 K) := by
          rw [h, Subgroup.card_top]
        rw [← hcard] at h2
        exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2)
  have hNZ : N ≤ Z := by
    intro x hx
    have : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [hNbar, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx2 : x ^ 2 = 1 := by
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hNZ hx)
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, Matrix.SpecialLinearGroup.coe_one,
      ← map_pow]
    simp only [Fintype.card_fin] at hr
    rw [hr, map_one]
  have hxN : x ^ Nat.card N = 1 := by
    have := pow_card_eq_one' (G := N) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  exact eq_one_of_pow_coprime (Nat.coprime_two_left.mpr hNodd) hx2 hxN

end CFSG.ABGLocalTools
