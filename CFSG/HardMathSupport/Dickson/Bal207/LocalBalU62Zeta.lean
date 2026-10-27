module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Shape
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62TorusB
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReduction
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealSingle

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

variable {K : Type} [Field K]

theorem u62lb_conjHom_eq_one_iff (h : UnitaryFieldData 2 1 K)
    (B : primeFormUnitary h (idGram K 6)) :
    primeFormConjHom h (idGram K 6) B = 1 ↔
      ∃ c : Kˣ, (B : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  constructor
  · intro h1
    have hC : IsPrimeFormGram (1 : GL (Fin 6) K) := isPrimeFormGram_idGram
    have hq' : ¬(6 = 3 ∧ 2 ^ 1 = 2) := by omega
    obtain ⟨-, -, hker1, -⟩ :=
      unitary_prime_form_full_semilinear_realization h hC (by norm_num) hq'
    have e : primeFormPsi h hC ⟨B, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one]
      exact h1
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 e
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact excU62_conjHom_scalar B hc

theorem u62lb_glAut_scalar (φ : K ≃+* K) (c : Kˣ) :
    glAut φ (Matrix.GeneralLinearGroup.scalar (Fin 6) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (φ : K →* K) c) := by
  apply Units.ext
  rw [coe_glAut, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem u62lb_scalar_injective {c d : Kˣ}
    (hcd : Matrix.GeneralLinearGroup.scalar (Fin 6) c =
      Matrix.GeneralLinearGroup.scalar (Fin 6) d) : c = d := by
  have := congrArg (fun U : GL (Fin 6) K => (U : Matrix (Fin 6) (Fin 6) K) 0 0) hcd
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem u62lb_conj_pow_three {G : Type*} [Group G] (M A z : G) (hz : ∀ g : G, g * z = z * g)
    (hMA : M * A * M⁻¹ = A * z) (hz3 : z ^ 3 = 1) : M ^ 3 * A * (M ^ 3)⁻¹ = A := by
  have hzM : M * z * M⁻¹ = z := by
    rw [hz M]
    group
  have e1 : M * (A * z) * M⁻¹ = A * z * z := by
    calc M * (A * z) * M⁻¹ = (M * A * M⁻¹) * (M * z * M⁻¹) := by group
      _ = A * z * z := by rw [hMA, hzM]
  have e2 : M * (A * z * z) * M⁻¹ = A * z * z * z := by
    calc M * (A * z * z) * M⁻¹ = (M * A * M⁻¹) * (M * z * M⁻¹) * (M * z * M⁻¹) := by group
      _ = A * z * z * z := by rw [hMA, hzM]
  have hM3 : M ^ 3 * A * (M ^ 3)⁻¹ = M * (M * (M * A * M⁻¹) * M⁻¹) * M⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  have hz3' : A * z * z * z = A * z ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc M ^ 3 * A * (M ^ 3)⁻¹ = M * (M * (M * A * M⁻¹) * M⁻¹) * M⁻¹ := hM3
    _ = M * (M * (A * z) * M⁻¹) * M⁻¹ := by rw [hMA]
    _ = M * (A * z * z) * M⁻¹ := by rw [e1]
    _ = A * z * z * z := e2
    _ = A * z ^ 3 := hz3'
    _ = A := by rw [hz3, mul_one]

section Perfect

variable (h : UnitaryFieldData 2 1 K)

theorem u62lb_commute_block (M : primeFormUnitary h (idGram K 6))
    (B₀ : Subgroup (gramSU h (idGram K 6))) (hB₀ : ⁅B₀, B₀⁆ = B₀)
    (hfix : ∀ s ∈ B₀, primeFormConjHom h (idGram K 6) M (s : primeFormP h (idGram K 6)) =
      (s : primeFormP h (idGram K 6))) :
    ∀ s ∈ B₀,
      (M : GL (Fin 6) K) * (s : GL (Fin 6) K) = (s : GL (Fin 6) K) * (M : GL (Fin 6) K) := by
  have hle : B₀ ≤ fixSubgroup (t6psub_actSU h 6 M) := by
    conv_lhs => rw [← hB₀]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact comm_mem_fixSubgroup (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6))
      u6r_ker_le_center (t6psub_actSU h 6 M) (primeFormConjHom h (idGram K 6) M)
      (fun x => t6psub_hact M x) (hfix a ha) (hfix b hb)
  intro s hs
  have h1 : t6psub_actSU h 6 M s = s := mem_fixSubgroup.1 (hle hs)
  have h2 := congrArg (fun u : gramSU h (idGram K 6) => (u : GL (Fin 6) K)) h1
  have h3 : (M : GL (Fin 6) K) * (s : GL (Fin 6) K) * (M : GL (Fin 6) K)⁻¹ = (s : GL (Fin 6) K) :=
    h2
  generalize (M : GL (Fin 6) K) = m at h3 ⊢
  generalize (s : GL (Fin 6) K) = s' at h3 ⊢
  calc m * s' = (m * s' * m⁻¹) * m := by group
    _ = s' * m := by rw [h3]

end Perfect

theorem u62lb_fieldCore_zeta_of_pow (h : UnitaryFieldData 2 1 K)
    (A : primeFormUnitary h (idGram K 6)) {c : Kˣ}
    (hA3 : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) (hc : c ≠ 1)
    (hZ : ∀ Y : primeFormUnitary h (idGram K 6), Y * A = A * Y →
      (∀ i : t6psub_Idx h 6 A, ∀ s ∈ t6psub_block A i,
        (Y : GL (Fin 6) K) * (s : GL (Fin 6) K) = (s : GL (Fin 6) K) * (Y : GL (Fin 6) K)) →
      Y ^ 9 = 1) :
    FieldCoreAt 3 (primeFormConjHom h (idGram K 6) A) := by
  classical
  haveI := excU62_finite h
  have hcube : ∀ a : Kˣ, a ^ 3 ≠ c := fun a ha => hc (ha.symm.trans (excU62_units_pow_three h a))
  obtain ⟨i₀, hi₀, hT⟩ := u6r_single odd_one A hA3 hcube
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A) :=
    t6psuh_primaryData_toLin' h A.2 Nat.prime_three (by norm_num) hA3
  have hTq : CFSG.IsQuasisimple (excU62_N A i₀) := u6r_block_quasisimple A H i₀
  have hTF : excU62_N A i₀ ≤ fixSub (primeFormConjHom h (idGram K 6) A) :=
    (u6r_block_le A i₀).trans (u6r_map_fix_le A)
  have hTperf : ⁅excU62_N A i₀, excU62_N A i₀⁆ = excU62_N A i₀ :=
    Subgroup.isPerfect_iff.mp hTq.1
  have hB₀perf : ⁅t6psub_block A i₀, t6psub_block A i₀⁆ = t6psub_block A i₀ :=
    Subgroup.isPerfect_iff.mp (t6psub_isQuasisimple_block A H i₀).1
  refine ⟨excU62_N A i₀, hTF, ?_, hTq, ?_, ?_⟩
  ·
    intro f hf t ht
    have hsup : (⨆ i : t6psub_Idx h 6 A, excU62_N A i) ≤ excU62_N A i₀ :=
      iSup_le fun i => by rw [hi₀ i]
    have hP : ⁅(excU62_N A i₀).map (MulAut.conj f).toMonoidHom,
        (excU62_N A i₀).map (MulAut.conj f).toMonoidHom⁆ =
        (excU62_N A i₀).map (MulAut.conj f).toMonoidHom := by
      rw [← Subgroup.map_commutator, hTperf]
    have hPC : (excU62_N A i₀).map (MulAut.conj f).toMonoidHom ≤
        fixSubgroup (primeFormConjHom h (idGram K 6) A) := by
      rintro _ ⟨t', ht', rfl⟩
      have h1 : primeFormConjHom h (idGram K 6) A f = f := mem_fixSub.1 hf
      have h2 : primeFormConjHom h (idGram K 6) A t' = t' := mem_fixSub.1 (hTF ht')
      show (primeFormConjHom h (idGram K 6) A) (f * t' * f⁻¹) = f * t' * f⁻¹
      rw [map_mul, map_mul, map_inv, h1, h2]
    exact excU62_perfect_le A H hsup _ hPC hP ⟨t, ht, rfl⟩
  ·
    intro hcop
    have hdvd : 3 ∣ Nat.card (excU62_N A i₀) :=
      (u6r_three_dvd_of_isTypeL2 hT).trans (Subgroup.card_quotient_dvd_card _)
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)
  ·
    intro g hg3 hgx hgT
    have hC : IsPrimeFormGram (1 : GL (Fin 6) K) := isPrimeFormGram_idGram
    obtain ⟨φ, ⟨M, hM⟩, -⟩ := existsUnique_primeFormFieldFactor h hC (by norm_num) (by omega) g
    have hconj : primeFormFieldHom h hC φ * primeFormConjHom h (idGram K 6) A *
        (primeFormFieldHom h hC φ)⁻¹ =
        primeFormConjHom h (idGram K 6) (primeFormFieldU h hC φ A) :=
      primeFormField_conj_eq h hC φ A
    have h1 : primeFormConjHom h (idGram K 6) (M * primeFormFieldU h hC φ A * M⁻¹) =
        primeFormConjHom h (idGram K 6) A := by
      calc primeFormConjHom h (idGram K 6) (M * primeFormFieldU h hC φ A * M⁻¹)
          = g * primeFormConjHom h (idGram K 6) A * g⁻¹ := by
            rw [map_mul, map_mul, map_inv, ← hconj, hM]
            group
        _ = primeFormConjHom h (idGram K 6) A := by rw [hgx]; group
    have h2 : primeFormConjHom h (idGram K 6)
        (A⁻¹ * (M * primeFormFieldU h hC φ A * M⁻¹)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    obtain ⟨l, hl⟩ := (u62lb_conjHom_eq_one_iff h _).1 h2
    have hl' : (A : GL (Fin 6) K)⁻¹ * ((M : GL (Fin 6) K) * glAut φ (A : GL (Fin 6) K) *
        (M : GL (Fin 6) K)⁻¹) = Matrix.GeneralLinearGroup.scalar (Fin 6) l := hl
    have hMA : (M : GL (Fin 6) K) * glAut φ (A : GL (Fin 6) K) * (M : GL (Fin 6) K)⁻¹ =
        (A : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) l :=
      inv_mul_eq_iff_eq_mul.1 hl'
    have hzc : ∀ g : GL (Fin 6) K,
        g * Matrix.GeneralLinearGroup.scalar (Fin 6) l =
          Matrix.GeneralLinearGroup.scalar (Fin 6) l * g := fun g =>
      (Matrix.GeneralLinearGroup.scalar_commute l g).symm
    have hz3 : Matrix.GeneralLinearGroup.scalar (Fin 6) l ^ 3 = 1 := by
      rw [← map_pow, excU62_units_pow_three h l, map_one]
    have hcube1 : ((M : GL (Fin 6) K) * glAut φ (A : GL (Fin 6) K) *
        (M : GL (Fin 6) K)⁻¹) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (φ : K →* K) c) := by
      rw [conj_pow, ← map_pow, hA3, u62lb_glAut_scalar]
      exact mul_inv_eq_iff_eq_mul.2 (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
    have hcube2 : ((A : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) l) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      have hcomm : Commute (A : GL (Fin 6) K) (Matrix.GeneralLinearGroup.scalar (Fin 6) l) :=
        hzc _
      rw [hcomm.mul_pow, hA3, hz3, mul_one]
    have hscal : Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (φ : K →* K) c) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      rw [← hcube1, hMA, hcube2]
    have hφc : φ (c : K) = c := by
      have := congrArg (fun u : Kˣ => (u : K)) (u62lb_scalar_injective hscal)
      simpa using this
    have hφ : φ = 1 := u62lb_torus_ringEquiv_eq_one h hc hφc
    subst hφ
    have hgM : g = primeFormConjHom h (idGram K 6) M := by rw [hM, map_one, mul_one]
    have hgl : glAut (1 : K ≃+* K) (A : GL (Fin 6) K) = (A : GL (Fin 6) K) := by
      have e : primeFormFieldU h hC 1 A = A := by rw [map_one]; rfl
      exact congrArg (fun u : primeFormUnitary h (idGram K 6) => (u : GL (Fin 6) K)) e
    rw [hgl] at hMA
    have hYA : M ^ 3 * A = A * M ^ 3 := by
      apply Subtype.ext
      have h4 := u62lb_conj_pow_three (M : GL (Fin 6) K) (A : GL (Fin 6) K)
        (Matrix.GeneralLinearGroup.scalar (Fin 6) l) hzc hMA hz3
      exact mul_inv_eq_iff_eq_mul.1 h4
    have hfixM : ∀ s ∈ t6psub_block A i₀,
        primeFormConjHom h (idGram K 6) M (s : primeFormP h (idGram K 6)) =
          (s : primeFormP h (idGram K 6)) := by
      intro s hs
      have := hgT (s : primeFormP h (idGram K 6)) ⟨s, hs, rfl⟩
      rwa [hgM] at this
    have hcommM := u62lb_commute_block h M (t6psub_block A i₀) hB₀perf hfixM
    have hY : ∀ i : t6psub_Idx h 6 A, ∀ s ∈ t6psub_block A i,
        ((M ^ 3 : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) * (s : GL (Fin 6) K) =
          (s : GL (Fin 6) K) * ((M ^ 3 : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) := by
      intro i s hs
      obtain rfl := hi₀ i
      exact (Commute.pow_left (show Commute (M : GL (Fin 6) K) (s : GL (Fin 6) K) from
        hcommM s hs) 3).eq
    have hpow : (M ^ 3) ^ 9 = 1 := hZ (M ^ 3) hYA hY
    have hM27 : M ^ 27 = 1 := by
      rw [show (27 : ℕ) = 3 * 9 from rfl, pow_mul]
      exact hpow
    have hg27 : g ^ (3 ^ 3) = 1 := by
      rw [hgM, ← map_pow, show (3 : ℕ) ^ 3 = 27 from rfl, hM27, map_one]
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3 hg3.symm)
      (orderOf_dvd_of_pow_eq_one hg27))

end CFSG.HardMathSupport.Dickson.Bal207

end
