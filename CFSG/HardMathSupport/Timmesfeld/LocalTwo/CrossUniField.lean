module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f : ℕ} {K : Type} [Field K]

section Normalizer

variable (h : UnitaryFieldData ℓ f K) (n : ℕ) {σ : K ≃+* K} {e : ℕ}
  (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
  (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)

theorem conj_mem_range_subfieldPSU
    {g t : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hg : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ g = g)
    (ht : t ∈ (subfieldPSU h h₀ hbar n).range) :
    g * t * g⁻¹ ∈ (subfieldPSU h h₀ hbar n).range := by
  obtain ⟨t0, rfl⟩ := ht
  induction t0 using QuotientGroup.induction_on with
  | H T0 =>
    induction g using QuotientGroup.induction_on with
    | H G =>
      rw [subfieldPSU_mk]
      change primeFormFieldAut h isPrimeFormGram_one σ
        ((G : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        ((G : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
          primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) at hg
      rw [primeFormFieldAut_mk] at hg
      obtain ⟨c, -, -, hcz⟩ := QuotientGroup.eq.1 hg.symm
      have hGσ : glAut σ (G : GL (Fin n) K) =
          (G : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
        have : (G : GL (Fin n) K)⁻¹ * glAut σ (G : GL (Fin n) K) =
            GeneralLinearGroup.scalar (Fin n) c := hcz
        rw [← this, mul_inv_cancel_left]
      have hT0σ : glAut σ (subfieldGL (fixSubfield σ) n (T0 : GL (Fin n) (fixSubfield σ))) =
          subfieldGL (fixSubfield σ) n (T0 : GL (Fin n) (fixSubfield σ)) := by
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [coe_glAut, coe_subfieldGL]
        exact (((T0 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2
      set Tt := subfieldGL (fixSubfield σ) n (T0 : GL (Fin n) (fixSubfield σ)) with hTt
      have hX : glAut σ ((G : GL (Fin n) K) * Tt * (G : GL (Fin n) K)⁻¹) =
          (G : GL (Fin n) K) * Tt * (G : GL (Fin n) K)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hGσ, hT0σ]
        have hc : GeneralLinearGroup.scalar (Fin n) c * Tt =
            Tt * GeneralLinearGroup.scalar (Fin n) c := GeneralLinearGroup.scalar_commute c Tt
        calc (G : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c * Tt *
              ((G : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c)⁻¹
            = (G : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) c * Tt) *
              (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * (G : GL (Fin n) K)⁻¹ := by group
          _ = (G : GL (Fin n) K) * (Tt * GeneralLinearGroup.scalar (Fin n) c) *
              (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * (G : GL (Fin n) K)⁻¹ := by rw [hc]
          _ = (G : GL (Fin n) K) * Tt * (G : GL (Fin n) K)⁻¹ := by group
      obtain ⟨X0, hX0⟩ := exists_subfieldGL_eq_of_fixed n hX
      have hXmem : (G : GL (Fin n) K) * Tt * (G : GL (Fin n) K)⁻¹ ∈
          gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        mul_mem (mul_mem G.2 (subfieldGL_mem_gramSU h h₀ hbar n T0.2)) (inv_mem G.2)
      have hX0mem := mem_gramSU_of_subfieldGL h n h₀ hbar (g₀ := X0) (by rw [hX0]; exact hXmem)
      refine ⟨((⟨X0, hX0mem⟩ : gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) : primeFormP h₀ _), ?_⟩
      rw [subfieldPSU_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hX0

end Normalizer

section Core

variable (h : UnitaryFieldData ℓ f K) {n p : ℕ}

theorem fieldCoreAt_fieldHom_of_subfield [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2))
    (hJp : p ∣ Nat.card (primeSubfieldPSU h hp hp2 hσ n).range) :
    FieldCoreAt p (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  classical
  have hfin := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨hpf, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hinj := subfieldPSU_injective h h₀ hbar n (by omega)
  have := isSimpleGroup_primeFormP_one h₀ hn hq₀
  have hnc := not_commute_primeFormP_one h₀ hn hq₀
  let eJ := MonoidHom.ofInjective hinj
  have hsimple : IsSimpleGroup (subfieldPSU h h₀ hbar n).range := eJ.symm.isSimpleGroup
  have hnab : ∃ a b : (subfieldPSU h h₀ hbar n).range, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    apply hnc
    intro x y
    have h1 := congrArg eJ.symm (hc (eJ x) (eJ y))
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
  obtain ⟨hfixing, hmap, -⟩ := fixingSubgroup_range_subfieldPSU h n h₀ hbar hn hne hq₀
  refine ⟨(subfieldPSU h h₀ hbar n).range, fun x hx => ?_, fun g hg t ht => ?_,
    isQuasisimple_of_simple_nonabelian (fun hc => by
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc a b)), fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc hJp,
    ?_⟩
  · exact range_subfieldPSU_le h n h₀ hbar hx
  · exact conj_mem_range_subfieldPSU h n h₀ hbar (mem_fixSub.1 hg) ht
  · intro g hgp _ hgJ
    have hgmem : g ∈ fixingSubgroup (MulAut (primeFormP h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
        ((subfieldPSU h h₀ hbar n).range : Set (primeFormP h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
      (mem_fixingSubgroup_iff _).2 fun u hu => hgJ u hu
    rw [hfixing, hmap] at hgmem
    have hδp : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ ^ p = 1 := by
      rw [← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
    have hdvd : orderOf g ∣ p :=
      (orderOf_dvd_of_mem_zpowers hgmem).trans (orderOf_dvd_of_pow_eq_one hδp)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

end Core

section Numerics

variable {L : Type} [Field L] [Finite L] {e : ℕ} (h₀ : UnitaryFieldData ℓ e L)
include h₀

theorem exists_normOne_unit_of_prime_dvd {p : ℕ} (hp : p.Prime) (hpq : p ∣ ℓ ^ e + 1) :
    ∃ v : Lˣ, v ^ p = 1 ∧ v ≠ 1 ∧ h₀.norm (v : L) = 1 := by
  classical
  have hq2 : 2 ≤ ℓ ^ e :=
    calc 2 ≤ ℓ := h₀.prime.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right h₀.prime.pos h₀.one_le
  have hN : Nat.card Lˣ = (ℓ ^ e + 1) * (ℓ ^ e - 1) := by
    rw [Nat.card_units, h₀.card, show ℓ ^ (2 * e) = (ℓ ^ e) ^ 2 by rw [← pow_mul, mul_comm]]
    zify [Nat.one_le_pow 2 (ℓ ^ e) (by omega), show 1 ≤ ℓ ^ e by omega]
    ring
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hord : orderOf w = Nat.card Lˣ := orderOf_eq_card_of_forall_mem_zpowers hw
  have hwN : w ^ Nat.card Lˣ = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
  obtain ⟨m, hm⟩ := hpq
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm; omega
    · exact h0
  have hq1 : 0 < ℓ ^ e - 1 := by omega
  set v : Lˣ := w ^ ((ℓ ^ e - 1) * m) with hv
  have hvp : v ^ p = 1 := by
    rw [hv, ← pow_mul, show (ℓ ^ e - 1) * m * p = Nat.card Lˣ by rw [hN, hm]; ring]
    exact hwN
  have hvq : v ^ (ℓ ^ e + 1) = 1 := by
    rw [hv, ← pow_mul, hm, show (ℓ ^ e - 1) * m * (p * m) = Nat.card Lˣ * m by
      rw [hN, hm]; ring, pow_mul, hwN, one_pow]
  refine ⟨v, hvp, ?_, (CFSG.RankThree.PartOne.KCUnitaryModel.pow_succ_eq_one_iff_norm h₀ v).mp hvq⟩
  intro hv1
  rw [hv, pow_eq_one_iff_modEq, hord] at hv1
  have hdvd : Nat.card Lˣ ∣ (ℓ ^ e - 1) * m := by
    exact (Nat.modEq_zero_iff_dvd).1 hv1
  have ha : 0 < (ℓ ^ e - 1) * m := by positivity
  have := Nat.le_of_dvd ha hdvd
  rw [hN, hm, show p * m * (ℓ ^ e - 1) = p * ((ℓ ^ e - 1) * m) by ring] at this
  nlinarith [hp.two_le]

theorem dvd_card_primeFormP_one {n p : ℕ} (hp : p.Prime) (hn : 3 ≤ n) (hpq : p ∣ ℓ ^ e + 1) :
    p ∣ Nat.card (primeFormP h₀ ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
  classical
  obtain ⟨v, hvp, hv1, hvn⟩ := exists_normOne_unit_of_prime_dvd h₀ hp hpq
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  set c : Fin n := ⟨2, by omega⟩ with hc
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hac : a ≠ c := by simp [ha, hc, Fin.ext_iff]
  have hbc : b ≠ c := by simp [hb, hc, Fin.ext_iff]
  obtain ⟨hd1, hd2⟩ := pairDiag_norm_prod h₀ hvn a c
  set d : Fin n → Lˣ := Pi.mulSingle a v * Pi.mulSingle c v⁻¹ with hd
  let D : gramSU h₀ ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    ⟨unitaryDiagGL d, unitaryDiagGL_mem_gramSU h₀ hd1 hd2⟩
  have hda : d a = v := by simp [hd, Pi.mulSingle_apply, hac]
  have hdb : d b = 1 := by simp [hd, Pi.mulSingle_apply, hab.symm, hbc]
  have hdp : ∀ i, d i ^ p = 1 := by
    intro i
    by_cases hia : i = a
    · rw [hia, hda]; exact hvp
    · by_cases hic : i = c
      · have : d c = v⁻¹ := by simp [hd, Pi.mulSingle_apply, hac.symm]
        rw [hic, this, inv_pow, hvp, inv_one]
      · have : d i = 1 := by simp [hd, Pi.mulSingle_apply, hia, hic]
        rw [this, one_pow]
  have hxp : (D : primeFormP h₀ ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : D ^ p = 1 := by
      refine Subtype.ext (Units.ext ?_)
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      change (Matrix.diagonal fun i => (d i : L)) ^ p = 1
      rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
      congr 1
      funext i
      have := congrArg (fun u : Lˣ => (u : L)) (hdp i)
      simpa using this
    rw [this]
    exact one_mem _
  have hx1 : (D : primeFormP h₀ ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c0, -, -, hc0⟩ := h1
    have e1 := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L) b b) hc0
    have e2 := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L) a a) hc0
    simp only [coe_unitaryDiagGL, Matrix.diagonal_apply_eq, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at e1 e2
    change (d b : L) = c0 at e1
    change (d a : L) = c0 at e2
    rw [hdb] at e1
    rw [hda] at e2
    apply hv1
    apply Units.ext
    exact e2.trans e1.symm
  have : Fact p.Prime := ⟨hp⟩
  have hord := orderOf_eq_prime hxp hx1
  rw [← hord]
  exact orderOf_dvd_natCard _

end Numerics

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
