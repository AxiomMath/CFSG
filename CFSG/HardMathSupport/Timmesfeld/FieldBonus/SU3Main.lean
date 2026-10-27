module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SU3Core
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.PGlue
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (FieldBonus IsInnerAut)

variable {f : ℕ} {K : Type} [Field K]

@[expose] def SU3DiagonalRank : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), Odd f → 3 ≤ f →
    ∀ H : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))),
      H ≤ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → IsElemAbelian 3 H →
        Nat.card H ≠ 27

theorem isPrimeFormGram_one3 : IsPrimeFormGram (1 : GL (Fin 3) K) :=
  CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.isPrimeFormGram_idGL

theorem not_three_two_of_three_le {f : ℕ} (hf3 : 3 ≤ f) : ¬(3 = 3 ∧ 2 ^ f = 2) := by
  rintro ⟨-, h⟩
  have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  omega

variable [Finite K] (h : UnitaryFieldData 2 f K)

omit [Finite K] in
theorem Z3_eq_center (hf : Odd f) (hZ : Nat.card (Subgroup.center (S3 h)) = 3) :
    Z3 h = Subgroup.center (S3 h) := by
  have hfin := h.finite
  refine Subgroup.eq_of_le_of_card_ge (normOneScalars_le_center h _ 3) ?_
  rw [hZ, CFSG.RankThree.Classical.card_normOneScalars_one h (by norm_num),
    Nat.gcd_eq_left (three_dvd_two_pow_add_one hf)]

theorem isPerfect_S3 (hf3 : 3 ≤ f) : Group.IsPerfect (S3 h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : (3, 2 ^ f) ≠ (3, 2) := fun hh => not_three_two_of_three_le hf3 ⟨rfl, by
    simpa using congrArg Prod.snd hh⟩
  have hperf : Group.IsPerfect ↥(StatedSU 3 (2 ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (by rw [h.card_eq_sq]) (n := 3) le_rfl hnq
  have : Group.IsPerfect ↥(unitarySU 2 f K 3) := hperf
  exact Group.IsPerfect.ofSurjective
    (f := (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).toMonoidHom)
    (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).surjective

theorem PhiAut_injective (hZ : Z3 h = Subgroup.center (S3 h)) (hf3 : 3 ≤ f) :
    Function.Injective (PhiAut h hZ) := by
  have := isPerfect_S3 h hf3
  exact (MulAut.congr (eP h hZ).symm).injective.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective (S3 h))

omit [Finite K] in
theorem PhiAut_conjSU (hZ : Z3 h = Subgroup.center (S3 h))
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    PhiAut h hZ (primeFormConjSU h _ A : MulAut (S3 h)) = primeFormConjHom h _ A := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [PhiAut_mk]
  exact (primeFormConjHom_mk h _ A g).symm

omit [Finite K] in
theorem PhiAut_fieldSU (hZ : Z3 h = Subgroup.center (S3 h)) (σ : K ≃+* K) :
    PhiAut h hZ (primeFormFieldSU h isPrimeFormGram_one3 σ : MulAut (S3 h)) =
      primeFormFieldHom h isPrimeFormGram_one3 σ := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [PhiAut_mk]
  exact (primeFormFieldAut_mk h isPrimeFormGram_one3 σ g).symm

omit [Finite K] in
theorem PhiAut_conj (hZ : Z3 h = Subgroup.center (S3 h)) (g : S3 h) :
    PhiAut h hZ (MulAut.conj g) =
      primeFormConjHom h _ ⟨(g : GL (Fin 3) K), ((mem_gramSU_iff_unitary h).1 g.2).1⟩ := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [PhiAut_mk, primeFormConjHom_mk]
  rfl

theorem fieldBonus_su3 (hD : SU3DiagonalRank) (hf : Odd f) (hf3 : 3 ≤ f)
    (hZ : Nat.card (Subgroup.center (S3 h)) = 3)
    (hm : CFSG.Open.pRank 3 (⊤ : Subgroup (S3 h)) = 2) (hw : GLATwoLocalRank 3 (S3 h) = 1)
    (H : Subgroup (MulAut (S3 h))) (hH : IsElemAbelian 3 H) (hc : Nat.card H = 27) :
    FieldBonus (S3 h) 3 H := by
  have hfin := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ0 := Z3_eq_center h hf hZ
  have hinj := PhiAut_injective h hZ0 hf3
  have hne := not_three_two_of_three_le hf3
  have hC1 : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one3
  have hex : ∃ ψ ∈ H, primeFormFieldFactor h hC1 le_rfl hne (PhiAut h hZ0 ψ) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hD f K h hf hf3 (H.map (PhiAut h hZ0)) (fun x hx => ?_)
      (CFSG.SectionRank.isElemAbelian_map hH _) (by rw [Subgroup.card_map_of_injective hinj, hc])
    obtain ⟨ψ, hψ, rfl⟩ := hx
    rw [← ker_primeFormFieldFactor h hC1 le_rfl hne]
    exact hcon ψ hψ
  obtain ⟨ψ, hψH, hψσ⟩ := hex
  set σ := primeFormFieldFactor h hC1 le_rfl hne (PhiAut h hZ0 ψ) with hσdef
  have hψ3 : ψ ^ 3 = 1 := hH.2 ψ hψH
  have hΦ3 : (PhiAut h hZ0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hΦ3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hψσ
  have hΦ1 : PhiAut h hZ0 ψ ≠ 1 := fun h1 => hψσ (by rw [hσdef, h1, map_one])
  have hΦord : orderOf (PhiAut h hZ0 ψ) = 3 := orderOf_eq_prime hΦ3 hΦ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h le_rfl hne
      Nat.prime_three (by norm_num) (by norm_num) (PhiAut h hZ0 ψ) hΦord σ rfl hσord
  have hψeq : ψ = (primeFormConjSU h _ M : MulAut (S3 h)) *
      (primeFormFieldSU h hC1 σ : MulAut (S3 h)) * (primeFormConjSU h _ M : MulAut (S3 h))⁻¹ := by
    apply hinj
    rw [map_mul, map_mul, map_inv, PhiAut_conjSU, PhiAut_fieldSU]
    rw [← hM]
    group
  have hcore : FBCore (S3 h) 3 ψ := by
    rw [hψeq]
    exact (fbCore_fieldSU h hC1 hf hm hw hσord).conj _
  have hni : ¬ IsInnerAut ψ := by
    rintro ⟨g, hg⟩
    have hψg : ψ = MulAut.conj g := MulEquiv.ext fun t => by simpa [MulAut.conj_apply] using hg t
    have h1 : PhiAut h hZ0 ψ = primeFormConjHom h _ ⟨(g : GL (Fin 3) K),
        ((mem_gramSU_iff_unitary h).1 g.2).1⟩ := by
      rw [hψg]; exact PhiAut_conj h hZ0 g
    apply hψσ
    have := primeFormFieldFactor_apply h hC1 le_rfl hne
      ⟨(g : GL (Fin 3) K), ((mem_gramSU_iff_unitary h).1 g.2).1⟩ 1
    rw [map_one, mul_one] at this
    rw [hσdef, h1]
    exact this
  exact fieldBonus_of_fbCore hψH hni hcore

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
