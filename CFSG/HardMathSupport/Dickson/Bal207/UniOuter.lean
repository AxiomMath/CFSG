module

public import CFSG.HardMathSupport.Dickson.Bal207.UniNormalAut
public import CFSG.HardMathSupport.Dickson.Bal207.UniOrder
import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Type

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.UnitaryDescent
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

theorem uni_fixSubgroup_conj {S : Type*} [Group S] (α β : MulAut S) :
    fixSubgroup (β * α * β⁻¹) = (fixSubgroup α).map β.toMonoidHom := by
  ext x
  constructor
  · intro hx
    have hx' : β (α (β⁻¹ x)) = x := hx
    refine ⟨β⁻¹ x, ?_, MulAut.apply_inv_self (e := β) (m := x)⟩
    show α (β⁻¹ x) = β⁻¹ x
    calc α (β⁻¹ x) = β⁻¹ (β (α (β⁻¹ x))) := (MulAut.inv_apply_self (e := β) (m := _)).symm
      _ = β⁻¹ x := by rw [hx']
  · rintro ⟨y, hy, rfl⟩
    have hy' : α y = y := hy
    show β (α (β⁻¹ (β y))) = β y
    rw [MulAut.inv_apply_self, hy']

section Lang

variable {f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uni_psi_inr (τ : F ≃+* F) :
    primeFormPsi h uni_isPrimeFormGram_one (SemidirectProduct.inr τ : UniGamma h n) =
      primeFormFieldHom h uni_isPrimeFormGram_one τ := by
  rw [show (SemidirectProduct.inr τ : UniGamma h n) = ⟨1, τ⟩ from rfl, primeFormPsi_apply,
    map_one, one_mul]

variable {h}

theorem uni_diag_cube (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1) (j : Fin n) :
    ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j ^ 3 = 1 := by
  have h1 : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hD3, Subgroup.coe_one, Units.val_one]
  rw [← hD.diagonal_diag, diagonal_pow] at h1
  have h2 := congrFun (congrFun h1 j) j
  rw [diagonal_apply_eq, one_apply_eq, Pi.pow_apply, diag_apply] at h2
  exact h2

theorem uni_glAut_diag (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1)
    {φ : F ≃+* F} (hφ : φ ^ 3 = 1) : glAut φ (D : GL (Fin n) F) = D := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    exact uni_fix_cube_root hφ (uni_diag_cube D hD hD3 i)
  · rw [hD hij, map_zero]

theorem uni_twistedNorm_diag (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1)
    {τ : F ≃+* F} (hτ : τ ^ 3 = 1) : twistedNorm τ (D : GL (Fin n) F) 3 = 1 := by
  have hk : ∀ k : ℕ, glAut (τ ^ k) (D : GL (Fin n) F) = D := fun k =>
    uni_glAut_diag D hD hD3 (by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow])
  have h3' : (D : GL (Fin n) F) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hD3, Subgroup.coe_one]
  rw [twistedNorm_succ, twistedNorm_succ, twistedNorm_succ, twistedNorm_zero, hk, hk, hk, one_mul,
    mul_assoc, ← pow_three, h3']

theorem uni_exists_conj_inr (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1)
    {τ : F ≃+* F} (hτ3 : τ ^ 3 = 1) (hτo : orderOf τ = 3) :
    ∃ M : primeFormUnitary h (oneGram F n),
      (SemidirectProduct.inl D * SemidirectProduct.inr τ : UniGamma h n) =
        SemidirectProduct.inl M * SemidirectProduct.inr τ * (SemidirectProduct.inl M)⁻¹ := by
  obtain ⟨M, hMU, hM⟩ := uni_exists_fixed_unitary h Nat.prime_three (by norm_num) hτo D.2
    (uni_twistedNorm_diag D hD hD3 hτ3)
  refine ⟨⟨M, hMU⟩, eq_mul_inv_of_mul_eq ?_⟩
  have hφM : D * primeFormFieldU h uni_isPrimeFormGram_one τ ⟨M, hMU⟩ = ⟨M, hMU⟩ :=
    Subtype.ext (by
      rw [Subgroup.coe_mul, coe_primeFormFieldU]
      exact hM)
  rw [mul_assoc, uni_inr_mul_inl, ← mul_assoc, ← map_mul, hφM]

end Lang

section Outer

variable {f n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 f F}

theorem uni_outer_card_ne (hf : f = 1 ∨ f = 3) (hn : 4 ≤ n) (h3 : ¬ 3 ∣ n)
    (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1)
    {τ : F ≃+* F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {L : Subgroup (primeFormP h (oneGram F n))}
    (hL : CFSG.Open.IsComponentOf L (fixSubgroup (primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl D * SemidirectProduct.inr τ)))) :
    Nat.card (↥L ⧸ Subgroup.center ↥L) ≠ 5515776 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hτo : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  have hZ : ¬ 3 ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n) := by
    rw [uni_normOneScalars_eq_bot h hf h3 (by omega), Subgroup.card_bot]
    norm_num
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -, -, hsimp, -⟩ :=
    prime_subfield_fixed_group_package h Nat.prime_three (by norm_num) hτo n (by omega)
      (fun h' => absurd h'.1 (by omega)) hZ
  have hf3 : f = 3 := by
    rcases hf with rfl | rfl
    · norm_num at hpf
    · rfl
  obtain ⟨hS, -⟩ := hsimp (fun h' => absurd h'.1 (by omega))
  obtain ⟨M, hM⟩ := uni_exists_conj_inr D hD hD3 hτ3 hτo
  have hΨ : primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl D * SemidirectProduct.inr τ) =
        primeFormConjHom h (oneGram F n) M * primeFormFieldHom h uni_isPrimeFormGram_one τ *
          (primeFormConjHom h (oneGram F n) M)⁻¹ := by
    rw [hM, map_mul, map_mul, map_inv, uni_psi_inl, uni_psi_inr]
  have hC : fixSubgroup (primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl D * SemidirectProduct.inr τ)) =
        (fieldFixedPSU h n τ).map (primeFormConjHom h (oneGram F n) M).toMonoidHom := by
    rw [hΨ]
    exact uni_fixSubgroup_conj _ _
  rw [hC] at hL
  have hβi : Function.Injective (primeFormConjHom h (oneGram F n) M).toMonoidHom :=
    (primeFormConjHom h (oneGram F n) M).injective
  have hCs : IsSimpleGroup
      ↥((fieldFixedPSU h n τ).map (primeFormConjHom h (oneGram F n) M).toMonoidHom) :=
    (Subgroup.equivMapOfInjective (fieldFixedPSU h n τ) _ hβi).symm.isSimpleGroup
  have hLC : L = (fieldFixedPSU h n τ).map (primeFormConjHom h (oneGram F n) M).toMonoidHom := by
    rcases hL.2.1.eq_bot_or_eq_of_isSimpleGroup hCs with hb | he
    · haveI := excU62_nontrivial_of_isQuasisimple hL.2.2
      exact absurd hb ((Subgroup.nontrivial_iff_ne_bot L).1 inferInstance)
    · exact he
  haveI : IsSimpleGroup ↥L := by
    rw [hLC]
    exact hCs
  have hcardL : Nat.card ↥L = Nat.card ↥(fieldFixedPSU h n τ) := by
    rw [hLC]
    exact Subgroup.card_map_of_injective hβi
  intro hcard
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥L) with h1 | h1
  · have e : Nat.card (↥L ⧸ (⊥ : Subgroup ↥L)) = Nat.card ↥L := Subgroup.index_bot
    rw [h1, e, hcardL, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at hcard
    have h9 := uni_eq_nine_of_card _ (by omega : 1 ≤ n) hcard
    rw [hf3, Nat.div_self (by norm_num), one_mul] at h9
    exact uni_choose_two_ne_nine n h9
  · have e : Nat.card (↥L ⧸ (⊤ : Subgroup ↥L)) = 1 := Subgroup.index_top
    rw [h1, e] at hcard
    norm_num at hcard

end Outer

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
