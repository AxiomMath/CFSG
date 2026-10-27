module

public import CFSG.ClassicalInvolution.AschTight.S1916Inv
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.GorensteinWalter

theorem eq_three_two {p f : ℕ} (hp : p.Prime) (hq : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    norm_num at hq
  exact Nat.Prime.pow_inj' hp Nat.prime_three hf two_ne_zero (hq.trans (by norm_num))

theorem eq_of_ne_one_of_card_le_two {M : Type*} [Group M] [Finite M] (h : Nat.card M ≤ 2)
    {x y : M} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  by_contra hxy
  have hinj : Function.Injective (![1, x, y] : Fin 3 → M) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem ringEquiv_eq_of_ne_one {p : ℕ} [Fact p.Prime]
    {σ τ : GaloisField p 2 ≃+* GaloisField p 2} (hσ : σ ≠ 1) (hτ : τ ≠ 1) : σ = τ := by
  let toAlg : (GaloisField p 2 ≃+* GaloisField p 2) →
      (GaloisField p 2 ≃ₐ[ZMod p] GaloisField p 2) :=
    fun σ => AlgEquiv.ofRingEquiv (f := σ) fun x => by
      simp only [Algebra.algebraMap_eq_smul_one]
      rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul, map_nsmul, map_one]
  have hinj : Function.Injective toAlg := fun σ τ h => by
    ext x
    exact congrArg (fun α : GaloisField p 2 ≃ₐ[ZMod p] GaloisField p 2 => α x) h
  have hcard : Nat.card (GaloisField p 2 ≃ₐ[ZMod p] GaloisField p 2) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank p two_ne_zero]
  have : Finite (GaloisField p 2 ≃ₐ[ZMod p] GaloisField p 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Finite (GaloisField p 2 ≃+* GaloisField p 2) := Finite.of_injective toAlg hinj
  have hle : Nat.card (GaloisField p 2 ≃+* GaloisField p 2) ≤ 2 :=
    le_of_le_of_eq (Nat.card_le_card_of_injective toAlg hinj) hcard
  exact eq_of_ne_one_of_card_le_two hle hσ hτ

theorem eq_frobenius_of_ne_one {σ : GaloisField 3 2 ≃+* GaloisField 3 2} (hσ : σ ≠ 1) :
    ∀ x, σ x = x ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ := frobeniusEquiv (GaloisField 3 2) 3 with hφ
  have hφ1 : φ ≠ 1 := by
    intro h
    have hroot : ∀ x : GaloisField 3 2, x ^ 3 = x := fun x => by
      have := congrArg (fun τ : GaloisField 3 2 ≃+* GaloisField 3 2 => τ x) h
      simp only [hφ, frobeniusEquiv_apply] at this
      rwa [frobenius_def] at this
    let _ := Fintype.ofFinite (GaloisField 3 2)
    have hcard : Fintype.card (GaloisField 3 2) = 9 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 two_ne_zero]
      norm_num
    classical
    have hdeg : (Polynomial.X ^ 3 - Polynomial.X : Polynomial (GaloisField 3 2)).natDegree = 3 := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
      simp
    have hne : (Polynomial.X ^ 3 - Polynomial.X : Polynomial (GaloisField 3 2)) ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hdeg
      omega
    have hsub : (Finset.univ : Finset (GaloisField 3 2)) ⊆
        (Polynomial.X ^ 3 - Polynomial.X : Polynomial (GaloisField 3 2)).roots.toFinset := by
      intro x _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      simp [hroot x]
    have h1 := Finset.card_le_card hsub
    have h2 := Multiset.toFinset_card_le
      (Polynomial.X ^ 3 - Polynomial.X : Polynomial (GaloisField 3 2)).roots
    have h3 := Polynomial.card_roots'
      (Polynomial.X ^ 3 - Polynomial.X : Polynomial (GaloisField 3 2))
    rw [Finset.card_univ, hcard] at h1
    omega
  have := ringEquiv_eq_of_ne_one hσ hφ1
  intro x
  rw [this, hφ, frobeniusEquiv_apply, frobenius_def]

theorem ringEquiv_eq_of_ne_one_of_eq_nine {p f : ℕ} [Fact p.Prime] (hq : p ^ f = 9)
    {σ τ : GaloisField p f ≃+* GaloisField p f} (hσ : σ ≠ 1) (hτ : τ ≠ 1) : σ = τ := by
  obtain ⟨-, rfl⟩ := eq_three_two Fact.out hq
  exact ringEquiv_eq_of_ne_one hσ hτ

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem inv_mul_mem_of_not_mem [IsSimpleGroup G] (hd : Sec19Data p f K z S W) (hq : p ^ f = 9)
    {x y : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G))
    (hy : y ∈ Subgroup.centralizer ({z} : Set G))
    (hxH : x ∉ sec19X K z ⊔ centralizerModOdd ⊤ K)
    (hyH : y ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    x⁻¹ * y ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD hd.tight
  have hNC := S1916.sd_normalizer_eq hd
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hNC.ge hx
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hNC.ge hy
  let nx : Subgroup.normalizer (K : Set G) := ⟨x, hxN⟩
  let ny : Subgroup.normalizer (K : Set G) := ⟨y, hyN⟩
  have hfx : (normalizerToPGammaL2Mod e hFcard hF h3 nx).right ≠ 1 := fun h =>
    hxH ((S1916.psi_mem_iff hd e hFcard hF h3 nx).mp (mem_range_inl_of_right_eq_one h))
  have hfy : (normalizerToPGammaL2Mod e hFcard hF h3 ny).right ≠ 1 := fun h =>
    hyH ((S1916.psi_mem_iff hd e hFcard hF h3 ny).mp (mem_range_inl_of_right_eq_one h))
  have heq := ringEquiv_eq_of_ne_one_of_eq_nine hq hfx hfy
  have h1 : (normalizerToPGammaL2Mod e hFcard hF h3 (nx⁻¹ * ny)).right = 1 := by
    rw [map_mul, map_inv, SemidirectProduct.mul_right, SemidirectProduct.inv_right, heq,
      inv_mul_cancel]
  exact (S1916.psi_mem_iff hd e hFcard hF h3 (nx⁻¹ * ny)).mp (mem_range_inl_of_right_eq_one h1)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19N
