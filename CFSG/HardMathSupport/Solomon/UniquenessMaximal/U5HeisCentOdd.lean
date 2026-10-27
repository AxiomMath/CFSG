module

public import CFSG.RankThree.PartOne.S12.Sec1511U5ModA
public import CFSG.RankThree.PartOne.KC.UnitaryGoodLift
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsHeis
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartOne.S12.Sec1511U5Irr
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

section Aux

variable {K : Type} [Field K]

theorem scalar_five_injective {c d : Kˣ}
    (hcd : (GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) d) : c = d := by
  have := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 0 0) hcd
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem glAut_scalar_five (σ : K ≃+* K) (c : Kˣ) :
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ
      (GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, diagonal_map (map_zero σ), Units.coe_map]
  rfl

theorem central_conj {G : Type*} [Group G] {s t A B : G} (hs : ∀ g, Commute s g)
    (ht : ∀ g, Commute t g) : (s * A) * (t * B) * (s * A)⁻¹ = t * (A * B * A⁻¹) := by
  have e1 : (s * A) * (t * B) = s * (t * (A * B)) := by
    rw [mul_assoc, ← mul_assoc A t B, ← (ht A).eq, mul_assoc t A B]
  have e2 : (s * A)⁻¹ = A⁻¹ * s⁻¹ := mul_inv_rev s A
  rw [e1, e2]
  have e3 : s * (t * (A * B)) * (A⁻¹ * s⁻¹) = s * (t * (A * B * A⁻¹)) * s⁻¹ := by
    group
  rw [e3, (hs _).eq]
  group


theorem scalar_pow_eq_one {M A : GL (Fin 5) K} {l a₀ : Kˣ}
    (hA5 : A ^ 5 = GeneralLinearGroup.scalar (Fin 5) a₀)
    (hl : M * A * M⁻¹ = GeneralLinearGroup.scalar (Fin 5) l * A) : l ^ 5 = 1 := by
  have h1 : M * A ^ 5 * M⁻¹ = A ^ 5 := by
    rw [hA5, ← GeneralLinearGroup.scalar_commute a₀ M, mul_inv_cancel_right]
  have h2 : M * A ^ 5 * M⁻¹ = (M * A * M⁻¹) ^ 5 := (conj_pow).symm
  have h3 : (GeneralLinearGroup.scalar (Fin 5) l * A) ^ 5 =
      GeneralLinearGroup.scalar (Fin 5) (l ^ 5) * A ^ 5 := by
    rw [(Commute.mul_pow (GeneralLinearGroup.scalar_commute l A) 5), map_pow]
  rw [h2, hl, h3] at h1
  have h4 : GeneralLinearGroup.scalar (Fin 5) (l ^ 5) * A ^ 5 = 1 * A ^ 5 := by
    rw [h1, one_mul]
  have h5 := mul_right_cancel h4
  exact scalar_five_injective (K := K) (by rw [h5, map_one])

end Aux

section Main

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem conjHom_eq_of_eq_mul_scalar {M N : primeFormUnitary h (idGram K 5)} {s : Kˣ}
    (hMN : (M : GL (Fin 5) K) = (N : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) s) :
    primeFormConjHom h (idGram K 5) M = primeFormConjHom h (idGram K 5) N := by
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
  rw [primeFormConjHom_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  show (M : GL (Fin 5) K) * (g : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ =
    (N : GL (Fin 5) K) * (g : GL (Fin 5) K) * (N : GL (Fin 5) K)⁻¹
  rw [hMN, _root_.mul_inv_rev]
  calc (N : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) s * (g : GL (Fin 5) K) *
        ((GeneralLinearGroup.scalar (Fin 5) s)⁻¹ * (N : GL (Fin 5) K)⁻¹)
      = (N : GL (Fin 5) K) * (GeneralLinearGroup.scalar (Fin 5) s * (g : GL (Fin 5) K) *
        (GeneralLinearGroup.scalar (Fin 5) s)⁻¹) * (N : GL (Fin 5) K)⁻¹ := by group
    _ = (N : GL (Fin 5) K) * (g : GL (Fin 5) K) * (N : GL (Fin 5) K)⁻¹ := by
      rw [GeneralLinearGroup.scalar_commute s (g : GL (Fin 5) K)]
      group

open CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP in
theorem eq_one_of_commute_heis_primeFormP_five (hm : m % 4 = 2)
    {A B : primeFormUnitary h (idGram K 5)} {ω : Kˣ}
    (hAB : (A : GL (Fin 5) K) * B * (A : GL (Fin 5) K)⁻¹ * (B : GL (Fin 5) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) ω) (hω : ω ≠ 1)
    (hA5 : primeFormConjHom h (idGram K 5) A ^ 5 = 1)
    (hB5 : primeFormConjHom h (idGram K 5) B ^ 5 = 1)
    {x : MulAut (primeFormP h (idGram K 5))}
    (hxA : x * primeFormConjHom h (idGram K 5) A = primeFormConjHom h (idGram K 5) A * x)
    (hxB : x * primeFormConjHom h (idGram K 5) B = primeFormConjHom h (idGram K 5) B * x)
    {e : ℕ} (hx2 : x ^ 2 ^ e = 1) : x = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq : 3 < 2 ^ m := by
    have h2m : 2 ≤ m := by omega
    calc 3 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2m
  have hn : (3 : ℕ) ≤ 5 := by norm_num
  have hpow5 : ∀ C : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) C ^ 5 = 1 →
      ∃ a : Kˣ, (C : GL (Fin 5) K) ^ 5 = GeneralLinearGroup.scalar (Fin 5) a := by
    intro C hC
    have h1 : primeFormConjHom h (idGram K 5) (C ^ 5) = 1 := by rw [map_pow]; exact hC
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn hq _).1 h1
    exact ⟨c, by rw [← Subgroup.coe_pow]; exact hc⟩
  obtain ⟨a₀, ha₀⟩ := hpow5 A hA5
  obtain ⟨b₀, hb₀⟩ := hpow5 B hB5
  have hrel : (A : GL (Fin 5) K) * B * (A : GL (Fin 5) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) ω * B := HeisP.rel_AB hAB
  have hω5 : ω ^ 5 = 1 := by
    have h1 : (A : GL (Fin 5) K) * (B : GL (Fin 5) K) ^ 5 * (A : GL (Fin 5) K)⁻¹ =
        (B : GL (Fin 5) K) ^ 5 := by
      rw [hb₀, ← GeneralLinearGroup.scalar_commute b₀ (A : GL (Fin 5) K), mul_inv_cancel_right]
    have h2 : (A : GL (Fin 5) K) * (B : GL (Fin 5) K) ^ 5 * (A : GL (Fin 5) K)⁻¹ =
        ((A : GL (Fin 5) K) * B * (A : GL (Fin 5) K)⁻¹) ^ 5 := (conj_pow).symm
    have h3 : (GeneralLinearGroup.scalar (Fin 5) ω * (B : GL (Fin 5) K)) ^ 5 =
        GeneralLinearGroup.scalar (Fin 5) (ω ^ 5) * (B : GL (Fin 5) K) ^ 5 := by
      rw [(Commute.mul_pow (GeneralLinearGroup.scalar_commute ω (B : GL (Fin 5) K)) 5), map_pow]
    rw [h2, hrel, h3] at h1
    have h4 : GeneralLinearGroup.scalar (Fin 5) (ω ^ 5) * (B : GL (Fin 5) K) ^ 5 =
        1 * (B : GL (Fin 5) K) ^ 5 := by rw [h1, one_mul]
    exact scalar_five_injective (K := K) (by rw [mul_right_cancel h4, map_one])
  have hωprim : IsPrimitiveRoot ω 5 := by
    have : orderOf ω = 5 := orderOf_eq_prime hω5 hω
    rw [← this]
    exact IsPrimitiveRoot.orderOf ω
  obtain ⟨⟨M, σ⟩, rfl⟩ := surjective_primeFormPsi (h := h) (n := 5) hn hq x
  have key : ∀ C : primeFormUnitary h (idGram K 5),
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) ⟨M, σ⟩ *
          primeFormConjHom h (idGram K 5) C =
        primeFormConjHom h (idGram K 5) C *
          primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) ⟨M, σ⟩ →
      ∃ c : Kˣ, (M : GL (Fin 5) K) * glAut σ (C : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 5) c * C := by
    intro C hC
    have h1 : primeFormConjHom h (idGram K 5) (idUAction h 5 ⟨M, σ⟩ C * C⁻¹) = 1 := by
      rw [map_mul, map_inv, ← primeFormPsi_conj_primeFormConjHom, hC]
      group
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn hq _).1 h1
    refine ⟨c, ?_⟩
    have h2 : ((idUAction h 5 ⟨M, σ⟩ C : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
        (M : GL (Fin 5) K) * glAut σ (C : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ := by
      rw [idUAction_mk]
      rfl
    have h3 : ((idUAction h 5 ⟨M, σ⟩ C * C⁻¹ : primeFormUnitary h (idGram K 5)) :
        GL (Fin 5) K) * (C : GL (Fin 5) K) =
        ((idUAction h 5 ⟨M, σ⟩ C : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) := by
      simp
    rw [← h2, ← h3, hc]
  obtain ⟨l, hl⟩ := key A hxA
  obtain ⟨u, hu⟩ := key B hxB
  have hσω : Units.map (σ : K →* K) ω = ω := by
    have hrel' : glAut σ (A : GL (Fin 5) K) * glAut σ (B : GL (Fin 5) K) *
        (glAut σ (A : GL (Fin 5) K))⁻¹ =
        GeneralLinearGroup.scalar (Fin 5) (Units.map (σ : K →* K) ω) *
          glAut σ (B : GL (Fin 5) K) := by
      have := congrArg (glAut σ) hrel
      simpa only [map_mul, map_inv, glAut_scalar_five] using this
    have e1 : (M : GL (Fin 5) K) * (glAut σ (A : GL (Fin 5) K) * glAut σ (B : GL (Fin 5) K) *
        (glAut σ (A : GL (Fin 5) K))⁻¹) * (M : GL (Fin 5) K)⁻¹ =
        (GeneralLinearGroup.scalar (Fin 5) l * (A : GL (Fin 5) K)) *
          (GeneralLinearGroup.scalar (Fin 5) u * (B : GL (Fin 5) K)) *
          (GeneralLinearGroup.scalar (Fin 5) l * (A : GL (Fin 5) K))⁻¹ := by
      rw [← hl, ← hu]
      group
    have e : GeneralLinearGroup.scalar (Fin 5) (Units.map (σ : K →* K) ω * u) *
        (B : GL (Fin 5) K) =
        GeneralLinearGroup.scalar (Fin 5) (u * ω) * (B : GL (Fin 5) K) := by
      calc GeneralLinearGroup.scalar (Fin 5) (Units.map (σ : K →* K) ω * u) * (B : GL (Fin 5) K)
          = GeneralLinearGroup.scalar (Fin 5) (Units.map (σ : K →* K) ω) *
            (GeneralLinearGroup.scalar (Fin 5) u * (B : GL (Fin 5) K)) := by
            rw [map_mul, mul_assoc]
        _ = (M : GL (Fin 5) K) * (GeneralLinearGroup.scalar (Fin 5) (Units.map (σ : K →* K) ω) *
            glAut σ (B : GL (Fin 5) K)) * (M : GL (Fin 5) K)⁻¹ := by
            rw [conj_sc_mul, hu]
        _ = (M : GL (Fin 5) K) * (glAut σ (A : GL (Fin 5) K) * glAut σ (B : GL (Fin 5) K) *
            (glAut σ (A : GL (Fin 5) K))⁻¹) * (M : GL (Fin 5) K)⁻¹ := by rw [hrel']
        _ = (GeneralLinearGroup.scalar (Fin 5) l * (A : GL (Fin 5) K)) *
          (GeneralLinearGroup.scalar (Fin 5) u * (B : GL (Fin 5) K)) *
          (GeneralLinearGroup.scalar (Fin 5) l * (A : GL (Fin 5) K))⁻¹ := e1
        _ = GeneralLinearGroup.scalar (Fin 5) u *
            ((A : GL (Fin 5) K) * B * (A : GL (Fin 5) K)⁻¹) :=
            central_conj (fun g => GeneralLinearGroup.scalar_commute l g)
              (fun g => GeneralLinearGroup.scalar_commute u g)
        _ = GeneralLinearGroup.scalar (Fin 5) u *
            (GeneralLinearGroup.scalar (Fin 5) ω * (B : GL (Fin 5) K)) := by rw [hrel]
        _ = GeneralLinearGroup.scalar (Fin 5) (u * ω) * (B : GL (Fin 5) K) := by
            rw [map_mul, mul_assoc]
    have e' := scalar_five_injective (K := K) (mul_right_cancel e)
    rw [mul_comm u ω] at e'
    exact mul_right_cancel e'
  have hσζ : σ (ω : K) = ω := by simpa using congrArg Units.val hσω
  have hσ2 : σ ^ 2 ^ e = 1 := by
    have h1 : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5))
        ((⟨M, σ⟩ : CFSG.RankThree.PartOne.Sec1511.U5M.Gam h) ^ 2 ^ e) = 1 := by
      rw [map_pow]; exact hx2
    obtain ⟨hr, -⟩ := (primeFormPsi_eq_one_iff' hn hq _).1 h1
    have := map_pow (SemidirectProduct.rightHom :
      CFSG.RankThree.PartOne.Sec1511.U5M.Gam h →* (K ≃+* K)) ⟨M, σ⟩ (2 ^ e)
    simp only [SemidirectProduct.rightHom_eq_right] at this
    rw [← this]
    exact hr
  have hf5 : 5 ∣ 2 ^ m + 1 := by
    obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 2 := ⟨m / 4, by omega⟩
    subst hk
    have : 2 ^ (4 * k + 2) % 5 = 4 := by
      rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    omega
  have hσ1 : σ = 1 := by
    by_contra hne
    have hord : orderOf σ ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hσ2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.1 (by simpa using hk))
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hφ2 : σ ^ 2 ^ k' * σ ^ 2 ^ k' = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← hk]
      exact pow_orderOf_eq_one σ
    have hφ1 : σ ^ 2 ^ k' ≠ 1 :=
      pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
        (by rw [hk]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hfix : ∀ j : ℕ, (σ ^ j) (ω : K) = ω := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ, RingAut.mul_apply, hσζ, ih]
    exact CFSG.RankThree.PartOne.Sec1511.U5M.invol_moves_zeta h hf5
      (IsPrimitiveRoot.coe_units_iff.2 hωprim) hφ2 hφ1 (hfix _)
  subst hσ1
  have hl' : (M : GL (Fin 5) K) * (A : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) l * (A : GL (Fin 5) K) := by
    have : glAut (1 : K ≃+* K) (A : GL (Fin 5) K) = A := by rw [map_one]; rfl
    rwa [this] at hl
  have hu' : (M : GL (Fin 5) K) * (B : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) u * (B : GL (Fin 5) K) := by
    have : glAut (1 : K ≃+* K) (B : GL (Fin 5) K) = B := by rw [map_one]; rfl
    rwa [this] at hu
  have hl5 : l ^ 5 = 1 := scalar_pow_eq_one ha₀ hl'
  have hu5 : u ^ 5 = 1 := scalar_pow_eq_one hb₀ hu'
  have hpK : ((5 : ℕ) : K) ≠ 0 := by
    have := h.charP
    intro h5
    have := (CharP.cast_eq_zero_iff K 2 5).1 h5
    norm_num at this
  obtain ⟨i, j, m', hM⟩ := heisenberg_normalizer_p hωprim hAB hpK hl5 hu5 hl' hu'
  have hcomm : primeFormConjHom h (idGram K 5) A * primeFormConjHom h (idGram K 5) B =
      primeFormConjHom h (idGram K 5) B * primeFormConjHom h (idGram K 5) A := by
    rw [← map_mul, ← map_mul]
    refine conjHom_eq_of_eq_mul_scalar h (s := ω) ?_
    calc (↑(A * B) : GL (Fin 5) K) = (A : GL (Fin 5) K) * B := rfl
      _ = ((A : GL (Fin 5) K) * B * (A : GL (Fin 5) K)⁻¹ * (B : GL (Fin 5) K)⁻¹) *
          ((B : GL (Fin 5) K) * A) := by group
      _ = GeneralLinearGroup.scalar (Fin 5) ω * ((B : GL (Fin 5) K) * A) := by rw [hAB]
      _ = ((B : GL (Fin 5) K) * A) * GeneralLinearGroup.scalar (Fin 5) ω :=
          GeneralLinearGroup.scalar_commute ω _
  have hxM : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) ⟨M, 1⟩ =
      primeFormConjHom h (idGram K 5) A ^ i * primeFormConjHom h (idGram K 5) B ^ j := by
    rw [primeFormPsi_apply, map_one, mul_one]
    have : primeFormConjHom h (idGram K 5) M = primeFormConjHom h (idGram K 5) (A ^ i * B ^ j) :=
      conjHom_eq_of_eq_mul_scalar h (s := m') (by
        rw [hM]
        simp only [Subgroup.coe_mul, Subgroup.coe_pow])
    rw [this, map_mul, map_pow, map_pow]
  rw [hxM] at hx2 ⊢
  have hx5 : (primeFormConjHom h (idGram K 5) A ^ i * primeFormConjHom h (idGram K 5) B ^ j) ^ 5 =
      1 := by
    rw [(Commute.mul_pow ((show Commute (primeFormConjHom h (idGram K 5) A) (primeFormConjHom h (idGram K 5) B) from hcomm).pow_pow i j) 5), pow_right_comm _ i 5, pow_right_comm _ j 5,
      hA5, hB5, one_pow, one_pow, one_mul]
  have h5 := orderOf_dvd_of_pow_eq_one hx5
  have h2e := orderOf_dvd_of_pow_eq_one hx2
  have hdvd := Nat.dvd_gcd h5 h2e
  have hc : Nat.Coprime 5 (2 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
  rw [hc.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)

end Main

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
