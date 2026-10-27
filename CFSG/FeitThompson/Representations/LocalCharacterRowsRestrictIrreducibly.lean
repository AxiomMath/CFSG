module

public import CFSG.FeitThompson.Representations.LinearQuotientCharactersLocalArray
import CFSG.FeitThompson.Representations.AbelianQuotientExtensionInducedFamily
import CFSG.FeitThompson.Representations.DadeInverseConstantOffExceptionalFamily
import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
import CFSG.FeitThompson.Representations.InducedRectangleDifferencesNormThree
import CFSG.FeitThompson.Representations.LinearCharactersSeparateElements
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

theorem mem_Irr_resClassFun_of_cfInner_self_eq_one (K : Subgroup L) [Fintype ↥K] {χ : L → ℂ}
    (hχ : χ ∈ Irr L) (h1 : cfInner (resClassFun K χ) (resClassFun K χ) = 1) :
    resClassFun K χ ∈ Irr ↥K := by
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
  rw [resClassFun_fdRepCharacter] at h1 ⊢
  exact character_mem_Irr_of_isIrreducible _ ((isIrreducible_iff_cfInner_self_eq_one _).2 h1)

theorem toFinset_Irr_eq_irrFinset (G : Type*) [Group G] [Finite G] [Fintype ↑(Irr G)] :
    (Irr G).toFinset = irrFinset G := by
  ext χ
  rw [Set.mem_toFinset, mem_irrFinset]

namespace IsPrimeCyclicTIHyp

noncomputable def primeTIres (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (j : Irr ↥W₂) : ↥K → ℂ :=
  resClassFun K (h.primeTIirr σ (principalIrr ↥W₁) j)

theorem primeTIres_def (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    h.primeTIres σ j = resClassFun K (h.primeTIirr σ (principalIrr ↥W₁) j) := (rfl)

theorem primeTIres_apply (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) (x : ↥K) :
    h.primeTIres σ j x = h.primeTIirr σ (principalIrr ↥W₁) j (x : L) := by
  rw [primeTIres_def, resClassFun_apply]

theorem primeTIres_one (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    h.primeTIres σ j 1 = h.primeTIirr σ (principalIrr ↥W₁) j 1 := by
  rw [primeTIres_apply]
  norm_num

noncomputable def primeTIrow [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (j : Irr ↥W₂) : L → ℂ :=
  ∑ i : ↑(Irr ↥W₁), h.primeTIirr σ i j

theorem primeTIrow_def [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    h.primeTIrow σ j = ∑ i : ↑(Irr ↥W₁), h.primeTIirr σ i j := (rfl)

theorem primeTIrow_one [Finite L] [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (j : Irr ↥W₂) : h.primeTIrow σ j 1 = (Nat.card ↥W₁ : ℂ) * h.primeTIres σ j 1 := by
  have hcomm := h.isCyclicTIPair.isMulCommutative_left
  calc h.primeTIrow σ j 1
      = ∑ _i : ↑(Irr ↥W₁), h.primeTIirr σ (principalIrr ↥W₁) j 1 := by
        rw [primeTIrow_def, Finset.sum_apply]
        exact Finset.sum_congr rfl fun i _ => h.primeTIirr_one i j
    _ = (Nat.card ↥W₁ : ℂ) * h.primeTIres σ j 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
          card_Irr_eq_card_of_isMulCommutative, h.primeTIres_one j]

theorem inflateLeft_apply_of_mem (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) {k : L}
    (hk : k ∈ K) : h.inflateLeft i k = 1 := by
  have hcomm := h.isCyclicTIPair.isMulCommutative_left
  have hval := h.inflateLeft_apply_mul i hk W₁.one_mem
  rw [mul_one] at hval
  rw [hval, show (⟨(1 : L), W₁.one_mem⟩ : ↥W₁) = 1 from rfl, apply_one_eq_one_of_mem_Irr i.2]

theorem resClassFun_primeTIirr (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    resClassFun K (h.primeTIirr σ i j) = h.primeTIres σ j := by
  funext x
  rw [primeTIres_def, resClassFun_apply, resClassFun_apply, h.primeTIirr_eq_mul i j,
    Pi.mul_apply, h.inflateLeft_apply_of_mem i x.2, one_mul]

theorem sum_inflateLeft [Fintype L] [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    ∑ i : ↑(Irr ↥W₁), h.inflateLeft i = indClassFun K (1 : ↥K → ℂ) := by
  classical
  have hnormal := h.normal
  have hcomm := h.isCyclicTIPair.isMulCommutative_left
  let _ : CommGroup ↥W₁ := IsMulCommutative.instCommGroup
  have hindex : K.index = Nat.card ↥W₁ := h.isComplement'_left.index_eq_card
  funext g
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp g
  have hleft : (∑ i : ↑(Irr ↥W₁), h.inflateLeft i) (k * w)
      = if (⟨w, hw⟩ : ↥W₁) = 1 then (Nat.card ↥W₁ : ℂ) else 0 := by
    rw [Finset.sum_apply]
    calc ∑ i : ↑(Irr ↥W₁), h.inflateLeft i (k * w)
        = ∑ i : ↑(Irr ↥W₁), (i : ↥W₁ → ℂ) ⟨w, hw⟩ :=
          Finset.sum_congr rfl fun i _ => h.inflateLeft_apply_mul i hk hw
      _ = ∑ χ ∈ (Irr ↥W₁).toFinset, χ (⟨w, hw⟩ : ↥W₁) :=
          Finset.sum_set_coe (f := fun χ : ↥W₁ → ℂ => χ (⟨w, hw⟩ : ↥W₁)) (Irr ↥W₁)
      _ = if (⟨w, hw⟩ : ↥W₁) = 1 then (Nat.card ↥W₁ : ℂ) else 0 := by
          rw [toFinset_Irr_eq_irrFinset, sum_Irr_apply_eq_ite]
  rw [hleft]
  by_cases hw1 : (⟨w, hw⟩ : ↥W₁) = 1
  · have hw' : w = 1 := by simpa using congrArg Subtype.val hw1
    rw [if_pos hw1, hw', mul_one, NormalInducedFamily.indClassFun_one_apply_of_mem K hk, hindex]
  · have hwK : w ∉ K := by
      intro hcon
      have hmem : w ∈ K ⊓ W₁ := Subgroup.mem_inf.2 ⟨hcon, hw⟩
      rw [h.inf_eq_bot] at hmem
      exact hw1 (Subtype.ext (Subgroup.mem_bot.1 hmem))
    have hnot : k * w ∉ K := fun hcon => hwK (by simpa using K.mul_mem (K.inv_mem hk) hcon)
    rw [if_neg hw1, indClassFun_eq_zero_of_notMem K 1 hnot]

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem indClassFun_primeTIres [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    indClassFun K (h.primeTIres σ j) = h.primeTIrow σ j := by
  have hnormal := h.normal
  have hcf : h.primeTIirr σ (principalIrr ↥W₁) j ∈ classFun L :=
    Irr_subset_classFun (h.primeTIirr_principal_left_mem_Irr hσ j)
  have hprod := AbelianQuotientExtension.indClassFun_mul_resClassFun (I := L) (K := K)
    (1 : ↥K → ℂ) hcf
  rw [one_mul] at hprod
  rw [primeTIres_def, hprod, ← sum_inflateLeft h, primeTIrow_def, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (h.primeTIirr_eq_mul i j).symm

theorem cfInner_primeTIrow_primeTIirr [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    cfInner (h.primeTIrow σ j) (h.primeTIirr σ (principalIrr ↥W₁) j) = 1 := by
  classical
  rw [primeTIrow_def, cfInner_sum_left, Finset.sum_congr rfl
    fun i (_ : i ∈ (Finset.univ : Finset ↑(Irr ↥W₁))) =>
      h.cfInner_primeTIirr hσ i (principalIrr ↥W₁) j j]
  simp

theorem cfInner_primeTIrow_primeTIirr_of_ne [Fintype ↑(Irr ↥W₁)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {j k : Irr ↥W₂} (hjk : j ≠ k) :
    cfInner (h.primeTIrow σ j) (h.primeTIirr σ (principalIrr ↥W₁) k) = 0 := by
  classical
  rw [primeTIrow_def, cfInner_sum_left, Finset.sum_congr rfl
    fun i (_ : i ∈ (Finset.univ : Finset ↑(Irr ↥W₁))) =>
      h.cfInner_primeTIirr hσ i (principalIrr ↥W₁) j k]
  simp [hjk]

theorem cfInner_self_primeTIrow [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    cfInner (h.primeTIrow σ j) (h.primeTIrow σ j) = (Nat.card ↥W₁ : ℂ) := by
  classical
  have hcomm := h.isCyclicTIPair.isMulCommutative_left
  have hterm : ∀ i : ↑(Irr ↥W₁), cfInner (h.primeTIirr σ i j) (h.primeTIrow σ j) = 1 := by
    intro i
    rw [primeTIrow_def, cfInner_sum_right, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun k _ hki => by rw [h.cfInner_primeTIirr hσ, if_neg (by simp [Ne.symm hki])]),
      h.cfInner_primeTIirr hσ, if_pos ⟨rfl, rfl⟩]
  calc cfInner (h.primeTIrow σ j) (h.primeTIrow σ j)
      = ∑ _i : ↑(Irr ↥W₁), (1 : ℂ) := by
        rw [primeTIrow_def, cfInner_sum_left]
        exact Finset.sum_congr rfl fun i _ => hterm i
    _ = (Nat.card ↥W₁ : ℂ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
          card_Irr_eq_card_of_isMulCommutative]

theorem cfInner_self_primeTIres [Fintype ↥K] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    cfInner (h.primeTIres σ j) (h.primeTIres σ j) = 1 := by
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have hcf : h.primeTIirr σ (principalIrr ↥W₁) j ∈ classFun L :=
    Irr_subset_classFun (h.primeTIirr_principal_left_mem_Irr hσ j)
  have hrec := cfInner_indClassFun K (h.primeTIres σ j) hcf
  rw [h.indClassFun_primeTIres hσ, h.cfInner_primeTIrow_primeTIirr hσ] at hrec
  rw [primeTIres_def]
  exact hrec.symm

theorem primeTIres_mem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) : h.primeTIres σ j ∈ Irr ↥K := by
  have : Fintype ↥K := Fintype.ofFinite _
  exact mem_Irr_resClassFun_of_cfInner_self_eq_one K
    (h.primeTIirr_principal_left_mem_Irr hσ j) (h.cfInner_self_primeTIres hσ j)

theorem primeTIres_injective (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j k : Irr ↥W₂}
    (hjk : h.primeTIres σ j = h.primeTIres σ k) : j = k := by
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  by_contra hne
  have hrow : h.primeTIrow σ j = h.primeTIrow σ k := by
    rw [← h.indClassFun_primeTIres hσ, ← h.indClassFun_primeTIres hσ, hjk]
  have h1 := h.cfInner_primeTIrow_primeTIirr hσ k
  rw [← hrow, h.cfInner_primeTIrow_primeTIirr_of_ne hσ hne] at h1
  exact zero_ne_one h1

theorem primeTIres_principal (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) : h.primeTIres σ (principalIrr ↥W₂) = 1 := by
  rw [primeTIres_def, h.primeTIirr_principal hσ, resClassFun_one]

end Fintype

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
