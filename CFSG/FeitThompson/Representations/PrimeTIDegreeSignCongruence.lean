module

public import CFSG.FeitThompson.Representations.LinearQuotientCharactersLocalArray
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
import CFSG.FeitThompson.Representations.FrobeniusSchurIndicatorReality
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem eq_of_intModEq_of_sign {n : ℤ} (hn : 3 ≤ n) {e e' : ℤ} (he : e = 1 ∨ e = -1)
    (he' : e' = 1 ∨ e' = -1) (hmod : e ≡ e' [ZMOD n]) : e = e' := by
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · rfl
  · exfalso
    have hd : n ∣ (2 : ℤ) := dvd_neg.mp (by simpa using hmod.dvd)
    have := Int.le_of_dvd (by norm_num) hd
    omega
  · exfalso
    have hd : n ∣ (2 : ℤ) := by simpa using hmod.dvd
    have := Int.le_of_dvd (by norm_num) hd
    omega
  · rfl

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

namespace IsPrimeCyclicTIHyp

theorem three_le_natCard_left (h : IsPrimeCyclicTIHyp K W₁ W₂) : 3 ≤ Nat.card ↥W₁ := by
  have hodd := Nat.odd_iff.1 (Nat.Odd.of_mul_left h.odd_natCard)
  have h1 : Nat.card ↥W₁ ≠ 1 := fun hc => h.left_ne_bot (Subgroup.card_eq_one.1 hc)
  omega

open scoped Classical in
noncomputable def primeTISignInt (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (j : Irr ↥W₂) : ℤ :=
  if h.primeTISign σ j = 1 then 1 else -1

theorem primeTISignInt_eq_one_or_eq_neg_one (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    h.primeTISignInt σ j = 1 ∨ h.primeTISignInt σ j = -1 := by
  classical
  rw [primeTISignInt]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp]
theorem intCast_primeTISignInt (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    ((h.primeTISignInt σ j : ℤ) : ℂ) = h.primeTISign σ j := by
  classical
  rw [primeTISignInt]
  split
  · rename_i hc
    rw [hc]
    norm_num
  · rename_i hc
    rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with h1 | h1
    · exact absurd h1 hc
    · rw [h1]
      norm_num

theorem primeTISign_eq_of_primeTISignInt_eq (h : IsPrimeCyclicTIHyp K W₁ W₂) {j k : Irr ↥W₂}
    (hjk : h.primeTISignInt σ j = h.primeTISignInt σ k) :
    h.primeTISign σ j = h.primeTISign σ k := by
  rw [← h.intCast_primeTISignInt (σ := σ) j, ← h.intCast_primeTISignInt (σ := σ) k, hjk]

theorem primeTISign_eq_one_of_primeTISignInt_eq_one (h : IsPrimeCyclicTIHyp K W₁ W₂)
    {j : Irr ↥W₂} (hj : h.primeTISignInt σ j = 1) : h.primeTISign σ j = 1 := by
  rw [← h.intCast_primeTISignInt (σ := σ) j, hj]
  norm_num

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem primeTIirr_apply_of_mem_primeTIset (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂)
    {v : ↥(W₁ ⊔ W₂)} (hv : (v : L) ∈ primeTIset W₁ W₂) :
    h.primeTIirr σ i j (v : L)
      = h.primeTISign σ j * h.isCyclicTIPair.prodChar (i : ↥W₁ → ℂ) (j : ↥W₂ → ℂ) v := by
  have key := h.apply_eq_of_mem_primeTIset hσ (h.isCyclicTIPair.basisProdIrr (i, j)) hv
  rw [h.coe_apply_basisProdIrr_eq_smul_primeTIirr hσ i j,
    IsCyclicTIPair.coe_basisProdIrr_apply] at key
  have key2 : h.primeTISign σ j * h.primeTIirr σ i j (v : L)
      = h.isCyclicTIPair.prodChar (i : ↥W₁ → ℂ) (j : ↥W₂ → ℂ) v := by
    simpa using key
  calc h.primeTIirr σ i j (v : L)
      = h.primeTISign σ j * h.primeTISign σ j * h.primeTIirr σ i j (v : L) := by
        rw [h.primeTISign_mul_self, one_mul]
    _ = h.primeTISign σ j * (h.primeTISign σ j * h.primeTIirr σ i j (v : L)) := by ring
    _ = _ := by rw [key2]

theorem primeTIirr_apply_coe_left (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) {x : ↥W₁}
    (hx : x ≠ 1) : h.primeTIirr σ i j (x : L) = h.primeTISign σ j * (i : ↥W₁ → ℂ) x := by
  have hW := h.isCyclicTIPair
  have := hW.isMulCommutative_right
  have hxW₂ : (x : L) ∉ W₂ := by
    intro hc
    have hmem : (x : L) ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.2 ⟨x.2, hc⟩
    rw [h.inf_left_right_eq_bot] at hmem
    exact hx (Subtype.ext (Subgroup.mem_bot.1 hmem))
  have hv : ((⟨(x : L), Subgroup.mem_sup_left x.2⟩ : ↥(W₁ ⊔ W₂)) : L) ∈ primeTIset W₁ W₂ :=
    mem_primeTIset.2 ⟨Subgroup.mem_sup_left x.2, hxW₂⟩
  rw [h.primeTIirr_apply_of_mem_primeTIset hσ i j hv, hW.prodChar_apply_coe_left,
    apply_one_eq_one_of_mem_Irr j.2, mul_one]

theorem exists_primeTIirr_one_modEq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    ∃ d : ℕ, 0 < d ∧ h.primeTIirr σ i j 1 = (d : ℂ) ∧
      (d : ℤ) ≡ h.primeTISignInt σ j [ZMOD (Nat.card ↥W₁ : ℤ)] := by
  classical
  have hW := h.isCyclicTIPair
  have hcomm1 := hW.isMulCommutative_left
  have hfin1 : Finite ↥W₁ := hW.finite_left
  have hF1 : Fintype ↥W₁ := Fintype.ofFinite _
  obtain ⟨d, hdpos, hd⟩ :=
    NormalInducedFamily.exists_apply_one_eq_of_mem_Irr (h.primeTIirr_mem_Irr hσ i j)
  refine ⟨d, hdpos, hd, ?_⟩
  set f : ↥W₁ → ℂ :=
    resClassFun W₁ (h.primeTIirr σ i j) - h.primeTISign σ j • (i : ↥W₁ → ℂ) with hf
  have hres : resClassFun W₁ (h.primeTIirr σ i j) ∈ Submodule.span ℤ (Irr ↥W₁) := by
    have hc := comp_mem_span_Irr (X := ↥W₁) W₁.subtype
      (Submodule.subset_span (h.primeTIirr_mem_Irr hσ i j))
    have he : h.primeTIirr σ i j ∘ W₁.subtype = resClassFun W₁ (h.primeTIirr σ i j) := by
      funext x
      simp [resClassFun_apply]
    rwa [he] at hc
  have hfspan : f ∈ Submodule.span ℤ (Irr ↥W₁) := by
    rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hδ | hδ
    · rw [hf, hδ, one_smul]
      exact sub_mem hres (Submodule.subset_span i.2)
    · rw [hf, hδ]
      have hneg : (-1 : ℂ) • (i : ↥W₁ → ℂ) = -(i : ↥W₁ → ℂ) := by module
      rw [hneg, sub_neg_eq_add]
      exact add_mem hres (Submodule.subset_span i.2)
  obtain ⟨n, hn⟩ := exists_int_cfInner_of_mem_span_Irr hfspan
    (Submodule.subset_span (one_mem_Irr (G := ↥W₁)))
  rw [cfInner_one_right] at hn
  have hsum : ∑ x : ↥W₁, f x = f 1 := by
    refine Fintype.sum_eq_single 1 fun x hx => ?_
    rw [hf]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, resClassFun_apply]
    rw [h.primeTIirr_apply_coe_left hσ i j hx, sub_self]
  rw [hsum] at hn
  have hf1 : f 1 = (d : ℂ) - (h.primeTISignInt σ j : ℤ) := by
    rw [hf]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, resClassFun_apply]
    rw [show ((1 : ↥W₁) : L) = (1 : L) from rfl, hd, apply_one_eq_one_of_mem_Irr i.2, mul_one,
      h.intCast_primeTISignInt]
  have hcard : (Nat.card ↥W₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hmul := congrArg (fun z : ℂ => (Nat.card ↥W₁ : ℂ) * z) hn
  simp only [← mul_assoc, mul_inv_cancel₀ hcard, one_mul] at hmul
  have hkey : ((d : ℤ) : ℂ) - ((h.primeTISignInt σ j : ℤ) : ℂ)
      = ((Nat.card ↥W₁ : ℤ) : ℂ) * ((n : ℤ) : ℂ) := by
    push_cast
    rw [← hf1, hmul]
  have hint : (d : ℤ) - h.primeTISignInt σ j = (Nat.card ↥W₁ : ℤ) * n := by
    exact_mod_cast hkey
  exact Int.modEq_iff_dvd.2 ⟨-n, by linarith⟩

theorem primeTIirr_one_modEq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) {m : ℤ}
    (hm : h.primeTIirr σ i j 1 = (m : ℂ)) :
    m ≡ h.primeTISignInt σ j [ZMOD (Nat.card ↥W₁ : ℤ)] := by
  obtain ⟨d, -, hd, hmod⟩ := h.exists_primeTIirr_one_modEq hσ i j
  have hmd : (m : ℂ) = ((d : ℤ) : ℂ) := by rw [← hm, hd]; push_cast; ring
  have : m = (d : ℤ) := by exact_mod_cast hmd
  rwa [this]

theorem primeTISign_eq_of_primeTIirr_one_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j k : Irr ↥W₂)
    (hone : h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1) :
    h.primeTISign σ j = h.primeTISign σ k := by
  obtain ⟨d, -, hd, hj⟩ := h.exists_primeTIirr_one_modEq hσ i j
  have hk := h.primeTIirr_one_modEq hσ i k (m := (d : ℤ)) (by rw [← hone, hd]; push_cast; ring)
  refine h.primeTISign_eq_of_primeTISignInt_eq ?_
  refine eq_of_intModEq_of_sign (n := (Nat.card ↥W₁ : ℤ)) (by exact_mod_cast h.three_le_natCard_left)
    (h.primeTISignInt_eq_one_or_eq_neg_one (σ := σ) j)
    (h.primeTISignInt_eq_one_or_eq_neg_one (σ := σ) k) (hj.symm.trans hk)

theorem primeTISign_eq_one_of_intCast_modEq_one (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) {m : ℤ}
    (hm : h.primeTIirr σ i j 1 = (m : ℂ)) (hmod : m ≡ 1 [ZMOD (Nat.card ↥W₁ : ℤ)]) :
    h.primeTISign σ j = 1 := by
  refine h.primeTISign_eq_one_of_primeTISignInt_eq_one ?_
  refine eq_of_intModEq_of_sign (n := (Nat.card ↥W₁ : ℤ)) (by exact_mod_cast h.three_le_natCard_left)
    (h.primeTISignInt_eq_one_or_eq_neg_one (σ := σ) j) (Or.inl rfl)
    (((h.primeTIirr_one_modEq hσ i j hm).symm).trans hmod)

end Fintype

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
