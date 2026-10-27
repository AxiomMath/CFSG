module

public import CFSG.FeitThompson.Representations.PrimeTIEnlargedInduction
public import CFSG.FeitThompson.Representations.LinearTwistCyclicTIIsometry
import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence
import CFSG.FeitThompson.Representations.SignedPairInducedBlockSpans
import CFSG.FeitThompson.Representations.FixedDegreeCharacterSumVanishing
import CFSG.FeitThompson.Foundations.ComplementsDifferByCrossedHom

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}

theorem existsUnique_sign_smul_mem_Irr [Finite L] {f : L → ℂ} (hf : f ∈ signedIrr L) :
    ∃! δ : ℂ, (δ = 1 ∨ δ = -1) ∧ δ • f ∈ Irr L := by
  have hno : ∀ g : L → ℂ, g ∈ Irr L → -g ∈ Irr L → False := fun g h1 h2 =>
    ne_neg_of_mem_Irr h2 h1 rfl
  rcases mem_signedIrr.1 hf with hpos | hneg
  · refine ⟨1, ⟨Or.inl rfl, by simpa using hpos⟩, ?_⟩
    rintro δ ⟨hδ | hδ, hmem⟩
    · exact hδ
    · rw [hδ] at hmem
      exact absurd (by simpa using hmem) fun hc => hno f hpos hc
  · refine ⟨-1, ⟨Or.inr rfl, by simpa using hneg⟩, ?_⟩
    rintro δ ⟨hδ | hδ, hmem⟩
    · rw [hδ, one_smul] at hmem
      exact absurd hneg fun hc => hno f hmem hc
    · exact hδ

namespace IsPrimeCyclicTIHyp

theorem isComplement'_left (h : IsPrimeCyclicTIHyp K W₁ W₂) : W₁.IsComplement' K := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ (Set.eq_univ_of_forall fun g => ?_)
  · rw [disjoint_iff, inf_comm]
    exact h.inf_eq_bot
  · obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp g
    have hmem : w⁻¹ * k * w ∈ K := by
      simpa using h.normal.conj_mem _ hk w⁻¹
    exact ⟨w, hw, w⁻¹ * k * w, hmem, by group⟩

noncomputable def projLeft (h : IsPrimeCyclicTIHyp K W₁ W₂) : L →* ↥W₁ :=
  have := h.normal
  h.isComplement'_left.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' K)

theorem projLeft_apply_mul (h : IsPrimeCyclicTIHyp K W₁ W₂) {k w : L} (hk : k ∈ K)
    (hw : w ∈ W₁) : h.projLeft (k * w) = ⟨w, hw⟩ := by
  have := h.normal
  have hmem : w⁻¹ * k⁻¹ * w ∈ K := by
    simpa using h.normal.conj_mem _ (K.inv_mem hk) w⁻¹
  have hq : (QuotientGroup.mk (k * w) : L ⧸ K) = QuotientGroup.mk ((⟨w, hw⟩ : ↥W₁) : L) := by
    refine QuotientGroup.eq.2 ?_
    have he : (k * w)⁻¹ * w = w⁻¹ * k⁻¹ * w := by group
    rw [he]
    exact hmem
  calc h.projLeft (k * w)
      = h.isComplement'_left.QuotientMulEquiv (QuotientGroup.mk (k * w)) := rfl
    _ = h.isComplement'_left.QuotientMulEquiv
          (QuotientGroup.mk ((⟨w, hw⟩ : ↥W₁) : L)) := by rw [hq]
    _ = ⟨w, hw⟩ := quotientMulEquiv_mk_coe _ _

noncomputable def inflateLeft (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) : L → ℂ :=
  fun g => (i : ↥W₁ → ℂ) (h.projLeft g)

theorem inflateLeft_apply_mul (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) {k w : L}
    (hk : k ∈ K) (hw : w ∈ W₁) :
    h.inflateLeft i (k * w) = (i : ↥W₁ → ℂ) ⟨w, hw⟩ := by
  rw [inflateLeft, h.projLeft_apply_mul hk hw]

theorem inflateLeft_principal (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    h.inflateLeft (principalIrr ↥W₁) = 1 := by
  funext g
  rw [inflateLeft, coe_principalIrr]
  rfl

theorem inflateLeft_mem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) :
    h.inflateLeft i ∈ Irr L := by
  have := h.isCyclicTIPair.isMulCommutative_left
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_coe_eq_of_mem_Irr i.2
  have hmul := mul_mem_Irr (ψ.comp h.projLeft) (one_mem_Irr (G := L))
  refine (show (fun x : L => ((ψ.comp h.projLeft) x : ℂ) * (1 : L → ℂ) x)
    = h.inflateLeft i from ?_) ▸ hmul
  funext g
  rw [Pi.one_apply, mul_one, inflateLeft, ← hψ]
  rfl

theorem inflateLeft_one (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) :
    h.inflateLeft i 1 = 1 := by
  have := h.isCyclicTIPair.isMulCommutative_left
  rw [inflateLeft, map_one, apply_one_eq_one_of_mem_Irr i.2]

noncomputable def inflateLeftCF (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) : classFun L :=
  ⟨h.inflateLeft i, Irr_subset_classFun (h.inflateLeft_mem_Irr i)⟩

@[simp]
theorem coe_inflateLeftCF (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) :
    (h.inflateLeftCF i : L → ℂ) = h.inflateLeft i := (rfl)

theorem resClassFun_inflateLeft (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) :
    resClassFun (W₁ ⊔ W₂) (h.inflateLeft i)
      = h.isCyclicTIPair.prodChar (i : ↥W₁ → ℂ) 1 := by
  have hW := h.isCyclicTIPair
  funext x
  set p := hW.mulEquivProd.symm x with hp
  have hx : (x : L) = (p.1 : L) * (p.2 : L) := by
    have h2 := hW.coe_mulEquivProd_apply p
    rw [hp, MulEquiv.apply_symm_apply] at h2
    exact h2
  have hcomm : (p.1 : L) * (p.2 : L) = (p.2 : L) * (p.1 : L) :=
    hW.commute_of_mem p.1.2 p.2.2
  rw [resClassFun_apply, hx, hcomm,
    h.inflateLeft_apply_mul i (h.right_le p.2.2) p.1.2, hW.prodChar_apply, ← hp]
  simp

theorem resMul_inflateLeftCF_basisProdIrr (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁)
    (j : Irr ↥W₂) :
    classFun.resMul (W₁ ⊔ W₂) (h.inflateLeftCF i)
        (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j))
      = h.isCyclicTIPair.basisProdIrr (i, j) := by
  have hW := h.isCyclicTIPair
  refine Subtype.ext ?_
  rw [classFun.coe_resMul, coe_inflateLeftCF, h.resClassFun_inflateLeft,
    IsCyclicTIPair.coe_basisProdIrr_apply, IsCyclicTIPair.coe_basisProdIrr_apply, coe_principalIrr,
    hW.prodChar_mul_prodChar]

theorem basisProdIrr_mem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    ((h.isCyclicTIPair.basisProdIrr (i, j) : classFun ↥(W₁ ⊔ W₂)) : ↥(W₁ ⊔ W₂) → ℂ)
      ∈ Irr ↥(W₁ ⊔ W₂) := by
  rw [IsCyclicTIPair.coe_basisProdIrr_apply]
  exact h.isCyclicTIPair.prodChar_mem_Irr i.2 j.2

open scoped Classical in
noncomputable def primeTISign (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (j : Irr ↥W₂) : ℂ :=
  if (σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j)) : L → ℂ) ∈ Irr L then 1 else -1

variable {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

theorem primeTISign_eq_one_or_eq_neg_one (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    h.primeTISign σ j = 1 ∨ h.primeTISign σ j = -1 := by
  classical
  rw [primeTISign]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem primeTISign_mul_self (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    h.primeTISign σ j * h.primeTISign σ j = 1 := by
  rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hδ | hδ <;> rw [hδ] <;> ring

theorem conj_primeTISign (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    (starRingEnd ℂ) (h.primeTISign σ j) = h.primeTISign σ j := by
  rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hδ | hδ <;> rw [hδ] <;> simp

noncomputable def primeTIirr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (i : Irr ↥W₁) (j : Irr ↥W₂) : L → ℂ :=
  h.inflateLeft i *
    (h.primeTISign σ j • (σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j)) : L → ℂ))

theorem primeTIirr_principal_left (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    h.primeTIirr σ (principalIrr ↥W₁) j
      = h.primeTISign σ j • (σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j)) : L → ℂ) := by
  rw [primeTIirr, h.inflateLeft_principal, one_mul]

theorem primeTIirr_eq_mul (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    h.primeTIirr σ i j = h.inflateLeft i * h.primeTIirr σ (principalIrr ↥W₁) j := by
  rw [h.primeTIirr_principal_left, primeTIirr]

theorem primeTIirr_one (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    h.primeTIirr σ i j 1 = h.primeTIirr σ (principalIrr ↥W₁) j 1 := by
  rw [h.primeTIirr_eq_mul i j, Pi.mul_apply, h.inflateLeft_one, one_mul]

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem exists_isCyclicTIIsometry (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    ∃ τ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L, IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ τ :=
  h.isCyclicTIPair.exists_isCyclicTIIsometry

theorem coe_apply_basisProdIrr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    (σ (h.isCyclicTIPair.basisProdIrr (i, j)) : L → ℂ)
      = h.inflateLeft i * (σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j)) : L → ℂ) := by
  have hW := h.isCyclicTIPair
  have hkey := IsCyclicTIIsometry.apply_resMul hW hσ (lam := h.inflateLeftCF i)
    (by rw [coe_inflateLeftCF]; exact h.inflateLeft_mem_Irr i)
    (by rw [coe_inflateLeftCF]; exact h.inflateLeft_one i)
    (h.basisProdIrr_mem_Irr (principalIrr ↥W₁) j)
  rw [h.resMul_inflateLeftCF_basisProdIrr i j] at hkey
  rw [hkey, coe_inflateLeftCF]

theorem primeTIirr_eq_smul_apply (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    h.primeTIirr σ i j
      = h.primeTISign σ j • (σ (h.isCyclicTIPair.basisProdIrr (i, j)) : L → ℂ) := by
  rw [primeTIirr, h.coe_apply_basisProdIrr hσ i j]
  funext g
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem coe_apply_basisProdIrr_eq_smul_primeTIirr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    (σ (h.isCyclicTIPair.basisProdIrr (i, j)) : L → ℂ)
      = h.primeTISign σ j • h.primeTIirr σ i j := by
  rw [h.primeTIirr_eq_smul_apply hσ, smul_smul, h.primeTISign_mul_self, one_smul]

theorem primeTIirr_principal_left_mem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    h.primeTIirr σ (principalIrr ↥W₁) j ∈ Irr L := by
  classical
  rw [h.primeTIirr_principal_left, primeTISign]
  split
  · rwa [one_smul]
  · rename_i hc
    have hs := hσ.apply_mem_signedIrr (h.basisProdIrr_mem_Irr (principalIrr ↥W₁) j)
    rcases mem_signedIrr.1 hs with hpos | hneg
    · exact absurd hpos hc
    · simpa using hneg

theorem primeTIirr_mem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    h.primeTIirr σ i j ∈ Irr L := by
  rw [h.primeTIirr_eq_mul i j]
  exact mul_mem_Irr_of_apply_one_eq_one (h.inflateLeft_mem_Irr i) (h.inflateLeft_one i)
    (h.primeTIirr_principal_left_mem_Irr hσ j)

theorem existsUnique_primeTISign (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    ∃! δ : ℂ, (δ = 1 ∨ δ = -1) ∧
      δ • (σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j)) : L → ℂ) ∈ Irr L :=
  existsUnique_sign_smul_mem_Irr
    (hσ.apply_mem_signedIrr (h.basisProdIrr_mem_Irr (principalIrr ↥W₁) j))

theorem primeTISign_principal (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) :
    h.primeTISign σ (principalIrr ↥W₂) = 1 := by
  classical
  rw [primeTISign, if_pos]
  rw [h.isCyclicTIPair.basisProdIrr_principal, hσ.map_principalClassFun, coe_principalClassFun]
  exact one_mem_Irr

theorem primeTIirr_principal (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) :
    h.primeTIirr σ (principalIrr ↥W₁) (principalIrr ↥W₂) = 1 := by
  rw [h.primeTIirr_principal_left, h.primeTISign_principal hσ, one_smul,
    h.isCyclicTIPair.basisProdIrr_principal, hσ.map_principalClassFun, coe_principalClassFun]

theorem primeTIirr_principal_right (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) :
    h.primeTIirr σ i (principalIrr ↥W₂) = h.inflateLeft i := by
  rw [h.primeTIirr_eq_mul i, h.primeTIirr_principal hσ, mul_one]

open scoped Classical in
theorem cfInner_primeTIirr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i k : Irr ↥W₁) (j l : Irr ↥W₂) :
    cfInner (h.primeTIirr σ i j) (h.primeTIirr σ k l) = if i = k ∧ j = l then 1 else 0 := by
  rw [h.primeTIirr_eq_smul_apply hσ, h.primeTIirr_eq_smul_apply hσ, cfInner_smul_left,
    cfInner_smul_right, hσ.inner_eq, h.isCyclicTIPair.cfInner_basisProdIrr, h.conj_primeTISign]
  by_cases hjl : j = l
  · subst hjl
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, mul_one, h.primeTISign_mul_self]
    · rw [if_neg (by simp [Prod.ext_iff, hik]), if_neg (by simp [hik])]
      ring
  · rw [if_neg (by simp [Prod.ext_iff, hjl]), if_neg (by simp [hjl])]
    ring

open scoped Classical in
theorem cfInner_primeTIirr_eq_ite (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (p q : Irr ↥W₁ × Irr ↥W₂) :
    cfInner (h.primeTIirr σ p.1 p.2) (h.primeTIirr σ q.1 q.2) = if p = q then 1 else 0 := by
  rw [h.cfInner_primeTIirr hσ]
  exact if_congr Prod.ext_iff.symm rfl rfl

end Fintype

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
