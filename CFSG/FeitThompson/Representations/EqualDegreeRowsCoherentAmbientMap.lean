module

public import CFSG.FeitThompson.Representations.PrimeCubeLocalArrayNonlinearCharacters
public import CFSG.FeitThompson.Representations.DadeRowDifferenceTransfer
public import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence
public import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Representations.OddBridgeProjectionRigidity
import CFSG.FeitThompson.Representations.DegreeZeroNormalInductionsPuncturedSupport
public import Mathlib.Analysis.CStarAlgebra.Classes

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Reduction

variable {L G : Type*} [Group L] [Group G]

theorem eq_sum_smul_of_eq_on_sub {ι : Type*} [Fintype ι] {S : Set (L → ℂ)}
    {u : ι → L → ℂ} (hS : S = Set.range u) {e : ℂ} (he : e ≠ 0) (hdeg : ∀ i, u i 1 = e)
    {v : ι → G → ℂ} {τ : charSpanZero S →+ Submodule.span ℤ (Irr G)}
    (hsub : ∀ i k : ι, ∀ w : charSpanZero S, (w : L → ℂ) = u i - u k →
      (τ w : G → ℂ) = v i - v k)
    (w : charSpanZero S) (c : ι → ℤ) (hw : (w : L → ℂ) = ∑ i, (c i : ℂ) • u i) :
    (τ w : G → ℂ) = ∑ i, (c i : ℂ) • v i := by
  classical
  have hsum0 : ∑ i, (c i : ℂ) = 0 := by
    have h0 : (∑ i, (c i : ℂ) • u i) 1 = 0 := by rw [← hw]; exact charSpanZero_apply_one w
    rw [Finset.sum_apply] at h0
    have h1 : (∑ i, (c i : ℂ)) * e = 0 := by
      rw [Finset.sum_mul]; simpa [hdeg] using h0
    exact (mul_eq_zero.1 h1).resolve_right he
  rcases isEmpty_or_nonempty ι with hemp | hne
  · have hw0 : w = 0 := Subtype.ext (by rw [hw]; simp)
    rw [hw0, map_zero]; simp
  · obtain ⟨i₀⟩ := hne
    have hmemS : ∀ i : ι, u i ∈ S := fun i => by rw [hS]; exact ⟨i, rfl⟩
    have hA : ∀ i : ι, u i - u i₀ ∈ charSpanZero S := fun i =>
      mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span (hmemS i))
        (Submodule.subset_span (hmemS i₀)), by simp [hdeg]⟩
    have hwsum : w = ∑ i, c i • (⟨u i - u i₀, hA i⟩ : charSpanZero S) := by
      refine Subtype.ext ?_
      rw [AddSubmonoidClass.coe_finsetSum, hw]
      have hcoe : ∀ i : ι,
          ((c i • (⟨u i - u i₀, hA i⟩ : charSpanZero S) : charSpanZero S) : L → ℂ)
            = (c i : ℂ) • u i - (c i : ℂ) • u i₀ := fun i => by
        rw [SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_sub]
      rw [Finset.sum_congr rfl fun i _ => hcoe i, Finset.sum_sub_distrib, ← Finset.sum_smul,
        hsum0, zero_smul, sub_zero]
    rw [hwsum, map_sum, AddSubmonoidClass.coe_finsetSum]
    have hterm : ∀ i : ι,
        ((τ (c i • (⟨u i - u i₀, hA i⟩ : charSpanZero S)) : Submodule.span ℤ (Irr G)) : G → ℂ)
          = (c i : ℂ) • v i - (c i : ℂ) • v i₀ := fun i => by
      rw [map_zsmul, SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, hsub i i₀ _ rfl, smul_sub]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.sum_smul,
      hsum0, zero_smul, sub_zero]

end Reduction

section LocalRows

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L} {h : IsPrimeCyclicTIHyp K W₁ W₂}

section Family

variable [Fintype ↑(Irr ↥W₁)]

theorem primeTIrowFam_eq_range (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    primeTIrowFam h σ
      = Set.range fun j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} =>
          h.primeTIrow σ (j : Irr ↥W₂) := by
  ext f
  rw [mem_primeTIrowFam]
  exact ⟨fun ⟨j, hj, hf⟩ => ⟨⟨j, hj⟩, hf⟩, fun ⟨j, hj⟩ => ⟨j, j.2, hj⟩⟩

theorem primeTIrow_mem_primeTIrowFam {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIrow σ j ∈ primeTIrowFam h σ := mem_primeTIrowFam.2 ⟨j, hj, rfl⟩

end Family

theorem star_inflateLeft [Finite L] (h : IsPrimeCyclicTIHyp K W₁ W₂) (i : Irr ↥W₁) :
    star (h.inflateLeft i) = h.inflateLeft (starIrr i) := by
  funext g
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp g
  rw [Pi.star_apply, h.inflateLeft_apply_mul i hk hw, h.inflateLeft_apply_mul _ hk hw,
    coe_starIrr]
  rfl

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem star_primeTIirr_principal_left (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂)
    (hsign : h.primeTISign σ j = h.primeTISign σ (starIrr j)) :
    star (h.primeTIirr σ (principalIrr ↥W₁) j)
      = h.primeTIirr σ (principalIrr ↥W₁) (starIrr j) := by
  have hstar : (classFun.starₗ ↥(W₁ ⊔ W₂)) (h.isCyclicTIPair.basisProdIrr
      (principalIrr ↥W₁, j)) = h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, starIrr j) := by
    refine h.isCyclicTIPair.starₗ_basisProdIrr ?_ (coe_starIrr j)
    rw [coe_principalIrr]
    simp
  have hsr : star (h.primeTISign σ (starIrr j)) = h.primeTISign σ (starIrr j) :=
    h.conj_primeTISign _
  rw [h.primeTIirr_principal_left, h.primeTIirr_principal_left, hsign, star_smul, hsr]
  congr 1
  rw [← classFun.coe_starₗ, ← hσ.map_starₗ h.isCyclicTIPair, hstar]

theorem star_primeTIirr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂)
    (hsign : h.primeTISign σ j = h.primeTISign σ (starIrr j)) :
    star (h.primeTIirr σ i j) = h.primeTIirr σ (starIrr i) (starIrr j) := by
  rw [h.primeTIirr_eq_mul i j, h.primeTIirr_eq_mul (starIrr i) (starIrr j), star_mul',
    star_inflateLeft h i, star_primeTIirr_principal_left h hσ j hsign]

variable [Fintype ↑(Irr ↥W₁)] {ζ : L → ℂ} {d n δ : ℤ}

theorem primeTIrow_mem_virtualChars (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    h.primeTIrow σ j ∈ virtualChars L := by
  rw [IsPrimeCyclicTIHyp.primeTIrow_def]
  exact Submodule.sum_mem _ fun i _ => Irr_subset_virtualChars (h.primeTIirr_mem_Irr hσ i j)

theorem primeTIrowFam_subset_indFam [K.Normal] (hB : h.IsUniformBridgeData σ ζ d n δ) :
    primeTIrowFam h σ ⊆ indFam K (Irr ↥K \ {1}) := by
  intro f hf
  obtain ⟨j, hj, rfl⟩ := mem_primeTIrowFam.1 hf
  exact primeTIrow_mem_indFam_sdiff hB hj

theorem primeTIrow_apply_one (hB : h.IsUniformBridgeData σ ζ d n δ) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIrow σ j 1 = (Nat.card ↥W₁ : ℂ) * (d : ℂ) := by
  rw [h.primeTIrow_one j, h.primeTIres_one j, hB.primeTIirr_one _ j hj]

omit [Fintype ↑(Irr ↥W₁)] in
theorem natCard_mul_degree_ne_zero (hB : h.IsUniformBridgeData σ ζ d n δ) :
    ((Nat.card ↥W₁ : ℂ)) * (d : ℂ) ≠ 0 := by
  have hd : (0 : ℤ) < d := by linarith [hB.one_lt]
  refine mul_ne_zero ?_ ?_
  · simpa using (Nat.card_pos (α := ↥W₁)).ne'
  · exact_mod_cast hd.ne'

theorem cfInner_primeTIrow_primeTIrow (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j k : Irr ↥W₂) [Decidable (j = k)] :
    cfInner (h.primeTIrow σ j) (h.primeTIrow σ k)
      = if j = k then (Nat.card ↥W₁ : ℂ) else 0 := by
  classical
  have hcomm : IsMulCommutative ↥W₁ := h.isCyclicTIPair.isMulCommutative_left
  have hterm : ∀ i : ↑(Irr ↥W₁),
      cfInner (h.primeTIirr σ i j) (∑ i' : ↑(Irr ↥W₁), h.primeTIirr σ i' k)
        = if j = k then (1 : ℂ) else 0 := by
    intro i
    rw [cfInner_sum_right, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun l _ hli => by rw [h.cfInner_primeTIirr hσ, if_neg (by simp [Ne.symm hli])]),
      h.cfInner_primeTIirr hσ]
    by_cases hjk : j = k <;> simp [hjk]
  rw [IsPrimeCyclicTIHyp.primeTIrow_def, IsPrimeCyclicTIHyp.primeTIrow_def, cfInner_sum_left,
    Finset.sum_congr rfl fun i _ => hterm i]
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos hjk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, card_Irr_eq_card_of_isMulCommutative]
  · rw [if_neg hjk, if_neg hjk, Finset.sum_const, smul_zero]

theorem star_primeTIrow (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂)
    (hsign : h.primeTISign σ j = h.primeTISign σ (starIrr j)) :
    star (h.primeTIrow σ j) = h.primeTIrow σ (starIrr j) := by
  rw [IsPrimeCyclicTIHyp.primeTIrow_def, IsPrimeCyclicTIHyp.primeTIrow_def, star_sum,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => star_primeTIirr h hσ i j hsign]
  exact Fintype.sum_bijective starIrr starIrr_involutive.bijective _ _ fun i => rfl

theorem star_mem_primeTIrowFam (hB : h.IsUniformBridgeData σ ζ d n δ) {f : L → ℂ}
    (hf : f ∈ primeTIrowFam h σ) : star f ∈ primeTIrowFam h σ := by
  obtain ⟨j, hj, rfl⟩ := mem_primeTIrowFam.1 hf
  have hjbar : starIrr j ≠ principalIrr ↥W₂ := fun hc =>
    hj (by rw [← starIrr_starIrr j, hc, starIrr_principalIrr])
  have hsign : h.primeTISign σ j = h.primeTISign σ (starIrr j) := by
    rw [hB.primeTISign_eq j hj, hB.primeTISign_eq _ hjbar]
  rw [star_primeTIrow h hB.isometry j hsign]
  exact primeTIrow_mem_primeTIrowFam hjbar

end Fintype

end LocalRows

section RowEta

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G}
  {K W₁ W₂ : Subgroup ↥L} [Fintype ↑(Irr ↥W₁)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}

noncomputable def rowEtaSum
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G) (δ : ℤ) (j : Irr ↥W₂) : G → ℂ :=
  (δ : ℂ) • ∑ i : ↑(Irr ↥W₁), hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem rowEtaSum_def
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (δ : ℤ) (j : Irr ↥W₂) :
    rowEtaSum hW ω δ j
      = (δ : ℂ) • ∑ i : ↑(Irr ↥W₁),
          hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j) := (rfl)

theorem rowEtaSum_mem_span_Irr
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ω) (δ : ℤ) (j : Irr ↥W₂) :
    rowEtaSum hW ω δ j ∈ Submodule.span ℤ (Irr G) := by
  rw [rowEtaSum_def, Int.cast_smul_eq_zsmul]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
  exact mem_span_Irr_of_mem_virtualChars (hW.prodCharEta_mem_virtualChars hω _ _)

theorem cfInner_rowEtaSum [IsMulCommutative ↥W₁]
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ω) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) (j k : Irr ↥W₂)
    [Decidable (j = k)] :
    cfInner (rowEtaSum hW ω δ j) (rowEtaSum hW ω δ k)
      = if j = k then (Nat.card ↥W₁ : ℂ) else 0 := by
  classical
  have hterm : ∀ i : ↑(Irr ↥W₁),
      cfInner (hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j))
          (∑ i' : ↑(Irr ↥W₁),
            hW.prodCharEta ω (irrMapSubtype L W₁ i') (irrMapSubtype L W₂ k))
        = if j = k then (1 : ℂ) else 0 := by
    intro i
    rw [cfInner_sum_right, Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun l _ hli => by
      rw [hW.cfInner_prodCharEta hω, if_neg (by
        rintro ⟨h1, -⟩
        exact hli (irrMapSubtype_injective L W₁ h1.symm))]),
      hW.cfInner_prodCharEta hω]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [if_neg (by rintro ⟨-, h2⟩; exact hjk (irrMapSubtype_injective L W₂ h2)), if_neg hjk]
  rw [rowEtaSum_def, rowEtaSum_def, cfInner_smul_left, cfInner_smul_right, cfInner_sum_left,
    Finset.sum_congr rfl fun i _ => hterm i]
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos hjk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, card_Irr_eq_card_of_isMulCommutative]
    rcases hδ with rfl | rfl <;> norm_num
  · rw [if_neg hjk, if_neg hjk, Finset.sum_const, smul_zero, mul_zero, mul_zero]

end RowEta

section Coherence

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {ζ : ↥L → ℂ} {d n δ : ℤ} {h : IsPrimeCyclicTIHyp K W₁ W₂}
  {A₀ : Set G} {T : G → Subgroup G}

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem charSpanZero_primeTIrowFam_le_dadeZDomain [K.Normal]
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀) :
    charSpanZero (primeTIrowFam h σ) ≤ dadeZDomain L A₀ := by
  intro f hf
  obtain ⟨hfspan, hf1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeZDomain.2 ⟨Submodule.span_le.2 ?_ hfspan, fun x hx => ?_⟩
  · intro g hg
    obtain ⟨j, -, rfl⟩ := mem_primeTIrowFam.1 hg
    exact primeTIrow_mem_virtualChars h hB.isometry _
  · by_cases hxK : (x : ↥L) ∈ K
    · have hx1 : x = 1 := by
        by_contra hne
        exact hx (hA₀ ⟨x, subset_bridgeSupport_left ⟨hxK, hne⟩, rfl⟩)
      rw [hx1]; exact hf1
    · exact NormalInducedFamily.eq_zero_of_mem_span_indFam_of_notMem K
        (primeTIrowFam_subset_indFam hB) hfspan hxK

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
noncomputable def rowDadeHom [K.Normal] (hD : IsDadeData L A₀ T)
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀) :
    charSpanZero (primeTIrowFam h σ) →+ Submodule.span ℤ (Irr G) :=
  ((Submodule.inclusion (charSpanZero_le (Irr G))).toAddMonoidHom).comp
    ((dadeZMap hD).comp
      (Submodule.inclusion (charSpanZero_primeTIrowFam_le_dadeZDomain hB hA₀)).toAddMonoidHom)

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem coe_rowDadeHom [K.Normal] (hD : IsDadeData L A₀ T)
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (f : charSpanZero (primeTIrowFam h σ)) (F : dadeDomain L A₀)
    (hF : (F : ↥L → ℂ) = (f : ↥L → ℂ)) :
    ((rowDadeHom hD hB hA₀ f : Submodule.span ℤ (Irr G)) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have harg : (⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain
      (charSpanZero_primeTIrowFam_le_dadeZDomain hB hA₀ f.2)⟩ : dadeDomain L A₀) = F :=
    Subtype.ext hF.symm
  have h1 : ((rowDadeHom hD hB hA₀ f : Submodule.span ℤ (Irr G)) : G → ℂ)
      = ((dadeZMap hD ⟨(f : ↥L → ℂ),
          charSpanZero_primeTIrowFam_le_dadeZDomain hB hA₀ f.2⟩ :
        charSpanZero (Irr G)) : G → ℂ) := (rfl)
  rw [h1, coe_dadeZMap, harg]

theorem dadeMap_primeTIrow_sub_eq [K.Normal]
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ω)
    {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (F : dadeDomain L A₀) (hF : (F : ↥L → ℂ) = h.primeTIrow σ j - h.primeTIrow σ k) :
    ((dadeMap hD F : classFun G) : G → ℂ)
      = rowEtaSum (h.isCyclicTIPair_map_subtype hstab hdisj) ω δ j
        - rowEtaSum (h.isCyclicTIPair_map_subtype hstab hdisj) ω δ k := by
  classical
  have hA : ∀ y ∈ K, y ≠ (1 : ↥L) →
      ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ (K : Set ↥L) \ {1} :=
    fun _ _ _ _ hx => ⟨hx.1.1, hx.2⟩
  have hone : ∀ i : ↑(Irr ↥W₁), h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1 := fun i => by
    rw [hB.primeTIirr_one i j hj, hB.primeTIirr_one i k hk]
  have hmemi : ∀ i : ↑(Irr ↥W₁),
      h.primeTIirr σ i j - h.primeTIirr σ i k ∈ dadeDomain L A₀ := fun i =>
    h.primeTIirr_sub_mem_dadeDomain hB.isometry h.right_le hA hA₀ i hj hk (hone i)
  have hsum : F = ∑ i : ↑(Irr ↥W₁),
      (⟨h.primeTIirr σ i j - h.primeTIirr σ i k, hmemi i⟩ : dadeDomain L A₀) := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum, hF, IsPrimeCyclicTIHyp.primeTIrow_def,
      IsPrimeCyclicTIHyp.primeTIrow_def, ← Finset.sum_sub_distrib]
  rw [hsum, map_sum, AddSubmonoidClass.coe_finsetSum]
  have hterm : ∀ i : ↑(Irr ↥W₁),
      ((dadeMap hD ⟨h.primeTIirr σ i j - h.primeTIirr σ i k, hmemi i⟩ : classFun G) : G → ℂ)
        = (δ : ℂ) • ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
            - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k)) := by
    intro i
    rw [← hB.primeTISign_eq j hj]
    exact h.dadeMap_primeTIirr_sub_eq hB.isometry h.right_le hA hA₀ hD hstab hdisj hω i hj hk
      (hone i)
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.smul_sum, rowEtaSum_def, rowEtaSum_def,
    ← smul_sub, Finset.sum_sub_distrib]

theorem exists_isCoherentWith_primeTIrowFam [K.Normal]
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ω) :
    ∃ ν₂ : Submodule.span ℤ (primeTIrowFam h σ) →+ virtualChars G,
      IsCoherentWith (primeTIrowFam h σ)
        ((spanIrrToVirtualChars G).comp (rowDadeHom hD hB hA₀)) ν₂ ∧
      ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ →
        ∀ w : Submodule.span ℤ (primeTIrowFam h σ), (w : ↥L → ℂ) = h.primeTIrow σ j →
          ((ν₂ w : virtualChars G) : G → ℂ)
            = rowEtaSum (h.isCyclicTIPair_map_subtype hstab hdisj) ω δ j := by
  classical
  have hfin : Fintype {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} := Fintype.ofFinite _
  have hcomm : IsMulCommutative ↥W₁ := h.isCyclicTIPair.isMulCommutative_left
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  set u : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} → ↥L → ℂ :=
    fun j => h.primeTIrow σ (j : Irr ↥W₂) with hudef
  set v : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂} → G → ℂ :=
    fun j => rowEtaSum hW ω δ (j : Irr ↥W₂) with hvdef
  have hSrange : primeTIrowFam h σ = Set.range u := primeTIrowFam_eq_range h
  have hgramu : ∀ j k, cfInner (u j) (u k) = if j = k then (Nat.card ↥W₁ : ℂ) else 0 := by
    intro j k
    rw [hudef, cfInner_primeTIrow_primeTIrow h hB.isometry]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos (by rw [hjk])]
    · rw [if_neg hjk, if_neg fun hc => hjk (Subtype.ext hc)]
  have hgramv : ∀ j k, cfInner (v j) (v k) = if j = k then (Nat.card ↥W₁ : ℂ) else 0 := by
    intro j k
    rw [hvdef, cfInner_rowEtaSum hW hω hB.sign]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos (by rw [hjk])]
    · rw [if_neg hjk, if_neg fun hc => hjk (Subtype.ext hc)]
  have hgne : ∀ _j : {j : Irr ↥W₂ // j ≠ principalIrr ↥W₂},
      ((Nat.card ↥W₁ : ℂ)) ≠ 0 := fun _ => by
    simpa using (Nat.card_pos (α := ↥W₁)).ne'
  have hvmem : ∀ j, v j ∈ Submodule.span ℤ (Irr G) := fun _ =>
    rowEtaSum_mem_span_Irr hW hω δ _
  have hdeg : ∀ j, u j 1 = (Nat.card ↥W₁ : ℂ) * (d : ℂ) := fun j =>
    primeTIrow_apply_one hB j.2
  have hsub : ∀ j k, ∀ w : charSpanZero (primeTIrowFam h σ), (w : ↥L → ℂ) = u j - u k →
      ((rowDadeHom hD hB hA₀ w : Submodule.span ℤ (Irr G)) : G → ℂ) = v j - v k := by
    intro j k w hw
    have hFmem : (w : ↥L → ℂ) ∈ dadeDomain L A₀ :=
      mem_dadeDomain_of_mem_dadeZDomain
        (charSpanZero_primeTIrowFam_le_dadeZDomain hB hA₀ w.2)
    rw [coe_rowDadeHom hD hB hA₀ w ⟨(w : ↥L → ℂ), hFmem⟩ rfl]
    exact dadeMap_primeTIrow_sub_eq hB hA₀ hD hstab hdisj hω j.2 k.2 _ hw
  obtain ⟨ν₂, hcoh, hval⟩ := exists_isCoherentWith_of_gram_eq (v := v) hSrange hgramu hgne hvmem
    hgramv (τ := rowDadeHom hD hB hA₀)
    (fun w c hwc => eq_sum_smul_of_eq_on_sub hSrange
      (natCard_mul_degree_ne_zero hB) hdeg hsub w c hwc)
  exact ⟨ν₂, hcoh, fun j hj w hwj => hval ⟨j, hj⟩ w hwj⟩

theorem isCoherent_primeTIrowFam [K.Normal]
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ω) :
    IsCoherent (primeTIrowFam h σ)
      ((spanIrrToVirtualChars G).comp (rowDadeHom hD hB hA₀)) := by
  obtain ⟨ν₂, hcoh, -⟩ := exists_isCoherentWith_primeTIrowFam hB hA₀ hD hstab hdisj hω
  exact IsCoherentWith.isCoherent hcoh

end Coherence

end CFSG.FeitThompson

end
