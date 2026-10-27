module

public import CFSG.FeitThompson.Representations.CoherenceDeterminesUniformBridgeImage
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.CoherentInducedImageVanishesMixedTI
import CFSG.FeitThompson.Representations.NormOneCommonPivotAmbiguity
import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.InducedFamilyIrreducibleRowOrthogonal
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

theorem one_le_sq_add_sq_of_sub_eq_one_or {r s : ℤ} (hrs : r - s = 1 ∨ r - s = -1) :
    1 ≤ r ^ 2 + s ^ 2 := by
  rcases eq_or_ne r 0 with rfl | hr
  · have hs : s = -1 ∨ s = 1 := by omega
    rcases hs with rfl | rfl <;> norm_num
  · have h1 : 1 ≤ r ^ 2 := by
      rcases lt_or_gt_of_ne hr with hlt | hgt <;> nlinarith
    nlinarith [sq_nonneg s]

theorem sum_sq_eq_and_eq_zero_of_sum_sq_le {I J : Type*} [Fintype I] [Fintype J]
    {b : I × J → ℤ} {j j₀ : J} (hjj₀ : j ≠ j₀)
    (hdiff : ∀ i, b (i, j) - b (i, j₀) = 1 ∨ b (i, j) - b (i, j₀) = -1)
    (hbound : ∑ p, b p ^ 2 ≤ (Fintype.card I : ℤ)) :
    (∑ p, b p ^ 2 = (Fintype.card I : ℤ)) ∧ (∀ i, b (i, j) ^ 2 + b (i, j₀) ^ 2 = 1) ∧
      ∀ (i : I) (k : J), k ≠ j → k ≠ j₀ → b (i, k) = 0 := by
  classical
  set t : I → ℤ := fun i => ∑ k, b (i, k) ^ 2 with ht
  set s : I → ℤ := fun i => b (i, j) ^ 2 + b (i, j₀) ^ 2 with hs
  have hsum : ∑ p, b p ^ 2 = ∑ i, t i := Fintype.sum_prod_type (fun p => b p ^ 2)
  have hst : ∀ i, s i ≤ t i := by
    intro i
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({j, j₀} : Finset J))
      (fun x _ _ => sq_nonneg (b (i, x)))
    rwa [Finset.sum_pair hjj₀] at hle
  have hs1 : ∀ i, 1 ≤ s i := fun i => one_le_sq_add_sq_of_sub_eq_one_or (hdiff i)
  have hcard : ∑ _i : I, (1 : ℤ) = (Fintype.card I : ℤ) := by simp
  have hle1 : (Fintype.card I : ℤ) ≤ ∑ i, s i := by
    rw [← hcard]; exact Finset.sum_le_sum fun i _ => hs1 i
  have hle2 : ∑ i, s i ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => hst i
  have htot : ∑ i, t i = (Fintype.card I : ℤ) := le_antisymm (hsum ▸ hbound) (hle1.trans hle2)
  have hseq : ∀ i, s i = t i := by
    have heq : ∑ i, s i = ∑ i, t i := le_antisymm hle2 (by rw [htot]; exact hle1)
    intro i
    exact (Finset.sum_eq_sum_iff_of_le fun i _ => hst i).1 heq i (Finset.mem_univ i)
  have hsone : ∀ i, s i = 1 := by
    have hstot : ∑ i, s i = (Fintype.card I : ℤ) := by
      rw [Finset.sum_congr rfl fun i _ => hseq i, htot]
    have heq : ∑ _i : I, (1 : ℤ) = ∑ i, s i := by rw [hcard, hstot]
    intro i
    exact ((Finset.sum_eq_sum_iff_of_le fun i _ => hs1 i).1 heq i (Finset.mem_univ i)).symm
  refine ⟨by rw [hsum, htot], hsone, fun i k hkj hkj₀ => ?_⟩
  have h3 := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({k, j, j₀} : Finset J)) (fun x _ _ => sq_nonneg (b (i, x)))
  rw [Finset.sum_insert (by simp [hkj, hkj₀]), Finset.sum_pair hjj₀] at h3
  have hsi := hseq i
  have h4 : b (i, k) ^ 2 ≤ 0 := by
    simp only [hs, ht] at hsi h3
    linarith
  exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h4 (sq_nonneg _))

namespace IsUniformBridgeCoherenceData

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {d n δ : ℤ} {A : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G}
  (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)

noncomputable def etaLocal (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)
    (i : Irr ↥W₁) (k : Irr ↥W₂) : G → ℂ :=
  hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k)

omit [K.Normal] [Fintype ↑(Irr ↥W₁)] in
theorem etaLocal_def (i : Irr ↥W₁) (k : Irr ↥W₂) : hC.etaLocal i k
    = hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k) := (rfl)

omit [K.Normal] [Fintype ↑(Irr ↥W₁)] in
open scoped Classical in
include hC in
theorem cfInner_etaLocal (i i' : Irr ↥W₁) (k k' : Irr ↥W₂) :
    cfInner (hC.etaLocal i k) (hC.etaLocal i' k') = if i = i' ∧ k = k' then 1 else 0 := by
  rw [etaLocal, etaLocal, hC.isCyclicTIPair.cfInner_prodCharEta hC.omega_isometry]
  by_cases hi : i = i'
  · by_cases hk : k = k'
    · simp [hi, hk]
    · rw [if_neg ?_, if_neg (by simp [hk])]
      exact fun hcon => hk (irrMapSubtype_injective L W₂ hcon.2)
  · rw [if_neg ?_, if_neg (by simp [hi])]
    exact fun hcon => hi (irrMapSubtype_injective L W₁ hcon.1)

omit [K.Normal] [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem etaLocal_mem_virtualChars (i : Irr ↥W₁) (k : Irr ↥W₂) :
    hC.etaLocal i k ∈ virtualChars G :=
  hC.isCyclicTIPair.prodCharEta_mem_virtualChars hC.omega_isometry _ _

omit [K.Normal] [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem etaLocal_principal : hC.etaLocal (principalIrr ↥W₁) (principalIrr ↥W₂) = 1 := by
  rw [etaLocal, irrMapSubtype_principal, irrMapSubtype_principal]
  exact hC.isCyclicTIPair.prodCharEta_principal hC.omega_isometry

omit [K.Normal] [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem isOrthonormalFamily_etaLocal [DecidableEq (Irr ↥W₁ × Irr ↥W₂)] :
    IsOrthonormalFamily fun p : Irr ↥W₁ × Irr ↥W₂ => hC.etaLocal p.1 p.2 := by
  refine IsOrthonormalFamily.of_cfInner_eq_ite fun p q => ?_
  classical
  rw [hC.cfInner_etaLocal p.1 q.1 p.2 q.2]
  by_cases hpq : p = q
  · simp [hpq]
  · rw [if_neg fun hcon => hpq (Prod.ext hcon.1 hcon.2), if_neg hpq]

include hC in
theorem nuRow_eq_nu {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    hC.nuRow hk = (ν ⟨h.primeTIrow σ k,
      Submodule.subset_span (primeTIrow_mem_indFam_sdiff hC.local_data hk)⟩ : G → ℂ) := by
  have hMk : h.primeTIrow σ k ∈ indFam K (Irr ↥K \ {1}) :=
    primeTIrow_mem_indFam_sdiff hC.local_data hk
  have hsplit : (⟨h.primeTIrow σ k - (d : ℂ) • ζ,
      charSpanZero_le _ (primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hk)⟩ :
        Submodule.span ℤ (indFam K (Irr ↥K \ {1})))
      = ⟨h.primeTIrow σ k, Submodule.subset_span hMk⟩
        - d • ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_sub, SetLike.val_smul]
    rw [show (d : ℂ) • ζ = d • ζ from Int.cast_smul_eq_zsmul _ _ _]
  have key : hC.nuRow hk - (d : ℂ) • hC.nuZeta
      = (ν ⟨h.primeTIrow σ k, Submodule.subset_span hMk⟩ : G → ℂ) - (d : ℂ) • hC.nuZeta := by
    rw [hC.nuRow_sub_smul_nuZeta hk, hsplit, map_sub, map_zsmul, hC.nuZeta_def]
    simp only [Submodule.coe_sub, SetLike.val_smul]
    rw [show (d : ℂ) • (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ)
      = d • (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ) from
        Int.cast_smul_eq_zsmul _ _ _]
  exact sub_left_injective key

include hC in
theorem nuRow_mem_virtualChars {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    hC.nuRow hk ∈ virtualChars G := by
  rw [hC.nuRow_eq_nu hk]; exact (ν _).2

include hC in
theorem nuRow_mem_classFun {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    hC.nuRow hk ∈ classFun G :=
  mem_classFun_of_mem_span_Irr (mem_span_Irr_of_mem_virtualChars (hC.nuRow_mem_virtualChars hk))

include hC in
theorem cfInner_nuZeta_nuRow {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    cfInner hC.nuZeta (hC.nuRow hk) = 0 := by
  rw [hC.nuZeta_def, hC.nuRow_eq_nu hk, hC.nu_inner]
  exact h.cfInner_primeTIrow_eq_zero hC.local_data.isometry hC.local_data.mem_indFam
    hC.local_data.mem_Irr hC.local_data.apply_one k

include hC in
theorem nuRow_apply_eq_zero_of_mem_cyclicTIDiff {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂)
    {v : G} (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype)) : hC.nuRow hk v = 0 := by
  have hW2K : W₂.map L.subtype ≤ K.map L.subtype := Subgroup.map_mono h.right_le
  have hW1K : W₁.map L.subtype ⊓ K.map L.subtype = ⊥ := by
    rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]
  have hvK : v ∉ K.map L.subtype :=
    notMem_map_subtype_of_mem_cyclicTIDiff hC.isCyclicTIPair hW2K hW1K hv
  have hvL : v ∈ L := Subgroup.map_subtype_le _ (mem_cyclicTIDiff.1 hv).1
  have hvK' : (⟨v, hvL⟩ : ↥L) ∉ K := fun hc => hvK ⟨⟨v, hvL⟩, hc, rfl⟩
  set f : ↥L → ℂ := h.primeTIrow σ k - (d : ℂ) • ζ with hf
  have hfz : f ∈ charSpanZero (indFam K (Irr ↥K \ {1})) :=
    primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hk
  have hfD : f ∈ dadeDomain L A :=
    mem_dadeDomain_of_mem_dadeZDomain (hC.mem_dadeZDomain_of_mem_charSpanZero hfz)
  have hval : (ν ⟨f, charSpanZero_le _ hfz⟩ : G → ℂ) v = f ⟨v, hvL⟩ := by
    rw [hC.nu_eq_tau ⟨f, charSpanZero_le _ hfz⟩ ⟨f, hfD⟩ rfl]
    exact dadeMap_apply_mem hC.isDadeData ⟨f, hfD⟩ (hC.cyclicTIDiff_subset_param hv)
  have hf0 : f ⟨v, hvL⟩ = 0 := by
    have hM : h.primeTIrow σ k ⟨v, hvL⟩ = 0 :=
      eq_zero_of_mem_indFam_of_notMem K (primeTIrow_mem_indFam_sdiff hC.local_data hk) hvK'
    have hz : ζ ⟨v, hvL⟩ = 0 :=
      eq_zero_of_mem_indFam_of_notMem K hC.local_data.mem_indFam hvK'
    simp [hf, hM, hz]
  have hkey := congrFun (hC.nuRow_sub_smul_nuZeta hk) v
  rw [hval, hf0] at hkey
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hC.nuZeta_apply_eq_zero_of_mem_cyclicTIDiff hv, mul_zero, sub_zero] at hkey
  exact hkey

include hC in
theorem cfInner_tauBridge_nuRow (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.tauBridge i hj) (hC.nuRow hj) = 1 := by
  classical
  have hf := primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hj
  have hcoh : cfInner (hC.tauBridge i hj) (hC.nuRow hj - (d : ℂ) • hC.nuZeta)
      = 1 + (d : ℂ) * (n : ℂ) := by
    rw [hC.nuRow_sub_smul_nuZeta hj, hC.cfInner_tauBridge_nu i hj hf, cfInner_sub_right,
      cfInner_smul_right, h.cfInner_primeTIbridge_primeTIrow hC.local_data i j j,
      h.cfInner_primeTIbridge_zeta hC.local_data i j, if_pos rfl, if_neg (Ne.symm hj),
      map_intCast]
    ring
  rw [cfInner_sub_right, cfInner_smul_right, hC.cfInner_tauBridge_nuZeta i hj, map_intCast] at hcoh
  linear_combination hcoh

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem tauBridge_eq_etaLocal (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.tauBridge i hj
      = (δ : ℂ) • (hC.etaLocal i j - hC.etaLocal i (principalIrr ↥W₂)) - (n : ℂ) • hC.nuZeta := by
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  rw [hC.tau_primeTIbridge_eq i hj, hC.etaLocal_def, hC.etaLocal_def, irrMapSubtype_principal]

include hC in
theorem cfInner_nuRow_etaLocal_sub (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.nuRow hj) (hC.etaLocal i j)
      - cfInner (hC.nuRow hj) (hC.etaLocal i (principalIrr ↥W₂)) = (δ : ℂ) := by
  have h1 := hC.cfInner_tauBridge_nuRow i hj
  rw [hC.tauBridge_eq_etaLocal i hj, cfInner_sub_left, cfInner_smul_left, cfInner_smul_left,
    cfInner_sub_left, hC.cfInner_nuZeta_nuRow hj, mul_zero, sub_zero] at h1
  have hδ : (δ : ℂ) * (δ : ℂ) = 1 := hC.local_data.sign_sq
  have h2 : cfInner (hC.etaLocal i j) (hC.nuRow hj)
      - cfInner (hC.etaLocal i (principalIrr ↥W₂)) (hC.nuRow hj) = (δ : ℂ) := by
    linear_combination (δ : ℂ) * h1 - (cfInner (hC.etaLocal i j) (hC.nuRow hj)
      - cfInner (hC.etaLocal i (principalIrr ↥W₂)) (hC.nuRow hj)) * hδ
  have h3 := congrArg (starRingEnd ℂ) h2
  rw [map_sub, conj_cfInner, conj_cfInner, map_intCast] at h3
  exact h3

omit [K.Normal] [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem image_puncturedCore_subset :
    (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A := by
  rintro g ⟨x, ⟨hxK, hx1⟩, rfl⟩
  exact hC.image_subset
    ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hxK (by simpa using hx1), rfl⟩

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem nontrivial_indFam : (indFam K (Irr ↥K \ {1})).Nontrivial :=
  ⟨ζ, hC.local_data.mem_indFam, star ζ, hC.star_zeta_mem_indFam,
    (NormalInducedFamily.star_ne_self_of_odd hC.odd rfl hC.local_data.mem_indFam
      hC.local_data.mem_Irr).symm⟩

omit [Fintype G] [Fintype ↥L] [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] hC in
theorem index_eq_natCard_left (hyp : IsPrimeCyclicTIHyp K W₁ W₂) :
    (K.index : ℂ) = (Nat.card ↥W₁ : ℂ) := by
  rw [Subgroup.IsComplement'.index_eq_card hyp.isComplement'_left]

noncomputable def nuSpan
    (ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G) :
    Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ Submodule.span ℤ (Irr G) :=
  (Submodule.inclusion (virtualChars_le_span_Irr (G := G))).toAddMonoidHom.comp ν

omit [Fintype G] [K.Normal] [Fintype ↑(Irr ↥W₁)] in
theorem coe_nuSpan (f : Submodule.span ℤ (indFam K (Irr ↥K \ {1}))) :
    ((nuSpan ν f : Submodule.span ℤ (Irr G)) : G → ℂ) = (ν f : G → ℂ) := (rfl)

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem cfInner_nu_one {ξ : ↥L → ℂ} (hξ : ξ ∈ indFam K (Irr ↥K \ {1})) :
    cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) (1 : G → ℂ) = 0 := by
  have key := NormalInducedFamily.cfInner_one_eq_zero_of_mem_indFam_sdiff (ν := nuSpan ν)
    (isDadeData_puncturedCore hC.isDadeData hC.image_puncturedCore_subset) rfl rfl
    (fun f g => by rw [coe_nuSpan, coe_nuSpan]; exact hC.nu_inner f g)
    (fun f F hfF => by
      rw [coe_nuSpan]
      exact coe_nu_eq_dadeMap_puncturedCore hC.isDadeData hC.image_puncturedCore_subset
        hC.nu_eq_tau f F hfF)
    hC.local_data.mem_indFam hC.local_data.mem_Irr
    (by rw [hC.local_data.apply_one, ← index_eq_natCard_left h])
    hC.nontrivial_indFam hξ
  rw [coe_nuSpan] at key
  exact key

include hC in
theorem cfInner_nuRow_one {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    cfInner (hC.nuRow hk) (1 : G → ℂ) = 0 := by
  rw [hC.nuRow_eq_nu hk]
  exact hC.cfInner_nu_one (primeTIrow_mem_indFam_sdiff hC.local_data hk)

include hC in
theorem cfInner_nuRow_etaLocal_exchange {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (i : Irr ↥W₁) (k : Irr ↥W₂) :
    cfInner (hC.nuRow hj) (hC.etaLocal i k)
        + cfInner (hC.nuRow hj) (hC.etaLocal (principalIrr ↥W₁) (principalIrr ↥W₂))
      = cfInner (hC.nuRow hj) (hC.etaLocal i (principalIrr ↥W₂))
        + cfInner (hC.nuRow hj) (hC.etaLocal (principalIrr ↥W₁) k) := by
  have key := hC.isCyclicTIPair.cfInner_prodCharEta_exchange hC.omega_isometry
    (hC.nuRow_mem_classFun hj) (fun x hx => hC.nuRow_apply_eq_zero_of_mem_cyclicTIDiff hj hx)
    (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k)
  rw [← irrMapSubtype_principal L W₁, ← irrMapSubtype_principal L W₂] at key
  exact key

include hC in
theorem nuRow_eq_smul_sum_etaLocal {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.nuRow hj = (δ : ℂ) • ∑ i : Irr ↥W₁, hC.etaLocal i j := by
  classical
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  set Q : G → ℂ := hC.nuRow hj with hQ
  set η : Irr ↥W₁ × Irr ↥W₂ → G → ℂ := fun p => hC.etaLocal p.1 p.2
  have hON : IsOrthonormalFamily η := hC.isOrthonormalFamily_etaLocal
  have hQmem : Q ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars (hC.nuRow_mem_virtualChars hj)
  obtain ⟨b, hb⟩ : ∃ b : Irr ↥W₁ × Irr ↥W₂ → ℤ, ∀ p, cfInner Q (η p) = (b p : ℂ) := by
    choose b hb using fun p : Irr ↥W₁ × Irr ↥W₂ => exists_int_cfInner_of_mem_span_Irr hQmem
      (mem_span_Irr_of_mem_virtualChars (hC.etaLocal_mem_virtualChars p.1 p.2))
    exact ⟨b, hb⟩
  have hcardI : (Fintype.card ↑(Irr ↥W₁) : ℤ) = (Nat.card ↥W₁ : ℤ) := by
    rw [← Nat.card_eq_fintype_card, h.isCyclicTIPair.card_Irr_left]
  have hQnorm : cfInner Q Q = (Fintype.card ↑(Irr ↥W₁) : ℂ) := by
    rw [hQ, hC.cfInner_self_nuRow hj]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hcardI.symm
  have hbound : ∑ p, b p ^ 2 ≤ (Fintype.card ↑(Irr ↥W₁) : ℤ) := by
    have hbes := sum_norm_sq_cfInner_le hON Q
    rw [hQnorm] at hbes
    simp only [Complex.natCast_re] at hbes
    have hrw : ∀ p ∈ (Finset.univ : Finset (Irr ↥W₁ × Irr ↥W₂)),
        ‖cfInner Q (η p)‖ ^ 2 = ((b p ^ 2 : ℤ) : ℝ) := by
      intro p _
      rw [hb p, Complex.norm_intCast]
      push_cast
      rw [sq_abs]
    rw [Finset.sum_congr rfl hrw] at hbes
    have : ((∑ p, b p ^ 2 : ℤ) : ℝ) ≤ ((Fintype.card ↑(Irr ↥W₁) : ℤ) : ℝ) := by
      push_cast at hbes ⊢
      exact hbes
    exact_mod_cast this
  have hdelta : ∀ i : Irr ↥W₁, b (i, j) - b (i, principalIrr ↥W₂) = δ := by
    intro i
    have hkey := hC.cfInner_nuRow_etaLocal_sub i hj
    rw [show cfInner Q (hC.etaLocal i j) = ((b (i, j) : ℤ) : ℂ) from hb (i, j),
      show cfInner Q (hC.etaLocal i (principalIrr ↥W₂))
        = ((b (i, principalIrr ↥W₂) : ℤ) : ℂ) from hb (i, principalIrr ↥W₂)] at hkey
    exact_mod_cast hkey
  have hdiff : ∀ i : Irr ↥W₁,
      b (i, j) - b (i, principalIrr ↥W₂) = 1 ∨ b (i, j) - b (i, principalIrr ↥W₂) = -1 := by
    intro i
    rcases hC.local_data.sign with hδ | hδ
    · exact Or.inl (by rw [hdelta i, hδ])
    · exact Or.inr (by rw [hdelta i, hδ])
  obtain ⟨hsat, hrowpair, hzero⟩ := sum_sq_eq_and_eq_zero_of_sum_sq_le hj hdiff hbound
  have hb00 : b (principalIrr ↥W₁, principalIrr ↥W₂) = 0 := by
    have h1 := hb (principalIrr ↥W₁, principalIrr ↥W₂)
    rw [show η (principalIrr ↥W₁, principalIrr ↥W₂) = (1 : G → ℂ) from hC.etaLocal_principal,
      hQ, hC.cfInner_nuRow_one hj] at h1
    exact_mod_cast h1.symm
  obtain ⟨k, hkj, hk0⟩ := exists_ne_ne_of_isPrimeCyclicTIHyp h j
  have hcol0 : ∀ i : Irr ↥W₁, b (i, principalIrr ↥W₂) = 0 := by
    intro i
    have hexch := hC.cfInner_nuRow_etaLocal_exchange hj i k
    rw [show cfInner Q (hC.etaLocal i k) = ((b (i, k) : ℤ) : ℂ) from hb (i, k),
      show cfInner Q (hC.etaLocal (principalIrr ↥W₁) (principalIrr ↥W₂))
        = ((b (principalIrr ↥W₁, principalIrr ↥W₂) : ℤ) : ℂ) from
          hb (principalIrr ↥W₁, principalIrr ↥W₂),
      show cfInner Q (hC.etaLocal i (principalIrr ↥W₂))
        = ((b (i, principalIrr ↥W₂) : ℤ) : ℂ) from hb (i, principalIrr ↥W₂),
      show cfInner Q (hC.etaLocal (principalIrr ↥W₁) k)
        = ((b (principalIrr ↥W₁, k) : ℤ) : ℂ) from hb (principalIrr ↥W₁, k)] at hexch
    have hint : b (i, k) + b (principalIrr ↥W₁, principalIrr ↥W₂)
        = b (i, principalIrr ↥W₂) + b (principalIrr ↥W₁, k) := by exact_mod_cast hexch
    rw [hzero i k hkj hk0, hzero (principalIrr ↥W₁) k hkj hk0, hb00] at hint
    omega
  have hcolj : ∀ i : Irr ↥W₁, b (i, j) = δ := by
    intro i
    have hd := hdelta i
    rw [hcol0 i] at hd
    omega
  have hproj : Q = ∑ p, ((b p : ℤ) : ℂ) • η p := by
    refine NormOnePivot.eq_sum_smul_of_cfInner_self_eq_sum_mul_conj hON hb ?_
    rw [hQnorm]
    have hconj : ∑ p, ((b p : ℤ) : ℂ) * (starRingEnd ℂ) ((b p : ℤ) : ℂ)
        = ((∑ p, b p ^ 2 : ℤ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun p _ => by simp [sq]
    rw [hconj, hsat]
    norm_num
  have hsingle : ∀ (i : Irr ↥W₁) (l : Irr ↥W₂), l ≠ j → ((b (i, l) : ℤ) : ℂ) • η (i, l) = 0 := by
    intro i l hlj
    by_cases hl0 : l = principalIrr ↥W₂
    · rw [hl0, hcol0 i]; simp
    · rw [hzero i l hlj hl0]; simp
  rw [hproj, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun l _ hlj => hsingle i l hlj, hcolj i]

include hC in
theorem nu_primeTIrow_eq {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    (ν ⟨h.primeTIrow σ j,
        Submodule.subset_span (primeTIrow_mem_indFam_sdiff hC.local_data hj)⟩ : G → ℂ)
      = (δ : ℂ) • ∑ i : Irr ↥W₁,
          hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j) := by
  rw [← hC.nuRow_eq_nu hj, hC.nuRow_eq_smul_sum_etaLocal hj]
  simp only [hC.etaLocal_def]

end IsUniformBridgeCoherenceData

end CFSG.FeitThompson
