module

public import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
public import CFSG.FeitThompson.Representations.ActualPairedSupportSaturation
import CFSG.FeitThompson.Representations.PairedSupportingKernelCollapse
import CFSG.FeitThompson.Representations.TypeThreeFourPrincipalRowProjection
import CFSG.FeitThompson.Representations.TypeIIIToVCoherenceFrobeniusPartner
public import CFSG.FeitThompson.Representations.TypeIIIVCoherentCrossedRowData
import CFSG.FeitThompson.Representations.CyclicTIColumnSumAxisNonvanishing
public import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
public import CFSG.FeitThompson.Representations.PrimeDadePrincipalRowSmallComplement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace RealBridgeLowFamily

open Subgroup CFSG.FeitThompson.Prep06
open scoped ComplexConjugate

universe u

theorem orderOf_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a
  simpa [MulAut.conj_apply] using this.symm

theorem not_isConj_of_mem_mixedSupport {G : Type*} [Group G] [Finite G]
    {S U W₁ W₂ D : Subgroup G} (hcS : IsWitnessedPConfiguration S U W₁ W₂) {k : ℕ}
    (hH : Nat.card (CFSG.FeitThompson.Prep03.hallCoreIn S) = Nat.card W₂ ^ k)
    (hcop : (Nat.card W₂).Coprime (Nat.card D)) {a v : G}
    (ha : a ∈ CFSG.FeitThompson.Prep03.mixedSupport S W₁ W₂) (hv : v ∈ (D : Set G) \ {1}) :
    ¬ IsConj a v := by
  intro hav
  have hord := orderOf_eq_of_isConj hav
  have hvD : orderOf v ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hv.1
  have hcopv : (Nat.card W₂).Coprime (orderOf a) := hord ▸ Nat.Coprime.coprime_dvd_right hvD hcop
  rcases ha with ⟨haH, ha1⟩ | ha
  · have h1 : orderOf a ∣ Nat.card W₂ ^ k := hH ▸ Subgroup.orderOf_dvd_natCard _ haH
    have h2 : orderOf a = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcopv).symm h1
    exact ha1 (orderOf_eq_one_iff.1 h2)
  · simp only [CFSG.FeitThompson.Prep03.cyclicTIsetConjIn, CFSG.FeitThompson.Prep03.conjSet,
      Set.mem_iUnion, Set.mem_image] at ha
    obtain ⟨s, -, z, hz, rfl⟩ := ha
    have hzord : orderOf (s⁻¹ * z * s) = orderOf z := by
      have := orderOf_eq_of_isConj (isConj_iff.2 ⟨s⁻¹, rfl⟩ : IsConj z (s⁻¹ * z * s⁻¹⁻¹))
      simpa using this.symm
    rw [hzord] at hcopv
    rw [mem_cyclicTIset] at hz
    obtain ⟨hzW, hz1, hz2⟩ := hz
    have hzW' : z ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := hzW
    rw [hcS.coe_sup_W₁_W₂] at hzW'
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 hzW'
    set n := orderOf (x * y)
    have hpow : (x * y) ^ n = 1 := pow_orderOf_eq_one _
    rw [(hcS.commute_W₁_W₂ hx hy).mul_pow] at hpow
    have hyn : y ^ n ∈ W₁ ⊓ W₂ := by
      refine Subgroup.mem_inf.2 ⟨?_, pow_mem (show y ∈ W₂ from hy) n⟩
      have : y ^ n = (x ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]; exact inv_mem (pow_mem (show x ∈ W₁ from hx) n)
    rw [hcS.inf_W₁_W₂, Subgroup.mem_bot] at hyn
    have hyp : y ^ Nat.card W₂ = 1 := by
      have := Subgroup.orderOf_dvd_natCard W₂ hy
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hy1 : y = 1 := by
      have := pow_gcd_eq_one.2 ⟨hyp, hyn⟩
      rwa [hcopv, pow_one] at this
    subst hy1
    exact hz1 (by simpa using hx)

theorem cfInner_eq_zero_of_forall_cfInner_eq {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (hn : 2 ≤ n) {v : Fin n → G → ℂ} (hv : IsOrthonormalFamily v)
    (hvspan : ∀ i, v i ∈ Submodule.span ℤ (Irr G)) {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hf1 : cfInner f f = 1)
    (hconst : ∀ i j, cfInner (v i) f = cfInner (v j) f) (i : Fin n) :
    cfInner (v i) f = 0 := by
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr (hvspan i) hf
  have hb := sum_norm_sq_cfInner_le_re hv f
  have hk : ∀ k, ‖cfInner f (v k)‖ ^ 2 = ((m : ℝ)) ^ 2 := by
    intro k
    rw [← conj_cfInner, hconst k i, hm, map_intCast, Complex.norm_intCast, sq_abs]
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hf1,
    Complex.one_re] at hb
  rw [hm]
  by_contra hne
  have hm0 : m ≠ 0 := fun h => hne (by simp [h])
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ m ^ 2 := by rcases lt_or_gt_of_ne hm0 with h | h <;> nlinarith
    exact_mod_cast this
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem eq_conj_of_add_conj_eq {G : Type*} [Group G] [Fintype G] (hodd : Odd (Nat.card G))
    {X Y : G → ℂ} (hX : X ∈ signedIrr G) (hY : Y ∈ signedIrr G)
    (hY1 : cfInner Y (1 : G → ℂ) = 0) (hYX : cfInner Y X = 0)
    (hsum : X + (fun g => conj (X g)) = Y + (fun g => conj (Y g))) :
    Y = fun g => conj (X g) := by
  obtain ⟨ε, hε, χ, hχ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hY
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    rw [cfInner_smul_left, cfInner_self_of_mem_Irr one_mem_Irr] at hY1
    rcases hε with rfl | rfl <;> norm_num at hY1
  have hχc := ne_conj_of_mem_Irr_of_ne_one_of_odd hodd hχ hχ1
  have hYY : cfInner (ε • χ) (fun g => conj ((ε • χ) g)) = 0 := by
    have : (fun g => conj ((ε • χ) g)) = (conj ε) • fun g => conj (χ g) := by
      funext g; simp
    rw [this, cfInner_smul_left, cfInner_smul_right, cfInner_eq_zero_of_mem_Irr hχ
      (conj_mem_Irr hχ) hχc]
    simp
  have hεε : ε * conj ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hYnorm : cfInner (ε • χ) (ε • χ) = 1 := by
    rw [cfInner_smul_left, cfInner_smul_right, cfInner_self_of_mem_Irr hχ, mul_one, hεε]
  obtain ⟨ε', hε', χ', hχ', rfl⟩ := mem_signedIrr_iff_exists_sign.1 hX
  have hXnorm : cfInner (ε' • χ') (ε' • χ') = 1 := by
    have hεε' : ε' * conj ε' = 1 := by rcases hε' with rfl | rfl <;> simp
    rw [cfInner_smul_left, cfInner_smul_right, cfInner_self_of_mem_Irr hχ', mul_one, hεε']
  set X := ε' • χ' with hXdef
  set Y := ε • χ with hYdef
  have h1 : cfInner Y (fun g => conj (X g)) = 1 := by
    have h2 : cfInner Y (X + fun g => conj (X g)) = 1 := by
      rw [hsum, cfInner_add_right, hYnorm, hYY, add_zero]
    rw [cfInner_add_right, hYX, zero_add] at h2
    exact h2
  have h3 : cfInner (fun g => conj (X g)) (fun g => conj (X g)) = 1 := by
    rw [cfInner_conj_conj, hXnorm, map_one]
  have h4 : cfInner (fun g => conj (X g)) Y = 1 := by rw [← conj_cfInner, h1, map_one]
  have h5 : cfInner (Y - fun g => conj (X g)) (Y - fun g => conj (X g)) = 0 := by
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hYnorm, h1, h4, h3]; ring
  exact sub_eq_zero.1 (cfInner_self_eq_zero.1 h5)

theorem dadeTau_sub {G : Type*} [Group G] [Finite G] (M W₁ W₂ : Subgroup G) (f g : ↥M → ℂ) :
    dadeTau M W₁ W₂ (f - g) = dadeTau M W₁ W₂ f - dadeTau M W₁ W₂ g := by
  rw [dadeTau_eq, dadeTau_eq, dadeTau_eq, sub_eq_add_neg, dadeMapFun_add, dadeMapFun_neg,
    ← sub_eq_add_neg]

theorem dadeTau_star {G : Type*} [Group G] [Finite G] (M W₁ W₂ : Subgroup G) (f : ↥M → ℂ) :
    dadeTau M W₁ W₂ (star f) = star (dadeTau M W₁ W₂ f) := by
  rw [dadeTau_eq, dadeTau_eq, dadeMapFun_star]

theorem dadeTau_eq_indClassFun_of_typeIII
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_full_support_ti_induction.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsMinimalOddSimple G)
    {T V W₁ W₂ : Subgroup G} (hT : IsCoatom T) (hIII : IsTypeIII T)
    (hc : IsWitnessedPConfiguration T V W₂ W₁) {f : ↥T → ℂ} (hf : f ∈ classFun ↥T)
    (hvan : ∀ z : ↥T, (z : G) ∉ ((⁅T, T⁆ : Subgroup G) : Set G) \ {1} → f z = 0) :
    dadeTau T W₂ W₁ f = indClassFun T f := by
  have hG5 := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  obtain ⟨-, -, -, -, hind⟩ := h₄ G hG5 T V W₂ W₁ hT hIII hc _ rfl
  have := hind f (CFSG.FeitThompson.Proofs.Recip.isClassFun_of_mem hf)
    (fun z hz => hvan z fun hz' => hz (Or.inl hz'))
  rw [← tauDerived_eq_dadeTau, this, CFSG.FeitThompson.Prep05.indToTop]
  congr 1
  exact Subsingleton.elim _ _

attribute [local instance] CFSG.FeitThompson.Proofs.subgroupFintype in
theorem exists_isSigmaMap_sign_mem_Irr {G : Type u} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) {S U W₁ W₂ : Subgroup G}
    (hcS : IsWitnessedPConfiguration S U W₁ W₂) :
    ∃ σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ), CFSG.FeitThompson.IsSigmaMap S W₁ W₂ σ ∧
      ∀ (b : Irr ↥W₂) (f : ↥(W₁ ⊔ W₂) → ℂ),
        (∀ (x y : G) (_hx : x ∈ W₁) (hy : y ∈ W₂) (hxy : x * y ∈ W₁ ⊔ W₂),
          f ⟨x * y, hxy⟩ = (b : ↥W₂ → ℂ) ⟨y, hy⟩) →
        ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧ δ • σ f ∈ Irr ↥S := by
  have : Fintype G := Fintype.ofFinite G
  have h1 : W₁ ≤ S := hcS.le_M_W₁
  have h2 : W₂ ≤ S := hcS.le_M_W₂
  have hWpair : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := CrossedRowData.isCyclicTIPair_sup hodd hcS
  have hcyc : IsCyclic ↥(W₁ ⊔ W₂) := hWpair.isCyclic
  have hPC := hcS.isPrimeCyclicTIHyp_subgroupOf hodd
  obtain ⟨τ, hτ⟩ := hPC.exists_isCyclicTIIsometry
  refine ⟨CFSG.FeitThompson.Proofs.Recip.sigmaT h1 h2 hcyc τ,
    CFSG.FeitThompson.Proofs.Recip.isSigmaMap_sigmaT h1 h2 hcyc hτ, ?_⟩
  intro b f hf
  have hpp : (principalIrr ↥(W₁.subgroupOf S))
      = CFSG.FeitThompson.Proofs.Recip.irrSub h1 (principalIrr ↥W₁) := by
    apply Subtype.ext
    funext y
    rw [CFSG.FeitThompson.Proofs.Recip.coe_irrSub, coe_principalIrr, coe_principalIrr]
    rfl
  have hkey := CFSG.FeitThompson.Proofs.Recip.pullCF_prodChar h1 h2 hcyc hPC.isCyclicTIPair
    (principalIrr ↥W₁) b f (fun x y hx hy hxy => by
      rw [hf x y hx hy hxy, coe_principalIrr]; simp)
  refine ⟨hPC.primeTISign τ (CFSG.FeitThompson.Proofs.Recip.irrSub h2 b),
    hPC.primeTISign_eq_one_or_eq_neg_one _, ?_⟩
  have heq : hPC.primeTISign τ (CFSG.FeitThompson.Proofs.Recip.irrSub h2 b) •
      CFSG.FeitThompson.Proofs.Recip.sigmaT h1 h2 hcyc τ f
      = hPC.primeTIirr τ (principalIrr ↥(W₁.subgroupOf S))
          (CFSG.FeitThompson.Proofs.Recip.irrSub h2 b) := by
    rw [hPC.primeTIirr_principal_left, CFSG.FeitThompson.Proofs.Recip.sigmaT_apply, hkey, ← hpp]
  rw [heq]
  exact hPC.primeTIirr_principal_left_mem_Irr hτ _

open scoped Classical in
attribute [local instance] CFSG.FeitThompson.Proofs.subgroupFintype in
theorem exists_bridge_of_actualBridgeRemainder
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_actual_bridge_remainder.{u})
    {G : Type u} [Group G] [Fintype G] (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G)
    {S U W₁ W₂ : Subgroup G} (hS : IsCoatom S) (hcS : IsWitnessedPConfiguration S U W₁ W₂)
    (hW' : IsCyclicTIPair (W₂ ⊔ W₁) W₂ W₁) [instW : Fintype ↥(W₂ ⊔ W₁)]
    {τ' : ↥(classFun ↥(W₂ ⊔ W₁)) →ₗ[ℂ] ↥(classFun G)}
    (hτ₀ : IsCyclicTIIsometry (W₂ ⊔ W₁) W₂ W₁ τ') :
    ∃ j₀ : Irr ↥W₂, j₀ ≠ principalIrr ↥W₂ ∧ ∃ Γ : G → ℂ,
      Γ ∈ Submodule.span ℤ (Irr G) ∧ (∀ g, (Γ g).im = 0) ∧ cfInner Γ (1 : G → ℂ) = 0 ∧
      cfInner ((1 : G → ℂ) - hW'.prodCharEta τ' j₀ (principalIrr ↥W₁) + Γ)
          ((1 : G → ℂ) - hW'.prodCharEta τ' j₀ (principalIrr ↥W₁) + Γ) =
        ((((Nat.card U : ℝ) - 1) / (Nat.card W₁ : ℝ) : ℝ) : ℂ) + 2 ∧
      ∀ x : G, (∀ a ∈ CFSG.FeitThompson.Prep03.mixedSupport S W₁ W₂, ¬ IsConj x a) →
        ((1 : G → ℂ) - hW'.prodCharEta τ' j₀ (principalIrr ↥W₁) + Γ) x = 0 := by
  have hτ' : @IsCyclicTIIsometry G _ _ (W₂ ⊔ W₁) W₂ W₁
      (CFSG.FeitThompson.Proofs.subgroupFintype _) τ' := by
    convert hτ₀
  clear instW hτ₀
  have hodd := hG.odd
  have hamb : CFSG.FeitThompson.Prep03.IsAmbient G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hconf : CFSG.FeitThompson.Prep03.IsPConfigSetup G S U W₁ W₂ := ⟨hamb, hS, hcS⟩
  set eI := Finite.equivFin (Irr ↥W₁) with heI
  set eJ := Finite.equivFin (Irr ↥W₂) with heJ
  set α : Fin (Nat.card (Irr ↥W₁)) → ↥W₁ → ℂ := fun i => (eI.symm i : ↥W₁ → ℂ) with hα
  set β : Fin (Nat.card (Irr ↥W₂)) → ↥W₂ → ℂ := fun j => (eJ.symm j : ↥W₂ → ℂ) with hβ
  set i0 := eI (principalIrr ↥W₁) with hi0
  set j0' := eJ (principalIrr ↥W₂) with hj0'
  set w : Fin (Nat.card (Irr ↥W₁)) → Fin (Nat.card (Irr ↥W₂)) → ↥(W₁ ⊔ W₂) → ℂ :=
    fun i j z => hW'.prodChar (β j) (α i) (MulEquiv.subgroupCongr (sup_comm W₁ W₂) z) with hw
  have hwprod : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y := by
    intro i j x y z hz
    have hz' : (MulEquiv.subgroupCongr (sup_comm W₁ W₂) z : ↥(W₂ ⊔ W₁))
        = ⟨(y : G) * (x : G), mul_mem (hW'.left_le y.2) (hW'.right_le x.2)⟩ := by
      apply Subtype.ext
      rw [MulEquiv.subgroupCongr_apply, hz]
      exact (hcS.commute_W₁_W₂ x.2 y.2).eq
    simp only [hw]
    rw [hz', hW'.prodChar_apply_mul _ _ y.2 x.2, mul_comm]
  have hα0 : α i0 = 1 := by
    simp only [hα, hi0]; rw [Equiv.symm_apply_apply, coe_principalIrr]
  have hβ0 : β j0' = 1 := by
    simp only [hβ, hj0']; rw [Equiv.symm_apply_apply, coe_principalIrr]
  have hcyc' : IsCyclic ↥(W₂ ⊔ W₁) := hW'.isCyclic
  set ω := CFSG.FeitThompson.Proofs.Recip.omegaR (PairedSupportingKernel.omegaUnbundled hcyc' τ')
    with hωdef
  have hω : CFSG.FeitThompson.IsOmegaMap W₁ W₂ ω := CFSG.FeitThompson.Proofs.Recip.isOmegaMap_omegaR
    (PairedSupportingKernel.isOmegaMap_omegaUnbundled hcyc' hτ')
  have hωw : ∀ i j, ω (w i j) = hW'.prodCharEta τ' (eJ.symm j) (eI.symm i) := by
    intro i j
    rw [hωdef, CFSG.FeitThompson.Proofs.Recip.omegaR_apply, PairedSupportingKernel.omegaUnbundled_apply,
      IsCyclicTIPair.prodCharEta_eq_coe_apply]
    congr 2
    apply Subtype.ext
    rw [IsCyclicTIPair.coe_basisProdIrr_apply]
    funext z
    simp only [hw, Function.comp_apply]
    rfl
  obtain ⟨σ, hσ, hsign⟩ := exists_isSigmaMap_sign_mem_Irr hodd hcS
  have hsign' : ∀ j, ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧ δ • σ (w i0 j) ∈ Irr ↥S := by
    intro j
    refine hsign (eJ.symm j) (w i0 j) (fun x y hx hy hxy => ?_)
    rw [hwprod i0 j ⟨x, hx⟩ ⟨y, hy⟩ ⟨x * y, hxy⟩ rfl, hα0]
    simp [hβ]
  choose δ hδ hμ using hsign'
  have hWS : W₁ ⊔ W₂ ≤ S := hcS.le_M_sup_W₁_W₂
  set γ : ↥S → ℂ := indClassFun (((CFSG.FeitThompson.Prep03.hallCoreIn S) ⊔ W₁).subgroupOf S)
    (fun _ => (1 : ℂ)) with hγ
  set μ : Fin (Nat.card (Irr ↥W₂)) → ↥S → ℂ := fun j => δ j • σ (w i0 j) with hμdef
  set bb : Fin (Nat.card (Irr ↥W₂)) → ↥S → ℂ := fun j => γ - μ j with hbb
  set η : Fin (Nat.card (Irr ↥W₁)) → Fin (Nat.card (Irr ↥W₂)) → G → ℂ :=
    fun i j => ω (w i j) with hη
  have key := h₁ G hamb S U W₁ W₂ hconf (Nat.card U) (Nat.card W₂) (Nat.card W₁) rfl rfl rfl
    (Fin (Nat.card (Irr ↥W₁))) (Fin (Nat.card (Irr ↥W₂))) inferInstance inferInstance i0 j0'
    α β (fun i => (eI.symm i).2) (fun j => (eJ.symm j).2)
    (fun a b hab => eI.symm.injective (Subtype.ext hab))
    (fun a b hab => eJ.symm.injective (Subtype.ext hab))
    (fun χ hχ => ⟨eI ⟨χ, hχ⟩, by simp only [hα]; rw [Equiv.symm_apply_apply]⟩)
    (fun χ hχ => ⟨eJ ⟨χ, hχ⟩, by simp only [hβ]; rw [Equiv.symm_apply_apply]⟩)
    hα0 hβ0
    w hwprod (⇑σ) (fun f x => ω f x) (CFSG.FeitThompson.Proofs.isTIExtension_sigma hWS hσ)
    (CFSG.FeitThompson.Proofs.isTIExtension_omega hω) δ μ η hδ (fun j => rfl) hμ (fun i j => rfl)
    (fun _ => γ) bb (fun _ => rfl) (fun _ => rfl)
  obtain ⟨hfirst, -, hrest⟩ := key
  obtain ⟨jj, hjj⟩ := exists_ne_principalIrr hcS.ne_bot_W₂ hcS.isCyclic_W₂
  have hne : eJ jj ≠ j0' := fun h => hjj (eJ.injective h)
  obtain ⟨hΓv, hΓreal, hΓ1, hlast⟩ := hrest (eJ jj) hne _ rfl
  obtain ⟨hdec, hnorm, -⟩ := hlast (eJ jj) hne
  have hbsupp := (hfirst (eJ jj) hne).2.2.2.1
  have hηeq : η i0 (eJ jj) = hW'.prodCharEta τ' jj (principalIrr ↥W₁) := by
    simp only [hη]; rw [hωw, Equiv.symm_apply_apply, hi0, Equiv.symm_apply_apply]
  have hBeq : CFSG.FeitThompson.Prep03.indG S (bb (eJ jj))
      = (1 : G → ℂ) - hW'.prodCharEta τ' jj (principalIrr ↥W₁)
        + (CFSG.FeitThompson.Prep03.indG S (bb (eJ jj)) - 1 + η i0 (eJ jj)) := by
    rw [hηeq]; abel
  refine ⟨jj, hjj, CFSG.FeitThompson.Prep03.indG S (bb (eJ jj)) - 1 + η i0 (eJ jj),
    mem_span_Irr_of_mem_virtualChars hΓv, fun g => Complex.conj_eq_iff_im.1 (hΓreal g), hΓ1,
    ?_, ?_⟩
  · rw [← hBeq, hnorm]; push_cast; ring
  · intro x hx
    rw [← hBeq]
    exact indClassFun_apply_eq_zero_of_forall_not_isConj S hbsupp hx

set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem exists_low_family_of_typeIII
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_full_support_ti_induction.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsMinimalOddSimple G)
    {T V W₁ W₂ : Subgroup G} (hT : IsCoatom T) (hIII : IsTypeIII T)
    (hc : IsWitnessedPConfiguration T V W₂ W₁) (hW : IsCyclicTIPair (W₂ ⊔ W₁) W₂ W₁)
    {ω : ↥(classFun ↥(W₂ ⊔ W₁)) →ₗ[ℂ] ↥(classFun G)}
    (hω : IsCyclicTIIsometry (W₂ ⊔ W₁) W₂ W₁ ω) :
    ∃ v : Fin (Nat.card (indFamKer T (derivedOf T)
        ((Prep06.hallCoreIn T ⊔ (V ⊓ centralizer ((Prep06.hallCoreIn T : Subgroup G) : Set G)) :
          Subgroup G).subgroupOf T))) → G → ℂ,
      IsOrthonormalFamily v ∧ (∀ i, v i ∈ signedIrr G) ∧
      (∀ i a b, IsOrthogonal (v i) (hW.prodCharEta ω a b)) ∧
      ∀ i, ∃ Δ : G → ℂ, Δ ∈ Submodule.span ℤ (Irr G) ∧ (∀ g, (Δ g).im = 0) ∧
        IsOrthogonal Δ (1 : G → ℂ) ∧
        (∀ a b, cfInner ((1 : G → ℂ) - v i + Δ) (hW.prodCharEta ω a b) =
          if a = principalIrr ↥W₂ then 1 else 0) ∧
        ∀ x : G, ((1 : G → ℂ) - v i + Δ) x ≠ 0 →
          ∃ c ∈ ((⁅T, T⁆ : Subgroup G) : Set G) \ {1}, IsConj x c := by
  have hfin : Finite G := Finite.of_fintype G
  have hodd := hG.odd
  have : Fintype ↑(Irr ↥(W₂.subgroupOf T)) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn : (derivedOf T).Normal := h.normal
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  set w : ↑(Irr ↥(W₂.subgroupOf T)) → ↑(Irr ↥(W₁.subgroupOf T)) →
      ↥(classFun ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T)) :=
    fun i j => h.isCyclicTIPair.basisProdIrr (i, j) with hw
  set l : ↑(Irr ↥(W₂.subgroupOf T)) → ↥T → ℂ := fun i => h.inflateLeft i with hl
  have hrowD : IsRowData T W₂ W₁ σ w l := by
    refine { isometry := hσ, prod := ?_, infl := ?_ }
    · intro i j x y z hz
      rw [hw, h.isCyclicTIPair.coe_basisProdIrr_apply]
      have h6 := h.isCyclicTIPair.prodChar_apply_mul (i : ↥(W₂.subgroupOf T) → ℂ)
        (j : ↥(W₁.subgroupOf T) → ℂ) x.2 y.2
      convert h6 using 2
      exact Subtype.ext hz
    · intro i k v z hz
      subst hz
      exact h.inflateLeft_apply_mul i k.2 v.2
  set sg : ↑(Irr ↥(W₁.subgroupOf T)) → ℂ := fun j => h.primeTISign σ j with hsg
  set mu : ↑(Irr ↥(W₂.subgroupOf T)) → ↑(Irr ↥(W₁.subgroupOf T)) → ↥T → ℂ :=
    fun i j => h.primeTIirr σ i j with hmu
  have hsetup : IsRowSetup T W₂ W₁ σ w l sg mu := by
    refine { toIsRowData := hrowD, sign := ?_, mu_zero_mem := ?_, mu_eq := ?_ }
    · intro j; exact h.primeTISign_eq_one_or_eq_neg_one j
    · intro j
      have h4 := h.primeTIirr_principal_left_mem_Irr hσ j
      rw [h.primeTIirr_principal_left] at h4
      exact h4
    · intro i j
      change h.primeTIirr σ i j = _
      rw [h.primeTIirr_eq_mul i j, h.primeTIirr_principal_left]
  have hrowsum : ∀ j, (∑ᶠ i : ↑(Irr ↥(W₂.subgroupOf T)), mu i j) = h.primeTIrow σ j := by
    intro j
    rw [finsum_eq_sum_of_fintype, h.primeTIrow_def]
  have heta := isEtaSetup_basisProdIrr hW hω
  set C : Subgroup G := V ⊓ centralizer ((Prep06.hallCoreIn T : Subgroup G) : Set G) with hCdef
  set S₁ := indFamKer T (derivedOf T) ((Prep06.hallCoreIn T ⊔ C : Subgroup G).subgroupOf T) with hS₁def
  set S₂ := indFamDetectKer T (derivedOf T) (C.subgroupOf T) ((Prep06.hallCoreIn T).subgroupOf T)
    with hS₂def
  obtain ⟨-, -, -, -, hS₁star, -, -, hcoh₁, -, -, hS₁Irr, hS₁deg, n₁, hn₁card, -, hn₁2,
    -⟩ := CFSG.FeitThompson.Proofs.FPF_type_iii_iv_two_coherent_layers h₅ h₆ h₇ h₈ h₉ G hG T V W₂ W₁
      hT (Or.inl hIII) hc C rfl S₁ S₂ rfl rfl
  obtain ⟨hproj, -⟩ := CFSG.FeitThompson.Proofs.FPF_type_iii_iv_principal_row_projection h₅ h₆ h₇ h₈ h₉
    G hG T V W₂ W₁ hT (Or.inl hIII) hc σ w l sg mu hsetup ω _ _ heta
  obtain ⟨-, -, -, hD, -⟩ := h₇ G hG T V W₂ W₁ hT (by tauto) hc
  have hA := CrossedRowData.image_primeTIbridgeSupport_subset_dadeA0 hc
  have hA0 : ∀ x ∈ derivedOf T, x ≠ 1 → (x : G) ∈ dadeA0 T W₂ W₁ := fun x hx hx1 =>
    hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hx hx1, rfl⟩
  have hcard1 : Nat.card ↥(W₂.subgroupOf T) = Nat.card ↥W₂ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₁
  have hS₁ind : S₁ ⊆ indFam (derivedOf T) (Irr ↥(derivedOf T) \ {1}) := by
    intro f hf
    have := indFamKer_subset_indFamNonprincipal T _ _ hf
    rwa [indFamNonprincipal_eq_indFam_sdiff] at this
  have hTodd : Odd (Nat.card ↥T) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card T)
  have hS₁fin : Finite ↑S₁ := Nat.finite_of_card_ne_zero (by omega)
  set e := Finite.equivFin ↑S₁ with he
  set ζ : Fin (Nat.card ↑S₁) → ↥T → ℂ := fun i => ((e.symm i : ↑S₁) : ↥T → ℂ) with hζdef
  have hζmem : ∀ i, ζ i ∈ S₁ := fun i => (e.symm i).2
  have hζinj : ∀ i j, ζ i = ζ j → i = j := fun i j hij =>
    e.symm.injective (Subtype.ext hij)
  have hζ1 : ∀ i, ζ i 1 = (Nat.card ↥(W₂.subgroupOf T) : ℂ) := fun i => by
    rw [hcard1]; exact hS₁deg _ (hζmem i)
  obtain ⟨ν, hνiso, hντ⟩ := hcoh₁
  set vv : Fin (Nat.card ↑S₁) → G → ℂ :=
    fun i => ((ν ⟨ζ i, Submodule.subset_span (hζmem i)⟩ : virtualChars G) : G → ℂ) with hvvdef
  set M₀ : ↥T → ℂ := h.primeTIrow σ (principalIrr ↥(W₁.subgroupOf T)) with hM₀
  set ψ : Fin (Nat.card ↑S₁) → G → ℂ := fun i => dadeTau T W₂ W₁ (M₀ - ζ i) with hψdef
  have hζind : ∀ i, ζ i ∈ indFam (derivedOf T) (Irr ↥(derivedOf T) \ {1}) :=
    fun i => hS₁ind (hζmem i)
  have hζIrr : ∀ i, ζ i ∈ Irr ↥T := fun i => hS₁Irr (hζmem i)
  have hψη : ∀ i (a : ↑(Irr ↥W₂)) (b : ↑(Irr ↥W₁)),
      cfInner (ψ i) (hW.prodCharEta ω a b) = if a = principalIrr ↥W₂ then 1 else 0 := by
    intro i a b
    have h0 := hproj (ζ i) (hζmem i) a b
    rw [hrowsum, cfInner_sub_left, sub_eq_zero, finsum_eq_sum_of_fintype,
      cfInner_sum_left] at h0
    change cfInner (ψ i) _ = _ at h0
    rw [h0]
    simp_rw [hW.cfInner_prodCharEta hω]
    by_cases hi : a = principalIrr ↥W₂
    · subst hi; simp
    · simp [Ne.symm hi, hi]
  have hF : ∀ i, M₀ - ζ i ∈ dadeDomain T (dadeA0 T W₂ W₁) := fun i =>
    mem_dadeDomain.2 ⟨mem_classFun_of_mem_span_Irr (h.primeTIrow_sub_mem_span_Irr hσ (hζind i)),
      fun x hx => h.primeTIrow_sub_apply_eq_zero hσ (hζind i) (hζ1 i)
        fun hmem => hx (hA0 x hmem.1 hmem.2)⟩
  have hψspan : ∀ i, ψ i ∈ Submodule.span ℤ (Irr G) := by
    intro i
    have := hD.dadeMap_mem_span_Irr (hF i) (h.primeTIrow_sub_mem_span_Irr hσ (hζind i))
    rwa [coe_dadeMap, ← dadeTau_eq] at this
  have hvspan : ∀ i, vv i ∈ Submodule.span ℤ (Irr G) := fun i => coe_mem_span_Irr _
  have hvorth : ∀ i j, cfInner (vv i) (vv j) = if i = j then 1 else 0 := by
    intro i j
    rw [hvvdef, hνiso, cfInner_eq_ite_of_mem_Irr (hζIrr i) (hζIrr j)]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h' => hij (hζinj i j h')), if_neg hij]
  have hvnorm : ∀ i, cfInner (vv i) (vv i) = 1 := fun i => by rw [hvorth i i, if_pos rfl]
  have hvsigned : ∀ i, vv i ∈ signedIrr G := fun i =>
    mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one (hvspan i) (hvnorm i)
  have hvdiff : ∀ i j, vv i - vv j = dadeTau T W₂ W₁ (ζ i) - dadeTau T W₂ W₁ (ζ j) := by
    intro i j
    have hsub : (⟨ζ i, Submodule.subset_span (hζmem i)⟩ - ⟨ζ j, Submodule.subset_span (hζmem j)⟩ :
        ↥(Submodule.span ℤ S₁)) = ⟨ζ i - ζ j, Submodule.sub_mem _ (Submodule.subset_span (hζmem i))
          (Submodule.subset_span (hζmem j))⟩ := rfl
    have h1 := hντ ⟨ζ i - ζ j, Submodule.sub_mem _ (Submodule.subset_span (hζmem i))
      (Submodule.subset_span (hζmem j))⟩ (by
        change ζ i 1 - ζ j 1 = 0
        rw [hζ1, hζ1, sub_self])
    rw [← dadeTau_sub, ← h1, ← hsub, map_sub]
    rfl
  have hψdiff : ∀ i j, ψ i - ψ j = dadeTau T W₂ W₁ (ζ j) - dadeTau T W₂ W₁ (ζ i) := by
    intro i j
    simp only [hψdef, dadeTau_sub]
    abel
  have hηspan : ∀ (a : ↑(Irr ↥W₂)) (b : ↑(Irr ↥W₁)),
      hW.prodCharEta ω a b ∈ Submodule.span ℤ (Irr G) := fun a b =>
    mem_span_Irr_of_mem_virtualChars (hW.prodCharEta_mem_virtualChars hω a b)
  have hηnorm : ∀ (a : ↑(Irr ↥W₂)) (b : ↑(Irr ↥W₁)),
      cfInner (hW.prodCharEta ω a b) (hW.prodCharEta ω a b) = 1 := fun a b => by
    rw [hW.cfInner_prodCharEta hω]; simp
  have hvconst : ∀ a b i j, cfInner (vv i) (hW.prodCharEta ω a b) =
      cfInner (vv j) (hW.prodCharEta ω a b) := by
    intro a b i j
    rw [← sub_eq_zero, ← cfInner_sub_left, hvdiff, ← hψdiff j i, cfInner_sub_left, hψη, hψη,
      sub_self]
  have hn2 : 2 ≤ Nat.card ↑S₁ := hn₁card ▸ hn₁2
  have hvη : ∀ i a b, cfInner (vv i) (hW.prodCharEta ω a b) = 0 := fun i a b =>
    cfInner_eq_zero_of_forall_cfInner_eq hn2 (isOrthonormalFamily_iff.2 hvorth) hvspan
      (hηspan a b) (hηnorm a b) (hvconst a b) i
  have h1η : (1 : G → ℂ) = hW.prodCharEta ω (principalIrr ↥W₂) (principalIrr ↥W₁) :=
    (hW.prodCharEta_principal hω).symm
  have hv1 : ∀ i, cfInner (vv i) (1 : G → ℂ) = 0 := fun i => by rw [h1η]; exact hvη i _ _
  have hΦ : ∀ i j, ψ i + vv i = ψ j + vv j := by
    intro i j
    have e1 := hvdiff i j
    simp only [hψdef, dadeTau_sub] at e1 ⊢
    linear_combination e1
  have hM₀star : star M₀ = M₀ := by
    rw [hM₀, h.primeTIrow_principal hσ]
    have := conj_indClassFun (derivedOf T) (1 : ↥(derivedOf T) → ℂ)
    funext y
    have h2 := congrFun this y
    simp only [Pi.one_apply, map_one] at h2
    exact h2
  have hψstar : ∀ i k, ζ k = star (ζ i) → star (ψ i) = ψ k := by
    intro i k hk
    simp only [hψdef]
    rw [← dadeTau_star, star_sub, hM₀star, hk]
  have hstarIdx : ∀ i, ∃ k, ζ k = star (ζ i) ∧ k ≠ i := by
    intro i
    refine ⟨e ⟨star (ζ i), hS₁star _ (hζmem i)⟩, ?_, ?_⟩
    · simp only [hζdef, Equiv.symm_apply_apply]
    · intro hki
      have hz : ζ (e ⟨star (ζ i), hS₁star _ (hζmem i)⟩) = star (ζ i) := by
        simp only [hζdef, Equiv.symm_apply_apply]
      rw [hki] at hz
      exact NormalInducedFamily.star_ne_self_of_odd_natCard_of_mem_indFam_sdiff hTodd
        (hζind i) (hζIrr i) hz.symm
  have hΦreal : ∀ i, star (ψ i + vv i) = ψ i + vv i := by
    intro i
    obtain ⟨k, hk, hki⟩ := hstarIdx i
    have hk' : ζ i = star (ζ k) := by rw [hk, star_star]
    have hsik := hψstar i k hk
    have hski := hψstar k i hk'
    have hYX : cfInner (vv k) (vv i) = 0 := by rw [hvorth k i, if_neg hki]
    have hsum : vv i + (fun g => conj (vv i g)) = vv k + (fun g => conj (vv k g)) := by
      have e1 := hΦ i k
      have e2 : star (ψ i + vv i) = star (ψ k + vv k) := by rw [e1]
      rw [star_add, star_add, hsik, hski] at e2
      have e4 : vv i + star (vv i) = vv k + star (vv k) := by linear_combination e2 + e1
      exact e4
    have hY := eq_conj_of_add_conj_eq hodd (hvsigned i) (hvsigned k) (hv1 k) hYX hsum
    rw [star_add, hsik, hΦ i k]
    congr 1
    rw [hY]; rfl
  refine ⟨vv, isOrthonormalFamily_iff.2 hvorth, hvsigned,
    fun i a b => isOrthogonal_iff.2 (hvη i a b), fun i => ?_⟩
  have hβeq : (1 : G → ℂ) - vv i + (ψ i + vv i - 1) = ψ i := by abel
  refine ⟨ψ i + vv i - 1, Submodule.sub_mem _ (Submodule.add_mem _ (hψspan i) (hvspan i))
    (Submodule.subset_span one_mem_Irr), fun g => ?_, ?_, fun a b => ?_, fun x hx => ?_⟩
  · have hg := congrFun (hΦreal i) g
    have hg' : conj ((ψ i + vv i) g) = (ψ i + vv i) g := hg
    have him := Complex.conj_eq_iff_im.1 hg'
    simp only [Pi.sub_apply, Pi.one_apply, Complex.sub_im, Complex.one_im, sub_zero]
    exact him
  · rw [isOrthogonal_iff, cfInner_sub_left, cfInner_add_left, hv1, h1η, hψη, if_pos rfl, ← h1η,
      cfInner_one_one]
    ring
  · rw [hβeq, hψη]
  · rw [hβeq] at hx
    have hvan : ∀ z : ↥T, (z : G) ∉ ((⁅T, T⁆ : Subgroup G) : Set G) \ {1} → (M₀ - ζ i) z = 0 := by
      intro z hz
      refine h.primeTIrow_sub_apply_eq_zero hσ (hζind i) (hζ1 i) fun hmem => hz ⟨?_, ?_⟩
      · rw [← map_subtype_derivedOf]; exact Subgroup.mem_map_of_mem _ hmem.1
      · intro h1; exact hmem.2 (Subtype.ext h1)
    have hind : ψ i = indClassFun T (M₀ - ζ i) :=
      dadeTau_eq_indClassFun_of_typeIII h₄ hG hT hIII hc (mem_dadeDomain.1 (hF i)).1 hvan
    rw [hind] at hx
    by_contra hne
    exact hx (indClassFun_apply_eq_zero_of_forall_not_isConj T hvan
      (fun c hc hconj => hne ⟨c, hc, hconj⟩))

end RealBridgeLowFamily

end CFSG.FeitThompson
