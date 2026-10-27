module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOGen
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  exists_bilin_split_equiv eigen_ne_bot isCompl_ker_sub_one_ker_add_one invSMulOp_mul_self
  bilin_eq_zero_swap)
open CFSG.ComponentClassification.Burgoyne.Sp

variable {r : ℕ} {K : Type} [Field K]

theorem mem_spCent_iff_mem_centralizer {a g : StatedSp r K} :
    g ∈ spCent r K ⟨(a : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp a.2⟩ ↔
      g ∈ centralizer ({a} : Set (StatedSp r K)) := by
  rw [mem_spCent, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (Units.ext h.symm)
  · intro h
    exact (congrArg (fun x : StatedSp r K =>
      ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h).symm

theorem multiplier_eq_one_of_mem [NeZero r] (g : StatedSp r K) :
    (multiplier r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ : K) = 1 := by
  have h := multiplierUnit_eq (μ := 1) ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩
    (by rw [Units.val_one, one_smul]; exact mem_statedSp_iff.1 g.2)
  change ((multiplierUnit _ : Kˣ) : K) = 1
  rw [h, Units.val_one]

variable [Finite K]

theorem lift_cases_self (hK : ringChar K ≠ 2) (hK3 : Nat.card K ≠ 3) (hr : 2 ≤ r)
    {a : StatedSp r K}
    (hAns : ∀ c : Kˣ, (a : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    (hAA : ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1)
    {X : Type} [Group X] [Finite X] (π : StatedSp r K →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → s ∈ center (StatedSp r K)) {g : X}
    (hg : ∀ L : Subgroup (centralizer ({π a} : Set X)), IsComponent L → Even (Nat.card L) →
      ∀ k ∈ L, (k : X) * g = g * k)
    {g' : StatedSp r K} (hg' : π g' = g) :
    ((g' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 ∨
      ((g' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -1 ∨
        ((g' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ∨
          ((g' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
            -((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have : Fintype K := Fintype.ofFinite K
  have : NeZero r := ⟨by omega⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  set A : gsp r K := ⟨(a : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp a.2⟩ with hAdef
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hl0 : (1 : K) ≠ 0 := one_ne_zero
  have hAA₁ : M * M = ((1 : K) ^ 2) • 1 := by rw [one_pow, one_smul]; exact hAA
  have hJ : Mᵀ * formJ r K * M = ((1 : K) ^ 2) • formJ r K := by
    rw [one_pow, one_smul]
    exact mem_statedSp_iff.1 a.2
  have hJA : Mᵀ * formJ r K = formJ r K * M := transpose_mul_formJ (pow_ne_zero 2 hl0) hJ hAA₁
  have hAA' := linA_mul_self hAA₁
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp 1 ((linA A :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp 1 ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : K, ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 hl0 hAA' hAns'
  obtain ⟨horth, haltP, haltM, hndP, hndM, e, he⟩ :=
    exists_bilin_split_equiv h2 pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      hl0 hAA' hTB
  set Ψ := (spCentEquiv A).trans e with hΨ
  have hres : ∀ g : spCent r K A, (Ψ g).2 = 1 ↔ ∀ v ∈ VMl A 1,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv A g)).2 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A g)).2]
    simp only [spCentEquiv_apply]
  have hres' : ∀ g : spCent r K A, ((Ψ.trans (MulEquiv.prodComm)) g).2 = 1 ↔ ∀ v ∈ VPl A 1,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv A g)).1 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A g)).1]
    simp only [spCentEquiv_apply]
  have hqP : IsQuasisimple (fixSub r K A (VMl A 1)) :=
    isQuasisimple_fixSub_of_equiv Ψ hres
      (LocalCores.isQuasisimple_of_mulEquiv (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
        (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltP hndP
          (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP) hodd (Or.inr hK3)))
  have hqM : IsQuasisimple (fixSub r K A (VPl A 1)) :=
    isQuasisimple_fixSub_of_equiv (Ψ.trans (MulEquiv.prodComm)) hres'
      (LocalCores.isQuasisimple_of_mulEquiv (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
        (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltM hndM
          (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hMne _ haltM hndM) hodd (Or.inr hK3)))
  have hTP : ∀ v ∈ VPl A 1, ∀ c, transvSp v c ∈ fixSub r K A (VMl A 1) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenPlus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec, horth v hv w hw,
      zero_smul, smul_zero, add_zero]
  have hTM : ∀ v ∈ VMl A 1, ∀ c, transvSp v c ∈ fixSub r K A (VPl A 1) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenMinus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec,
      bilin_eq_zero_swap (B := pairedSympForm K r) pairedSympForm_isAlt (horth w hw v hv),
      zero_smul, smul_zero, add_zero]
  set Dm := ((g' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hDm
  have hlift : ∀ W : Submodule K (Fin r ⊕ Fin r → K),
      (∀ f ∈ spCent r K A, ∀ v ∈ W,
        ((f : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W) →
      IsQuasisimple (fixSub r K A W) → ∀ q ∈ fixSub r K A W, g' * q = q * g' := by
    intro W hW hq
    refine lift_commute_of_subnormal π hπ hker a hq le_rfl
      (fun x hx m hm => mul_mem (mul_mem hx hm) (inv_mem hx)) (fun x hx => ?_)
      (fun x hx n hn => ?_) hg hg'
    · exact mem_spCent_iff_mem_centralizer.1 (fixSub_le A W hx)
    · exact conj_mem_fixSub hW (mem_spCent_iff_mem_centralizer.2 hx) hn
  have heig : ∀ W W' : Submodule K (Fin r ⊕ Fin r → K),
      (∀ f ∈ spCent r K A, ∀ v ∈ W',
        ((f : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W') →
      IsQuasisimple (fixSub r K A W') → (∀ v ∈ W, ∀ c, transvSp v c ∈ fixSub r K A W') →
        ∀ v ∈ W, ∃ μ : K, Dm *ᵥ v = μ • v := by
    intro W W' hW' hq hT v hv
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, mulVec_zero, smul_zero]⟩
    obtain ⟨b, hb⟩ : ∃ b, (v ᵥ* formJ r K) b ≠ 0 := by
      by_contra h
      push Not at h
      exact vecMul_formJ_ne_zero hv0 (funext h)
    have h1 := hlift W' hW' hq _ (hT v hv 1)
    have h1' := congrArg (fun x : StatedSp r K =>
      ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, coe_transvSp, one_smul] at h1'
    have h2' : Dm * transvN v = transvN v * Dm := by
      have e1 : Dm * (1 + transvN v) = Dm + Dm * transvN v := by
        rw [Matrix.mul_add, Matrix.mul_one]
      have e2 : (1 + transvN v) * Dm = Dm + transvN v * Dm := by
        rw [Matrix.add_mul, Matrix.one_mul]
      rw [← hDm, e1, e2] at h1'
      exact add_left_cancel h1'
    exact exists_eigen_of_commute_vecMulVec' hb h2'
  have hPe := heig (VPl A 1) (VMl A 1) (fun f hf v hv => mulVec_mem_VMl hl0 hf hv) hqP hTP
  have hMe := heig (VMl A 1) (VPl A 1) (fun f hf v hv => mulVec_mem_VPl hl0 hf hv) hqM hTM
  obtain ⟨a₀, ha₀⟩ := exists_smul_of_eigen hPe
  obtain ⟨b₀, hb₀⟩ := exists_smul_of_eigen hMe
  have hsqa : a₀ ^ 2 = 1 := by
    rw [← multiplier_eq_sq_of_smul (D := ⟨(g' : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g'.2⟩)
      hPne hndP ha₀, multiplier_eq_one_of_mem]
  have hsqb : b₀ ^ 2 = 1 := by
    rw [← multiplier_eq_sq_of_smul (D := ⟨(g' : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g'.2⟩)
      hMne hndM hb₀, multiplier_eq_one_of_mem]
  have hc := isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA')
  have hDx : ∀ x : Fin r ⊕ Fin r → K, ∃ x₁ ∈ VPl A 1, ∃ x₂ ∈ VMl A 1, x = x₁ + x₂ ∧
      Dm *ᵥ x = a₀ • x₁ + b₀ • x₂ ∧ M *ᵥ x = x₁ - x₂ := by
    intro x
    obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint x
    refine ⟨x₁, hx₁, x₂, hx₂, hx.symm, ?_, ?_⟩
    · rw [← hx, mulVec_add, ha₀ x₁ hx₁, hb₀ x₂ hx₂]
    · rw [← hx, mulVec_add, (mem_eigenPlus hl0).1 hx₁, (mem_eigenMinus hl0).1 hx₂, one_smul,
        neg_one_smul, sub_eq_add_neg]
  have hsq1 : ∀ {c : K}, c ^ 2 = 1 → c = 1 ∨ c = -1 := fun hc =>
    mul_self_eq_one_iff.1 (by rw [← sq]; exact hc)
  have hab : a₀ = b₀ ∨ a₀ = -b₀ := by
    rcases hsq1 hsqa with h | h <;> rcases hsq1 hsqb with h' | h' <;> rw [h, h'] <;> simp
  rcases hab with hab | hab
  ·
    have hDs : Dm = a₀ • 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun x => ?_
      obtain ⟨x₁, -, x₂, -, rfl, hD, -⟩ := hDx x
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hD, hab, smul_mulVec, one_mulVec, smul_add]
    rcases hsq1 hsqa with h | h
    · left
      rw [hDs, h, one_smul]
    · right; left
      rw [hDs, h, neg_one_smul]
  ·
    have hDA : Dm = a₀ • M := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun x => ?_
      obtain ⟨x₁, -, x₂, -, -, hD, hMx⟩ := hDx x
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hD, smul_mulVec, hMx, hab]
      module
    rcases hsq1 hsqa with h | h
    · right; right; left
      rw [hDA, h, one_smul]
    · right; right; right
      rw [hDA, h, neg_one_smul]

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
