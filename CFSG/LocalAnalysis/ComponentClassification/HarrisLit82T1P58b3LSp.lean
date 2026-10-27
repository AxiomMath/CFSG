module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpSplit
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3F

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  exists_bilin_split_equiv eigen_ne_bot isCompl_ker_sub_one_ker_add_one invSMulOp_mul_self
  bilin_eq_zero_swap)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

namespace P58b3L

variable {F : Type} [Field F] {r : ℕ}

theorem false_of_sp {X : Type} [Group X] [Finite X] [Finite F] (hF : Nat.card F = 3)
    (hr : 3 ≤ r) (α : StatedSp r F →* X) (hαi : Function.Injective α)
    (hαs : Function.Surjective α) {g : StatedSp r F} (hgg : g * g = 1)
    (hgs : ∀ c : Fˣ, (g : GL (Fin r ⊕ Fin r) F) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {Q : Subgroup X} (hQt : Q ≤ centralizer {α g})
    (hQsub : (Q.subgroupOf (centralizer {α g})).IsSubnormal)
    (hQsolv : Group.IsSolvable (↥Q ⧸ pPrimeCore 2 ↥Q)) {a b : X} (ha : a ∈ Q) (hb : b ∈ Q)
    {c : X} (hc : ∀ y : StatedSp r F, α y = c →
      ((y : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = -1)
    (haa : a * a = c) (hbb : b * b = c) (hab : a * b = c * (b * a)) : False := by
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Foote5.OddLieCore.two_ne_zero_of_card hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  have hK : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two F hK
  set A : gsp r F := ⟨(g : GL (Fin r ⊕ Fin r) F), statedSp_le_gsp g.2⟩ with hAdef
  set M := ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hM
  have hl0 : (1 : F) ≠ 0 := one_ne_zero
  have hAA : M * M = ((1 : F) ^ 2) • 1 := by
    have h := congrArg (fun x : StatedSp r F =>
      ((x : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) hgg
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at h
    rw [one_pow, one_smul]
    exact h
  have hJ : Mᵀ * formJ r F * M = ((1 : F) ^ 2) • formJ r F := by
    rw [one_pow, one_smul]
    exact mem_statedSp_iff.1 g.2
  have hd0 : (1 : F) ^ 2 ≠ 0 := pow_ne_zero 2 hl0
  have hJA : Mᵀ * formJ r F = formJ r F * M := transpose_mul_formJ hd0 hJ hAA
  have hAA' := linA_mul_self hAA
  have hTB : ∀ v w, pairedSympForm F r (invSMulOp 1 ((linA A :
      LinearMap.GeneralLinearGroup F (Fin r ⊕ Fin r → F)) : Module.End F (Fin r ⊕ Fin r → F)) v)
      (invSMulOp 1 ((linA A : LinearMap.GeneralLinearGroup F (Fin r ⊕ Fin r → F)) :
        Module.End F (Fin r ⊕ Fin r → F)) w) = pairedSympForm F r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : F, ((linA A : LinearMap.GeneralLinearGroup F (Fin r ⊕ Fin r → F)) :
      Module.End F (Fin r ⊕ Fin r → F)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hgs
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 hl0 hAA' hAns'
  obtain ⟨horth, haltP, haltM, hndP, hndM, e, he⟩ :=
    exists_bilin_split_equiv h2 pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      hl0 hAA' hTB
  set Ψ := (spCentEquiv A).trans e with hΨ
  have hres : ∀ x : spCent r F A, (Ψ x).2 = 1 ↔ ∀ v ∈ VMl A 1,
      (((x : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ
        v = v := by
    intro x
    change (e (spCentEquiv A x)).2 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A x)).2]
    simp only [spCentEquiv_apply]
  have hres' : ∀ x : spCent r F A, ((Ψ.trans (MulEquiv.prodComm)) x).2 = 1 ↔ ∀ v ∈ VPl A 1,
      (((x : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ
        v = v := by
    intro x
    change (e (spCentEquiv A x)).1 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A x)).1]
    simp only [spCentEquiv_apply]
  have hTP : ∀ v ∈ VPl A 1, ∀ c, transvSp v c ∈ fixSub r F A (VMl A 1) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenPlus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec, horth v hv w hw,
      zero_smul, smul_zero, add_zero]
  have hTM : ∀ v ∈ VMl A 1, ∀ c, transvSp v c ∈ fixSub r F A (VPl A 1) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenMinus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec,
      bilin_eq_zero_swap (B := pairedSympForm F r) pairedSympForm_isAlt (horth w hw v hv),
      zero_smul, smul_zero, add_zero]
  obtain ⟨a', rfl⟩ := hαs a
  obtain ⟨b', rfl⟩ := hαs b
  have e1 : (((a' * a' : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = -1 := hc _ (by rw [map_mul]; exact haa)
  have e2 : (((b' * b' : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = -1 := hc _ (by rw [map_mul]; exact hbb)
  have e3 : a' * b' = a' * a' * (b' * a') :=
    hαi (by rw [map_mul, map_mul, map_mul, map_mul, hab, haa])
  have key : ∀ W W' : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ →
      IsQuasisimple (fixSub r F A W') → (∀ v ∈ W, ∀ c, transvSp v c ∈ fixSub r F A W') →
      (∀ x ∈ spCent r F A, ∀ v ∈ W',
        ((x : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ v ∈ W') →
      (∃ s ∈ fixSub r F A W', s * s = 1 ∧ s ≠ 1) → False := by
    intro W W' hW hq hT hW' ⟨s, hs, hss, hs1⟩
    set N := fixSub r F A W' with hN
    have hNF : N ≤ ClassicalInvolution.Balance.fixedGroup (conjSp r F A) := fixSub_le A W'
    have hNcomp : Open.IsComponentOf N
        (ClassicalInvolution.Balance.fixedGroup (conjSp r F A)) := by
      refine ⟨hNF, ClassicalInvolution.isSubnormal_of_normal_subgroupOf hNF ?_,
        ⟨hq.1.commutator_eq_top, hq.2.1⟩⟩
      rw [Subgroup.normal_subgroupOf_iff hNF]
      exact fun q f hq' hf => conj_mem_fixSub hW' hf hq'
    have hker : α.ker ≤ center (StatedSp r F) := by
      rw [(MonoidHom.ker_eq_bot_iff α).mpr hαi]
      exact bot_le
    have hδ : ∀ y : StatedSp r F,
        α g * α (1 * y * 1⁻¹) * (α g)⁻¹ = α (1 * conjSp r F A y * 1⁻¹) := by
      intro y
      have hy : conjSp r F A y = g * y * g⁻¹ := by
        apply Subtype.ext
        rw [coe_conjSp]
        rfl
      simp only [one_mul, inv_one, mul_one]
      rw [hy, map_mul, map_mul, map_inv]
    have hmain := ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 (α g)
      (conjSp r F A) hδ hNcomp
    have e0 : α.comp (MulAut.conj (1 : StatedSp r F)).toMonoidHom = α := by
      ext
      simp
    rw [e0, MonoidHom.range_eq_top.mpr hαs, top_inf_eq] at hmain
    have hNC : N.map α ≤ centralizer {α g} := hmain.1
    have hNcomp' : IsComponent ((N.map α).subgroupOf (centralizer {α g})) :=
      (isComponentOf_iff_isComponent_subgroupOf hNC).mp
        ((AssemblyBPredicates.isComponentOf_iff_open _ _).mpr hmain)
    have hNeven : Even (Nat.card ((N.map α).subgroupOf (centralizer {α g}))) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hNC).toEquiv,
        Subgroup.card_map_of_injective hαi]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hord : orderOf (⟨s, hs⟩ : N) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · apply Subtype.ext
          change s ^ 2 = 1
          rw [pow_two, hss]
        · intro h
          exact hs1 (congrArg Subtype.val h)
      have := orderOf_dvd_natCard (⟨s, hs⟩ : N)
      rw [hord] at this
      exact even_iff_two_dvd.mpr this
    have hcomm := P51Q.commute_of_isComponent hQt hQsub hQsolv hNcomp' hNeven
    have hcen : ∀ y : StatedSp r F, α y ∈ Q → ∀ x ∈ N, y * x * y⁻¹ = x := by
      intro y hy x hx
      have hxN : α x ∈ N.map α := ⟨x, hx, rfl⟩
      have h1 := hcomm ⟨α x, hNC hxN⟩ (mem_subgroupOf.mpr hxN) (α y) hy
      have h3 : x * y = y * x := hαi (by rw [map_mul, map_mul]; exact h1)
      rw [← h3, mul_inv_cancel_right]
    have heig : ∀ y : StatedSp r F, α y ∈ Q → ∀ v ∈ W, ∃ μ : F,
        ((y : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ v = μ • v := by
      intro y hy
      have hfix : ∀ x ∈ N, (conjAut r F ⟨(y : GL (Fin r ⊕ Fin r) F), statedSp_le_gsp y.2⟩ *
          fieldAut r F 1) (proj r F x) = proj r F x := by
        intro x hx
        rw [map_one, mul_one, SymplecticHigher.conjAut_statedSp, MulAut.conj_apply, ← map_inv,
          ← map_mul, ← map_mul, hcen y hy x hx]
      exact (Foote5.OddLieCore.ClSp.eigen_of_fix hq hT hfix).2
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨l, hl⟩ := heig a' ha v hvW
    obtain ⟨m, hm⟩ := heig b' hb v hvW
    simp only [Subgroup.coe_mul, Units.val_mul] at e1 e2
    have e3' := congrArg (fun z : StatedSp r F =>
      ((z : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) e3
    simp only [Subgroup.coe_mul, Units.val_mul] at e3'
    rw [e1, neg_one_mul] at e3'
    set Ma := ((a' : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
    set Mb := ((b' : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
    have k1 : (Ma * Ma) *ᵥ v = (l * l) • v := by
      rw [← mulVec_mulVec, hl, mulVec_smul, hl, smul_smul]
    have k2 : (Mb * Mb) *ᵥ v = (m * m) • v := by
      rw [← mulVec_mulVec, hm, mulVec_smul, hm, smul_smul]
    have k3 : (Ma * Mb) *ᵥ v = (l * m) • v := by
      rw [← mulVec_mulVec, hm, mulVec_smul, hl, smul_smul, mul_comm]
    have k4 : (Mb * Ma) *ᵥ v = (l * m) • v := by
      rw [← mulVec_mulVec, hl, mulVec_smul, hm, smul_smul]
    rw [e1, neg_mulVec, one_mulVec] at k1
    rw [e2, neg_mulVec, one_mulVec] at k2
    rw [e3', neg_mulVec, k4] at k3
    have hsc : ∀ s : F, s • v = 0 → s = 0 := fun s hs =>
      (smul_eq_zero.mp hs).resolve_right hv0
    have hl2 : l * l = -1 := by
      have := hsc (l * l + 1) (by rw [add_smul, ← k1, one_smul, neg_add_cancel])
      linear_combination this
    have hm2 : m * m = -1 := by
      have := hsc (m * m + 1) (by rw [add_smul, ← k2, one_smul, neg_add_cancel])
      linear_combination this
    have hlm : 2 * (l * m) = 0 := by
      refine hsc (2 * (l * m)) ?_
      calc (2 * (l * m)) • v = (l * m) • v + (l * m) • v := by rw [two_mul, add_smul]
        _ = (l * m) • v + -((l * m) • v) := by rw [k3]
        _ = 0 := add_neg_cancel _
    have hl0' : l ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hl2
      exact one_ne_zero (neg_eq_zero.mp hl2.symm)
    have hm0' : m ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hm2
      exact one_ne_zero (neg_eq_zero.mp hm2.symm)
    exact mul_ne_zero h2 (mul_ne_zero hl0' hm0') hlm
  have hcompl : IsCompl (VPl A 1) (VMl A 1) :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA')
  have hdim : Module.finrank F (VPl A 1) + Module.finrank F (VMl A 1) = r + r := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
    exact this
  have hgm : (((a' * a' * g : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = -M := by
    simp only [Subgroup.coe_mul, Units.val_mul] at e1 ⊢
    rw [e1, neg_one_mul]
  have hMM : M * M = 1 := by rw [hAA, one_pow, one_smul]
  by_cases hPbig : 3 ≤ Module.finrank F (VPl A 1)
  · refine key (VPl A 1) (VMl A 1) hPne ?_ hTP (fun x hx v hv => mulVec_mem_VMl hl0 hx hv)
      ⟨a' * a' * g, ⟨?_, fun v hv => ?_⟩, ?_, ?_⟩
    · exact isQuasisimple_fixSub_of_equiv Ψ hres
        (LocalCores.isQuasisimple_of_mulEquiv
          (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
          (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltP hndP
            (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP) hodd
            (Or.inl (lt_of_lt_of_le (by norm_num) hPbig).ne')))
    · rw [mem_spCent, hgm, Matrix.mul_neg, Matrix.neg_mul]
    · rw [hgm, neg_mulVec, (mem_eigenMinus hl0).1 hv, neg_smul, one_smul, neg_neg]
    · apply Subtype.ext
      apply Units.ext
      change (((a' * a' * g : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        (((a' * a' * g : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1
      rw [hgm, neg_mul_neg, hMM]
    · intro h
      apply hgs (-1)
      apply Units.ext
      have h1 := congrArg (fun x : StatedSp r F =>
        ((x : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) h
      rw [hgm, Subgroup.coe_one, Units.val_one] at h1
      rw [GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, map_neg, map_one]
      change M = -1
      rw [← neg_neg M, h1]
  · have hMbig : 3 ≤ Module.finrank F (VMl A 1) := by omega
    refine key (VMl A 1) (VPl A 1) hMne ?_ hTM (fun x hx v hv => mulVec_mem_VPl hl0 hx hv)
      ⟨g, ⟨?_, fun v hv => ?_⟩, hgg, ?_⟩
    · exact isQuasisimple_fixSub_of_equiv (Ψ.trans MulEquiv.prodComm) hres'
        (LocalCores.isQuasisimple_of_mulEquiv
          (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
          (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltM hndM
            (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hMne _ haltM hndM) hodd
            (Or.inl (lt_of_lt_of_le (by norm_num) hMbig).ne')))
    · exact mem_spCent.mpr rfl
    · rw [(mem_eigenPlus hl0).1 hv, one_smul]
    · intro h
      apply hgs 1
      rw [h, map_one]
      rfl

theorem exists_sp_iso {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hO : pPrimeCore 2 X = ⊥) (hm : Blueprint.LieModel (X ⧸ center X) .PSp r 3 1) {c : X}
    (hc1 : c ≠ 1) (hcZ : c ∈ center X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (α : StatedSp r F →* X), Nat.card F = 3 ∧
      Function.Injective α ∧ Function.Surjective α ∧
      ∀ y, α y = c →
        ((y : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = -1 := by
  have : Group.IsPerfect X := hX.1
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨-, F, _, _, hFc, ⟨θ⟩⟩ := hcl
  have hF : Nat.card F = 3 := by rw [hFc, pow_one]
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  have hFr : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  set β : StatedSp r F →* X ⧸ center X := θ.symm.toMonoidHom.comp (SymplecticFlag.proj r F)
    with hβdef
  have hβ : Function.Surjective β :=
    θ.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSp r F),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : StatedSp r F →* E, ∀ x, π (s x) = x := fun E _ _ π hπ hker h2 => by
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.odd_symplectic_central_two_extension_splitting hFr r hπ hker h2
    exact ⟨s, hs⟩
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, hαβ, hαs, hker⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le
    (by rw [hη]; exact Sol78.center_isPGroup_two hO)
  have hβ1 : ∀ z, β z = 1 →
      ((z : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 ∨
        ((z : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = -1 := by
    intro z hz
    rw [hβdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hz
    have hz' := (QuotientGroup.eq_one_iff z).mp hz
    rw [mem_subgroupOf] at hz'
    obtain ⟨c', hc'⟩ := hz'
    rcases Foote5.OddLieCore.eq_zero_or_one_or_neg_one hF (c' : F) with h | h | h
    · exact absurd h (Units.ne_zero c')
    · left
      rw [← hc', GeneralLinearGroup.coe_scalar, h, map_one]
    · right
      rw [← hc', GeneralLinearGroup.coe_scalar, h, map_neg, map_one]
  obtain ⟨z₀, hz₀c, hz₀⟩ : ∃ z₀, α z₀ = c ∧
      ((z₀ : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = -1 := by
    have hc' : c ∈ (QuotientGroup.mk' (center X)).ker := by rw [hη]; exact hcZ
    rw [hker] at hc'
    obtain ⟨z, hz, hzc⟩ := hc'
    rcases hβ1 z hz with h | h
    · exfalso
      have hz1 : z = 1 := Subtype.ext (Units.ext (by rw [h]; rfl))
      exact hc1 (by rw [← hzc, hz1, map_one])
    · exact ⟨z, hzc, h⟩
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hβw : β w = 1 := by rw [← hαβ, hw, map_one]
    rcases hβ1 w hβw with h | h
    · exact Subtype.ext (Units.ext (by rw [h]; rfl))
    · exfalso
      have hwz : w = z₀ := Subtype.ext (Units.ext (h.trans hz₀.symm))
      exact hc1 (by rw [← hz₀c, ← hwz, hw])
  refine ⟨F, inferInstance, inferInstance, α, hF, hinj, hαs, fun y hy => ?_⟩
  have hyz : y = z₀ := hinj (hy.trans hz₀c.symm)
  rw [hyz, hz₀]

end P58b3L

open P58b3L in
theorem harris82Lemma58bThreeRow_PSp_of_three_le (h51E4 : Harris82Lemma51E4) {r : ℕ}
    (hr : 3 ≤ r) : Harris82Lemma58bThreeRow .PSp r := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ he₁ hKc hO₁ _ _ hz₂K hz₂Z f hm
  obtain rfl := field_eq_one h51E4 hz₁ hz₂ hL₁ hz₁L he₁ hKc hO₁ hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  obtain ⟨Q, hQt, hQsub, -, hQsolv, a, ha, b, hb, haa, hbb, hab⟩ :=
    exists_quat_config hz₁ hz₂ hL₁ hz₁L he₁ hKc.1 hO₁ hz₁K hz₂K
  obtain ⟨F, _, _, α, hF, hαi, hαs, hαc⟩ := exists_sp_iso hX hO hmX (mk_ne_one hz₁ hz₁K)
    (mk_mem_center hKc.1 hz₁K)
  obtain ⟨g, hg⟩ := hαs (QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩)
  have hgg : g * g = 1 := hαi (by rw [map_mul, hg, mk_mul_self hz₂ hz₂K, map_one])
  have hgs : ∀ c' : Fˣ,
      (g : GL (Fin r ⊕ Fin r) F) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c' := by
    intro c' hc'
    have hsc : ∀ Z : GL (Fin r ⊕ Fin r) F,
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c' * Z =
          Z * GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c' := fun Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
    have hcen : α g ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
      rw [mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hαs x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc']
      exact (hsc _).symm
    rw [hg] at hcen
    exact hz₂Z hcen
  rw [← hg] at hQt hQsub
  exact false_of_sp hF hr α hαi hαs hgg hgs hQt hQsub hQsolv ha hb hαc haa hbb hab

end CFSG.ComponentClassification.HarrisLit.T1
