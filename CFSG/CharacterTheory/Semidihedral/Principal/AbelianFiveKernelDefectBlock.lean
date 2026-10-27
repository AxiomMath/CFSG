module

public import CFSG.CharacterTheory.Semidihedral.Principal.AbelianFiveKernelDefectBlockSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.UnitClassScalarDefect
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectDegreeDivisibility

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace FiveKernel

theorem isIrreducible_comp_of_surjective {G H V : Type*} [Monoid G] [Monoid H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f)
    (hirr : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp f) := by
  let : Representation.IsIrreducible ρ := hirr
  have hbot : (⊥ : Subrepresentation (ρ.comp f)) ≠ ⊤ := by
    intro heq
    have hsub : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule heq
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ)
    exact Subrepresentation.toSubmodule_injective hsub
  refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, ?_⟩
  intro U
  let U' : Subrepresentation ρ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        obtain ⟨g, rfl⟩ := hf h
        exact U.apply_mem_toSubmodule g hv }
  rcases IsSimpleOrder.eq_bot_or_eq_top U' with hb | ht
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation ρ => S.toSubmodule) hb)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht)

section DirectProduct

variable {K : Type u} [Group K] {W J : Subgroup K} (hWJ : ∀ w ∈ W, ∀ j ∈ J, Commute w j)

@[expose] def prodMul : W × J →* K :=
  MonoidHom.noncommCoprod W.subtype J.subtype fun w j => hWJ w w.2 j j.2

theorem prodMul_apply (x : W × J) : prodMul hWJ x = (x.1 : K) * x.2 := rfl

theorem prodMul_bijective (hdisj : W ⊓ J = ⊥) (hsup : W ⊔ J = ⊤) :
    Function.Bijective (prodMul hWJ) := by
  constructor
  · intro x y h
    rw [prodMul_apply, prodMul_apply] at h
    have hmemW : (y.1 : K)⁻¹ * x.1 ∈ W := W.mul_mem (W.inv_mem y.1.2) x.1.2
    have hrel : (y.1 : K)⁻¹ * x.1 = y.2 * (x.2 : K)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have hmemJ : (y.1 : K)⁻¹ * x.1 ∈ J := by
      rw [hrel]
      exact J.mul_mem y.2.2 (J.inv_mem x.2.2)
    have hone : (y.1 : K)⁻¹ * x.1 = 1 := by
      have hmem : (y.1 : K)⁻¹ * x.1 ∈ W ⊓ J := ⟨hmemW, hmemJ⟩
      rw [hdisj] at hmem
      exact hmem
    have h1 : (x.1 : K) = y.1 := (inv_mul_eq_one.mp hone).symm
    have h2 : (x.2 : K) = y.2 := by
      rw [h1] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro k
    have hnorm : W ≤ Subgroup.normalizer (J : Set K) := by
      intro w hw
      rw [Subgroup.mem_normalizer_iff]
      intro j
      constructor
      · intro hj
        rw [(hWJ w hw j hj).eq, mul_inv_cancel_right]
        exact hj
      · intro hj
        have hc := (hWJ w hw _ hj).eq
        rw [inv_mul_cancel_right] at hc
        rw [← mul_left_cancel hc]
        exact hj
    have hk : k ∈ ((W ⊔ J : Subgroup K) : Set K) := by
      rw [hsup]
      trivial
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W J hnorm] at hk
    obtain ⟨w, hw, j, hj, rfl⟩ := hk
    exact ⟨(⟨w, hw⟩, ⟨j, hj⟩), rfl⟩

end DirectProduct

section Product

variable {K : Type u} [Group K] {W J : Subgroup K} (φ : W × J ≃* K)
  (hφ : ∀ x : W × J, φ x = (x.1 : K) * x.2)

@[expose] noncomputable def projW : K →* W := (MonoidHom.fst W J).comp φ.symm.toMonoidHom

@[expose] noncomputable def projJ : K →* J := (MonoidHom.snd W J).comp φ.symm.toMonoidHom

include hφ in
theorem symm_apply_mul (w : W) (j : J) : φ.symm ((w : K) * j) = (w, j) := by
  rw [MulEquiv.symm_apply_eq, hφ]

include hφ in
theorem projW_mul (w : W) (j : J) : projW φ ((w : K) * j) = w := by
  change (φ.symm ((w : K) * j)).1 = w
  rw [symm_apply_mul φ hφ]

include hφ in
theorem projJ_mul (w : W) (j : J) : projJ φ ((w : K) * j) = j := by
  change (φ.symm ((w : K) * j)).2 = j
  rw [symm_apply_mul φ hφ]

include hφ in
theorem projW_mul_projJ (k : K) : (projW φ k : K) * projJ φ k = k := by
  have h := hφ (φ.symm k)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

include hφ in
theorem projJ_coe (j : J) : projJ φ (j : K) = j := by
  have h := projJ_mul φ hφ 1 j
  rwa [OneMemClass.coe_one, one_mul] at h

include hφ in
theorem projW_coe (w : W) : projW φ (w : K) = w := by
  have h := projW_mul φ hφ w 1
  rwa [OneMemClass.coe_one, mul_one] at h

include hφ in
theorem projJ_surjective : Function.Surjective (projJ φ) :=
  fun j => ⟨j, projJ_coe φ hφ j⟩

include φ in
theorem card_eq_card_mul_card : Nat.card K = Nat.card W * Nat.card J := by
  rw [← Nat.card_prod, Nat.card_congr φ.toEquiv]

end Product

section Characters

variable {K : Type u} [Group K] [Fintype K] {W J : Subgroup K} [Fintype W] [Fintype J]
  (φ : W × J ≃* K) (hφ : ∀ x : W × J, φ x = (x.1 : K) * x.2)
  (basisW : FiniteIrreducibleCharacterBasis W) (basisJ : FiniteIrreducibleCharacterBasis J)
  (basisK : FiniteIrreducibleCharacterBasis K)

omit [Fintype W] in
include hφ in
theorem exists_pullback_label (ψ : basisJ.index) : ∃ l : basisK.index, ∀ k : K,
    (basisK.representation l).character k = (basisJ.representation ψ).character (projJ φ k) := by
  let data : FiniteComplexRepresentation K :=
    { vector := (basisJ.representation ψ).vector
      representation := (basisJ.representation ψ).representation.comp (projJ φ) }
  have hirr : data.IsIrreducible :=
    isIrreducible_comp_of_surjective _ _ (projJ_surjective φ hφ) (basisJ.irreducible ψ)
  obtain ⟨l, hl⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisK data hirr
  exact ⟨l, fun k => by rw [hl]; rfl⟩

omit [Fintype K] [Fintype J] in
theorem character_one_eq_one (hWab : ∀ a ∈ W, ∀ b ∈ W, Commute a b) (lam : basisW.index) :
    (basisW.representation lam).character 1 = 1 := by
  have : IsMulCommutative W := ⟨⟨fun a b => Subtype.ext (hWab a a.2 b b.2).eq⟩⟩
  have : (basisW.representation lam).representation.IsIrreducible := basisW.irreducible lam
  have hdim := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    (basisW.representation lam).representation
  rw [FiniteComplexRepresentation.character, Representation.char_one, hdim, Nat.cast_one]

omit [Fintype K] [Fintype J] in
theorem card_index_eq_card (hWab : ∀ a ∈ W, ∀ b ∈ W, Commute a b) :
    Fintype.card basisW.index = Nat.card W := by
  have h := finiteIrreducibleCharacterBasis_sum_finrank_sq basisW
  have h1 : ∀ lam, Module.finrank ℂ (basisW.representation lam).vector = 1 := fun lam =>
    finrank_eq_of_character_one basisW (by rw [character_one_eq_one basisW hWab lam, Nat.cast_one])
  simp only [h1, one_pow, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  exact h

omit [Fintype K] [Fintype J] in
@[expose] noncomputable def inflatedLinear (hWab : ∀ a ∈ W, ∀ b ∈ W, Commute a b)
    (lam : basisW.index) : K →* ℂˣ :=
  (degreeOneCharacterUnits (basisW.representation lam)
    (character_one_eq_one basisW hWab lam)).comp (projW φ)

omit [Fintype K] [Fintype J] in
theorem inflatedLinear_apply (hWab : ∀ a ∈ W, ∀ b ∈ W, Commute a b) (lam : basisW.index)
    (k : K) :
    (inflatedLinear φ basisW hWab lam k : ℂ) = (basisW.representation lam).character (projW φ k) :=
  rfl

omit [Fintype K] [Fintype J] in
theorem inflatedLinear_pow_card (hWab : ∀ a ∈ W, ∀ b ∈ W, Commute a b) (lam : basisW.index)
    (k : K) : inflatedLinear φ basisW hWab lam k ^ Nat.card W = 1 := by
  change (degreeOneCharacterUnits (basisW.representation lam)
    (character_one_eq_one basisW hWab lam)) (projW φ k) ^ Nat.card W = 1
  rw [← map_pow, pow_card_eq_one', map_one]

end Characters

end FiveKernel

open FiveKernel

theorem abelian_five_kernel_alternating_five_unique_defect_block {K : Type u} [Group K]
    [Fintype K] (W J : Subgroup K) [Fintype W] [Fintype J]
    (hWab : ∀ a ∈ W, ∀ b ∈ W, Commute a b) (hW : IsPGroup 5 W)
    (hWJ : ∀ w ∈ W, ∀ j ∈ J, Commute w j) (hdisj : W ⊓ J = ⊥) (hsup : W ⊔ J = ⊤)
    (hJ : Nonempty (J ≃* alternatingGroup (Fin 5))) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 5]
    (basisW : FiniteIrreducibleCharacterBasis W) (basisJ : FiniteIrreducibleCharacterBasis J)
    (basisK : FiniteIrreducibleCharacterBasis K) :
    let θ : J → ℂ := fun j => (Nat.card (MulAction.fixedBy (Sylow 5 J) j) : ℂ) - 1
    let b : Set (K → ℂ) := {ψ | ∃ lam : basisW.index, ∀ (w : W) (j : J),
      ψ ((w : K) * j) = (basisW.representation lam).character w * θ j}
    Nat.card (Sylow 5 J) = 6 ∧
    (∃ l : basisJ.index, (basisJ.representation l).character = θ) ∧
    θ 1 = 5 ∧ (∀ j : J, orderOf j = 2 → θ j = 1) ∧ (∀ j : J, orderOf j = 3 → θ j = -1) ∧
    (∀ j : J, orderOf j = 5 → θ j = 0) ∧
    (∀ l : basisJ.index, 5 ∣ Module.finrank ℂ (basisJ.representation l).vector →
      (basisJ.representation l).character = θ) ∧
    ∃ label : basisK.index,
      (fun l => (basisK.representation l).character) ''
          (coefficientBlock basisK (localizedComplexIntegerRing ideal) label : Set basisK.index) =
        b ∧
      (∀ ψ ∈ b, ψ 1 = 5) ∧
      coefficientBlockDefect basisK ideal 5 label W ∧
      ∀ l : basisK.index, coefficientBlockDefect basisK ideal 5 l W →
        l ∈ coefficientBlock basisK (localizedComplexIntegerRing ideal) label := by
  intro θ b
  obtain ⟨e⟩ := hJ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨th, hth⟩ := exists_label_sylowAugmentation e basisJ
  change (basisJ.representation th).character = θ at hth
  refine ⟨card_sylow_five e, ⟨th, hth⟩, sylowAugmentation_one e,
    fun j hj => sylowAugmentation_of_orderOf_two e hj,
    fun j hj => sylowAugmentation_of_orderOf_three e hj,
    fun j hj => sylowAugmentation_of_orderOf_five e hj,
    fun l hl => eq_sylowAugmentation_of_five_dvd e basisJ l hl, ?_⟩
  let φ : W × J ≃* K := MulEquiv.ofBijective (prodMul hWJ) (prodMul_bijective hWJ hdisj hsup)
  have hφ : ∀ x : W × J, φ x = (x.1 : K) * x.2 := fun x => rfl
  obtain ⟨a, ha⟩ := hW.exists_card_eq
  have hcardK : Nat.card K = 5 ^ a * 60 := by
    rw [card_eq_card_mul_card φ, ha, card_eq_sixty e]
  choose pull hpull using exists_pullback_label φ hφ basisJ basisK
  have hlam : ∀ (lam : basisW.index) (k : K), inflatedLinear φ basisW hWab lam k ^ 5 ^ a = 1 :=
    fun lam k => ha ▸ inflatedLinear_pow_card φ basisW hWab lam k
  choose L hL hLmem using fun x : basisW.index × basisJ.index =>
    exists_linearTwist_label_mem_coefficientBlock basisK ideal 5
      (inflatedLinear φ basisW hWab x.1) a (hlam x.1) (pull x.2)
  have hLchar : ∀ (x : basisW.index × basisJ.index) (k : K),
      (basisK.representation (L x)).character k =
        (basisW.representation x.1).character (projW φ k) *
          (basisJ.representation x.2).character (projJ φ k) := by
    intro x k
    rw [hL x k, inflatedLinear_apply, hpull]
  have hLmul : ∀ (x : basisW.index × basisJ.index) (w : W) (j : J),
      (basisK.representation (L x)).character ((w : K) * j) =
        (basisW.representation x.1).character w * (basisJ.representation x.2).character j := by
    intro x w j
    rw [hLchar, projW_mul φ hφ, projJ_mul φ hφ]
  have hLone : ∀ x : basisW.index × basisJ.index, (basisK.representation (L x)).character 1 =
      (basisJ.representation x.2).character 1 := by
    intro x
    rw [hLchar, map_one, map_one, character_one_eq_one basisW hWab, one_mul]
  have hfin : ∀ x : basisW.index × basisJ.index,
      Module.finrank ℂ (basisK.representation (L x)).vector =
        Module.finrank ℂ (basisJ.representation x.2).vector := by
    intro x
    apply finrank_eq_of_character_one basisK
    rw [hLone, FiniteComplexRepresentation.character, Representation.char_one]
  have hLinj : Function.Injective L := by
    intro x y h
    have hJeq : (basisJ.representation x.2).character = (basisJ.representation y.2).character := by
      funext j
      have hx := hLmul x 1 j
      have hy := hLmul y 1 j
      rw [h] at hx
      rw [character_one_eq_one basisW hWab, one_mul] at hx hy
      exact hx.symm.trans hy
    have h2 : x.2 = y.2 := basisJ.distinct hJeq
    have hWeq : (basisW.representation x.1).character = (basisW.representation y.1).character := by
      funext w
      have hx := hLmul x w 1
      have hy := hLmul y w 1
      rw [h, h2] at hx
      exact mul_right_cancel₀ (irreducible_character_degree_ne_zero _ (basisJ.irreducible y.2))
        (hx.symm.trans hy)
    exact Prod.ext (basisW.distinct hWeq) h2
  have hsum : ∑ x : basisW.index × basisJ.index,
      Module.finrank ℂ (basisK.representation (L x)).vector ^ 2 = Nat.card K := by
    calc ∑ x : basisW.index × basisJ.index,
          Module.finrank ℂ (basisK.representation (L x)).vector ^ 2
        = ∑ x : basisW.index × basisJ.index,
            Module.finrank ℂ (basisJ.representation x.2).vector ^ 2 :=
          Finset.sum_congr rfl fun x _ => by rw [hfin]
      _ = ∑ _lam : basisW.index, ∑ ψ : basisJ.index,
            Module.finrank ℂ (basisJ.representation ψ).vector ^ 2 := Fintype.sum_prod_type _
      _ = Fintype.card basisW.index * Nat.card J := by
          rw [Finset.sum_const, Finset.card_univ, finiteIrreducibleCharacterBasis_sum_finrank_sq,
            smul_eq_mul]
      _ = Nat.card K := by rw [card_index_eq_card basisW hWab, card_eq_card_mul_card φ]
  have hLsurj : Function.Surjective L :=
    finiteIrreducibleCharacterBasis_exhaustion_of_degree_sum basisK L hLinj hsum
  let tJ : J := e.symm involution
  have hθt : θ tJ = 1 := sylowAugmentation_of_orderOf_two e (orderOf_symm_involution e)
  have hmemC : ∀ k : K, k ∈ Subgroup.centralizer ({(tJ : K)} : Set K) ↔
      projJ φ k * tJ = tJ * projJ φ k := by
    intro k
    rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul,
      Subgroup.coe_mul]
    have hw := (hWJ (projW φ k) (projW φ k).2 tJ tJ.2).eq
    conv_lhs => rw [← projW_mul_projJ φ hφ k]
    constructor
    · intro h
      apply mul_left_cancel (a := (projW φ k : K))
      calc (projW φ k : K) * (projJ φ k * tJ) = (projW φ k * projJ φ k : K) * tJ :=
            (mul_assoc _ _ _).symm
        _ = tJ * (projW φ k * projJ φ k : K) := h
        _ = (tJ * projW φ k : K) * projJ φ k := (mul_assoc _ _ _).symm
        _ = (projW φ k * tJ : K) * projJ φ k := by rw [hw]
        _ = (projW φ k : K) * (tJ * projJ φ k) := mul_assoc _ _ _
    · intro h
      calc (projW φ k * projJ φ k : K) * tJ = (projW φ k : K) * (projJ φ k * tJ) :=
            mul_assoc _ _ _
        _ = (projW φ k : K) * (tJ * projJ φ k) := by rw [h]
        _ = (projW φ k * tJ : K) * projJ φ k := (mul_assoc _ _ _).symm
        _ = (tJ * projW φ k : K) * projJ φ k := by rw [hw]
        _ = tJ * (projW φ k * projJ φ k : K) := mul_assoc _ _ _
  have hcardC : Nat.card (Subgroup.centralizer ({(tJ : K)} : Set K)) = Nat.card W * 4 := by
    have e1 : Nat.card (Subgroup.centralizer ({(tJ : K)} : Set K)) =
        Nat.card {x : W × J // x.2 * tJ = tJ * x.2} :=
      Nat.card_congr (Equiv.subtypeEquiv φ.symm.toEquiv fun k => hmemC k)
    have e2 : Nat.card {x : W × J // x.2 * tJ = tJ * x.2} =
        Nat.card W * Nat.card {j : J // j * tJ = tJ * j} := by
      rw [← Nat.card_prod]
      exact Nat.card_congr
        { toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
          invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have e3 : Nat.card {j : J // j * tJ = tJ * j} = 4 := by
      rw [← card_centralizer_symm_involution e]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun j =>
        Subgroup.mem_centralizer_singleton_iff.symm)
    rw [e1, e2, e3]
  have hindex : (Subgroup.centralizer ({(tJ : K)} : Set K)).index = 15 := by
    have h := Subgroup.index_mul_card (Subgroup.centralizer ({(tJ : K)} : Set K))
    rw [hcardC, hcardK, ha] at h
    have h' : 5 ^ a * ((Subgroup.centralizer ({(tJ : K)} : Set K)).index * 4) = 5 ^ a * 60 := by
      rw [← h]
      ring
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h'
    omega
  have hWC : W ≤ Subgroup.centralizer ({(tJ : K)} : Set K) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hWJ w hw tJ tJ.2).eq
  have hWsub : IsPGroup 5 (W.subgroupOf (Subgroup.centralizer ({(tJ : K)} : Set K))) :=
    hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWC).symm
  have hWsubIndex : ¬ 5 ∣ (W.subgroupOf (Subgroup.centralizer ({(tJ : K)} : Set K))).index := by
    have h := Subgroup.index_mul_card (W.subgroupOf (Subgroup.centralizer ({(tJ : K)} : Set K)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv, hcardC] at h
    have h' : Nat.card W * (W.subgroupOf (Subgroup.centralizer ({(tJ : K)} : Set K))).index =
        Nat.card W * 4 := by
      rw [← h]
      ring
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h']
    norm_num
  have hclass : classDefect 5 (ConjClasses.mk (tJ : K)) W :=
    ⟨tJ, rfl, hWsub.toSylow hWsubIndex, (Subgroup.map_subgroupOf_eq_of_le hWC).symm⟩
  have hω : (localCentralCharacterHom basisK ideal (pull th)
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk (tJ : K))) :
        ℂ) = 3 := by
    rw [localCentralCharacterHom_conjugacyClassSum_mk, hindex, hpull, hpull, projJ_coe φ hφ,
      map_one, hth, hθt, show θ 1 = 5 from sylowAugmentation_one e]
    norm_num
  have hres : centralCharacterResidueHom basisK ideal (pull th)
      (centralConjugacyClassSum _ (ConjClasses.mk (tJ : K))) ≠ 0 := by
    have h3 : localCentralCharacterHom basisK ideal (pull th)
        (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk (tJ : K))) =
          ((3 : ℕ) : localizedComplexIntegerRing ideal) := by
      apply Subtype.ext
      rw [hω]
      push_cast
      rfl
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basisK ideal (pull th)
      (centralConjugacyClassSum _ (ConjClasses.mk (tJ : K)))) ≠ 0
    rw [h3, map_natCast]
    intro h
    have := (CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) 5 3).mp h
    norm_num at this
  have hcentral : ∀ n ∈ W, ∀ g : K, g * n = n * g := by
    intro n hn g
    have h1 := (hWab n hn (projW φ g) (projW φ g).2).eq
    have h2 := (hWJ n hn (projJ φ g) (projJ φ g).2).eq
    rw [← projW_mul_projJ φ hφ g]
    calc (projW φ g * projJ φ g : K) * n = (projW φ g : K) * (projJ φ g * n) := mul_assoc _ _ _
      _ = (projW φ g : K) * (n * projJ φ g) := by rw [h2]
      _ = (projW φ g * n : K) * projJ φ g := (mul_assoc _ _ _).symm
      _ = (n * projW φ g : K) * projJ φ g := by rw [h1]
      _ = n * (projW φ g * projJ φ g : K) := mul_assoc _ _ _
  have hWnormal : W.Normal :=
    ⟨fun n hn g => by rw [hcentral n hn g, mul_inv_cancel_right]; exact hn⟩
  obtain ⟨D, hD⟩ := coefficientBlockDefect_exists basisK ideal 5 (pull th)
  have hWD : W ≤ D := normal_p_le_coefficientBlockDefect basisK ideal 5 W hW hD
  have hdefect : coefficientBlockDefect basisK ideal 5 (pull th) W :=
    ⟨⟨ConjClasses.mk (tJ : K), hclass, hres⟩, fun Y Q hY hYres =>
      subgroupSubconjugate_trans (subgroupSubconjugate_of_le hWD) (hD.2 Y Q hY hYres)⟩
  have hvK : padicValNat 5 (Nat.card K) = a + 1 := by
    rw [hcardK, show 5 ^ a * 60 = 5 ^ (a + 1) * 12 by ring,
      padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num), add_zero]
  have hdvd5 : ∀ l : basisK.index, coefficientBlockDefect basisK ideal 5 l W →
      5 ∣ Module.finrank ℂ (basisK.representation l).vector := by
    intro l hl
    obtain ⟨-, -, hdeg⟩ := block_class_defect_witness_character_degree_dvd basisK ideal 5 l W hl
    have h := (hdeg a ha).2 l (coefficientBlock_self_mem basisK _ l)
    rwa [hvK, Nat.add_sub_cancel_left, pow_one] at h
  have hkey : ∀ l : basisK.index, coefficientBlockDefect basisK ideal 5 l W →
      ∃ lam, l = L (lam, th) := by
    intro l hl
    obtain ⟨x, rfl⟩ := hLsurj l
    have h5 := hdvd5 _ hl
    rw [hfin x] at h5
    have hx2 : x.2 = th :=
      basisJ.distinct ((eq_sylowAugmentation_of_five_dvd e basisJ x.2 h5).trans hth.symm)
    exact ⟨x.1, by rw [← hx2]⟩
  have hblock : ∀ l, l ∈ coefficientBlock basisK (localizedComplexIntegerRing ideal) (pull th) ↔
      ∃ lam, l = L (lam, th) := by
    intro l
    constructor
    · intro hl
      have hsame := (coefficientBlock_mem_iff basisK _ (pull th) l).mp hl
      exact hkey l ((coefficientBlockDefect_iff_of_same_block basisK ideal 5 hsame W).mp hdefect)
    · rintro ⟨lam, rfl⟩
      exact hLmem (lam, th)
  refine ⟨pull th, ?_, ?_, hdefect, fun l hl => (hblock l).mpr (hkey l hl)⟩
  · ext ψ
    simp only [Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨lam, rfl⟩ := (hblock l).mp hl
      exact ⟨lam, fun w j => by rw [hLmul, hth]⟩
    · rintro ⟨lam, hψ⟩
      refine ⟨L (lam, th), (hblock _).mpr ⟨lam, rfl⟩, ?_⟩
      funext k
      rw [← projW_mul_projJ φ hφ k, hLmul, hψ, hth]
  · rintro ψ ⟨lam, hψ⟩
    have h := hψ 1 1
    rw [OneMemClass.coe_one, OneMemClass.coe_one, mul_one, character_one_eq_one basisW hWab,
      one_mul] at h
    rw [h]
    exact sylowAugmentation_one e

theorem abelian_five_kernel_alternating_five_unique_defect_block_shared {K : Type} [Group K]
    [Fintype K] (W J : Subgroup K) (hWab : ∀ a ∈ W, ∀ b ∈ W, Commute a b) (hW : IsPGroup 5 W)
    (hWJ : ∀ w ∈ W, ∀ j ∈ J, Commute w j) (hdisj : W ⊓ J = ⊥) (hsup : W ⊔ J = ⊤)
    (hJ : Nonempty (J ≃* alternatingGroup (Fin 5))) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    [CharP (BlocksAlgInt ⧸ m) 5] :
    let θ : J → ℂ := fun j => (Nat.card (MulAction.fixedBy (Sylow 5 J) j) : ℂ) - 1
    let b : Set (K → ℂ) := {ψ | ∃ lam ∈ BlocksIrr W, ∀ (w : W) (j : J),
      ψ ((w : K) * j) = lam w * θ j}
    Nat.card (Sylow 5 J) = 6 ∧ θ ∈ BlocksIrr J ∧ θ 1 = 5 ∧
    (∀ j : J, orderOf j = 2 → θ j = 1) ∧ (∀ j : J, orderOf j = 3 → θ j = -1) ∧
    (∀ j : J, orderOf j = 5 → θ j = 0) ∧
    (∀ ψ ∈ BlocksIrr J, (∃ n : ℕ, ψ 1 = 5 * n) → ψ = θ) ∧
    BlocksIsBlock m K b ∧ (∀ ψ ∈ b, ψ 1 = 5) ∧
    (∀ ψ ∈ b, CFSG.BrauerThirdMainTheorem.Helpers.blockDefect 5 m ψ W) ∧
    ∀ c : Set (K → ℂ), BlocksIsBlock m K c →
      (∀ ψ ∈ c, CFSG.BrauerThirdMainTheorem.Helpers.blockDefect 5 m ψ W) → c = b := by
  intro θ b
  have := hm
  obtain ⟨basisW⟩ := finiteIrreducibleCharacterBasis_exists (G := W)
  obtain ⟨basisJ⟩ := finiteIrreducibleCharacterBasis_exists (G := J)
  obtain ⟨basisK⟩ := finiteIrreducibleCharacterBasis_exists (G := K)
  obtain ⟨hsyl, ⟨th, hth⟩, h1, h2, h3, h5, huniq, label, himage, hdeg, hdef, hunique⟩ :=
    abelian_five_kernel_alternating_five_unique_defect_block W J hWab hW hWJ hdisj hsup hJ m
      basisW basisJ basisK
  have hb : b = BlocksBlockOf m K (basisK.representation label).character := by
    rw [← CFSG.BlockBasics.coefficientBlock_image basisK m label, himage]
    ext ψ
    constructor
    · rintro ⟨lam, hlam, hψ⟩
      obtain ⟨l, rfl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basisW hlam
      exact ⟨l, hψ⟩
    · rintro ⟨l, hψ⟩
      exact ⟨_, CFSG.BlockBasics.basis_character_mem_irr basisW l, hψ⟩
  have hirr := CFSG.BlockBasics.basis_character_mem_irr basisK label
  have hbBlock : BlocksIsBlock m K b := ⟨_, hirr, hb⟩
  have hbDef : ∀ ψ ∈ b, CFSG.BrauerThirdMainTheorem.Helpers.blockDefect 5 m ψ W := by
    rw [hb]
    exact (CFSG.BlockBasics.forall_blockDefect_iff 5 m hm ⟨_, hirr, rfl⟩
      (CFSG.BrauerThirdMainTheorem.Helpers.mem_blockOf_self m hirr) W).mpr
      ((CFSG.BlockBasics.coefficientBlockDefect_iff basisK m 5 label W).mp hdef)
  refine ⟨hsyl, ?_, h1, h2, h3, h5, fun ψ hψ hdvd => ?_, hbBlock, ?_, hbDef,
    fun c hc hcDef => ?_⟩
  · have hth' : (basisJ.representation th).character = θ := hth
    rw [← hth']
    exact CFSG.BlockBasics.basis_character_mem_irr basisJ th
  · obtain ⟨l, rfl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basisJ hψ
    apply huniq l
    obtain ⟨n, hn⟩ := hdvd
    rw [FiniteComplexRepresentation.character, Representation.char_one] at hn
    exact ⟨n, by exact_mod_cast hn⟩
  · rw [hb, ← CFSG.BlockBasics.coefficientBlock_image basisK m label]
    rintro ψ ⟨l, hl, rfl⟩
    have hmem : (basisK.representation l).character ∈
        (fun l => (basisK.representation l).character) ''
          (coefficientBlock basisK (localizedComplexIntegerRing m) label : Set basisK.index) :=
      ⟨l, hl, rfl⟩
    rw [himage] at hmem
    exact hdeg _ hmem
  · obtain ⟨χ, hχ, rfl⟩ := hc
    have hχmem := CFSG.BrauerThirdMainTheorem.Helpers.mem_blockOf_self m hχ
    obtain ⟨l, rfl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basisK hχ
    have hl := hunique l ((CFSG.BlockBasics.coefficientBlockDefect_iff basisK m 5 l W).mpr
      (hcDef _ hχmem))
    have hlb : (basisK.representation l).character ∈ b := by
      rw [hb, ← CFSG.BlockBasics.coefficientBlock_image basisK m label]
      exact ⟨l, hl, rfl⟩
    exact CFSG.BrauerThirdMainTheorem.Helpers.blocks_eq_of_common_member m ⟨_, hχ, rfl⟩ hbBlock
      hχmem hlb

end CFSG.Semidihedral.Principal
