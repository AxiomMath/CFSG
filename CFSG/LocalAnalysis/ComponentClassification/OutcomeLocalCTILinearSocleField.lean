module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.ReeOrder.JT.PSL2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem isSimpleGroup_projectiveSL {k : Type*} [Field k] {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup (projectiveSL n k) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := k) (n := n) (by omega)
    (Or.inl hn)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.isSimpleGroup

theorem statedClassicalModel_of_projectiveSL {X : Type} [Group X] {k : Type} [Field k]
    [Finite k] {n g : ℕ} (hn : 3 ≤ n) (hg : 1 ≤ g) (hk : Nat.card k = 2 ^ g)
    (eX : X ≃* projectiveSL n k) : StatedClassicalModel X .PSL n 2 g := by
  refine ⟨⟨Nat.prime_two, hg, by omega, ?_, ?_⟩, k, inferInstance, inferInstance, hk,
    ⟨eX.trans (SymmetricLocal.statedProjEquivProjectiveSL n k).symm⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

theorem linear_socle_field_case {A : Type} [Group A] [Finite A] {W : Subgroup A} {a : A}
    (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    {n e : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e) {K : Type} [Field K] (hK : Nat.card K = 2 ^ e)
    (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    {Aₘ : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut n K Aₘ * fieldAut n K σ) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) :
    ∃ c : GL (Fin n) K,
      ((n = 3 ∧ e = 2 ∧ p = 7 ∧ f = 1 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
          ∀ t, σ t = t ^ 2) ∨
        (n = 3 ∧ e = 4 ∧ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 ∧
          StatedClassicalModel L .PSL 3 2 2 ∧ ∀ t, σ t = t ^ 4)) ∧
      (centralizer {fieldAut n K σ} : Set (MulAut (projectiveSL n K))) =
        {α | ∃ (B : GL (Fin n) (fixedField K σ)) (τ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
          α = conjAut n K (subfieldGLMap (Fin n) K (fixedField K σ) B) * fieldAut n K τ *
            dualAut n K ^ ε} ∧
      ρ a = conjAut n K c * fieldAut n K σ * (conjAut n K c)⁻¹ ∧
      (centralizer {a}).map ρ = ρ.range ⊓
        (centralizer {fieldAut n K σ}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
      (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓
        (centralizer {fieldAut n K σ}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
      L.map ρ = (subfieldConj n σ).range.map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
      Nonempty (L ≃* projectiveSL n (fixedField K σ)) ∧
      centralizer (L : Set A) = zpowers a ∧ IsSimpleGroup L ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have hα2 : (conjAut n K Aₘ * fieldAut n K σ) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ :=
    LinearFlag.even_linear_field_involution_descent he hK hn Aₘ σ hσ hα2
  have hρa' : ρ a = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := hρa.trans hH
  obtain ⟨-, ⟨e₁, -⟩, hNinn, hCset, hNC, hNnormal, hCN⟩ :=
    linear_quadratic_field_full_centralizer_rigidity σ (n := n) hn
  set χ := conjAut n K H with hχ
  set β := fieldAut n K σ with hβ
  set N := (subfieldConj n σ).range with hNdef
  have hCa : centralizer {ρ a} = (centralizer {β}).map (MulAut.conj χ).toMonoidHom := by
    rw [hρa', map_conj_centralizer_singleton']
  have hCAimg : (centralizer {a}).map ρ = ρ.range ⊓ centralizer {ρ a} :=
    SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hW : W.map ρ = inner (projectiveSL n K) := map_eq_range_conj φ hρW
  have hWle : inner (projectiveSL n K) ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCWimg : (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (inner (projectiveSL n K) ⊓ centralizer {ρ a}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCWimg] at this
  have hY : (inner (projectiveSL n K) ⊓ centralizer {ρ a}).map (MulAut.conj χ⁻¹).toMonoidHom =
      inner (projectiveSL n K) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀ (inner (projectiveSL n K) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have : Finite (MulAut (projectiveSL n K)) :=
    Finite.of_injective (fun χ : MulAut (projectiveSL n K) => (χ : projectiveSL n K → _))
      (fun χ₁ χ₂ h => MulEquiv.ext (congrFun h))
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have : IsSimpleGroup (projectiveSL n (fixedField K σ)) := isSimpleGroup_projectiveSL hn
  have hNsimple : IsSimpleGroup N := e₁.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNsimple hL₀N
  have hid : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, Subgroup.map_map, hid, Subgroup.map_id]
  have eL : L ≃* projectiveSL n (fixedField K σ) :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans e₁.symm
  have hLsimple : IsSimpleGroup L := eL.isSimpleGroup
  have hLnab : ∃ x y : L, x * y ≠ y * x := exists_ne_commute_of_isQuasisimple hLCW.2.2
  have eZ : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hLnab)).trans
      QuotientGroup.quotientBot
  have hσσ : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    have := Fintype.ofFinite K
    rw [pow_two, RingAut.mul_apply, hσx, hσx, ← pow_mul, ← pow_add,
      show e / 2 + e / 2 = e by obtain ⟨m, hm⟩ := heven; omega, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hk : Nat.card (fixedField K σ) = 2 ^ (e / 2) := by
    have h1 := fixedField_card_square K σ hσσ hσ
    rw [hK, show e = 2 * (e / 2) by obtain ⟨m, hm⟩ := heven; omega, pow_mul'] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  have hg : 1 ≤ e / 2 := by obtain ⟨m, hm⟩ := heven; omega
  have hX := statedClassicalModel_of_projectiveSL hn hg hk (eZ.trans eL)
  obtain ⟨hpar, hA7, hP34⟩ :=
    SymmetricLocal.small_standard_source_even_higher_linear_parameters_stated hn hX
  have hcentN : (centralizer (N : Set (MulAut (projectiveSL n K)))).map
      (MulAut.conj χ).toMonoidHom =
        centralizer ((N.map (MulAut.conj χ).toMonoidHom : Subgroup _) : Set _) := by
    have h := CFSG.Walter.JT.map_centralizer_of_injective (MulAut.conj χ).toMonoidHom
      (MulAut.conj χ).injective N
    rwa [MonoidHom.range_eq_top.mpr (MulAut.conj χ).surjective, top_inf_eq] at h
  have hcent : centralizer (L : Set A) = zpowers a := by
    apply Subgroup.map_injective hinj
    rw [CFSG.Walter.JT.map_centralizer_of_injective ρ hinj L, hLimg, ← hcentN, hCN,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    have hz : (MulAut.conj χ).toMonoidHom β = ρ a := by
      rw [hρa']
      rfl
    rw [hz]
    exact inf_eq_right.mpr (zpowers_le.mpr ⟨a, rfl⟩)
  have hrest : (centralizer {β} : Set (MulAut (projectiveSL n K))) =
        {α | ∃ (B : GL (Fin n) (fixedField K σ)) (τ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
          α = conjAut n K (subfieldGLMap (Fin n) K (fixedField K σ) B) * fieldAut n K τ *
            dualAut n K ^ ε} ∧
      ρ a = χ * β * χ⁻¹ ∧
      (centralizer {a}).map ρ = ρ.range ⊓ (centralizer {β}).map (MulAut.conj χ).toMonoidHom ∧
      (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓
        (centralizer {β}).map (MulAut.conj χ).toMonoidHom ∧
      L.map ρ = N.map (MulAut.conj χ).toMonoidHom ∧
      Nonempty (L ≃* projectiveSL n (fixedField K σ)) ∧
      centralizer (L : Set A) = zpowers a ∧ IsSimpleGroup L ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) := by
    exact ⟨hCset, hρa', by rw [hCAimg, hCa], by rw [hCWimg, hCa], hLimg, ⟨eL⟩, hcent, hLsimple,
      hA7⟩
  have heq : e = 2 * (e / 2) := by obtain ⟨m, hm⟩ := heven; omega
  refine ⟨H, ?_, hrest⟩
  rcases hsrc with h2 | ⟨e7⟩ | h322
  · obtain ⟨hn3, hg1, hp7, hf1⟩ := hpar p f hp2 h2
    refine Or.inl ⟨hn3, by omega, hp7, hf1, h2, fun t => ?_⟩
    rw [hσx, hg1, pow_one]
  · exact (not_nonempty_iff.mpr hA7 e7).elim
  · obtain ⟨hn3, hg2⟩ := hP34 h322
    obtain ⟨hadm, K₃, i₁, i₂, hK₃, ⟨χ₃⟩⟩ := h322
    refine Or.inr ⟨hn3, by omega, ⟨hadm, K₃, i₁, i₂, hK₃, ⟨χ₃⟩⟩,
      ⟨hadm, K₃, i₁, i₂, hK₃, ⟨eZ.symm.trans χ₃⟩⟩, fun t => ?_⟩
    rw [hσx, hg2]
    norm_num

end CFSG.ComponentClassification.OutcomeLocal
