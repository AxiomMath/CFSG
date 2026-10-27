module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TypeL4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped commutatorElement

variable {F : Type} [Field F] [Fintype F]

theorem exists_centralizer_embedding_card (k : GL (Fin 4) F) (l : Fˣ)
    (hsq : k ^ 2 = GeneralLinearGroup.scalar (Fin 4) l) (hns : ¬ IsSquare (l : F)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (ρ : Subgroup.centralizer {k} →* GL (Fin 2) E),
      Nat.card E = Nat.card F ^ 2 ∧ Function.Injective ρ := by
  classical
  have hstr := nonsquare_projective_centralizer_structure 4 (by norm_num) k l hsq hns
  let : Fact (¬ IsSquare l.val) := ⟨hns⟩
  let := matrixModule k l hsq
  dsimp only at hstr
  obtain ⟨-, hfinE, hm, -, -, -, -, -, -, -, -, e', -, -, -, -, -, -, -, -⟩ := hstr
  have hm2 : Module.finrank (extension l.val) (Fin 4 → F) = 2 := by omega
  set τ : GL (Fin (Module.finrank (extension l.val) (Fin 4 → F))) (extension l.val) ≃*
      GL (Fin 2) (extension l.val) :=
    Units.mapEquiv (Matrix.reindexRingEquiv (extension l.val) (finCongr hm2)).toMulEquiv with hτ
  have hfin : Finite (extension l.val) := Module.finite_of_finite F
  refine ⟨extension l.val, inferInstance, hfin, τ.toMonoidHom.comp e'.toMonoidHom, ?_,
    τ.injective.comp e'.injective⟩
  rw [Module.natCard_eq_pow_finrank (K := F), hfinE]

omit [Fintype F] in
theorem commutator_mem_C₀ {X Y : SpecialLinearGroup (Fin 4) F}
    (hX : proj 4 F X ∈ Subgroup.centralizer {proj 4 F k₀})
    (hY : proj 4 F Y ∈ Subgroup.centralizer {proj 4 F k₀}) : ⁅X, Y⁆ ∈ C₀ F := by
  have hsc : scalars 4 F ≤ Subgroup.center (SpecialLinearGroup (Fin 4) F) :=
    (scalars_eq_center 4 F).le
  have hmem : ∀ Z : SpecialLinearGroup (Fin 4) F,
      proj 4 F Z ∈ Subgroup.centralizer {proj 4 F k₀} → Z * k₀ * Z⁻¹ * k₀⁻¹ ∈ scalars 4 F := by
    intro Z hZ
    rw [Subgroup.mem_centralizer_singleton_iff] at hZ
    rw [← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, hZ]
    group
  rw [C₀, Subgroup.mem_centralizer_singleton_iff]
  exact commutator_comm_of_comm_mod hsc (hmem X hX) (hmem Y hY)

omit [Fintype F] in
theorem le_J₀ {J' : Subgroup (projectiveSL 4 F)}
    (hJk : J' ≤ Subgroup.centralizer {proj 4 F k₀}) (hJp : ⁅J', J'⁆ = J') : J' ≤ J₀ F := by
  have hC : ⁅Subgroup.centralizer {proj 4 F k₀}, Subgroup.centralizer {proj 4 F k₀}⁆ ≤
      (C₀ F).map (proj 4 F) := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨X, rfl⟩ := proj_surjective 4 F u
    obtain ⟨Y, rfl⟩ := proj_surjective 4 F v
    exact ⟨⁅X, Y⁆, commutator_mem_C₀ hu hv, by rw [map_commutatorElement]⟩
  have h1 : J' ≤ (C₀ F).map (proj 4 F) := by
    rw [← hJp]
    exact (Subgroup.commutator_mono hJk hJk).trans hC
  rw [J₀, S₀, Subgroup.map_commutator, ← hJp]
  exact Subgroup.commutator_mono h1 h1

omit [Fintype F] in
theorem toGL_k₀_sq : SpecialLinearGroup.toGL (k₀ : SpecialLinearGroup (Fin 4) F) ^ 2 =
    GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, sq]
  change stdJ * stdJ = _
  rw [stdJ_mul_stdJ]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem card_S₀_le (hF : Fintype.card F % 4 = 3) :
    Nat.card (S₀ F) ≤ Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by
  classical
  have hns : ¬ IsSquare ((-1 : Fˣ) : F) := by
    rw [Units.val_neg, Units.val_one, FiniteField.isSquare_neg_one_iff]
    omega
  set k := SpecialLinearGroup.toGL (k₀ : SpecialLinearGroup (Fin 4) F) with hk
  obtain ⟨E, _, _, ρ, hE, hρ⟩ := exists_centralizer_embedding_card k (-1) toGL_k₀_sq hns
  let ι : C₀ F →* Subgroup.centralizer {k} :=
    (SpecialLinearGroup.toGL.comp (C₀ F).subtype).codRestrict _ fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, Subgroup.coe_subtype, hk,
        ← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_singleton_iff.mp x.2
  have hι : Function.Injective ι := fun a b hab => by
    apply Subtype.ext
    apply SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val hab
  set ψ : C₀ F →* Eˣ := GeneralLinearGroup.det.comp (ρ.comp ι) with hψ
  have hS : S₀ F ≤ ψ.ker.map (C₀ F).subtype := by
    rw [S₀, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : C₀ F), (⟨b, hb⟩ : C₀ F)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hSC : S₀ F ≤ C₀ F := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  let f : S₀ F → SpecialLinearGroup (Fin 2) E := fun x =>
    ⟨(ρ (ι ⟨x, hSC x.2⟩) : Matrix (Fin 2) (Fin 2) E), by
      obtain ⟨y, hy, hyx⟩ := hS x.2
      have hy' : y = ⟨x, hSC x.2⟩ := Subtype.ext hyx
      rw [← hy']
      have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
      rwa [hψ, MonoidHom.comp_apply, GeneralLinearGroup.val_det_apply, Units.val_one] at this⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ρ (ι ⟨x, hSC x.2⟩) = ρ (ι ⟨y, hSC y.2⟩) := Units.ext (congrArg Subtype.val hxy)
    have h2 := hι (hρ h1)
    exact Subtype.ext (congrArg (fun z : C₀ F => (z : SpecialLinearGroup (Fin 4) F)) h2)
  calc Nat.card (S₀ F) ≤ Nat.card (SpecialLinearGroup (Fin 2) E) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card E * (Nat.card E ^ 2 - 1) := by
        let := Fintype.ofFinite E
        have hq : 1 < Fintype.card E := Fintype.one_lt_card
        rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
          Nat.card_eq_fintype_card, show Fintype.card E ^ 2 - Fintype.card E =
            Fintype.card E * (Fintype.card E - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
          Nat.mul_div_cancel _ (by omega), mul_comm]
    _ = Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by rw [hE]

theorem two_mul_card_J₀_le (hF : Fintype.card F % 4 = 3) :
    2 * Nat.card (J₀ F) ≤ Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by
  classical
  set φ : S₀ F →* projectiveSL 4 F := (proj 4 F).comp (S₀ F).subtype with hφ
  have hrange : φ.range = J₀ F := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, J₀]
  have hneg : (⟨-1, neg_one_mem_S₀⟩ : S₀ F) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, proj_eq_one_iff,
      mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Units.val_neg,
      Units.val_one, map_neg, map_one]
  have h2F := two_ne_zero_of_card_mod_four hF
  have hne : (⟨-1, neg_one_mem_S₀⟩ : S₀ F) ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg (fun y : S₀ F =>
      ((y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h) 0) 0
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Subgroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply h2F
    linear_combination -this
  have hker : 2 ≤ Nat.card φ.ker := by
    have : 1 < Nat.card φ.ker := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hneg
      exact hne hneg
    omega
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hrange] at hmul
  calc 2 * Nat.card (J₀ F) ≤ Nat.card φ.ker * Nat.card (J₀ F) := Nat.mul_le_mul_right _ hker
    _ = Nat.card (S₀ F) := hmul
    _ ≤ _ := card_S₀_le hF

theorem hasUnipotents_J₀ (hF : Fintype.card F % 4 = 3) : HasUnipotents (J₀ F) := by
  have h2 := two_ne_zero_of_card_mod_four hF
  exact ⟨⟨_, slA_mem_S₀ h2 1 0, rfl⟩, ⟨_, slA_mem_S₀ h2 0 1, rfl⟩, ⟨_, slB_mem_S₀ h2 1 0, rfl⟩⟩

theorem eq_J₀ (hF : Fintype.card F % 4 = 3) {J' : Subgroup (projectiveSL 4 F)}
    (hJk : J' ≤ Subgroup.centralizer {proj 4 F k₀}) (hJp : ⁅J', J'⁆ = J')
    (hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J') : J' = J₀ F :=
  Subgroup.eq_of_le_of_card_ge (le_J₀ hJk hJp) (by
    have := two_mul_card_J₀_le hF
    omega)

end StabL

end CFSG.ComponentClassification.CatFactsL4U4
