module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23U
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L52
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocle
public import CFSG.LieType.Simplicity.Classical
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix Assembly.LowTwoRank LocalAnalysis.ComponentInitial UnitaryHigher
open ClassicalGroups.UnitaryFlag LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open UnbalancedCatalog.UnitaryFieldTransfer
open scoped commutatorElement

@[expose] def u52A : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 0, 1; 1, 1, 1, 0, 1; 0, 1, 1, 0, 1; 0, 0, 1, 1, 1; 0, 0, 0, 1, 1]

@[expose] def u52Ai : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 1, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 1, 1; 1, 1, 1, 1, 0; 1, 1, 1, 1, 1]

@[expose] def u52N : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 0]

theorem u52_facts : u52N * u52N = 0 ∧ u52Nᵀ = u52N ∧ u52Aᵀ * u52A = 1 + u52N ∧
    u52A * u52Ai = 1 ∧ l52MA * l52MB * l52MA * l52MB = 1 + u52N := by
  decide

theorem card_of_lieModel_U52 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSU 5 2 1) :
    Nat.card Y = 13685760 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two (h.statedClassicalModel (by decide))

theorem u52 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSU 5 2 1 := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  have := hN
  obtain ⟨⟨-, he, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ :=
    RestrictedStd.statedClassicalModel_of_lieModel (by decide) hY
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, he, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := h.charP
  have : CharP h.fixedField 2 := fixedField_charP h
  have hs : IsSimpleGroup ↥N := (LieType.Simplicity.fam_classical_converse ↥N
    ⟨.PSU, 5, 2, 1, RestrictedStd.statedClassicalModel_of_lieModel (by decide) hY⟩).2.2
  have hnab : ∃ x y : ↥N, x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have : IsMulCommutative ↥N := ⟨⟨hc⟩⟩
    have hpr := Group.is_simple_iff_prime_card.mp hs
    rw [card_of_lieModel_U52 hY] at hpr
    exact absurd hpr (by norm_num)
  have hJc : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  obtain ⟨p', f', hp', hp'2, hf', hsrc⟩ : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 p f ∨
        Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∨
        StatedClassicalModel (↥J ⧸ center ↥J) .PSL 3 2 2) := by
    rcases hsmall with ⟨p', f', hp', hp'2, hf', -, hm'⟩ | h7
    · exact ⟨p', f', hp', hp'2, hf',
        Or.inl (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm')⟩
    · exact ⟨3, 1, Nat.prime_three, by decide, le_rfl, Or.inr (Or.inl h7)⟩
  let φ' : ↥N ≃* unitaryPSU h 5 := φ.trans (unitaryPSUEquiv h (by norm_num)).symm
  obtain ⟨ρ, -, hρW, -, -, -, C, hC', -, θ, -, ρC, hρC, hρCinj, σ, hσ, hρCa, Cl, hCl, -, -,
      hinjU, -, -, -, -, -, hrows, -⟩ :=
    OutcomeLocal.faithful_even_unitary_socle_small_source_involution_selector hs hnab hC hα hJN
      hJc hp' hp'2 hf' hsrc h (by norm_num : 3 ≤ 5) (by norm_num) φ'
  rcases hrows with ⟨hn3, -⟩ | ⟨hn4, -⟩ | ⟨-, -, -, -, hC1, -, -, -, -, -, hLmap, -⟩
  · omega
  · omega
  have hCl1 : (Cl : Matrix (Fin 5) (Fin 5) h.fixedField) = 1 := by
    apply map_subtype_injective h
    dsimp only
    rw [hCl, hC1, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨hA, hB, -, -, hsq, hne⟩ := l52_facts
  obtain ⟨hN2, hNT, hAA, hAi, hgN⟩ := u52_facts
  have hmem : ∀ x : GL (Fin 5) (ZMod 2),
      (x : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ * (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 →
        GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) h.fixedField) x ∈
          matrixIsometryGroup (Cl : Matrix (Fin 5) (Fin 5) h.fixedField) := by
    intro x hx
    rw [hCl1]
    exact map_mem_isometry_one hx
  let aI : matrixIsometryGroup (Cl : Matrix (Fin 5) (Fin 5) h.fixedField) := ⟨_, hmem _ hA⟩
  let bI : matrixIsometryGroup (Cl : Matrix (Fin 5) (Fin 5) h.fixedField) := ⟨_, hmem _ hB⟩
  have hcoe : ((⁅aI, bI⁆ : matrixIsometryGroup (Cl : Matrix (Fin 5) (Fin 5) h.fixedField)) :
      GL (Fin 5) h.fixedField) =
        GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) h.fixedField) ⁅l52A, l52B⁆ := by
    rw [map_commutatorElement]
    exact map_commutatorElement (matrixIsometryGroup _).subtype aI bI
  have hgM : (((⁅aI, bI⁆ : matrixIsometryGroup (Cl : Matrix (Fin 5) (Fin 5) h.fixedField)) :
      GL (Fin 5) h.fixedField) : Matrix (Fin 5) (Fin 5) h.fixedField) =
        (1 + u52N).map (ZMod.castHom (dvd_refl 2) h.fixedField) := by
    rw [hcoe, ← hgN, ← coe_l52_comm]
    rfl
  have hz : ((primeFormConjHom h (C : Matrix (Fin 5) (Fin 5) K)).comp (fixedIsometryHom h hCl))
      ⁅aI, bI⁆ ∈ J.map ρC := by
    rw [hLmap, map_commutatorElement]
    exact commutator_mem_commutator ⟨aI, rfl⟩ ⟨bI, rfl⟩
  obtain ⟨z, hzJ, hρz⟩ := mem_map.mp hz
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective ρC hρCinj, hρz, orderOf_injective _ hinjU, ← Subgroup.orderOf_coe,
      hcoe, orderOf_injective _ map_castHom_injective]
    exact orderOf_eq_prime hsq hne
  obtain ⟨k, hkey⟩ := exists_lang_witness h hC' hC1 hCl hσ hN2 hNT hAA hAi ⁅aI, bI⁆ hgM
  have hργ₀ : ρC ((φ'.symm (θ (k : primeFormP h (C : Matrix (Fin 5) (Fin 5) K))) : N) : G) =
      MulAut.conj (k : primeFormP h (C : Matrix (Fin 5) (Fin 5) K)) := by
    refine MulEquiv.ext fun x => ?_
    rw [hρC, hρW, MulEquiv.apply_symm_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  refine concl_of_witness hJN hJα (oneClass_of_small hZ hsmall) hzJ hz2
    (φ'.symm (θ (k : primeFormP h (C : Matrix (Fin 5) (Fin 5) K)))).2 (hρCinj ?_)
  rw [map_mul, map_mul, map_inv, hργ₀, hρCa, map_mul, hρCa, hρz]
  exact hkey

end CFSG.ComponentClassification.GSThmB.CF23I
