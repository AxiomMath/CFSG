module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23U
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Fus
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocle
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven
public import CFSG.LieType.Simplicity.Classical
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix Assembly.LowTwoRank LocalAnalysis.ComponentInitial UnitaryHigher
open ClassicalGroups.UnitaryFlag LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open UnbalancedCatalog.UnitaryFieldTransfer

@[expose] def u34G : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def u34A : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 1, 1, 1; 0, 1, 1]

@[expose] def u34Ai : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 1; 1, 1, 0; 1, 1, 1]

@[expose] def u34N : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 1, 1, 0; 0, 0, 0]

theorem u34_facts : u34N * u34N = 0 ∧ u34Nᵀ = u34N ∧ u34Aᵀ * u34A = 1 + u34N ∧
    u34A * u34Ai = 1 ∧ u34G = 1 + u34N ∧ u34Gᵀ * u34G = 1 ∧ u34G * u34G = 1 ∧ u34G ≠ 1 := by
  decide

@[expose] def u34GL : GL (Fin 3) (ZMod 2) :=
  ⟨u34G, u34G, u34_facts.2.2.2.2.2.2.1, u34_facts.2.2.2.2.2.2.1⟩

theorem card_of_lieModel_U34 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSU 3 2 2) :
    Nat.card Y = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four (h.statedClassicalModel (by decide))

theorem u34 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSU 3 2 2 := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  have := hN
  obtain ⟨⟨-, he, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ :=
    RestrictedStd.statedClassicalModel_of_lieModel (by decide) hY
  have h : UnitaryFieldData 2 2 K := ⟨Nat.prime_two, he, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := h.charP
  have : CharP h.fixedField 2 := fixedField_charP h
  have hs : IsSimpleGroup ↥N := (LieType.Simplicity.fam_classical_converse ↥N
    ⟨.PSU, 3, 2, 2, RestrictedStd.statedClassicalModel_of_lieModel (by decide) hY⟩).2.2
  have hnab : ∃ x y : ↥N, x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have : IsMulCommutative ↥N := ⟨⟨hc⟩⟩
    have hpr := Group.is_simple_iff_prime_card.mp hs
    rw [card_of_lieModel_U34 hY] at hpr
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
  let φ' : ↥N ≃* unitaryPSU h 3 := φ.trans (unitaryPSUEquiv h (by norm_num)).symm
  obtain ⟨ρ, -, hρW, -, -, -, C, hC', -, θ, -, ρC, hρC, hρCinj, σ, hσ, hρCa, Cl, hCl, -, -,
      hinjU, -, -, -, -, -, hrows, -⟩ :=
    OutcomeLocal.faithful_even_unitary_socle_small_source_involution_selector hs hnab hC hα hJN
      hJc hp' hp'2 hf' hsrc h (by norm_num : 3 ≤ 3) (by norm_num) φ'
  rcases hrows with ⟨-, -, -, -, hC1, -, -, hLmap, -⟩ | ⟨hn4, -⟩ | ⟨hn5, -⟩
  rotate_left
  · omega
  · omega
  have hCl1 : (Cl : Matrix (Fin 3) (Fin 3) h.fixedField) = 1 := by
    apply map_subtype_injective h
    dsimp only
    rw [hCl, hC1, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨hN2, hNT, hAA, hAi, hgN, hgO, hsq, hne⟩ := u34_facts
  have hmem : GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) h.fixedField) u34GL ∈
      matrixIsometryGroup (Cl : Matrix (Fin 3) (Fin 3) h.fixedField) := by
    rw [hCl1]
    exact map_mem_isometry_one hgO
  let gI : matrixIsometryGroup (Cl : Matrix (Fin 3) (Fin 3) h.fixedField) := ⟨_, hmem⟩
  have hgM : ((gI : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) =
      (1 + u34N).map (ZMod.castHom (dvd_refl 2) h.fixedField) := by
    rw [← hgN]
    rfl
  have hz : ((primeFormConjHom h (C : Matrix (Fin 3) (Fin 3) K)).comp (fixedIsometryHom h hCl))
      gI ∈ J.map ρC := by
    rw [hLmap]
    exact ⟨gI, rfl⟩
  obtain ⟨z, hzJ, hρz⟩ := mem_map.mp hz
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective ρC hρCinj, hρz, orderOf_injective _ hinjU, ← Subgroup.orderOf_coe]
    show orderOf (GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) h.fixedField) u34GL) = 2
    rw [orderOf_injective _ map_castHom_injective_fin]
    exact orderOf_eq_prime (Units.ext (by rw [pow_two, Units.val_mul]; exact hsq))
      fun h1 => hne (by rw [← Units.val_one, ← h1]; rfl)
  obtain ⟨k, hkey⟩ := exists_lang_witness h hC' hC1 hCl hσ hN2 hNT hAA hAi gI hgM
  have hργ₀ : ρC ((φ'.symm (θ (k : primeFormP h (C : Matrix (Fin 3) (Fin 3) K))) : N) : G) =
      MulAut.conj (k : primeFormP h (C : Matrix (Fin 3) (Fin 3) K)) := by
    refine MulEquiv.ext fun x => ?_
    rw [hρC, hρW, MulEquiv.apply_symm_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  refine concl_of_witness hJN hJα (oneClass_of_small hZ hsmall) hzJ hz2
    (φ'.symm (θ (k : primeFormP h (C : Matrix (Fin 3) (Fin 3) K)))).2 (hρCinj ?_)
  rw [map_mul, map_mul, map_inv, hργ₀, hρCa, map_mul, hρCa, hρz]
  exact hkey

end CFSG.ComponentClassification.GSThmB.CF23I
