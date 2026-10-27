module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainShapeBKill
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelShapeB
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelQ3
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Close
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Child

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Stage1

variable {G : Type} [Group G]

theorem exists_link_shapeB_two
    {t r : G} {L : Subgroup G} (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) (hK : Stage0.StepK t L)
    (hSB : Stage0.ShapeB t L r) :
    ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G)
      (Q₃ P₃ : Subgroup G) (ψ₃ : V6 → G) (p₃ u₃ : Fin 6 → G),
      RadicalData .plus L U Q P a ψ p ∧ UGens .plus U Q ψ u ∧
        LinkFacts .plus L U Q P a ψ p u ∧ AutCent L Q ∧
      closure (Set.range u) ⊓ Q = ⊥ ∧ (∀ x ∈ L, x ∈ normalizer (U : Set G) → x ∈ U) ∧
      RadicalData .plus L U Q₃ P₃ a ψ₃ p₃ ∧ LinkFacts .plus L U Q₃ P₃ a ψ₃ p₃ u₃ ∧
      ψ₃ (Pi.single 0 1) = ψ (Pi.single 0 1) ∧ ψ₃ (Pi.single 1 1) = ψ (Pi.single 1 1) ∧
      ψ₃ (Pi.single 2 1) = u 3 ∧ ψ₃ (Pi.single 3 1) = ψ (Pi.single 2 1) ∧
      ψ₃ (Pi.single 4 1) = u 4 ∧ ψ₃ (Pi.single 5 1) = u 5 ∧
      (∀ x ∈ centralizer ({t} : Set G),
        x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → x ∈ L ⊔ zpowers t) ∧
      (∀ x ∈ centralizer ({t} : Set G),
        x ∈ normalizer ((Q₃ ⊔ zpowers t : Subgroup G) : Set G) → x ∈ L ⊔ zpowers t) := by
  obtain ⟨e⟩ := OmegaEight.nonempty_mulEquiv_omegaT hL
  set θ : L ≃* Model.Lm .plus :=
    (OmegaEight.mulEquivQuotientCenter hZ).symm.trans (e.trans OmegaEight.omegaRestrictEquiv)
  set θ₃ : L ≃* Model.Lm .plus := θ.trans Model.sigL.symm
  have hM := Model.modelLinkFacts .plus
  have hodd := OmegaEight.involutionsInOddPart_of_center_eq_bot hZ hL
  have hF := hM.transport θ
  have hA := (Model.autCent .plus).transport hM.Q_le_L θ
  have hF₃ := hM.transport θ₃
  have hU₃ : pull θ₃ (Model.UQm .plus) = pull θ (Model.UQm .plus) := by
    rw [pull_trans, Model.pull_sigL_symm_UQm]
  have ha₃ : pullE θ₃ (Model.aM .plus) hM.a_mem_L = pullE θ (Model.aM .plus) hM.a_mem_L := by
    rw [pullE_trans, MulEquiv.symm_symm, Model.sigL_aM]
  rw [hU₃, ha₃] at hF₃
  have hψ₃ : ∀ j : Fin 6, pullE θ₃ (Model.psiM .plus (Pi.single j 1)) (hM.ψ_mem_L _) =
      pullE θ (Model.sigTargetM j) (by
        rw [← Model.sigL_psiM j]
        exact (Model.sigL ⟨Model.psiM .plus (Pi.single j 1), _⟩).2) := by
    intro j
    rw [pullE_trans, MulEquiv.symm_symm]
    exact pullE_congr (Model.sigL_psiM j) _ _
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, hF.radicalData hodd, ⟨hF.u_mem, hF.u_act, hF.U_le⟩,
    hF, hA, ?_, ?_, hF₃.radicalData hodd, hF₃, hψ₃ 0, hψ₃ 1, hψ₃ 2, hψ₃ 3, hψ₃ 4, hψ₃ 5,
    CPrimeModel.normalizer_E_shapeB_plus hK hSB θ,
    CPrimeModel.normalizer_E_shapeB_plus hK hSB θ₃⟩
  · rw [eq_bot_iff]
    refine le_trans (inf_le_inf_right _ (closure_pullE_le θ (Model.uM .plus) hM.u_mem_L)) ?_
    rw [pull_inf_bot θ Model.closure_uM_inf_QMm]
  · intro x hx hxN
    exact mem_pull_of_normalizes θ hM.U_le_L (fun y hy hyN => Model.normalizer_UQm hy hyN) hx hxN

theorem l9_shapeB [Finite G]
    {t r : G} {L U Q P : Subgroup G}
    {a : G} {ψ : V6 → G} {p u : Fin 6 → G} (hK : Stage0.StepK t L) (hSB : Stage0.ShapeB t L r)
    (hS : Setup .plus t L U Q P a ψ p) (hu : UGens .plus U Q ψ u)
    (hU6 : closure (Set.range u) ⊓ Q = ⊥) (hNL : ∀ x ∈ L, x ∈ normalizer (U : Set G) → x ∈ U)
    (hNQ : ∀ x ∈ centralizer ({t} : Set G),
      x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → x ∈ L ⊔ zpowers t)
    (hQ₃ : ∃ (Q₃ P₃ : Subgroup G) (ψ₃ : V6 → G) (p₃ : Fin 6 → G) (W₃ : Subgroup G),
      Setup .plus t L U Q₃ P₃ a ψ₃ p₃ ∧ Q₃ ≤ W₃ ∧ t ∉ W₃ ∧ Nat.card W₃ = 4096 ∧
      (∀ x ∈ W₃, ∀ y ∈ W₃, x * y = y * x) ∧
      (∀ n ∈ normalizer ((Q₃ ⊔ zpowers t : Subgroup G) : Set G), ∀ w ∈ W₃, n * w * n⁻¹ ∈ W₃) ∧
      ({ψ (Pi.single 0 1), ψ (Pi.single 1 1), ψ (Pi.single 2 1), u 3, u 4, u 5} : Set G) ⊆ Q₃) :
    L9 t Q := by
  intro W hQW htW hcard hcomm hnorm
  have hW : Premises t Q W := ⟨hQW, htW, hcard, hcomm, hnorm⟩
  rcases hW.sq_eq_one_or_inv hS (endF2 .plus) with h | hinv
  · exact h
  · exfalso
    obtain ⟨Q₃, P₃, ψ₃, p₃, W₃, hS₃, h1, h2, h3, h4, h5, hsub⟩ := hQ₃
    exact homocyclic_false_shapeB hK hS (uData_of_uGens hu) hU6 hNL hNQ
      (fun x hx => CPrimeModel.pow_three_mem_of_shapeB hK hSB hx) hSB.relIndex_eq
      (exists_n3_sq hS₃ ⟨h1, h2, h3, h4, h5⟩ hsub fun x hx => a_central hS (uData_of_uGens hu) hx)
      hW hinv

section Final


theorem false_of_shapeB_plus' [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) {L : Subgroup G} (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) {t r : G}
    (hK : Stage0.StepK t L) (hSB : Stage0.ShapeB t L r) : False := by
  obtain ⟨U, Q, P, a, ψ, p, u, Q₃, P₃, ψ₃, p₃, u₃, hR, hU, hF, -, hU6, hNL, hR₃, hF₃,
    e0, e1, e2, e3, e4, e5, hNQ, hNQ₃⟩ := exists_link_shapeB_two hZ hL hK hSB
  have hS := Stage0.setup_of_shapeB hK hSB hR hF hNQ
  have hS₃ := Stage0.setup_of_shapeB hK hSB hR₃ hF₃ hNQ₃
  have hZ₃ := hS₃.mem_Zset hG hnab
  refine Stage0.false_of_shapeB_of_link hG hnab hK hSB hR hU hF hNQ
    (l9_shapeB hK hSB hS hU hU6 hNL hNQ ⟨Q₃, P₃, ψ₃, p₃, hS₃.Wsub hZ₃, hS₃,
      hS₃.Q_le_Wsub hZ₃, hS₃.t_not_mem_Wsub hZ₃, hS₃.card_Wsub hZ₃,
      fun x hx y hy => hS₃.Wsub_comm hZ₃ hx hy,
      fun n hn w hw => (mem_normalizer_iff.1 (hS₃.normalizer_E_le_normalizer_Wsub hZ₃ hn) w).1 hw,
      ?_⟩)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← e0]; exact hF₃.ψ_mem _
  · rw [← e1]; exact hF₃.ψ_mem _
  · rw [← e3]; exact hF₃.ψ_mem _
  · rw [← e2]; exact hF₃.ψ_mem _
  · rw [← e4]; exact hF₃.ψ_mem _
  · rw [← e5]; exact hF₃.ψ_mem _

theorem endgameB7 : Stage0.EndgameB7 := fun _ _ _ _ _ _ hH hK hB =>
  false_of_shapeB_plus' hH.1.simple hH.1.nonab hH.2.1 hH.2.2 hK hB

end Final

end CFSG.EvenSmallLie.OmegaEight.Chain
