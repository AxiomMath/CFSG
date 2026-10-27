module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInOrth
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Close
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage0
open CFSG.EvenSmallLie.OmegaEight.SplitC

variable {G : Type} [Group G] {t : G} {L : Subgroup G}

theorem levi_of {ε : Eps} {H₀ : Subgroup G} (hS : ShapeSplit t L H₀) {U Q P : Subgroup G} {a : G}
    {ψ : V6 → G} {p : Fin 6 → G} (hR : RadicalData ε L U Q P a ψ p) {x₀ : G}
    (hΘ : ∃ Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin (Model.aDeg ε)),
      (∀ y, Θ y ∈ Model.AT ε) ∧ (∀ y, Θ y = 1 ↔ (y : G) ∈ zpowers t) ∧
        ∀ v (hv : ψ v ∈ centralizer ({t} : Set G)), Θ ⟨ψ v, hv⟩ = Model.psiTM ε v)
    (hx₀ : x₀ ∈ H₀) (hx₀Q : x₀ ∈ normalizer (Q : Set G))
    (hNQ : ∀ h ∈ H₀, h ∈ normalizer (Q : Set G) → h ∈ P ⊔ zpowers x₀)
    (hOrth : InducesOrth ε H₀ Q ψ) :
    ∃ X : Subgroup G, X ≤ centralizer ({t} : Set G) ⊓ normalizer (Q : Set G) ∧
      X ⊓ (Q ⊔ zpowers t) = ⊥ ∧ ∀ σ ∈ orthGroup ε, ∃ g ∈ X, ∀ v, lin ψ g v = σ v := by
  obtain ⟨Θ, -, -, hΘψ⟩ := hΘ
  set z0 : Fin (Model.aDeg ε) := ⟨0, by have := Model.one_le_aDeg ε; omega⟩ with hz0def
  have hz0 : z0 ∈ Model.Rset ε := Model.aBase_mem_R Model.zero_mem_aBase
  have hKH : P ⊔ zpowers x₀ ≤ H₀ :=
    sup_le (hR.P_le_L.trans hS.L_le) (zpowers_le.2 hx₀)
  have hKC : P ⊔ zpowers x₀ ≤ centralizer ({t} : Set G) := hKH.trans hS.le_centralizer
  have hKN : P ⊔ zpowers x₀ ≤ normalizer (Q : Set G) :=
    sup_le hR.P_le_normalizer (zpowers_le.2 hx₀Q)
  have hψC : ∀ v, ψ v ∈ centralizer ({t} : Set G) := fun v =>
    hS.le_centralizer (hS.L_le (hR.Q_le_L (hR.ψ_mem v)))
  set X : Subgroup G := (P ⊔ zpowers x₀) ⊓
    ((MulAction.stabilizer (Equiv.Perm (Fin (Model.aDeg ε))) z0).comap Θ).map
      (centralizer ({t} : Set G)).subtype with hX
  have hmemX : ∀ h, h ∈ X ↔ h ∈ P ⊔ zpowers x₀ ∧
      ∃ hh : h ∈ centralizer ({t} : Set G), Θ ⟨h, hh⟩ z0 = z0 := by
    intro h
    rw [hX, mem_inf, mem_map]
    constructor
    · rintro ⟨hK, y, hy, rfl⟩
      exact ⟨hK, y.2, hy⟩
    · rintro ⟨hK, hh, hfix⟩
      exact ⟨hK, ⟨h, hh⟩, hfix, rfl⟩
  have hconjQ : ∀ (h : G) (hh : h ∈ centralizer ({t} : Set G)), h ∈ normalizer (Q : Set G) →
      ∀ v, ∃ w, (Θ ⟨h, hh⟩)⁻¹ * Model.psiTM ε v * Θ ⟨h, hh⟩ = Model.psiTM ε w ∧
        ψ w = h⁻¹ * ψ v * h⁻¹⁻¹ := by
    intro h hh hhQ v
    obtain ⟨w, hw⟩ := hR.mem_ψ _ ((mem_normalizer_iff.1 (inv_mem hhQ) _).1 (hR.ψ_mem v))
    refine ⟨w, ?_, hw⟩
    have e : (⟨ψ w, hψC w⟩ : centralizer ({t} : Set G)) =
        (⟨h, hh⟩ : centralizer ({t} : Set G))⁻¹ * ⟨ψ v, hψC v⟩ * ⟨h, hh⟩ := by
      apply Subtype.ext
      change ψ w = h⁻¹ * ψ v * h
      rw [hw, inv_inv]
    rw [← hΘψ v (hψC v), ← hΘψ w (hψC w), e, map_mul, map_mul, map_inv]
  refine ⟨X, fun h hh => ?_, ?_, fun σ hσ => ?_⟩
  · obtain ⟨hK, -⟩ := (hmemX h).1 hh
    exact ⟨hKC hK, hKN hK⟩
  · rw [eq_bot_iff]
    intro h hh
    obtain ⟨hhX, hhE⟩ := mem_inf.1 hh
    obtain ⟨hK, hhC, hfix⟩ := (hmemX h).1 hhX
    have hhQ : h ∈ Q := (hS.sup_inf_eq (hR.Q_le_L.trans hS.L_le)).le ⟨hhE, hKH hK⟩
    obtain ⟨v, rfl⟩ := hR.mem_ψ h hhQ
    rw [hΘψ v hhC] at hfix
    by_cases hv : v = 0
    · rw [hv, hR.ψ_zero]
      exact one_mem _
    · exact absurd hfix (hz0 v hv)
  · obtain ⟨h, hhH, hhQ, hlin⟩ := hOrth σ hσ
    have hhC : h ∈ centralizer ({t} : Set G) := hS.le_centralizer hhH
    have hzR : Θ ⟨h, hhC⟩ z0 ∈ Model.Rset ε := by
      intro v hv e
      obtain ⟨w, hw1, hw2⟩ := hconjQ h hhC hhQ v
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, hR.ψ_zero] at hw2
        apply hv
        apply hR.ψ_inj
        rw [hR.ψ_zero]
        have := congrArg (fun z => h * z * h⁻¹) hw2
        simpa [mul_assoc] using this.symm
      apply hz0 w hw0
      rw [← hw1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, e]
      simp
    obtain ⟨v₁, hv₁⟩ := Model.exists_psiTM_apply hzR
    refine ⟨(ψ v₁)⁻¹ * h, (hmemX _).2 ⟨mul_mem (inv_mem (mem_sup_left
      (hR.U_le_P (hR.Q_le_U (hR.ψ_mem v₁))))) (hNQ h hhH hhQ),
      mul_mem (inv_mem (hψC v₁)) hhC, ?_⟩, fun v => ?_⟩
    · have e : (⟨(ψ v₁)⁻¹ * h, mul_mem (inv_mem (hψC v₁)) hhC⟩ : centralizer ({t} : Set G)) =
          (⟨ψ v₁, hψC v₁⟩ : centralizer ({t} : Set G))⁻¹ * ⟨h, hhC⟩ := rfl
      rw [e, map_mul, map_inv, hΘψ v₁ (hψC v₁), Equiv.Perm.mul_apply, ← hv₁]
      simp [hz0def]
    · rw [hR.lin_mul (inv_mem (le_normalizer (hR.ψ_mem v₁))) hhQ,
        hR.lin_of_mem_Q (inv_mem (hR.ψ_mem v₁)), hlin]

theorem inputs_of_outerLink {ε : Eps} (hK : StepK t L) {H₀ : Subgroup G}
    (hS : ShapeSplit t L H₀) (hodd : InvolutionsInOddPart L) {U Q P : Subgroup G} {a : G}
    {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G} (hO : OuterLink ε t L U Q P a ψ p u x₀)
    (hx₀ : x₀ ∈ H₀) (hsq : x₀ * x₀ = 1) (hU : Nat.card U = 4096)
    (hsylow : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
      U ⊔ zpowers x₀ ⊔ zpowers t ≤ V → V = U ⊔ zpowers x₀ ⊔ zpowers t) :
    Inputs ε t L H₀ U Q P a ψ p u x₀ := by
  have hF := hO.link
  have hR := hF.radicalData hodd
  have hinv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hsq
  have hfw : ∀ y ∈ Q, x₀ * y * x₀⁻¹ ∈ Q := fun y hy => by
    obtain ⟨v, rfl⟩ := hF.mem_ψ y hy
    rw [hO.act]
    exact hF.ψ_mem _
  have hx₀Q : x₀ ∈ normalizer (Q : Set G) := mem_normalizer_iff.2 fun y => ⟨hfw y, fun hy => by
    have := hfw _ hy
    rwa [hinv, show x₀ * (x₀ * y * x₀) * x₀ = x₀ * x₀ * y * (x₀ * x₀) by group, hsq, one_mul,
      mul_one] at this⟩
  have hx₀L : x₀ ∉ L := fun h => hO.not_mem (mem_sup_left h)
  have hUQ : U ≤ normalizer (Q : Set G) := hF.U_le_P.trans hR.P_le_normalizer
  have hPL : ∀ y ∈ H₀, y ∈ L ⊔ zpowers t → y ∈ L := fun y hy hyN =>
    (hS.sup_inf_eq hS.L_le).le ⟨hyN, hy⟩
  have hNQ : ∀ h ∈ H₀, h ∈ normalizer (Q : Set G) → h ∈ P ⊔ zpowers x₀ := by
    intro h hh hhQ
    rcases hO.normalizer_Q h (hS.le_centralizer hh) hhQ with h1 | h1
    · exact mem_sup_left (hR.P_eq ▸ ⟨hPL h hh h1, hhQ⟩)
    · have h3 : h * x₀⁻¹ ∈ normalizer (Q : Set G) := mul_mem hhQ (inv_mem hx₀Q)
      have h2 : h * x₀⁻¹ ∈ P := hR.P_eq ▸ ⟨hPL _ (mul_mem hh (inv_mem hx₀)) h1, h3⟩
      have e : h = h * x₀⁻¹ * x₀ := by group
      rw [e]
      exact mul_mem (mem_sup_left h2) (mem_sup_right (mem_zpowers x₀))
  have hOrth := inducesOrth_of_refl hR hF.cent_Q hS.L_le hx₀ hsq hO.act
  refine ⟨⟨hS, hR, ⟨sup_le (hF.U_le_L.trans hS.L_le) (zpowers_le.2 hx₀), le_sup_left,
    isPGroup_sup_zpowers hF.U_pgroup hsq hO.normalizes_U, sup_le hUQ (zpowers_le.2 hx₀Q),
    hsylow, hO.autCent.centralizer_le hF.Q_le_L hK.le_centralizer hK.le_normalizer hK.inf_eq⟩⟩,
    hF, hO.autCent, ⟨hx₀, hx₀L, hsq, hO.act, hO.normalizes_U, hNQ⟩, ?_, hOrth, ?_, ?_⟩
  · rw [StepK.card_sup_zpowers_of_le hF.U_le_L hsq hO.not_mem hO.normalizes_U, hU]
  · exact levi_of hS hR hO.embed hx₀ hx₀Q hNQ hOrth
  · obtain ⟨Θ, hΘA, hΘ1, -⟩ := hO.embed
    refine ⟨Θ.comp (inclusion hS.le_centralizer), ?_, fun h => hΘA _⟩
    rw [injective_iff_map_eq_one]
    intro h hh1
    rcases hK.mem_zpowers_iff.1 ((hΘ1 _).1 hh1) with e | e
    · exact Subtype.ext e
    · exact absurd (e ▸ h.2) hS.not_mem

theorem exists_inputs_c_plus [Finite G] (hK : StepK t L) (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) {b : G} (hC : ShapeC t L b) :
    ∃ m ∈ L, ShapeC t L (b * m) ∧ ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G),
      Inputs .plus t L (L ⊔ zpowers b) U Q P a ψ p u (b * m) := by
  obtain ⟨m, hm, U, Q, P, a, ψ, p, u, hO⟩ := exists_outerLink_plus hK hZ hL hC.b_mem
    hC.b_not_mem (by rw [hC.b_sq]; exact one_mem _)
  have hC' := hK.shapeC_mul_right hC hm hO.sq_mem
  have hF := hO.link
  refine ⟨m, hm, hC', U, Q, P, a, ψ, p, u, inputs_of_outerLink hK hC.split
    (OmegaEight.involutionsInOddPart_of_center_eq_bot hZ hL) hO
    (mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left hm)) hC'.b_sq
    (card_U_plus hZ hL hF.U_le_L hF.U_max hF.U_pgroup)
    (hK.shapeC_sylow hC' hF.U_le_L hF.U_max)⟩

theorem exists_inputs_d_plus [Finite G] (hK : StepK t L) (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) {b r : G}
    (hD : ShapeD t L b r) :
    ∃ m ∈ L, ShapeD t L (b * m) r ∧ ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G),
      Inputs .plus t L (L ⊔ zpowers r ⊔ zpowers b) U Q P a ψ p u (b * m) := by
  obtain ⟨m, hm, U, Q, P, a, ψ, p, u, hO⟩ := exists_outerLink_plus hK hZ hL hD.b_mem
    hD.b_not_mem (by rw [hD.b_sq]; exact one_mem _)
  have hD' := hK.shapeD_mul_right hD hm hO.sq_mem
  have hF := hO.link
  refine ⟨m, hm, hD', U, Q, P, a, ψ, p, u, inputs_of_outerLink hK hD.split
    (OmegaEight.involutionsInOddPart_of_center_eq_bot hZ hL) hO
    (mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left (mem_sup_left hm))) hD'.b_sq
    (card_U_plus hZ hL hF.U_le_L hF.U_max hF.U_pgroup)
    (hK.shapeD_sylow hD' hF.U_le_L hF.U_max)⟩

theorem exists_inputs_c_minus [Finite G] (hK : StepK t L)
    (hL : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) {b : G} (hC : ShapeC t L b) :
    ∃ m ∈ L, ShapeC t L (b * m) ∧ ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G),
      Inputs .minus t L (L ⊔ zpowers b) U Q P a ψ p u (b * m) := by
  obtain ⟨m, hm, U, Q, P, a, ψ, p, u, hO⟩ := exists_outerLink_minus hK hL hC.b_mem hC.b_not_mem
  have hC' := hK.shapeC_mul_right hC hm hO.sq_mem
  have hF := hO.link
  refine ⟨m, hm, hC', U, Q, P, a, ψ, p, u, inputs_of_outerLink hK hC.split
    (OmegaEightMinus.involutionsInOddPart_of_lieModel_minus hL) hO
    (mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left hm)) hC'.b_sq
    (card_U_minus hL hF.U_le_L hF.U_max hF.U_pgroup)
    (hK.shapeC_sylow hC' hF.U_le_L hF.U_max)⟩

theorem Inputs.Zset_cases_plus [Finite G] {H₀ U Q P : Subgroup G}
    {a : G} {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G} (hI : Inputs .plus t L H₀ U Q P a ψ p u x₀)
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    (∀ v, v ∈ Zset t Q ψ ↔ qfV .plus v = 0) ∨ ∀ v, v ∈ Zset t Q ψ := by
  obtain ⟨J, hJ, hJA⟩ := hI.embed
  let j : (U ⊔ zpowers x₀ : Subgroup G) →* Equiv.Perm (Fin 360) :=
    J.comp (inclusion hI.setting.data.S₀_le)
  have hjA : ∀ s, j s ∈ OmegaEight.autT := fun s => Model.AT_plus ▸ hJA _
  exact hI.setting.Zset_cases_of_embedding_plus hG hnab j
    (hJ.comp (inclusion_injective _)) hjA hI.card_S₀

theorem Inputs.Zset_cases_minus [Finite G] {H₀ U Q P : Subgroup G}
    {a : G} {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G} (hI : Inputs .minus t L H₀ U Q P a ψ p u x₀)
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    (∀ v, v ∈ Zset t Q ψ ↔ qfV .minus v = 0) ∨ ∀ v, v ∈ Zset t Q ψ := by
  obtain ⟨J, hJ, hJA⟩ := hI.embed
  let j : (U ⊔ zpowers x₀ : Subgroup G) →* Equiv.Perm (Fin 136) :=
    J.comp (inclusion hI.setting.data.S₀_le)
  have hjA : ∀ s, j s ∈ OmegaEightMinus.autT := fun s => Model.AT_minus ▸ hJA _
  exact hI.setting.Zset_cases_of_embedding_minus hG hnab j
    (hJ.comp (inclusion_injective _)) hjA hI.card_S₀

theorem Inputs.x₀_mem_normalizer {ε : Eps} {H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
    {p u : Fin 6 → G} {x₀ : G} (hI : Inputs ε t L H₀ U Q P a ψ p u x₀) :
    x₀ ∈ normalizer (Q : Set G) :=
  hI.setting.data.le_normalizer (mem_sup_right (mem_zpowers x₀))

theorem Inputs.normalizer_E {ε : Eps} (hK : StepK t L) {H₀ U Q P : Subgroup G} {a : G}
    {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G} (hI : Inputs ε t L H₀ U Q P a ψ p u x₀) :
    centralizer ({t} : Set G) ⊓ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) =
      P ⊔ zpowers x₀ ⊔ zpowers t := by
  have hS := hI.setting
  have htE : t ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    le_normalizer (mem_sup_right (mem_zpowers t))
  have hEL : (Q ⊔ zpowers t : Subgroup G) ⊓ L = Q := by
    refine le_antisymm (fun x ⟨hxE, hxL⟩ => ?_) (le_inf le_sup_left hS.rad.Q_le_L)
    obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hxE
    · exact hS.rad.ψ_mem v
    · exact absurd (by simpa using L.mul_mem hxL (L.inv_mem (hS.rad.Q_le_L (hS.rad.ψ_mem v))))
        hK.not_mem
  have hx₀E : x₀ ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_sup hI.x₀_mem_normalizer
      (mem_normalizer_zpowers (hS.shape.commute_of_mem hI.outer.mem))
  have key : ∀ h ∈ H₀, h ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) →
      h ∈ P ⊔ zpowers x₀ := by
    intro h hh hhN
    have hhL : h ∈ normalizer (L : Set G) := hK.le_normalizer (hS.shape.le_centralizer hh)
    have hhQ : h ∈ normalizer (Q : Set G) := mem_normalizer_iff.2 fun y => by
      rw [← hEL]
      change y ∈ (Q ⊔ zpowers t : Subgroup G) ∧ y ∈ L ↔
        h * y * h⁻¹ ∈ (Q ⊔ zpowers t : Subgroup G) ∧ h * y * h⁻¹ ∈ L
      rw [← mem_normalizer_iff.1 hhN y, ← mem_normalizer_iff.1 hhL y]
    exact hI.outer.normalizer_Q h hh hhQ
  apply le_antisymm
  · intro g hg
    obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
    rw [hS.shape.centralizer_eq] at hgC
    obtain ⟨h, hh, e | e⟩ := (hS.shape.mem_sup_iff le_rfl).1 hgC
    · rw [e] at hgN ⊢
      exact mem_sup_left (key h hh hgN)
    · rw [e] at hgN ⊢
      have hhN : h ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
        have := mul_mem hgN (inv_mem htE)
        rwa [mul_inv_cancel_right] at this
      exact mul_mem (mem_sup_left (key h hh hhN)) (mem_sup_right (mem_zpowers t))
  · refine sup_le (sup_le (fun x hx => ⟨hS.shape.le_centralizer (hS.shape.L_le
      (hS.rad.P_le_L hx)), hS.P_le_normalizer_E hx⟩) (zpowers_le.2 ⟨hS.shape.le_centralizer
      hI.outer.mem, hx₀E⟩)) (zpowers_le.2 ⟨mem_centralizer_singleton_iff.2 rfl, htE⟩)

end CFSG.EvenSmallLie.OmegaEight.SplitIn
