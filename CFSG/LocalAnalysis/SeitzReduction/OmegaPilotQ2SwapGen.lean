module

public import CFSG.ClassicalGroups.Orthogonal.RootCenters
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoTorus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ClassicalGroups.Orthogonal
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Fix

variable {K : Type} [Field K] {d : ℕ}

@[expose] def fixVecSub (S : Set (Fin d → K)) : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) where
  carrier := {g | ∀ v ∈ S, g v = v}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {g h} hg hh v hv => by rw [LinearEquiv.mul_apply, hh v hv, hg v hv]
  inv_mem' := fun {g} hg v hv => by
    conv_lhs => rw [← hg v hv]
    exact g.symm_apply_apply v

theorem mem_fixVecSub {S : Set (Fin d → K)} {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} :
    g ∈ fixVecSub S ↔ ∀ v ∈ S, g v = v := Iff.rfl

theorem fixVecSub_anti {S S' : Set (Fin d → K)} (h : S ⊆ S') : fixVecSub S' ≤ fixVecSub S :=
  fun _ hg v hv => hg v (h hv)

theorem fixVecSub_le_of_subset_span {S S' : Set (Fin d → K)} (h : S' ⊆ Submodule.span K S) :
    fixVecSub S ≤ fixVecSub S' := by
  intro g hg v hv
  have key : ∀ x ∈ Submodule.span K S, g x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hg x hx
    | zero => exact map_zero g
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  exact key v (h hv)

theorem fixVecSub_union (S S' : Set (Fin d → K)) :
    fixVecSub (S ∪ S') = fixVecSub S ⊓ fixVecSub S' := by
  ext g
  simp only [mem_inf, mem_fixVecSub, Set.mem_union]
  exact ⟨fun h => ⟨fun v hv => h v (.inl hv), fun v hv => h v (.inr hv)⟩,
    fun h v hv => hv.elim (h.1 v) (h.2 v)⟩

variable (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def fixVecBar (S : Set (Fin d → K)) :
    Subgroup (matrixProjectiveDerived Q) :=
  ((fixVecSub S).subgroupOf (orthDerived Q)).map (projHom Q)

variable {Q}

theorem fixVecBar_anti {S S' : Set (Fin d → K)} (h : S ⊆ S') : fixVecBar Q S' ≤ fixVecBar Q S :=
  map_mono fun _ hg => mem_subgroupOf.2 (fixVecSub_anti h (mem_subgroupOf.1 hg))

theorem fixVecBar_inf [CharP K 2] (hQ : ∃ v, Q v ≠ 0) (S S' : Set (Fin d → K)) :
    fixVecBar Q S ⊓ fixVecBar Q S' = fixVecBar Q (S ∪ S') := by
  rw [fixVecBar, fixVecBar, fixVecBar, ← map_inf_eq _ _ _ (projHom_injective hQ), fixVecSub_union]
  congr 1

theorem map_conj_fixVecBar (g : orthDerived Q) (S : Set (Fin d → K)) :
    (fixVecBar Q S).map (MulAut.conj (projHom Q g)).toMonoidHom =
      fixVecBar Q ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' S) := by
  ext y
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨g * h * g⁻¹, mem_subgroupOf.2 ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      have hs' : (h : (Fin d → K) ≃ₗ[K] (Fin d → K)) s = s := mem_subgroupOf.1 hh s hs
      change (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((h : (Fin d → K) ≃ₗ[K] (Fin d → K))
        ((g : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹ ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) s))) = _
      rw [LinearEquiv.inv_apply_apply', hs']
    · simp [MulAut.conj_apply, map_mul, map_inv]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨projHom Q (g⁻¹ * k * g), ⟨g⁻¹ * k * g, mem_subgroupOf.2 fun s hs => ?_, rfl⟩, ?_⟩
    · have hk' : (k : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) s) =
          (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) s := mem_subgroupOf.1 hk _ ⟨s, hs, rfl⟩
      change ((g : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹ ((k : (Fin d → K) ≃ₗ[K] (Fin d → K))
        ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) s))) = s
      rw [hk', LinearEquiv.inv_apply_apply']
    · simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem pairPerpOf_eq_fixVecBar (a a' : Fin d) :
    pairPerpOf Q a a' = fixVecBar Q {Pi.single a 1, Pi.single a' 1} := by
  have h : stabSub (K := K) a a' = fixVecSub {Pi.single a 1, Pi.single a' 1} := by
    ext g
    simp [mem_stabSub, mem_fixVecSub]
  rw [pairPerpOf, fixVecBar, h]

theorem stabPairsBar_eq_fixVecBar (a a' b b' : Fin d) :
    stabPairsBar Q a a' b b' =
      fixVecBar Q {Pi.single a 1, Pi.single a' 1, Pi.single b 1, Pi.single b' 1} := by
  have h : stabSub (K := K) a a' ⊓ stabSub b b' =
      fixVecSub {Pi.single a 1, Pi.single a' 1, Pi.single b 1, Pi.single b' 1} := by
    ext g
    simp [mem_stabSub, mem_fixVecSub, and_assoc]
  rw [stabPairsBar, fixVecBar, h]

theorem anisoTorusOf_le_fixVecBar [CharP K 2] {a a' : Fin d} (hne : a ≠ a') (b c : K) :
    anisoTorusOf Q hne b c ≤ fixVecBar Q (perpSub K a a' : Set (Fin d → K)) := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, mem_subgroupOf.2 fun v hv => ?_, rfl⟩
  obtain ⟨p, s, -, hgv⟩ := mem_subgroupOf.1 hg
  rw [hgv]
  exact anisoRotLin_apply_of_mem_perpSub p s hv

end Fix

section CharTwoVec

variable {K : Type} [Field K] [CharP K 2] {d : ℕ}

theorem vec_add_self_charTwo (v : Fin d → K) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem vec_neg_charTwo (v : Fin d → K) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, vec_add_self_charTwo]

theorem polar_self_charTwo (Q : QuadraticForm K (Fin d → K)) (x : Fin d → K) :
    polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]

end CharTwoVec

section PlaneSwap

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' c c' : Fin d → K}

structure PlaneSwapData (Q : QuadraticForm K (Fin d → K)) (a a' c c' : Fin d → K) : Prop where
  map_eq : Q a = Q c
  map_eq' : Q a' = Q c'
  polar_aa : polar Q a a' = 1
  polar_cc : polar Q c c' = 1
  ac : polar Q a c = 0
  ac' : polar Q a c' = 0
  a'c : polar Q a' c = 0
  a'c' : polar Q a' c' = 0

theorem PlaneSwapData.map_sum (h : PlaneSwapData Q a a' c c') : Q (a + c) = 0 := by
  rw [QuadraticMap.map_add Q a c, h.map_eq, h.ac, add_zero, CharTwo.add_self_eq_zero]

theorem PlaneSwapData.map_sum' (h : PlaneSwapData Q a a' c c') : Q (a' + c') = 0 := by
  rw [QuadraticMap.map_add Q a' c', h.map_eq', h.a'c', add_zero, CharTwo.add_self_eq_zero]

theorem PlaneSwapData.polar_sum (h : PlaneSwapData Q a a' c c') :
    polar Q (a + c) (a' + c') = 0 := by
  rw [polar_add_left, polar_add_right, polar_add_right, h.polar_aa, h.ac', polar_comm Q c a',
    h.a'c, h.polar_cc, add_zero, zero_add, CharTwo.add_self_eq_zero]

theorem PlaneSwapData.eichler_left (h : PlaneSwapData Q a a' c c') :
    eichler Q (a + c) (a' + c') a = c := by
  rw [eichler_apply h.map_sum h.polar_sum, h.map_sum', polar_add_right, polar_add_right,
    polar_self_charTwo, h.ac, h.polar_aa, h.ac']
  simp only [add_zero, zero_smul, mul_zero, one_smul]
  rw [sub_add_cancel_left, vec_neg_charTwo]

theorem PlaneSwapData.eichler_left' (h : PlaneSwapData Q a a' c c') :
    eichler Q (a + c) (a' + c') a' = c' := by
  rw [eichler_apply h.map_sum h.polar_sum, h.map_sum', polar_add_right, polar_add_right,
    polar_self_charTwo, polar_comm Q a' a, h.polar_aa, h.a'c, h.a'c']
  simp only [add_zero, zero_mul, zero_smul, one_smul, sub_zero]
  rw [← add_assoc, vec_add_self_charTwo, zero_add]

theorem PlaneSwapData.eichler_right (h : PlaneSwapData Q a a' c c') :
    eichler Q (a + c) (a' + c') c = a := by
  rw [eichler_apply h.map_sum h.polar_sum, h.map_sum', polar_add_right, polar_add_right,
    polar_self_charTwo, polar_comm Q c a, h.ac, polar_comm Q c a', h.a'c, h.polar_cc]
  simp only [add_zero, zero_add, mul_zero, zero_smul, one_smul]
  rw [sub_add_cancel_right, vec_neg_charTwo]

theorem PlaneSwapData.eichler_right' (h : PlaneSwapData Q a a' c c') :
    eichler Q (a + c) (a' + c') c' = a' := by
  rw [eichler_apply h.map_sum h.polar_sum, h.map_sum', polar_add_right, polar_add_right,
    polar_self_charTwo, polar_comm Q c' a, h.ac', polar_comm Q c' c, h.polar_cc,
    polar_comm Q c' a', h.a'c']
  simp only [add_zero, zero_add, zero_mul, zero_smul, one_smul, sub_zero]
  rw [add_comm a' c', ← add_assoc, vec_add_self_charTwo, zero_add]

theorem PlaneSwapData.eichler_of_perp {x : Fin d → K} (h1 : polar Q x a = 0)
    (h2 : polar Q x a' = 0) (h3 : polar Q x c = 0) (h4 : polar Q x c' = 0) :
    eichler Q (a + c) (a' + c') x = x :=
  eichler_apply_of_polar_eq_zero (by rw [polar_add_right, h1, h3, add_zero])
    (by rw [polar_add_right, h2, h4, add_zero])

end PlaneSwap

section Gen

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] def pairSet (v : Fin 3 → Bool → Fin d → K) (i : Fin 3) : Set (Fin d → K) :=
  {v i true, v i false}

structure OrthPairTriple (Q : QuadraticForm K (Fin d → K)) (v : Fin 3 → Bool → Fin d → K) :
    Prop where
  one : ∀ i, polar Q (v i true) (v i false) = 1
  orth : ∀ i j, i ≠ j → ∀ s t, polar Q (v i s) (v j t) = 0

@[expose] def pairProj (Q : QuadraticForm K (Fin d → K)) (v : Fin 3 → Bool → Fin d → K)
    (i : Fin 3) (w : Fin d → K) : Fin d → K :=
  polar Q w (v i false) • v i true + polar Q w (v i true) • v i false

theorem polar_pairProj (v : Fin 3 → Bool → Fin d → K) (i : Fin 3) (y w : Fin d → K) :
    polar Q y (pairProj Q v i w) =
      polar Q w (v i false) * polar Q y (v i true) +
        polar Q w (v i true) * polar Q y (v i false) := by
  rw [pairProj, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul]

theorem OrthPairTriple.polar_pairProj_self {v : Fin 3 → Bool → Fin d → K} (h : OrthPairTriple Q v)
    (i : Fin 3) (s : Bool) (w : Fin d → K) :
    polar Q (v i s) (pairProj Q v i w) = polar Q (v i s) w := by
  rw [polar_pairProj]
  cases s
  · rw [polar_comm Q (v i false) (v i true), h.one, polar_self_charTwo, mul_zero, add_zero, mul_one,
      polar_comm]
  · rw [h.one, polar_self_charTwo, mul_zero, zero_add, mul_one, polar_comm]

theorem OrthPairTriple.polar_pairProj_ne {v : Fin 3 → Bool → Fin d → K} (h : OrthPairTriple Q v)
    {i j : Fin 3} (hij : j ≠ i) (s : Bool) (w : Fin d → K) :
    polar Q (v j s) (pairProj Q v i w) = 0 := by
  rw [polar_pairProj, h.orth j i hij s true, h.orth j i hij s false, mul_zero, mul_zero, add_zero]

theorem OrthPairTriple.polar_rest {v : Fin 3 → Bool → Fin d → K} (h : OrthPairTriple Q v)
    (j : Fin 3) (s : Bool) (w : Fin d → K) :
    polar Q (v j s) (w - pairProj Q v 0 w - pairProj Q v 1 w - pairProj Q v 2 w) = 0 := by
  have hp : ∀ i, polar Q (v j s) (pairProj Q v i w) = if i = j then polar Q (v j s) w else 0 := by
    intro i
    split_ifs with hij
    · subst hij
      exact h.polar_pairProj_self i s w
    · exact h.polar_pairProj_ne (Ne.symm hij) s w
  rw [polar_sub_right, polar_sub_right, polar_sub_right, hp 0, hp 1, hp 2]
  fin_cases j <;> simp

theorem eichler_mem_fixVecSub {u w : Fin d → K} {T : Set (Fin d → K)}
    (hu : ∀ y ∈ T, polar Q y u = 0) (hw : ∀ y ∈ T, polar Q y w = 0) :
    eichler Q u w ∈ fixVecSub T :=
  fun y hy => eichler_apply_of_polar_eq_zero (hu y hy) (hw y hy)

variable [Finite K]

@[expose] noncomputable def triFixSub (Q : QuadraticForm K (Fin d → K))
    (v : Fin 3 → Bool → Fin d → K) : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  ((fixVecSub (pairSet v 0 ∪ pairSet v 1)).subgroupOf (orthDerived Q) ⊔
    (fixVecSub (pairSet v 0 ∪ pairSet v 2)).subgroupOf (orthDerived Q) ⊔
    (fixVecSub (pairSet v 1 ∪ pairSet v 2)).subgroupOf (orthDerived Q)).map (orthDerived Q).subtype

theorem OrthPairTriple.isRootCenter {v : Fin 3 → Bool → Fin d → K} (h : OrthPairTriple Q v)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {e : Fin d → K}
    (he0 : e ≠ 0) (heQ : Q e = 0) (hev : ∀ i s, polar Q (v i s) e = 0) :
    IsRootCenter Q (triFixSub Q v) e := by
  refine ⟨he0, heQ, fun w hw => ?_⟩
  have hmem : ∀ (T : Set (Fin d → K)) (x : Fin d → K), (∀ y ∈ T, polar Q y x = 0) →
      (∀ y ∈ T, polar Q y e = 0) →
      ((fixVecSub T).subgroupOf (orthDerived Q)).map (orthDerived Q).subtype ≤ triFixSub Q v →
      eichler Q e x ∈ triFixSub Q v := fun T x hx he hle =>
    hle ⟨⟨eichler Q e x, eichler_mem_orthDerived hQ hT e x⟩,
      mem_subgroupOf.2 (eichler_mem_fixVecSub he hx), rfl⟩
  have hT₁ : ((fixVecSub (pairSet v 0 ∪ pairSet v 1)).subgroupOf (orthDerived Q)).map
      (orthDerived Q).subtype ≤ triFixSub Q v := map_mono (le_sup_left.trans le_sup_left)
  have hT₂ : ((fixVecSub (pairSet v 0 ∪ pairSet v 2)).subgroupOf (orthDerived Q)).map
      (orthDerived Q).subtype ≤ triFixSub Q v := map_mono (le_sup_right.trans le_sup_left)
  have hT₃ : ((fixVecSub (pairSet v 1 ∪ pairSet v 2)).subgroupOf (orthDerived Q)).map
      (orthDerived Q).subtype ≤ triFixSub Q v := map_mono le_sup_right
  have hset : ∀ (i : Fin 3) (y : Fin d → K), y ∈ pairSet v i → ∃ s, y = v i s := by
    intro i y hy
    rcases hy with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  have huni : ∀ (i j : Fin 3) (P : (Fin d → K) → Prop), (∀ s, P (v i s)) → (∀ s, P (v j s)) →
      ∀ y ∈ pairSet v i ∪ pairSet v j, P y := by
    intro i j P hi hj y hy
    rcases hy with hy | hy
    · obtain ⟨s, rfl⟩ := hset i y hy
      exact hi s
    · obtain ⟨s, rfl⟩ := hset j y hy
      exact hj s
  have hee : ∀ (i j : Fin 3), ∀ y ∈ pairSet v i ∪ pairSet v j, polar Q y e = 0 := fun i j =>
    huni i j _ (hev i) (hev j)
  set w₀ := pairProj Q v 0 w
  set w₁ := pairProj Q v 1 w
  set w₂ := pairProj Q v 2 w
  set wR := w - w₀ - w₁ - w₂ with hwR
  have hpe : ∀ i, polar Q e (pairProj Q v i w) = 0 := fun i => by
    rw [polar_pairProj, polar_comm Q e, polar_comm Q e, hev, hev, mul_zero, mul_zero, add_zero]
  have hRe : polar Q e wR = 0 := by
    rw [hwR, polar_sub_right, polar_sub_right, polar_sub_right, hw, hpe, hpe, hpe]
    simp
  have hdec : w = w₀ + (w₁ + (w₂ + wR)) := by
    rw [hwR]
    abel
  have e₀ : eichler Q e w₀ ∈ triFixSub Q v := hmem _ _ (huni 1 2 _
      (fun s => h.polar_pairProj_ne (by decide) s w) (fun s => h.polar_pairProj_ne (by decide) s w))
    (hee 1 2) hT₃
  have e₁ : eichler Q e w₁ ∈ triFixSub Q v := hmem _ _ (huni 0 2 _
      (fun s => h.polar_pairProj_ne (by decide) s w) (fun s => h.polar_pairProj_ne (by decide) s w))
    (hee 0 2) hT₂
  have e₂ : eichler Q e w₂ ∈ triFixSub Q v := hmem _ _ (huni 0 1 _
      (fun s => h.polar_pairProj_ne (by decide) s w) (fun s => h.polar_pairProj_ne (by decide) s w))
    (hee 0 1) hT₁
  have eR : eichler Q e wR ∈ triFixSub Q v := hmem _ _ (huni 0 1 _
      (fun s => h.polar_rest 0 s w) (fun s => h.polar_rest 1 s w)) (hee 0 1) hT₁
  have h₂R : polar Q e (w₂ + wR) = 0 := by rw [polar_add_right, hpe, hRe, add_zero]
  have h₁₂R : polar Q e (w₁ + (w₂ + wR)) = 0 := by rw [polar_add_right, hpe, h₂R, add_zero]
  rw [hdec, ← eichler_mul (hpe 0) h₁₂R, ← eichler_mul (hpe 1) h₂R, ← eichler_mul (hpe 2) hRe]
  exact mul_mem e₀ (mul_mem e₁ (mul_mem e₂ eR))

theorem OrthPairTriple.fixVecBar_sup_eq_top {v : Fin 3 → Bool → Fin d → K}
    (h : OrthPairTriple Q v) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (P : HypPair Q)
    (hve : ∀ i s, polar Q (v i s) P.e = 0) (hvf : ∀ i s, polar Q (v i s) P.f = 0) :
    fixVecBar Q (pairSet v 0 ∪ pairSet v 1) ⊔ fixVecBar Q (pairSet v 0 ∪ pairSet v 2) ⊔
      fixVecBar Q (pairSet v 1 ∪ pairSet v 2) = ⊤ := by
  have hO : triFixSub Q v ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (map_subtype_le _).trans fun x hx => Subgroup.commutator_le_self _ hx
  have he0 : P.e ≠ 0 := fun h0 => by
    have := P.polar_ef
    rw [h0, polar_zero_left] at this
    exact zero_ne_one this
  have hf0 : P.f ≠ 0 := fun h0 => by
    have := P.polar_ef
    rw [h0, polar_zero_right] at this
    exact zero_ne_one this
  have hE := elementaryGroup_le_of_hypPair hQ hO P (h.isRootCenter hQ hT he0 P.Q_e hve)
    (h.isRootCenter hQ hT hf0 P.Q_f hvf)
  have hΩ : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  have htop : (fixVecSub (pairSet v 0 ∪ pairSet v 1)).subgroupOf (orthDerived Q) ⊔
      (fixVecSub (pairSet v 0 ∪ pairSet v 2)).subgroupOf (orthDerived Q) ⊔
      (fixVecSub (pairSet v 1 ∪ pairSet v 2)).subgroupOf (orthDerived Q) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ elementaryGroup Q := hΩ ▸ g.2
    obtain ⟨y, hy, hyg⟩ := hE hg
    rw [← Subtype.ext hyg]
    exact hy
  rw [fixVecBar, fixVecBar, fixVecBar, ← Subgroup.map_sup, ← Subgroup.map_sup, htop,
    map_top_of_surjective _ (projHom_surjective Q)]

end Gen

end CFSG.SeitzReduction.OmegaPilot
