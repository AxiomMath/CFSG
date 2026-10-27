module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Natural
import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.BaumannIndex
import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.BaumannOffender
import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.BaumannConj
import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.BaumannNormal
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.SignalizerFunctorTheorem.ElementaryAbelian
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannA3
import CFSG.Quasithin.EmptyFaithful.Der6ACore

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped IsMulCommutative Pointwise

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem sup_eq_of_card_eq_g45le {Γ : Type*} [Group Γ] [Finite Γ]
    {V X Y : Subgroup Γ} {m : ℕ} (hX : X ≤ V) (hY : Y ≤ V)
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVX : Nat.card V = 2 ^ m * Nat.card X)
    (hVY : Nat.card V = 2 ^ m * Nat.card Y)
    (hVI : Nat.card V = 2 ^ (2 * m) * Nat.card ↥(X ⊓ Y)) :
    X ⊔ Y = V := by
  have h2pos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hIpos : 0 < Nat.card ↥(X ⊓ Y) := Nat.card_pos
  have hpow : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by
    rw [show 2 * m = m + m by omega, pow_add]
  have hXcard : Nat.card X = 2 ^ m * Nat.card ↥(X ⊓ Y) := by
    refine Nat.mul_left_cancel h2pos ?_
    rw [← hVX, ← mul_assoc, ← hpow, hVI]
  have hYcard : Nat.card Y = 2 ^ m * Nat.card ↥(X ⊓ Y) := by
    refine Nat.mul_left_cancel h2pos ?_
    rw [← hVY, ← mul_assoc, ← hpow, hVI]
  have hXYcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x :=
    fun x hx y hy => hcomm x (hX hx) y (hY hy)
  have hsup : Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) =
      Nat.card V * Nat.card ↥(X ⊓ Y) := by
    calc Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y)
        = Nat.card X * Nat.card Y :=
          (card_sup_mul_card_inf_of_commute X Y hXYcomm).1
      _ = (2 ^ m * Nat.card ↥(X ⊓ Y)) * (2 ^ m * Nat.card ↥(X ⊓ Y)) := by
            rw [hXcard, hYcard]
      _ = (2 ^ m * 2 ^ m) * (Nat.card ↥(X ⊓ Y) * Nat.card ↥(X ⊓ Y)) := by ring
      _ = (2 ^ (2 * m) * Nat.card ↥(X ⊓ Y)) * Nat.card ↥(X ⊓ Y) := by
            rw [← hpow, mul_assoc]
      _ = Nat.card V * Nat.card ↥(X ⊓ Y) := by rw [hVI]
  have hcard : Nat.card ↥(X ⊔ Y) = Nat.card V :=
    Nat.mul_right_cancel hIpos hsup
  exact Subgroup.eq_of_le_of_card_ge (sup_le hX hY) hcard.ge

private theorem le_centralizer_of_le_sup_g45le {Γ : Type*} [Group Γ] [Finite Γ]
    {X Y Z T : Subgroup Γ} (hXZ : X ≤ Z)
    (hXT : X ≤ Subgroup.centralizer (T : Set Γ))
    (hZYT : Z ⊓ Y ≤ Subgroup.centralizer (T : Set Γ))
    (hZle : Z ≤ X ⊔ Y)
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    Z ≤ Subgroup.centralizer (T : Set Γ) := by
  have hXY : ((X ⊔ Y : Subgroup Γ) : Set Γ) = (X : Set Γ) * (Y : Set Γ) :=
    (card_sup_mul_card_inf_of_commute X Y hc).2
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hz' : z ∈ (X : Set Γ) * (Y : Set Γ) := by
    rw [← hXY]
    exact hZle hz
  obtain ⟨x, hxX, y, hyY, hxy⟩ := hz'
  have hxZ : x ∈ Z := hXZ hxX
  have hyZ : y ∈ Z := by
    have hy : y = x⁻¹ * z := by
      rw [← hxy, inv_mul_cancel_left]
    rw [hy]
    exact Z.mul_mem (Z.inv_mem hxZ) hz
  have hxT : x ∈ Subgroup.centralizer (T : Set Γ) := hXT hxX
  have hyT : y ∈ Subgroup.centralizer (T : Set Γ) := hZYT ⟨hyZ, hyY⟩
  rw [Subgroup.mem_centralizer_iff] at hxT hyT
  rw [← hxy]
  calc t * (x * y) = (t * x) * y := by rw [mul_assoc]
    _ = (x * t) * y := by rw [hxT t ht]
    _ = x * (t * y) := by rw [mul_assoc]
    _ = x * (y * t) := by rw [hyT t ht]
    _ = (x * y) * t := by rw [mul_assoc]

private theorem exists_baum_basic_g45le (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h32 : GomiFact32) (h35 : GomiFact35) (h37 : GomiFact37OneCSP) (h373 : GomiFact37Three)
    (h374 : GomiFact37Four) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb)
    (hi : G ≤ conjClosure (baum S) G) :
    ∃ (m : ℕ) (A : Subgroup Ω) (g : Ω), 1 ≤ m ∧
      IsSLn ↥(autOn G (gomiV G)) 2 m ∧ IsMaxElemAbelian S A ∧
      ¬ A ≤ Subgroup.centralizer (gomiV G : Set Ω) ∧ pCoreOf 2 G ⊔ A = S ∧
      IsMaxElemAbelian S (gomiV G ⊔ (pCoreOf 2 G ⊓ A)) ∧ g ∈ G ∧
      S ⊔ S.map (MulAut.conj g).toMonoidHom = G := by
  obtain ⟨m, hm, hSL, -⟩ := h.natural_autOn h31 h32 h37 h373 h374 hL hg hi
  obtain ⟨A, hA, hAC⟩ := exists_isMaxElemAbelian_not_le_centralizer h
  have hrelS := h.relIndex_centralizer_gomiV_eq hSL
  obtain ⟨hrelA, hrelVA⟩ := h.relIndex_eq_of_isMaxElemAbelian h35 hm hSL hA hAC
  have hSQA : pCoreOf 2 G ⊔ A = S :=
    h.pCoreOf_sup_eq_of_relIndex_eq hA.1 (hrelA.trans hrelS.symm)
  have hB : IsMaxElemAbelian S (gomiV G ⊔ (pCoreOf 2 G ⊓ A)) :=
    h.isMaxElemAbelian_gomiV_sup hA (hrelA.trans hrelVA.symm)
  obtain ⟨g, hgG, hG⟩ := h.exists_sup_map_conj_eq hL hg
  exact ⟨m, A, g, hm, hSL, hA, hAC, hSQA, hB, hgG, hG⟩

omit [Finite Ω] in
private theorem map_conj_inf_centralizer_g45le {g : Ω} (hgG : g ∈ G) :
    (gomiV G ⊓ Subgroup.centralizer (S : Set Ω)).map (MulAut.conj g).toMonoidHom =
      gomiV G ⊓ Subgroup.centralizer
        (S.map (MulAut.conj g).toMonoidHom : Set Ω) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    CFSG.Quasithin.map_conj_eq_of_mem_normalizer ((gomiV_moduleSetting G).2 hgG),
    CFSG.Quasithin.centralizer_map_mulEquiv (MulAut.conj g) S]

private theorem card_eq_of_inf_centralizer_g45le (h : GomiThm45Counterexample c G S)
    (h35 : GomiFact35) {m : ℕ} (hm : 1 ≤ m)
    (hSL : IsSLn ↥(autOn G (gomiV G)) 2 m) {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A) (hAC : ¬ A ≤ Subgroup.centralizer (gomiV G : Set Ω))
    (hSQA : pCoreOf 2 G ⊔ A = S) {g : Ω} (hgG : g ∈ G) {X Y : Subgroup Ω}
    (hX : X = gomiV G ⊓ Subgroup.centralizer (S : Set Ω))
    (hY : Y = gomiV G ⊓ Subgroup.centralizer
      (S.map (MulAut.conj g).toMonoidHom : Set Ω)) :
    Nat.card (gomiV G) = 2 ^ m * Nat.card X ∧
      Nat.card (gomiV G) = 2 ^ m * Nat.card Y := by
  have hrelVA : (Subgroup.centralizer (A : Set Ω)).relIndex (gomiV G) = 2 ^ m :=
    (h.relIndex_eq_of_isMaxElemAbelian h35 hm hSL hA hAC).2
  have hXeq : X = gomiV G ⊓ Subgroup.centralizer (A : Set Ω) := by
    have hC : Subgroup.centralizer (S : Set Ω) =
        Subgroup.centralizer (pCoreOf 2 G : Set Ω) ⊓
          Subgroup.centralizer (A : Set Ω) := by
      rw [← hSQA]
      exact CFSG.SignalizerFunctorTheorem.centralizer_sup (pCoreOf 2 G) A
    have hVQ : gomiV G ≤ Subgroup.centralizer (pCoreOf 2 G : Set Ω) :=
      CFSG.Quasithin.Der6A.omegaOneCenterOf_le_centralizer (pCoreOf 2 G)
    rw [hX, hC, ← inf_assoc, inf_eq_left.mpr hVQ]
  have hcardX : Nat.card (gomiV G) = 2 ^ m * Nat.card X := by
    have h := Subgroup.relIndex_mul_card
      (H := Subgroup.centralizer (A : Set Ω)) (K := gomiV G)
    rw [hrelVA, inf_comm] at h
    simpa [hXeq] using h.symm
  have hYeq : Y = X.map (MulAut.conj g).toMonoidHom := by
    rw [hY, hX, ← map_conj_inf_centralizer_g45le hgG]
  refine ⟨hcardX, ?_⟩
  rw [show Nat.card Y = Nat.card X by
    rw [hYeq, Subgroup.card_map_of_injective (MulAut.conj g).injective], hcardX]

private theorem card_inf_eq_of_sup_g45le (h : GomiThm45Counterexample c G S) (h35 : GomiFact35)
    {m : ℕ} (hm : 1 ≤ m) (hSL : IsSLn ↥(autOn G (gomiV G)) 2 m) {g : Ω}
    (hG : S ⊔ S.map (MulAut.conj g).toMonoidHom = G) {X Y : Subgroup Ω}
    (hX : X = gomiV G ⊓ Subgroup.centralizer (S : Set Ω))
    (hY : Y = gomiV G ⊓ Subgroup.centralizer
      (S.map (MulAut.conj g).toMonoidHom : Set Ω)) :
    Nat.card (gomiV G) = 2 ^ (2 * m) * Nat.card ↥(X ⊓ Y) := by
  have hrelG : (Subgroup.centralizer (G : Set Ω)).relIndex (gomiV G) = 2 ^ (2 * m) :=
    h.relIndex_gomiV_centralizer_eq h35 hm hSL
  have hCs : Subgroup.centralizer (S : Set Ω) ⊓
      Subgroup.centralizer (S.map (MulAut.conj g).toMonoidHom : Set Ω) =
      Subgroup.centralizer (G : Set Ω) := by
    rw [← CFSG.SignalizerFunctorTheorem.centralizer_sup S
      (S.map (MulAut.conj g).toMonoidHom), hG]
  have hXYinf : X ⊓ Y = Subgroup.centralizer (G : Set Ω) ⊓ gomiV G := by
    rw [hX, hY]
    rw [show (gomiV G ⊓ Subgroup.centralizer (S : Set Ω)) ⊓
          (gomiV G ⊓ Subgroup.centralizer (S.map (MulAut.conj g).toMonoidHom : Set Ω)) =
        gomiV G ⊓ (Subgroup.centralizer (S : Set Ω) ⊓
          Subgroup.centralizer (S.map (MulAut.conj g).toMonoidHom : Set Ω)) by
      ext x
      simp only [Subgroup.mem_inf]
      tauto]
    rw [hCs, inf_comm]
  have h := Subgroup.relIndex_mul_card
    (H := Subgroup.centralizer (G : Set Ω)) (K := gomiV G)
  rw [hrelG] at h
  rw [hXYinf]
  exact h.symm

private theorem z_le_sup_map_conj_g45le (h : GomiThm45Counterexample c G S)
    {A : Subgroup Ω} (hA : IsMaxElemAbelian S A)
    (hSQA : pCoreOf 2 G ⊔ A = S)
    (hB : IsMaxElemAbelian S (gomiV G ⊔ (pCoreOf 2 G ⊓ A)))
    {g : Ω} (hgG : g ∈ G) (hG : S ⊔ S.map (MulAut.conj g).toMonoidHom = G)
    {X Y : Subgroup Ω} (hX : X = gomiV G ⊓ Subgroup.centralizer (S : Set Ω))
    (hY : Y = gomiV G ⊓ Subgroup.centralizer
      (S.map (MulAut.conj g).toMonoidHom : Set Ω))
    (hVsup : X ⊔ Y = gomiV G) :
    omegaOneCenterOf (thompsonJ S) ≤
      X ⊔ (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom := by
  have hXleV : X ≤ gomiV G := by rw [hX]; exact inf_le_left
  have hXZ : X ≤ omegaOneCenterOf (thompsonJ S) := by
    rw [hX]
    exact h.gomiV_inf_centralizer_le
  have hVmap : (gomiV G).map (MulAut.conj g).toMonoidHom = gomiV G :=
    CFSG.Quasithin.map_conj_eq_of_mem_normalizer ((gomiV_moduleSetting G).2 hgG)
  have hYeq : Y = X.map (MulAut.conj g).toMonoidHom := by
    rw [hY, hX, ← map_conj_inf_centralizer_g45le hgG]
  have hYleZg : Y ≤ (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom := by
    rw [hYeq]
    exact Subgroup.map_mono hXZ
  have hWmap : (gomiV G ⊔ omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom =
      gomiV G ⊔ omegaOneCenterOf (thompsonJ S) :=
    CFSG.Quasithin.map_conj_eq_of_mem_normalizer
      (h.le_normalizer_gomiV_sup hA hSQA hB hgG hG hgG)
  have hWg : gomiV G ⊔ (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom =
      gomiV G ⊔ omegaOneCenterOf (thompsonJ S) := by
    rw [← hWmap, Subgroup.map_sup, hVmap]
  have hVZg : gomiV G ⊔ (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom =
      X ⊔ (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm ?_ (sup_le (hXleV.trans le_sup_left) le_sup_right)
    rw [← hVsup]
    exact sup_le (sup_le le_sup_left (hYleZg.trans le_sup_right)) le_sup_right
  rw [← hVZg, hWg]
  exact le_sup_right

private theorem z_le_centralizer_of_sup_g45le (h : GomiThm45Counterexample c G S)
    {A : Subgroup Ω} (hA : IsMaxElemAbelian S A) (hSQA : pCoreOf 2 G ⊔ A = S)
    (hB : IsMaxElemAbelian S (gomiV G ⊔ (pCoreOf 2 G ⊓ A)))
    {g : Ω} (hgG : g ∈ G) (hG : S ⊔ S.map (MulAut.conj g).toMonoidHom = G)
    (hi : G ≤ conjClosure (baum S) G) {X : Subgroup Ω}
    (hX : X = gomiV G ⊓ Subgroup.centralizer (S : Set Ω))
    (hZle : omegaOneCenterOf (thompsonJ S) ≤
      X ⊔ (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom) :
    omegaOneCenterOf (thompsonJ S) ≤ Subgroup.centralizer (S : Set Ω) := by
  have hXZ : X ≤ omegaOneCenterOf (thompsonJ S) := by
    rw [hX]
    exact h.gomiV_inf_centralizer_le
  have hXCS : X ≤ Subgroup.centralizer (S : Set Ω) := by
    rw [hX]; exact inf_le_right
  have hVQ : gomiV G ≤ pCoreOf 2 G := gomiV_le_pCoreOf G
  have hZleB : omegaOneCenterOf (thompsonJ S) ≤ gomiV G ⊔ (pCoreOf 2 G ⊓ A) :=
    C56.omegaOneCenter_thompsonJ_le hB
  have hBQ : gomiV G ⊔ (pCoreOf 2 G ⊓ A) ≤ pCoreOf 2 G := sup_le hVQ inf_le_left
  have hZQ : omegaOneCenterOf (thompsonJ S) ≤ pCoreOf 2 G := hZleB.trans hBQ
  have hQmap : (pCoreOf 2 G).map (MulAut.conj g).toMonoidHom = pCoreOf 2 G :=
    CFSG.Quasithin.map_conj_eq_of_mem_normalizer
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G) hgG)
  have hZgQ : (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom ≤
      pCoreOf 2 G := by
    rw [← hQmap]
    exact Subgroup.map_mono hZQ
  have hXleV : X ≤ gomiV G := by rw [hX]; exact inf_le_left
  have hXCQ : X ≤ Subgroup.centralizer (pCoreOf 2 G : Set Ω) :=
    hXleV.trans (CFSG.Quasithin.Der6A.omegaOneCenterOf_le_centralizer (pCoreOf 2 G))
  have hcommXZg : ∀ x ∈ X, ∀ y ∈ (omegaOneCenterOf (thompsonJ S)).map
      (MulAut.conj g).toMonoidHom, x * y = y * x := by
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hXCQ hx)) y (hZgQ hy)).symm
  have hZZCS : omegaOneCenterOf (thompsonJ S) ⊓
      (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (S : Set Ω) :=
    (h.inf_map_conj_le_centralizer hA hSQA hgG hG hi).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.isSylowTwoOf.1))
  exact le_centralizer_of_le_sup_g45le hXZ hXCS hZZCS hZle hcommXZg

theorem baum_eq (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h32 : GomiFact32) (h35 : GomiFact35) (h37 : GomiFact37OneCSP) (h373 : GomiFact37Three)
    (h374 : GomiFact37Four) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb)
    (hi : G ≤ conjClosure (baum S) G) :
    baum S = S := by
  obtain ⟨m, A, g, hm, hSL, hA, hAC, hSQA, hB, hgG, hG⟩ :=
    exists_baum_basic_g45le h h31 h32 h35 h37 h373 h374 hL hg hi
  set X : Subgroup Ω := gomiV G ⊓ Subgroup.centralizer (S : Set Ω) with hXdef
  set Y : Subgroup Ω := gomiV G ⊓
    Subgroup.centralizer (S.map (MulAut.conj g).toMonoidHom : Set Ω) with hYdef
  obtain ⟨hcardX, hcardY⟩ :=
    card_eq_of_inf_centralizer_g45le h h35 hm hSL hA hAC hSQA hgG hXdef hYdef
  have hcardI : Nat.card (gomiV G) = 2 ^ (2 * m) * Nat.card ↥(X ⊓ Y) :=
    card_inf_eq_of_sup_g45le h h35 hm hSL hG hXdef hYdef
  have hcommV : ∀ x ∈ gomiV G, ∀ y ∈ gomiV G, x * y = y * x :=
    CFSG.Quasithin.isMulCommutative_subgroup_iff.mp (gomiV_moduleSetting G).1.1
  have hVsup : X ⊔ Y = gomiV G :=
    sup_eq_of_card_eq_g45le (by rw [hXdef]; exact inf_le_left)
      (by rw [hYdef]; exact inf_le_left) hcommV hcardX hcardY hcardI
  have hZle : omegaOneCenterOf (thompsonJ S) ≤
      X ⊔ (omegaOneCenterOf (thompsonJ S)).map (MulAut.conj g).toMonoidHom :=
    z_le_sup_map_conj_g45le h hA hSQA hB hgG hG hXdef hYdef hVsup
  have hZCS : omegaOneCenterOf (thompsonJ S) ≤ Subgroup.centralizer (S : Set Ω) :=
    z_le_centralizer_of_sup_g45le h hA hSQA hB hgG hG hi hXdef hZle
  rw [baum]
  exact inf_eq_left.mpr (Subgroup.le_centralizer_iff.mpr hZCS)

end CFSG.GroupTheory.GomiThm45Counterexample
