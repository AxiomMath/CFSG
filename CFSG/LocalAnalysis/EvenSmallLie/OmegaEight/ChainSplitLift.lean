module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Lift
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

section LiftOf

variable [Finite G]
  {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G}

theorem exists_coord_lift_of (hR : RadicalData ε L U Q P a ψ p)
    (hPQ : ∀ x ∈ P, x ∈ centralizer (Q : Set G) → x ∈ Q) {A : Subgroup G} (hL : Level Q 2 A)
    (hPA : ∀ x ∈ P, ∀ y ∈ A, x * y * x⁻¹ ∈ A) :
    ∃ Φ, Coord4 A ψ Φ ∧ ∀ w : List ℕ, Rep Φ (wordElt p w) (prodW ε (c0Mat ε) w) := by
  have hQ := hR.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hR.Q_mul_self hq
  obtain ⟨Φ, hΦ⟩ := exists_coord4 (A := A) (Q := Q) (ψ := ψ) hL.comm
    (fun x hx => by simpa using hL.pow_eq_one x hx)
    (fun x hx => by simpa [sq] using hL.pow_mem_Q (by norm_num) hx)
    hL.mem_Q hL.Q_le
    (fun q hq => by
      obtain ⟨x, hx, hxq⟩ := hL.exists_pow_eq hQ hQ2 (by norm_num) hq
      exact ⟨x, hx, by simpa [sq] using hxq⟩)
    (by rw [hL.card_eq]; norm_num) hR.ψ_add hR.ψ_mem hR.mem_ψ
  have hrep : ∀ s : Fin 6, ∃ D : Mat6, Rep Φ (p s) (liftW ε (fun _ => D) s) := by
    intro s
    obtain ⟨F, hF⟩ := hΦ.exists_rep (hPA _ (hR.p_mem s))
    have hred := hΦ.map_red4_of_rep hF hR.ψ_inj (hR.p_act s)
    obtain ⟨D, hD⟩ := eq_lift4_add F
    refine ⟨D, ?_⟩
    rw [liftW, ← hred, ← hD]
    exact hF
  choose D hD using hrep
  set C : ℕ → Mat6 := fun s => if h : s < 6 then D ⟨s, h⟩ else 0 with hCdef
  have hrepAt : ∀ s : ℕ, Rep Φ (pAt p s) (liftW ε C s) := by
    intro s
    by_cases hs : s < 6
    · have e1 : pAt p s = p ⟨s, hs⟩ := by simp [pAt, hs]
      have e2 : liftW ε C s = liftW ε (fun _ => D ⟨s, hs⟩) s := by simp [liftW, hCdef, hs]
      rw [e1, e2]
      exact hD ⟨s, hs⟩
    · have e1 : pAt p s = 1 := by simp [pAt, hs]
      have e2 : liftW ε C s = 1 := by
        rw [liftW, genMat_of_le ε (not_lt.1 hs), lift4_one]
        simp [hCdef, hs, lift4_zero]
      rw [e1, e2]
      exact Coord4.rep_one
  have hwordElt : ∀ (s : ℕ) (w : List ℕ), wordElt p (s :: w) = pAt p s * wordElt p w := by
    intro s w
    rw [wordElt, List.map_cons, List.prod_cons]
    rfl
  have hrepW : ∀ w, Rep Φ (wordElt p w) (prodW ε C w) := by
    intro w
    induction w with
    | nil => exact Coord4.rep_one
    | cons s w ih =>
      rw [hwordElt, prodW_cons]
      exact Coord4.rep_mul (hrepAt s) ih
  have hrel : ∀ w ∈ extRels ε, prodW ε C w = 1 := by
    intro w hw
    have hid : toMat 6 6 (wordRows ε w) = 1 := by
      have h := (cohChecks ε).1
      simp only [relCheck6, Bool.and_eq_true, List.all_eq_true] at h
      exact toMat_eq_one_of_bIsId (h.2 w hw)
    have hN := hR.P_le_normalizer (hR.wordElt_mem w)
    have hQw : wordElt p w ∈ Q := by
      refine hPQ _ (hR.wordElt_mem w) (mem_centralizer_iff.2 fun q hq => ?_)
      obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
      have h1 := (hR.lin_eq_iff hN v v).1 (by rw [lin_wordElt_eq hR, hid, one_mulVec])
      calc ψ v * wordElt p w = wordElt p w * ψ v * (wordElt p w)⁻¹ * wordElt p w := by rw [h1]
        _ = wordElt p w * ψ v := by group
    exact hΦ.rep_unique (hrepW w) (hΦ.rep_of_mem_A hL.comm (hL.Q_le hQw))
  have hUR : ∀ w ∈ extRels ε, (urMat6 ε (C - c0Mat ε) w).2 = 0 := by
    intro w hw
    have h := prodW_sub ε C (c0Mat ε) w
    rw [hrel w hw, prodW_c0_rel ε hw, sub_self] at h
    exact two_smul_lift4_eq_zero h.symm
  obtain ⟨X, hX⟩ := exists_coboundary6 ε (fun s : Fin 6 => (C - c0Mat ε) s) fun w hw => by
    rw [← hUR w hw]
    refine urMat6_congr ε w fun s hs => ?_
    obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.1 hw
    have hs' : s ∈ (extRels ε).getD k [] := by rw [List.getD_eq_getElem _ _ hk, hkw]; exact hs
    have hs6 := extRels_lt ε hs'
    simp [extC, hs6]
  refine ⟨_, hΦ.change X, fun w => ?_⟩
  have hgen : ∀ s : ℕ, Rep (fun v => Φ ((1 + (2 : ZMod 4) • lift4 X) *ᵥ v)) (pAt p s)
      (liftW ε (c0Mat ε) s) := by
    intro s
    have h := Coord4.rep_change X (hrepAt s)
    rwa [liftW, conj_two, c0_identity C X (fun h6 => hX ⟨s, h6⟩)
      (fun h6 => by simp [hCdef, show ¬ s < 6 by omega])] at h
  induction w with
  | nil => exact Coord4.rep_one
  | cons s w ih =>
    rw [hwordElt, prodW_cons]
    exact Coord4.rep_mul (hgen s) ih

omit [Finite G] in
theorem rep_of_mem_P (hR : RadicalData ε L U Q P a ψ p)
    (hPQ : ∀ x ∈ P, x ∈ centralizer (Q : Set G) → x ∈ Q) {B : Subgroup G} (hL : Level Q 2 B)
    {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 B ψ Φ)
    (hw : ∀ w, Rep Φ (wordElt p w) (prodW ε (c0Mat ε) w)) {x : G} (hx : x ∈ P) {w : List ℕ}
    (hxw : ∀ v, lin ψ x v = toMat 6 6 (wordRows ε w) *ᵥ v) :
    Rep Φ x (prodW ε (c0Mat ε) w) := by
  have hwP := hR.wordElt_mem w
  have hwN := hR.P_le_normalizer hwP
  have hxN := hR.P_le_normalizer hx
  have hyQ : (wordElt p w)⁻¹ * x ∈ Q := by
    refine hPQ _ (mul_mem (inv_mem hwP) hx) (mem_centralizer_iff.2 fun q hq => ?_)
    obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
    have h1 : lin ψ ((wordElt p w)⁻¹ * x) v = v := by
      rw [hR.lin_mul (inv_mem hwN) hxN, hxw, ← lin_wordElt_eq hR, hR.lin_inv' hwN]
    have h2 := (hR.lin_eq_iff (mul_mem (inv_mem hwN) hxN) v v).1 h1
    calc ψ v * ((wordElt p w)⁻¹ * x) =
        (wordElt p w)⁻¹ * x * ψ v * ((wordElt p w)⁻¹ * x)⁻¹ * ((wordElt p w)⁻¹ * x) := by
          rw [h2]
      _ = (wordElt p w)⁻¹ * x * ψ v := by group
  have h := Coord4.rep_mul (hw w) (hΦ.rep_of_mem_A hL.comm (hL.Q_le hyQ))
  rwa [mul_one, mul_inv_cancel_left] at h

end LiftOf

end CFSG.EvenSmallLie.OmegaEight.Chain
