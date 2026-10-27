module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Coord
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1D
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainBasic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

theorem lift4_one : lift4 (1 : Mat6) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [lift4, map_apply, one_apply_eq]
    rfl
  · simp [lift4, h]

theorem lift4_zero : lift4 (0 : Mat6) = 0 := by
  ext i j
  simp [lift4]

theorem c0Mat_of_le (ε : Eps) {s : ℕ} (hs : 6 ≤ s) : c0Mat ε s = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 6 := ⟨s - 6, by omega⟩
  rw [c0Mat]
  cases ε <;> exact toMat_zero6

theorem lin_wordElt_eq {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
    (hR : RadicalData ε L U Q P a ψ p) (w : List ℕ) (v : V6) :
    lin ψ (wordElt p w) v = toMat 6 6 (wordRows ε w) *ᵥ v := by
  induction w generalizing v with
  | nil => rw [show wordElt p [] = 1 from rfl, hR.lin_one, wordRows, toMat_id6', one_mulVec]
  | cons i w ih =>
    have h : wordElt p (i :: w) = pAt p i * wordElt p w := by
      rw [wordElt, List.map_cons, List.prod_cons]; rfl
    rw [h, hR.lin_mul (hR.P_le_normalizer (hR.pAt_mem i))
      (hR.P_le_normalizer (hR.wordElt_mem w)), ih, hR.lin_pAt, wordRows, toMat_bmul,
      mulVec_mulVec, genMat]

section Lift

variable [Finite G]
  {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G}

omit [Finite G] in
theorem c0_identity (C : ℕ → Mat6) (X : Mat6) {s : ℕ}
    (hs : s < 6 → (C - c0Mat ε) s = genMat ε s * X + X * genMat ε s) (hs' : 6 ≤ s → C s = 0) :
    C s + X * genMat ε s + genMat ε s * X = c0Mat ε s := by
  have h2 : ∀ Y : Mat6, Y + Y = 0 := fun Y => CharTwo.add_self_eq_zero Y
  by_cases h6 : s < 6
  · have h := hs h6
    rw [Pi.sub_apply, sub_eq_iff_eq_add] at h
    rw [h]
    calc genMat ε s * X + X * genMat ε s + c0Mat ε s + X * genMat ε s + genMat ε s * X =
        c0Mat ε s + (genMat ε s * X + genMat ε s * X) + (X * genMat ε s + X * genMat ε s) := by
          abel
      _ = c0Mat ε s := by rw [h2, h2, add_zero, add_zero]
  · rw [hs' (not_lt.1 h6), c0Mat_of_le ε (not_lt.1 h6), genMat_of_le ε (not_lt.1 h6), mul_one,
      one_mul, zero_add, h2]

theorem exists_coord_lift (hS : Setup ε t L U Q P a ψ p) {A : Subgroup G} (hL : Level Q 2 A)
    (hPA : ∀ x ∈ P, ∀ y ∈ A, x * y * x⁻¹ ∈ A) :
    ∃ Φ, Coord4 A ψ Φ ∧ ∀ w : List ℕ, Rep Φ (wordElt p w) (prodW ε (c0Mat ε) w) := by
  have hR := hS.rad
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
      refine hS.mem_Q_of_mem_P (hR.wordElt_mem w) (mem_centralizer_iff.2 fun q hq => ?_)
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

end Lift

end CFSG.EvenSmallLie.OmegaEight.Chain
