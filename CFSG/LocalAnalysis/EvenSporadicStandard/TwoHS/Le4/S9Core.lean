module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9E1
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HCoord

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier
  Matrix

section Basis

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : G}

@[expose] def bL (ι : L ≃* HSCover) (w : HSCover) : G := (ι.symm w : G)

theorem bL_mul (ι : L ≃* HSCover) (a b : HSCover) : bL ι (a * b) = bL ι a * bL ι b := by
  simp [bL]

theorem bL_one (ι : L ≃* HSCover) : bL ι 1 = 1 := by simp [bL]

theorem bL_inv (ι : L ≃* HSCover) (a : HSCover) : bL ι a⁻¹ = (bL ι a)⁻¹ := by simp [bL]

theorem bL_pow (ι : L ≃* HSCover) (a : HSCover) (n : ℕ) : bL ι (a ^ n) = bL ι a ^ n := by
  simp [bL]

theorem bL_mem (ι : L ≃* HSCover) (w : HSCover) : bL ι w ∈ L := (ι.symm w).2

theorem bL_injective (ι : L ≃* HSCover) : Function.Injective (bL ι) := fun _ _ h =>
  ι.symm.injective (Subtype.ext h)

theorem f_not_mem_L (hF : FourHyp G L f) : f ∉ L := by
  intro hf
  rcases hF.eq_one_or_eq_sq_of_mem hf hF.mem_cent with h | h
  · have := hF.order
    rw [h] at this
    simp at this
  · have h4 := hF.pow_four
    have h2 : f ^ 2 = f := h.symm
    have : f = 1 := by
      calc f = f ^ 2 * f⁻¹ := by group
        _ = f * f⁻¹ := by rw [h2]
        _ = 1 := by group
    have := hF.order
    rw [‹f = 1›] at this
    simp at this

theorem bL_comm_f (hF : FourHyp G L f) (ι : L ≃* HSCover) (w : HSCover) :
    bL ι w * f = f * bL ι w := comm_f_of_mem hF (bL_mem ι w)

theorem bL_tL (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) :
    bL ι tL = f ^ 2 := by
  have hτc : ι.symm tL ∈ center L := (centerCongr ι.symm ⟨tL, hΛ.tL_mem_center⟩).2
  have hτ1 : ι.symm tL ≠ 1 := fun h => (tL_involution hΛ).2 (by simpa using congrArg ι h)
  have hcent : (ι.symm tL : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have := Subgroup.mem_center_iff.1 hτc ⟨l, hl⟩
    exact congrArg Subtype.val this
  rcases hF.eq_one_or_eq_sq_of_mem (ι.symm tL).2 hcent with h | h
  · exact absurd (Subtype.ext (by simpa using h)) hτ1
  · exact h

theorem bL_comm_of (ι : L ≃* HSCover) {a b : HSCover} (h : a * b = b * a) :
    bL ι a * bL ι b = bL ι b * bL ι a := by
  rw [← bL_mul, ← bL_mul, h]

@[expose] def bas (ι : L ≃* HSCover) (f : G) : Fin 4 → G
  | 0 => bL ι (bet 0)
  | 1 => bL ι (bet 1)
  | 2 => f
  | 3 => bL ι (bet 2)

section BasisProps


theorem bas_comm (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) :
    ∀ i j, bas ι f i * bas ι f j = bas ι f j * bas ι f i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [bas] <;>
    first
    | rfl
    | exact bL_comm_of ι (hΛ.bet_comm (by norm_num) (by norm_num))
    | exact bL_comm_f hF ι _
    | exact (bL_comm_f hF ι _).symm

theorem bas_four (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) :
    ∀ i, bas ι f i ^ 4 = 1 := by
  intro i
  fin_cases i
  · simp only [bas, ← bL_pow, hΛ.bet_pow_four (by norm_num : 0 < 3), bL_one]
  · simp only [bas, ← bL_pow, hΛ.bet_pow_four (by norm_num : 1 < 3), bL_one]
  · exact hF.pow_four
  · simp only [bas, ← bL_pow, hΛ.bet_pow_four (by norm_num : 2 < 3), bL_one]

theorem bas_inj (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) :
    ∀ v : V4, basisElt (bas ι f) v = 1 → v = 0 := by
  intro v hv
  have hd4 : (v 2).val < 4 := ZMod.val_lt _
  have hc : f ^ (v 2).val * bL ι (bet 2) ^ (v 3).val =
      bL ι (bet 2) ^ (v 3).val * f ^ (v 2).val :=
    ((((show Commute (bL ι (bet 2)) f from bL_comm_f hF ι _).pow_left (v 3).val).pow_right
      (v 2).val)).eq.symm
  have hv' : bL ι (bet 0 ^ (v 0).val * bet 1 ^ (v 1).val * bet 2 ^ (v 3).val) *
      f ^ (v 2).val = 1 := by
    rw [← hv]
    simp only [basisElt, bas, bL_mul, bL_pow]
    calc bL ι (bet 0) ^ (v 0).val * bL ι (bet 1) ^ (v 1).val * bL ι (bet 2) ^ (v 3).val *
          f ^ (v 2).val
        = bL ι (bet 0) ^ (v 0).val * bL ι (bet 1) ^ (v 1).val *
            (bL ι (bet 2) ^ (v 3).val * f ^ (v 2).val) := by rw [mul_assoc _ _ (f ^ _)]
      _ = bL ι (bet 0) ^ (v 0).val * bL ι (bet 1) ^ (v 1).val *
            (f ^ (v 2).val * bL ι (bet 2) ^ (v 3).val) := by rw [hc]
      _ = _ := by rw [← mul_assoc]
  set X := bet 0 ^ (v 0).val * bet 1 ^ (v 1).val * bet 2 ^ (v 3).val with hX
  have ha : (v 0).val < 4 := ZMod.val_lt _
  have hb : (v 1).val < 4 := ZMod.val_lt _
  have hcc : (v 3).val < 4 := ZMod.val_lt _
  have hfL : ∀ d : ℕ, d % 2 = 1 → f ^ d ∈ L → False := by
    intro d hd hmem
    apply f_not_mem_L hF
    obtain ⟨m, rfl⟩ : ∃ m, d = 2 * m + 1 := ⟨d / 2, by omega⟩
    have h1 : f ^ (2 * m + 1) * ((f ^ 2) ^ m)⁻¹ = f := by
      rw [pow_succ', pow_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [← h1]
    exact L.mul_mem hmem (L.inv_mem (L.pow_mem hF.sq_mem m))
  have hnL : bL ι X ∈ L := bL_mem ι X
  have hzero : ∀ i : Fin 4, (v i).val = 0 → v i = 0 := fun i h => (ZMod.val_eq_zero _).1 h
  obtain h0 | h1 | h2 | h3 : (v 2).val = 0 ∨ (v 2).val = 1 ∨ (v 2).val = 2 ∨ (v 2).val = 3 := by
    omega
  · rw [h0, pow_zero, mul_one] at hv'
    have hX1 : X = 1 := bL_injective ι (by rw [hv', bL_one])
    obtain ⟨e0, e1, e3, -⟩ := bet_indep (u := 0) ha hb hcc (by norm_num)
      (by rw [pow_zero, mul_one]; exact hX1)
    funext i
    fin_cases i
    · exact hzero 0 e0
    · exact hzero 1 e1
    · exact hzero 2 h0
    · exact hzero 3 e3
  · exfalso
    have hfm : f ^ (v 2).val ∈ L := by
      have : f ^ (v 2).val = (bL ι X)⁻¹ := eq_inv_of_mul_eq_one_right hv'
      rw [this]
      exact L.inv_mem hnL
    exact hfL _ (by omega) hfm
  · exfalso
    rw [h2, ← bL_tL hΛ hF ι, ← bL_mul] at hv'
    have hXt : X * tL = 1 := bL_injective ι (by rw [hv', bL_one])
    obtain ⟨-, -, -, hu⟩ := bet_indep (u := 1) ha hb hcc (by norm_num) (by rw [pow_one]; exact hXt)
    exact absurd hu (by norm_num)
  · exfalso
    have hfm : f ^ (v 2).val ∈ L := by
      have : f ^ (v 2).val = (bL ι X)⁻¹ := eq_inv_of_mul_eq_one_right hv'
      rw [this]
      exact L.inv_mem hnL
    exact hfL _ (by omega) hfm

@[expose] noncomputable def basisCoord (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) :
    ECoord G :=
  ECoord.ofBasis (bas ι f) (bas_comm hΛ hF ι) (bas_four hΛ hF ι) (bas_inj hΛ hF ι)

theorem basisCoord_elt (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) (v : V4) :
    (basisCoord hΛ hF ι).elt v = basisElt (bas ι f) v := rfl

theorem bas_mem (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) (i : Fin 4) :
    bas ι f i ∈ (basisCoord hΛ hF ι).E :=
  ECoord.ofBasis_mem _ _ _ _ i

theorem fVec_eq : fVec = Pi.single 2 1 := by
  funext i
  fin_cases i <;> simp [fVec, vecOfList]

theorem vec_f (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) :
    (basisCoord hΛ hF ι).vec f = fVec := by
  have := ECoord.ofBasis_vec (bas ι f) (bas_comm hΛ hF ι) (bas_four hΛ hF ι) (bas_inj hΛ hF ι) 2
  rw [fVec_eq]
  exact this

theorem f_mem_E (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) :
    f ∈ (basisCoord hΛ hF ι).E := bas_mem hΛ hF ι 2

theorem bL_kapL (hΛ : HSCtx) (hF : FourHyp G L f) (ι : L ≃* HSCover) {c : List ℕ}
    (hc : ∀ i, c.getD i 0 < 4) (h2 : c.getD 2 0 % 2 = 0) :
    bL ι (kapL c) = (basisCoord hΛ hF ι).elt (vecOfList c) := by
  rw [basisCoord_elt]
  have hv : ∀ i : Fin 4, (vecOfList c i).val = c.getD i.val 0 := by
    intro i
    simp only [vecOfList]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hc i.val)]
  simp only [basisElt, hv, kapL, bL_mul, bL_pow, bL_tL hΛ hF ι, bas]
  have : (f ^ 2) ^ (c.getD 2 0 / 2) = f ^ c.getD 2 0 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [this]
  rfl

theorem conj_mem_of_closure {S : Set G} {x : G} (h : ∀ s ∈ S, x * s * x⁻¹ ∈ closure S) :
    ∀ g ∈ closure S, x * g * x⁻¹ ∈ closure S := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => simp
  | mul a b _ _ ha hb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {x : G} (h : ∀ g ∈ H, x * g * x⁻¹ ∈ H) :
    x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  let φ : H → H := fun e => ⟨x * e * x⁻¹, h e e.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [φ] at this
    exact Subtype.ext (by simpa using this)
  obtain ⟨e, he⟩ := Finite.surjective_of_injective hinj ⟨x * g * x⁻¹, hg⟩
  have : x * (e : G) * x⁻¹ = x * g * x⁻¹ := congrArg Subtype.val he
  have h3 : (e : G) = g := by simpa using this
  rw [← h3]
  exact e.2

theorem colOf_getD (d : List ℕ) (j : ℕ) (i : ℕ) (hi : i < 4) :
    (colOf d j).getD i 0 = d.getD (4 * i + j) 0 := by
  simp [colOf, List.getD_eq_getElem?_getD, hi]

theorem mat_eq_of_conj_basis {C : ECoord G} {x : G} {d : List ℕ}
    (hx : ∀ j : Fin 4, x * C.elt (Pi.single j 1) * x⁻¹ = C.elt (vecOfList (colOf d j.val))) :
    C.mat x = matOfList d := by
  ext i j
  have h1 : C.mat x i j = C.act x (Pi.single j 1) i := rfl
  have h2 : C.act x (Pi.single j 1) = vecOfList (colOf d j.val) := by
    unfold ECoord.act
    rw [hx j, C.vec_elt]
  rw [h1, h2]
  simp only [vecOfList, matOfList, Matrix.of_apply]
  rw [colOf_getD d j.val i.val i.2]

theorem colOf_lt {d : List ℕ} (hd : ∀ x ∈ d, x < 4) (j i : ℕ) : (colOf d j).getD i 0 < 4 := by
  by_cases hi : i < 4
  · rw [colOf_getD d j i hi]
    by_cases h : 4 * i + j < d.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hd _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      norm_num
  · have : (colOf d j).length = 4 := by simp [colOf]
    rw [List.getD_eq_default _ _ (by omega)]
    norm_num

end BasisProps

end Basis

end CFSG.EvenSporadicStandard.TwoHS
