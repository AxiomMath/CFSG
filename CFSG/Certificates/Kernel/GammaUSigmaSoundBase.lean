
module

public import Certificates.Data.Kernel.GammaUSigmaK
public import CFSG.Certificates.Kernel.IdxFourCosetSound
public import CFSG.Certificates.Kernel.IdxFourSiftSound
public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs
public import CFSG.GF2Type.Smith1979.GammaU.Violation
public import CFSG.GF2Type.Smith1979.GammaU.SpanList
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.GF2Type.Smith1979.GammaU.SigmaBase
public import CFSG.GF2Type.Smith1979.GammaU.Enum
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairBase

@[expose] public section

namespace CFSG.KC.GUS

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.GammaU.ResPair CFSG.GF2Type.Smith1979.GammaU.SigmaP Module
open scoped commutatorElement

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem fld_packL : ∀ (l : List Nat), (∀ x ∈ l, x < 4096) → ∀ j, fld (CFSG.KC.IF4R.packL l) j = l.getD j 0
  | [], _, j => by
    change (0 >>> (12 * j)) &&& 4095 = 0
    simp
  | a :: l, hl, j => by
    have ha : a < 4096 := hl a List.mem_cons_self
    have hrec := fld_packL l (fun x hx => hl x (List.mem_cons_of_mem a hx))
    have hp : CFSG.KC.IF4R.packL (a :: l) = a + 4096 * CFSG.KC.IF4R.packL l := rfl
    cases j with
    | zero =>
      change ((CFSG.KC.IF4R.packL (a :: l)) >>> (12 * 0)) &&& 4095 = a
      rw [hp, Nat.mul_zero, Nat.shiftRight_zero, (by rfl : (4095 : Nat) = 2 ^ 12 - 1),
        Nat.and_two_pow_sub_one_eq_mod]
      omega
    | succ j =>
      rw [← fld_shiftRight, hp, Nat.shiftRight_eq_div_pow,
        (by omega : (a + 4096 * CFSG.KC.IF4R.packL l) / 2 ^ 12 = CFSG.KC.IF4R.packL l), hrec]
      rfl

theorem rowsOK_spec {r : List Nat} (h : rowsOK r = true) : r.length = 12 ∧ ∀ x ∈ r, x < 4096 := by
  unfold rowsOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, List.all_eq_true, Nat.blt_eq] at h
  exact h

theorem rowsP_packR {r : Array Nat} (h : rowsOK r.toList = true) :
    rowsP (CFSG.KC.IF4R.packR r) = r := by
  obtain ⟨hl, hb⟩ := rowsOK_spec h
  have hs : r.size = 12 := by simpa using hl
  apply Array.ext
  · simp [rowsP, hs]
  · intro j h1 h2
    simp only [rowsP, List.getElem_toArray, List.getElem_map, List.getElem_range]
    rw [CFSG.KC.IF4R.packR, fld_packL _ hb, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [hs] using h2)]
    simp

theorem isP_packR {r : Array Nat} (h : rowsOK r.toList = true) (U : GL) :
    IsP U (CFSG.KC.IF4R.packR r) ↔ ∀ v, U v = linOfRows r v :=
  CFSG.KC.IF4R.isP_iff_of_rowsP (rowsP_packR h) U

theorem rows_lt {r : Array Nat} (h : rowsOK r.toList = true) : ∀ x ∈ r, x < 4096 := fun x hx =>
  (rowsOK_spec h).2 x (by simpa using hx)

theorem linOfRows_invR {g : Array ℕ} (hg : ∀ x ∈ g, x < 4096) {U : GL}
    (hU : ∀ v, U v = linOfRows g v) (v : V12) : linOfRows (invR g) v = U⁻¹ v := by
  have hf : linOfRows (invR g) = (U⁻¹ : GL).toLinearMap := linMap_ext fun j => by
    rw [linOfRows_unit]
    have hget : (invR g)[(j : ℕ)]! =
        ((List.range 4096).find? fun n => appN g n == 2 ^ (j : ℕ)).getD 0 := by
      simp [invR, getElem!_pos, j.2]
    rw [hget]
    set x0 := codeOf (U⁻¹ (vecOf (2 ^ (j : ℕ))))
    have hx0 : appN g x0 = 2 ^ (j : ℕ) := by
      refine vecOf_inj (appN_lt hg x0) (two_pow_lt j) ?_
      rw [vecOf_appN, ← hU, vecOf_codeOf]
      exact LinearEquiv.apply_symm_apply U _
    have hsome : ((List.range 4096).find? fun n => appN g n == 2 ^ (j : ℕ)).isSome := by
      rw [List.find?_isSome]
      exact ⟨x0, List.mem_range.2 (codeOf_lt _), by simp [hx0]⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hsome
    rw [hn, Option.getD_some]
    have hpn := List.find?_some hn
    simp only [beq_iff_eq] at hpn
    have h1 : U (vecOf n) = vecOf (2 ^ (j : ℕ)) := by rw [hU, ← vecOf_appN, hpn]
    change vecOf n = U⁻¹ (vecOf (2 ^ (j : ℕ)))
    rw [← h1]
    exact (inv_apply_apply U (vecOf n)).symm
  exact LinearMap.congr_fun hf v

theorem mulPk_eq_of_fld : ∀ (k : Nat) (g h g' h' : Nat),
    (∀ j < k, fld (mulPk k g h) j = fld (mulPk k g' h') j) → mulPk k g h = mulPk k g' h'
  | 0, _, _, _, _, _ => rfl
  | k + 1, g, h, g', h', H => by
    have h0 := H 0 (by omega)
    rw [fld_mulPk _ _ _ 0 (by omega), fld_mulPk _ _ _ 0 (by omega)] at h0
    have ht : mulPk k g (h >>> 12) = mulPk k g' (h' >>> 12) := by
      refine mulPk_eq_of_fld k _ _ _ _ fun j hj => ?_
      have := H (j + 1) (by omega)
      rw [fld_mulPk _ _ _ _ (by omega), fld_mulPk _ _ _ _ (by omega), ← fld_shiftRight,
        ← fld_shiftRight h'] at this
      rw [fld_mulPk _ _ _ _ hj, fld_mulPk _ _ _ _ hj]
      exact this
    change (ap12 g (h &&& 4095) ||| mulPk k g (h >>> 12) <<< 12) =
      (ap12 g' (h' &&& 4095) ||| mulPk k g' (h' >>> 12) <<< 12)
    have e1 : (h &&& 4095) = fld h 0 := rfl
    have e2 : (h' &&& 4095) = fld h' 0 := rfl
    rw [e1, e2, h0, ht]

theorem fld_lt (m j : Nat) : fld m j < 4096 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem linP_single (m : Nat) (j : Fin 12) : linP m (Pi.single j 1) = vecOf (fld m j) := by
  rw [linP_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem mulP_eq_of_linP {g h g' h' : Nat} (H : ∀ v, linP (mulP g h) v = linP (mulP g' h') v) :
    mulP g h = mulP g' h' := by
  refine mulPk_eq_of_fld 12 g h g' h' fun j hj => ?_
  have := H (Pi.single ⟨j, hj⟩ 1)
  rw [linP_single, linP_single] at this
  exact vecOf_inj (fld_lt _ _) (fld_lt _ _) this

theorem nthD_map {α β : Type} (f : α → β) (d : β) (l : List α) (d' : α) {k : Nat}
    (hk : k < l.length) : nthD d (l.map f) k = f (l.getD k d') := by
  rw [nthD_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]
  rfl

theorem invsOK_spec {NG : List Nat} {NI : Nat} (h : invsOK NG NI = true) :
    ∀ l < NG.length, mulP (nthD 0 NG l) (look NI l) = idP ∧ mulP (look NI l) (nthD 0 NG l) = idP := by
  unfold invsOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h
  exact h

theorem wordG_isP {K : Subgroup GL} {gs : List Nat}
    (hgs : ∀ l < gs.length, ∃ U ∈ K, IsP U (nthD 0 gs l)) :
    ∀ w : List Nat, (∀ l ∈ w, l < gs.length) → ∃ U ∈ K, IsP U (wordG gs w)
  | [], _ => ⟨1, K.one_mem, IsP.one⟩
  | l :: w, hw => by
    obtain ⟨U, hU, hUP⟩ := hgs l (hw l List.mem_cons_self)
    obtain ⟨V, hV, hVP⟩ := wordG_isP hgs w fun l' hl' => hw l' (List.mem_cons_of_mem l hl')
    exact ⟨U * V, K.mul_mem hU hV, hUP.mul hVP⟩

theorem wordsG_spec {gs : List Nat} {ws : List (List Nat)} {ts : List Nat}
    (h : wordsG gs ws ts = true) : ws.length = ts.length ∧
      ∀ k < ts.length, (∀ l ∈ ws.getD k [], l < gs.length) ∧ wordG gs (ws.getD k []) = ts.getD k 0 := by
  unfold wordsG at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨hl, hall⟩ := h
  refine ⟨hl, fun k hk => ?_⟩
  have hk' : k < ws.length := hl ▸ hk
  have hm : (ws[k], ts[k]) ∈ List.zip ws ts := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp [hk, hk'], by simp⟩
  have := hall _ hm
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]
  exact ⟨this.1, this.2⟩

theorem stabOK_spec {gs S : List Nat} (h : stabOK gs S = true) :
    ∀ x ∈ S, ∀ g ∈ gs, ap12 g x ∈ S := by
  unfold stabOK at h
  simp only [List.all_eq_true, memN_iff] at h
  exact h

theorem reachRecs_spec {gs OL : List Nat} : ∀ {es : List (List Nat)} {x0 : Nat},
    reachRecs gs OL es x0 = true → ∀ p < es.length,
      (es.getD p []).getD 0 0 < x0 + p ∧ (es.getD p []).getD 1 0 < gs.length ∧
        ap12 (gs.getD ((es.getD p []).getD 1 0) 0) (OL.getD ((es.getD p []).getD 0 0) 0) =
          OL.getD (x0 + p) 0
  | [], _, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | e :: es, x0, h, p, hp => by
    change (Nat.blt (nthD 0 e 0) x0 && Nat.blt (nthD 0 e 1) (lenN gs) &&
      Nat.beq (ap12 (nthD 0 gs (nthD 0 e 1)) (nthD 0 OL (nthD 0 e 0))) (nthD 0 OL x0) &&
        reachRecs gs OL es (Nat.succ x0)) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nthD_eq, lenN_eq] at h
    cases p with
    | zero => exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
    | succ p =>
      have := reachRecs_spec h.2 p (by simpa using hp)
      have hx : x0 + (p + 1) = Nat.succ x0 + p := by omega
      rw [hx]
      simpa only [List.getD_cons_succ] using this

theorem reachOK_spec {gs OL : List Nat} {a : Nat} {OT : List (List Nat)} {S : List Nat}
    (h : reachOK gs a OL OT S = true) :
    OL.getD 0 0 = a ∧ OL.length = OT.length + 1 ∧ (∀ s ∈ S, s ∈ OL) ∧
      ∀ p < OT.length, (OT.getD p []).getD 0 0 < 1 + p ∧ (OT.getD p []).getD 1 0 < gs.length ∧
        ap12 (gs.getD ((OT.getD p []).getD 1 0) 0) (OL.getD ((OT.getD p []).getD 0 0) 0) =
          OL.getD (1 + p) 0 := by
  unfold reachOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, nthD_eq, lenN_eq, List.all_eq_true, memN_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.2, reachRecs_spec h.1.2⟩

theorem ncOK_spec {c p : Nat} {B : List Nat} (h : ncOK c B p = true) :
    (∀ b ∈ B, ap12 c b = b) ∧ mulP c p ≠ mulP p c := by
  unfold ncOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
  refine ⟨h.1, fun he => ?_⟩
  have h2 := h.2
  rw [he] at h2
  simp at h2

theorem pairsOK_spec {cp : List (Nat × Nat)} {n : Nat} (h : pairsOK cp n = true) :
    ∀ p ∈ cp, p.1 < n ∧ p.2 < n := by
  unfold pairsOK at h
  simp only [List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem nthD_mem {α : Type} (d : α) {l : List α} {k : Nat} (hk : k < l.length) :
    nthD d l k ∈ l := by
  rw [nthD_eq, getD_of_lt d hk]
  exact List.getElem_mem hk

theorem mem_normalizer_of_conj {G : Type*} [Group G] [Finite G] {P : Subgroup G} {g : G}
    (h : ∀ x ∈ P, g * x * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : P → P := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using this)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hx⟩
  have : g * (y : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hy
  have hxy : (y : G) = x := by simpa using this
  exact hxy ▸ y.2

theorem sigmaBasis_lt (i : ℕ) : ∀ b ∈ sigmaBasis i, b < 4096 := by
  unfold sigmaBasis
  split <;> decide

theorem linOfRows_thetaRows (v : V12) : linOfRows thetaRows v = theta0 v := by
  have hf : linOfRows thetaRows = theta0 := linMap_ext fun j => by
    rw [linOfRows_unit]
    have hj : (j : ℕ) < thetaRows.size := by simp [thetaRows]
    rw [getElem!_pos thetaRows (j : ℕ) hj]
    simp only [thetaRows, List.getElem_toArray, List.getElem_map, List.getElem_range]
    exact vecOf_theta0N (two_pow_lt j)
  exact LinearMap.congr_fun hf v

theorem rowsOK_thetaRows : rowsOK thetaRows.toList = true := by decide +kernel

end CFSG.KC.GUS

end
