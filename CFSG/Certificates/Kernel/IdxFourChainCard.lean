
module

public import CFSG.Certificates.Kernel.IdxFourChainSound
public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public section

namespace CFSG.KC.IF4C

open CFSG.GF2Type.Smith1979.GammaU

variable {SP SI : Nat} {T O PS B : List Nat} {TL WD : List (List Nat)}
  {TR R : List (List (List Nat))} {k j0 n : Nat}

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem pathP_nil (ts : List Nat) : pathP ts [] = idP := by
  cases ts <;> rfl

namespace TreeHyp

variable (hC : TreeHyp SP SI T O PS B TL WD TR k j0 n)
include hC

theorem j0_le : j0 ≤ n := by
  have := (wordsOK_spec SP SI WD hC.words).1
  omega

theorem tl_lt {i : Nat} (hi : i < k) {g : Nat} (hg : g ∈ TL.getD i []) : g < n := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [hC.tl0, List.mem_range] at hg
    exact Nat.lt_of_lt_of_le hg hC.j0_le
  · rw [tlOK_spec SP B TL (hC.tl i hi0 hi), mem_fixL] at hg
    exact hg.1

theorem exists_isP {l : Nat} (hl : l < n) : ∃ U, IsP U (look SP l) :=
  IsP.exists_of_mul (invOK_spec SP SI hC.inv l hl)

theorem exists_gen : ∀ l < n, ∃ U ∈ lvlGrp SP TL 0, IsP U (look SP l) := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro hl
    by_cases hl0 : l < j0
    · obtain ⟨U, hU⟩ := hC.exists_isP hl
      refine ⟨U, Subgroup.subset_closure ⟨l, ?_, hU⟩, hU⟩
      rw [hC.tl0]
      exact List.mem_range.2 hl0
    · obtain ⟨hlen, hw⟩ := wordsOK_spec SP SI WD hC.words
      obtain ⟨heq, hlet⟩ := hw (l - j0) (by omega)
      have hl' : l = j0 + (l - j0) := by omega
      rw [hl', heq]
      have hword : ∀ w : List Nat, (∀ e ∈ w, e / 2 < l) →
          ∃ U ∈ lvlGrp SP TL 0, IsP U (wordP SP SI w) := by
        intro w
        induction w with
        | nil => exact fun _ => ⟨1, Subgroup.one_mem _, IsP.one⟩
        | cons e w ihw =>
          intro he
          obtain ⟨V, hV, hVP⟩ := ihw fun e' h' => he e' (List.mem_cons_of_mem _ h')
          have hel : e / 2 < l := he e List.mem_cons_self
          obtain ⟨U, hU, hUP⟩ := ih (e / 2) hel (by omega)
          change ∃ U ∈ lvlGrp SP TL 0, IsP U (mulP (bif Nat.beq (Nat.mod e 2) 0 then
            look SP (Nat.div e 2) else look SI (Nat.div e 2)) (wordP SP SI w))
          cases hb : Nat.beq (Nat.mod e 2) 0
          · exact ⟨U⁻¹ * V, Subgroup.mul_mem _ (Subgroup.inv_mem _ hU) hV,
              (hUP.inv (invOK_spec SP SI hC.inv _ (by omega))).mul hVP⟩
          · exact ⟨U * V, Subgroup.mul_mem _ hU hV, hUP.mul hVP⟩
      exact hword _ fun e he => by have := hlet e he; omega

theorem lvlGrp_eq_bot : lvlGrp SP TL k = ⊥ := by
  rw [lvlGrp, Subgroup.closure_eq_bot_iff]
  rintro U ⟨g, hg, -⟩
  rw [hC.tlk] at hg
  exact absurd hg List.not_mem_nil

theorem le_zero {i : Nat} (hi : i ≤ k) : lvlGrp SP TL i ≤ lvlGrp SP TL 0 := by
  rcases Nat.lt_or_ge i k with hik | hik
  · rw [lvlGrp, Subgroup.closure_le]
    rintro U ⟨g, hg, hU⟩
    obtain ⟨V, hV, hVP⟩ := hC.exists_gen g (hC.tl_lt hik hg)
    rw [hU.inj hVP]
    exact hV
  · have hik' : i = k := by omega
    rw [hik', hC.lvlGrp_eq_bot]
    exact bot_le

theorem succ_le {i : Nat} (hi1 : 1 ≤ i) (hi : i < k) :
    lvlGrp SP TL (i + 1) ≤ lvlGrp SP TL i := by
  rcases Nat.lt_or_ge (i + 1) k with hik | hik
  · refine Subgroup.closure_mono ?_
    rintro U ⟨g, hg, hU⟩
    refine ⟨g, ?_, hU⟩
    rw [tlOK_spec SP B TL (hC.tl (i + 1) (by omega) hik), mem_fixL] at hg
    rw [tlOK_spec SP B TL (hC.tl i hi1 hi), mem_fixL]
    exact ⟨hg.1, fun q hq => hg.2 q (by omega)⟩
  · have hik' : i + 1 = k := by omega
    rw [hik', hC.lvlGrp_eq_bot]
    exact bot_le

theorem le_of_le {m l : Nat} (hm : 1 ≤ m) (hml : m ≤ l) (hl : l ≤ k) :
    lvlGrp SP TL l ≤ lvlGrp SP TL m := by
  induction l, hml using Nat.le_induction with
  | base => exact le_rfl
  | succ l hml ih => exact (hC.succ_le (by omega) (by omega)).trans (ih (by omega))

theorem fix {l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ k) {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ lvlGrp SP TL l) {q : Nat} (hq : q < l) :
    U (vecOf (B.getD q 0)) = vecOf (B.getD q 0) := by
  induction hU using Subgroup.closure_induction with
  | mem U hU =>
    obtain ⟨g, hg, hUg⟩ := hU
    rcases Nat.lt_or_ge l k with hlk | hlk
    · rw [tlOK_spec SP B TL (hC.tl l hl1 hlk), mem_fixL] at hg
      rw [hUg.apply_code, hg.2 q hq]
    · have hlk' : l = k := by omega
      rw [hlk', hC.tlk] at hg
      exact absurd hg List.not_mem_nil
  | one => rfl
  | mul U V _ _ hU hV => rw [LinearEquiv.mul_apply, hV, hU]
  | inv U _ hU =>
    calc U⁻¹ (vecOf (B.getD q 0)) = U⁻¹ (U (vecOf (B.getD q 0))) := by rw [hU]
      _ = (U⁻¹ * U) (vecOf (B.getD q 0)) := rfl
      _ = _ := by rw [inv_mul_cancel]; rfl

theorem tr {i : Nat} (hi : i < k) :
    ∀ x < O.getD i 0, ∃ U ∈ lvlGrp SP TL i, IsP U (look (T.getD i 0) x) := by
  obtain ⟨h0, hlen, hrec⟩ := treeOK_spec SP T O TL TR (hC.tree i hi)
  have hsp := treeRecs_spec SP T TL hrec
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    cases x with
    | zero => exact ⟨1, Subgroup.one_mem _, by rw [h0]; exact IsP.one⟩
    | succ p =>
      obtain ⟨hpar, hg, heq⟩ := hsp p (by omega)
      have hpar' : ((TR.getD i []).getD p []).getD 0 0 < p + 1 := by omega
      obtain ⟨V, hV, hVP⟩ := ih _ hpar' (by omega)
      obtain ⟨U, hUP⟩ := hC.exists_isP (hC.tl_lt hi hg)
      refine ⟨U * V, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hg, hUP⟩) hV, ?_⟩
      have hl : look (T.getD i 0) (p + 1) = look (T.getD i 0) (1 + p) := by rw [Nat.add_comm]
      rw [hl, ← heq]
      exact hUP.mul hVP

theorem exists_tr {i : Nat} (hi : i < k) :
    ∀ x < O.getD i 0, ∃ U ∈ lvlGrp SP TL 0, IsP U (look (T.getD i 0) x) := by
  intro x hx
  obtain ⟨U, hU, hUP⟩ := hC.tr hi x hx
  exact ⟨U, hC.le_zero hi.le hU, hUP⟩

theorem succ_le_self {i : Nat} (hi : i < k) : lvlGrp SP TL (i + 1) ≤ lvlGrp SP TL i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact hC.le_zero (by omega)
  · exact hC.succ_le hi0 hi

theorem idx_eq {i : Nat} (hi : i < k) {x x' : Nat} (hx : x < O.getD i 0) (hx' : x' < O.getD i 0)
    {V V' : V12 ≃ₗ[ZMod 2] V12} (hV : IsP V (look (T.getD i 0) x))
    (hV' : IsP V' (look (T.getD i 0) x'))
    (h : V (vecOf (B.getD i 0)) = V' (vecOf (B.getD i 0))) : x = x' := by
  rw [hV.apply_code, hV'.apply_code] at h
  have := vecOf_inj (ap12_lt _ _) (ap12_lt _ _) h
  have hp := posOK_spec T O PS B (hC.pos i hi)
  rw [← hp x hx, ← hp x' hx', this]

theorem card_succ_le {i : Nat} (hi : i < k) :
    O.getD i 0 * Nat.card (lvlGrp SP TL (i + 1)) ≤ Nat.card (lvlGrp SP TL i) := by
  have htr := hC.tr hi
  choose! Tr hTrH hTrP using htr
  have hle := hC.succ_le_self hi
  let φ : Fin (O.getD i 0) × lvlGrp SP TL (i + 1) → lvlGrp SP TL i := fun q =>
    ⟨Tr q.1 * q.2, Subgroup.mul_mem _ (hTrH _ q.1.2) (hle q.2.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨x, h⟩ ⟨x', h'⟩ hxx
    have heq : Tr x * h = Tr x' * h' := congrArg Subtype.val hxx
    have hb := congrArg (fun U : V12 ≃ₗ[ZMod 2] V12 => U (vecOf (B.getD i 0))) heq
    simp only [LinearEquiv.mul_apply] at hb
    rw [hC.fix (by omega) (by omega) h.2 (Nat.lt_succ_self i),
      hC.fix (by omega) (by omega) h'.2 (Nat.lt_succ_self i)] at hb
    have hxx' : (x : Nat) = x' := hC.idx_eq hi x.2 x'.2 (hTrP _ x.2) (hTrP _ x'.2) hb
    have hx : x = x' := Fin.ext hxx'
    subst hx
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq))
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at this

theorem prod_le_card : O.prod ≤ Nat.card (lvlGrp SP TL 0) := by
  have key : ∀ d i, i + d = k → (O.drop i).prod ≤ Nat.card (lvlGrp SP TL i) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      rw [Nat.add_zero] at hi
      subst hi
      rw [List.drop_eq_nil_of_le (by rw [hC.lenO]), List.prod_nil]
      exact Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    | succ d ih =>
      intro i hi
      have hik : i < k := by omega
      have hO : i < O.length := by rw [hC.lenO]; exact hik
      rw [List.drop_eq_getElem_cons hO, List.prod_cons, ← getD_of_lt 0 hO]
      exact (Nat.mul_le_mul_left _ (ih (i + 1) (by omega))).trans (hC.card_succ_le hik)
  simpa using key k 0 (by omega)

end TreeHyp

namespace ChainHyp

variable (hC : ChainHyp SP SI T O PS B TL WD TR R k j0 n)
include hC

theorem path {i : Nat} : ∀ (as : List Nat) (s : Nat), i + 1 ≤ s →
    pathOK (O.drop s) as = true → ∃ P ∈ lvlGrp SP TL (i + 1), IsP P (pathP (T.drop s) as)
  | [], s, _, _ => ⟨1, Subgroup.one_mem _, by rw [pathP_nil]; exact IsP.one⟩
  | a :: as, s, hs, h => by
    by_cases hsk : s < k
    · have hO : s < O.length := by rw [hC.lenO]; exact hsk
      have hT : s < T.length := by rw [hC.lenT]; exact hsk
      rw [List.drop_eq_getElem_cons hO] at h
      change (Nat.blt a O[s] && pathOK (O.drop (s + 1)) as) = true at h
      rw [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨U, hU, hUP⟩ := hC.tr hsk a (by rw [getD_of_lt _ hO]; exact h.1)
      obtain ⟨P, hP, hPP⟩ := path (i := i) as (s + 1) (by omega) h.2
      refine ⟨U * P, Subgroup.mul_mem _ (hC.le_of_le (by omega) hs hsk.le hU) hP, ?_⟩
      rw [List.drop_eq_getElem_cons hT]
      change IsP _ (mulP (look T[s] a) (pathP (T.drop (s + 1)) as))
      rw [← getD_of_lt 0 hT]
      exact hUP.mul hPP
    · rw [List.drop_eq_nil_of_le (by rw [hC.lenO]; omega)] at h
      exact absurd (h : false = true) Bool.false_ne_true

theorem rec_all {i : Nat} (hi : i < k) :
    ∀ r < O.getD i 0 * (TL.getD i []).length,
      recOK SP T O TL i r ((R.getD i []).getD r []) = true := by
  intro r hr
  have hcnt := hC.cnt i hi
  unfold cntOK at hcnt
  simp only [Nat.beq_eq, nthD_eq, lenN_eq, Nat.mul_eq] at hcnt
  have hrl : r < (R.getD i []).length := by rw [hcnt]; exact hr
  have hb := hC.blk i hi (r / 32) (by omega)
  unfold blkOK at hb
  simp only [takeN_eq, dropN_eq, nthD_eq, Nat.mul_eq] at hb
  have := recsOK_spec SP T O TL hb (r % 32)
    (by rw [List.length_take, List.length_drop]; omega)
  have hr32 : 32 * (r / 32) + r % 32 = r := by omega
  rw [hr32] at this
  rwa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    hr32, ← List.getD_eq_getElem?_getD] at this

theorem surj {i : Nat} (hi : i < k) {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ lvlGrp SP TL i) :
    ∃ x < O.getD i 0, ∃ V, IsP V (look (T.getD i 0) x) ∧
      ∃ h ∈ lvlGrp SP TL (i + 1), U = V * h := by
  obtain ⟨h0, hlen, -⟩ := treeOK_spec SP T O TL TR (hC.tree i hi)
  refine mem_of_closure (K := {U | ∃ x < O.getD i 0, ∃ V, IsP V (look (T.getD i 0) x) ∧
    ∃ h ∈ lvlGrp SP TL (i + 1), U = V * h}) ?_ ?_ hU
  · exact ⟨0, by omega, 1, by rw [h0]; exact IsP.one, 1, Subgroup.one_mem _, by rw [mul_one]⟩
  · rintro s ⟨g, hg, hs⟩ _ ⟨x, hx, V, hV, h, hh, rfl⟩
    obtain ⟨p, hp, hpg⟩ := List.mem_iff_getElem.1 hg
    set N := (TL.getD i []).length with hN
    have hN0 : 0 < N := by omega
    have hr : p + N * x < O.getD i 0 * N := by
      have : N * (x + 1) ≤ N * O.getD i 0 := Nat.mul_le_mul_left _ hx
      rw [Nat.mul_comm (O.getD i 0)]
      rw [Nat.mul_succ] at this
      omega
    obtain ⟨y, as, -, hy, hpath, heq⟩ := recOK_spec SP T O TL (hC.rec_all hi _ hr)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp, Nat.add_mul_div_left _ _ hN0,
      Nat.div_eq_of_lt hp, Nat.zero_add, getD_of_lt _ hp, hpg] at heq
    obtain ⟨W, -, hWP⟩ := hC.tr hi y hy
    obtain ⟨P, hP, hPP⟩ := hC.path (i := i) as (i + 1) le_rfl hpath
    have hsv : s * V = W * P := IsP.inj (hs.mul hV) (by rw [heq]; exact hWP.mul hPP)
    exact ⟨y, hy, W, hWP, P * h, Subgroup.mul_mem _ hP hh, by rw [← mul_assoc, hsv, mul_assoc]⟩

theorem card_succ {i : Nat} (hi : i < k) :
    Nat.card (lvlGrp SP TL i) = O.getD i 0 * Nat.card (lvlGrp SP TL (i + 1)) := by
  have htr := hC.tr hi
  choose! Tr hTrH hTrP using htr
  have hle := hC.succ_le_self hi
  let φ : Fin (O.getD i 0) × lvlGrp SP TL (i + 1) → lvlGrp SP TL i := fun q =>
    ⟨Tr q.1 * q.2, Subgroup.mul_mem _ (hTrH _ q.1.2) (hle q.2.2)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨x, h⟩ ⟨x', h'⟩ hxx
      have heq : Tr x * h = Tr x' * h' := congrArg Subtype.val hxx
      have hb := congrArg (fun U : V12 ≃ₗ[ZMod 2] V12 => U (vecOf (B.getD i 0))) heq
      simp only [LinearEquiv.mul_apply] at hb
      rw [hC.fix (by omega) (by omega) h.2 (Nat.lt_succ_self i),
        hC.fix (by omega) (by omega) h'.2 (Nat.lt_succ_self i)] at hb
      have hxx' : (x : Nat) = x' := hC.idx_eq hi x.2 x'.2 (hTrP _ x.2) (hTrP _ x'.2) hb
      have hx : x = x' := Fin.ext hxx'
      subst hx
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq))
    · rintro ⟨U, hU⟩
      obtain ⟨x, hx, V, hV, h, hh, rfl⟩ := hC.surj hi hU
      refine ⟨(⟨x, hx⟩, ⟨h, hh⟩), Subtype.ext ?_⟩
      change Tr x * h = V * h
      rw [IsP.inj (hTrP x hx) hV]
  rw [← Nat.card_eq_of_bijective φ hφ, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin]

theorem card_zero : Nat.card (lvlGrp SP TL 0) = O.prod := by
  have key : ∀ d i, i + d = k → Nat.card (lvlGrp SP TL i) = (O.drop i).prod := by
    intro d
    induction d with
    | zero =>
      intro i hi
      rw [Nat.add_zero] at hi
      subst hi
      rw [hC.lvlGrp_eq_bot, List.drop_eq_nil_of_le (by rw [hC.lenO]), List.prod_nil,
        Subgroup.card_bot]
    | succ d ih =>
      intro i hi
      have hik : i < k := by omega
      have hO : i < O.length := by rw [hC.lenO]; exact hik
      rw [hC.card_succ hik, ih (i + 1) (by omega), List.drop_eq_getElem_cons hO, List.prod_cons,
        getD_of_lt _ hO]
  simpa using key k 0 (by omega)

theorem eq_one_of_fix {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ lvlGrp SP TL 0)
    (hfix : ∀ q < k, U (vecOf (B.getD q 0)) = vecOf (B.getD q 0)) : U = 1 := by
  have key : ∀ d i, i + d = k → ∀ U ∈ lvlGrp SP TL i,
      (∀ q, i ≤ q → q < k → U (vecOf (B.getD q 0)) = vecOf (B.getD q 0)) → U = 1 := by
    intro d
    induction d with
    | zero =>
      intro i hi U hU _
      rw [Nat.add_zero] at hi
      subst hi
      rw [hC.lvlGrp_eq_bot] at hU
      exact (Subgroup.mem_bot).1 hU
    | succ d ih =>
      intro i hi U hU hf
      have hik : i < k := by omega
      obtain ⟨h0, -, -⟩ := treeOK_spec SP T O TL TR (hC.tree i hik)
      obtain ⟨x, hx, V, hV, h, hh, rfl⟩ := hC.surj hik hU
      have hhb := hC.fix (by omega) (by omega) hh (Nat.lt_succ_self i)
      have hVb : V (vecOf (B.getD i 0)) = (1 : V12 ≃ₗ[ZMod 2] V12) (vecOf (B.getD i 0)) := by
        have := hf i le_rfl hik
        rw [LinearEquiv.mul_apply, hhb] at this
        exact this
      have h1 : IsP (1 : V12 ≃ₗ[ZMod 2] V12) (look (T.getD i 0) 0) := by rw [h0]; exact IsP.one
      have hx0 := hC.idx_eq hik hx (by omega) hV h1 hVb
      subst hx0
      rw [IsP.inj hV h1, one_mul] at hf ⊢
      exact ih (i + 1) (by omega) h hh fun q hq hqk => hf q (by omega) hqk
  exact key k 0 (by omega) U hU fun q _ hq => hfix q hq

end ChainHyp

end CFSG.KC.IF4C

end
