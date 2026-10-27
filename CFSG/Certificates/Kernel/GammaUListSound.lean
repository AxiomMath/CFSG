module

public import Certificates.Data.Kernel.GammaUList
public import CFSG.GF2Type.Smith1979.GammaU.ResConjInputs
public import CFSG.GF2Type.Smith1979.GammaU.NativeBridge
public import CFSG.GF2Type.Smith1979.IdxFourIdentFLCheck

public section

namespace Certificates.Kernel.GammaUList

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
  CFSG.GF2Type.Smith1979.IdxFour

theorem appL_eq_fl : appL = FLCheck.appL := by
  funext l n
  induction l generalizing n with
  | nil => rfl
  | cons r l ih =>
    change Nat.xor (Nat.mul (Nat.mod n 2) r) (appL l (Nat.div n 2)) =
      Nat.xor (Nat.mul (Nat.mod n 2) r) (FLCheck.appL l (Nat.div n 2))
    rw [ih]

theorem mulL_eq_fl : mulL = FLCheck.mulL := by
  funext g h
  simp only [mulL, FLCheck.mulL, appL_eq_fl]

theorem appL_lt {l : List ℕ} (hb : ∀ x ∈ l, x < 4096) (n : ℕ) : appL l n < 4096 := by
  induction l generalizing n with
  | nil => exact Nat.zero_lt_succ _
  | cons r l ih =>
    change Nat.xor (Nat.mul (Nat.mod n 2) r) (appL l (Nat.div n 2)) < 4096
    have hr : n % 2 * r < 2 ^ 12 := by
      have := hb r List.mem_cons_self
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
    exact Nat.xor_lt_two_pow hr (ih (fun x hx => hb x (List.mem_cons_of_mem r hx)) _)

theorem appN_eq {g : Array ℕ} (hl : g.toList.length = 12) (hb : ∀ x ∈ g.toList, x < 4096)
    (n : ℕ) : CFSG.GammaU.Native.appN g n = appL g.toList n := by
  refine vecOf_inj (appN_lt (fun x hx => hb x (Array.mem_toList_iff.2 hx)) n) (appL_lt hb n) ?_
  rw [native_appN, vecOf_appN, appL_eq_fl, FLCheck.appL_spec hl, Array.toArray_toList]

theorem mulR_toList {g : Array ℕ} (hl : g.toList.length = 12) (hb : ∀ x ∈ g.toList, x < 4096)
    (h : Array ℕ) : (CFSG.GammaU.Native.mulR g h).toList = mulL g.toList h.toList := by
  simp only [CFSG.GammaU.Native.mulR, Array.toList_map, mulL]
  exact List.map_congr_left fun n _ => appN_eq hl hb n

theorem mulL_lt {g : List ℕ} (hb : ∀ x ∈ g, x < 4096) (h : List ℕ) :
    ∀ x ∈ mulL g h, x < 4096 := by
  intro x hx
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
  exact appL_lt hb n

theorem beq_toList (a b : Array ℕ) : (a == b) = (a.toList == b.toList) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]

theorem contains_toList (C : List (Array ℕ)) (x : Array ℕ) :
    C.contains x = (C.map Array.toList).contains x.toList := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => Array.toList_inj.1 hyx ▸ hy⟩

theorem idR_toList : CFSG.GammaU.Native.idR.toList = idL := rfl

theorem isoN_of_isoB {r : Array ℕ} (h : isoB r.toList = true) :
    CFSG.GammaU.Native.isoN r = true := by
  simp only [isoB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨hl, hb⟩, hq⟩, hf⟩ := h
  rw [native_q0b] at hq
  rw [native_f0b] at hf
  have hget : ∀ j, r[j]! = r.toList[j]! := fun j => by
    rw [← List.getElem!_toArray, Array.toArray_toList]
  have hqv : ∀ j : Fin 12, q0 (vecOf r[(j : ℕ)]!) = q0 (vecOf (2 ^ (j : ℕ))) := fun j => by
    rw [q0_vecOf, q0_vecOf, hget, hq j j.isLt]
  have hfv : ∀ j k : Fin 12, f0 (vecOf r[(j : ℕ)]!) (vecOf r[(k : ℕ)]!) =
      f0 (vecOf (2 ^ (j : ℕ))) (vecOf (2 ^ (k : ℕ))) := fun j k => by
    rw [f0_vecOf, f0_vecOf, hget, hget, hf j j.isLt k k.isLt]
  have hb' : ∀ x ∈ r, x < 4096 := fun x hx => hb x (Array.mem_toList_iff.2 hx)
  simp only [native_isoN, isoN, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨by rw [← Array.length_toList, hl], ?_⟩, fun n hn => ?_⟩
  · rw [← Array.all_toList, List.all_eq_true]
    exact fun x hx => decide_eq_true (hb x hx)
  · have hv := FLCheck.q0_linOfRows hqv hfv (vecOf n)
    rw [← vecOf_appN, q0_vecOf, q0_vecOf] at hv
    revert hv
    cases q0b (appN r n) <;> cases q0b n <;> decide

theorem unitaryN_eq {g : Array ℕ} (hl : g.toList.length = 12) (hb : ∀ x ∈ g.toList, x < 4096) :
    CFSG.GammaU.Native.unitaryN g = unitaryL g.toList := by
  simp only [CFSG.GammaU.Native.unitaryN, unitaryL, appN_eq hl hb]

theorem antiN_eq {g : Array ℕ} (hl : g.toList.length = 12) (hb : ∀ x ∈ g.toList, x < 4096) :
    CFSG.GammaU.Native.antiN g = antiL g.toList := by
  simp only [CFSG.GammaU.Native.antiN, antiL, appN_eq hl hb]

theorem isoB_rows {l : List ℕ} (h : isoB l = true) : l.length = 12 ∧ ∀ x ∈ l, x < 4096 := by
  simp only [isoB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem gammaUN_of {g : Array ℕ} (h : gammaUL g.toList = true) :
    CFSG.GammaU.Native.gammaUN g = true := by
  simp only [gammaUL, Bool.and_eq_true] at h
  obtain ⟨hl, hb⟩ := isoB_rows h.1
  rw [CFSG.GammaU.Native.gammaUN, isoN_of_isoB h.1, unitaryN_eq hl hb, antiN_eq hl hb, h.2,
    Bool.true_and]

theorem nlOKAt_of (S : List ℕ) (C : List (Array ℕ)) (W : List (Array ℕ × Array ℕ))
    (hC : ∀ x ∈ C, x.toList.length = 12)
    (h : nlOKAtL S (C.map Array.toList) (W.map fun p => (p.1.toList, p.2.toList)) = true) :
    CFSG.GammaU.Native.nlOKAt S C W = true := by
  simp only [nlOKAtL, List.all_map, List.all_eq_true] at h
  simp only [CFSG.GammaU.Native.nlOKAt, List.all_eq_true]
  rintro ⟨g, gi⟩ hp
  have hgp := h (g, gi) hp
  simp only [Function.comp_apply, Bool.and_eq_true] at hgp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, hgi⟩, hm1⟩, hm2⟩, ha⟩, hd⟩, hdi⟩, hc⟩, hci⟩ := hgp
  have ⟨hgl, hgb⟩ := isoB_rows (l := g.toList)
    (by simp only [gammaUL, Bool.and_eq_true] at hg; exact hg.1)
  have ⟨hil, hib⟩ := isoB_rows (l := gi.toList)
    (by simp only [gammaUL, Bool.and_eq_true] at hgi; exact hgi.1)
  have conj : ∀ {a b : Array ℕ}, a.toList.length = 12 → (∀ x ∈ a.toList, x < 4096) →
      b.toList.length = 12 → (∀ x ∈ b.toList, x < 4096) →
      (∀ x, x ∈ C.map Array.toList → (C.map Array.toList).contains
        (mulL (mulL a.toList x) b.toList) = true) →
      ∀ x ∈ C, C.contains (CFSG.GammaU.Native.mulR (CFSG.GammaU.Native.mulR a x) b) = true := by
    intro a b hal hab hbl hbb hall x hx
    have hax : (CFSG.GammaU.Native.mulR a x).toList = mulL a.toList x.toList := mulR_toList hal hab x
    have haxl : (CFSG.GammaU.Native.mulR a x).toList.length = 12 := by
      rw [hax, mulL, List.length_map, hC x hx]
    have haxb : ∀ y ∈ (CFSG.GammaU.Native.mulR a x).toList, y < 4096 := by
      rw [hax]; exact mulL_lt hab _
    rw [contains_toList, mulR_toList haxl haxb, hax]
    exact hall _ (List.mem_map_of_mem hx)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨gammaUN_of hg, gammaUN_of hgi⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Array.toList_inj, mulR_toList hgl hgb, idR_toList]
    exact beq_iff_eq.1 hm1
  · rw [← Array.toList_inj, mulR_toList hil hib, idR_toList]
    exact beq_iff_eq.1 hm2
  · rw [appN_eq hgl hgb]
    exact beq_iff_eq.1 ha
  · intro d hd'
    rw [appN_eq hgl hgb]
    exact List.all_eq_true.1 hd d hd'
  · intro d hd'
    rw [appN_eq hil hib]
    exact List.all_eq_true.1 hdi d hd'
  · exact conj hgl hgb hil hib (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact List.all_eq_true.1 hc y hy)
  · exact conj hil hib hgl hgb (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact List.all_eq_true.1 hci y hy)

theorem idL_getElem (j : ℕ) (hj : j < 12) : idL[j]! = 2 ^ j := by
  revert j
  decide

theorem invR_eq {c r : List ℕ} (h : invOK c r = true) :
    CFSG.GammaU.Native.invR c.toArray = r.toArray := by
  simp only [invOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hcl, hcb⟩, hrl⟩, hrb⟩, hcr⟩, hrc⟩ := h
  have hleft : ∀ n, vecOf (appL r (appL c n)) = vecOf n := fun n => by
    have h1 := FLCheck.mulL_spec hrl c (vecOf n)
    rw [← mulL_eq_fl, hrc] at h1
    rw [appL_eq_fl, FLCheck.appL_spec hrl, FLCheck.appL_spec hcl, ← h1]
    exact linOfRows_idR (vecOf n)
  have hrow : ∀ j, j < 12 → appL c r[j]! = 2 ^ j := fun j hj => by
    have : (mulL c r)[j]! = idL[j]! := by rw [hcr]
    rw [mulL_eq_fl, FLCheck.getElem!_mulL, ← appL_eq_fl, idL_getElem j hj] at this
    exact this
  have hrlt : ∀ j, j < 12 → r[j]! < 4096 := fun j hj => by
    rw [getElem!_pos r j (by omega)]
    exact hrb _ (List.getElem_mem _)
  have hcN : ∀ n, CFSG.GammaU.Native.appN c.toArray n = appL c n := fun n =>
    appN_eq (by simpa using hcl) (by simpa using hcb) n
  have hfind : ∀ j, j < 12 →
      (List.range 4096).find? (fun n => CFSG.GammaU.Native.appN c.toArray n == 2 ^ j) =
        some r[j]! := fun j hj => by
    rw [List.find?_range_eq_some]
    refine ⟨by rw [hcN, hrow j hj, beq_self_eq_true], List.mem_range.2 (hrlt j hj), ?_⟩
    intro m hm
    rw [Bool.not_eq_true', beq_eq_false_iff_ne, hcN]
    intro hmj
    have h2 := hleft m
    rw [hmj, ← hrow j hj, hleft] at h2
    exact absurd (vecOf_inj (lt_trans hm (hrlt j hj)) (hrlt j hj) h2.symm) (by omega)
  rw [CFSG.GammaU.Native.invR]
  refine congrArg List.toArray
    (List.ext_getElem (by rw [List.length_map, List.length_range, hrl]) fun j hj _ => ?_)
  rw [List.length_map, List.length_range] at hj
  rw [List.getElem_map, List.getElem_range, hfind j hj, Option.getD_some,
    getElem!_pos r j (by omega)]

theorem k0_rows : CFSG.GammaU.Native.k0.toList.length = 12 ∧
    ∀ x ∈ CFSG.GammaU.Native.k0.toList, x < 4096 := by decide +kernel

theorem cBasis_rows : ∀ i < 5, CFSG.GammaU.Native.cBasis[i]!.toList.length = 12 ∧
    ∀ x ∈ CFSG.GammaU.Native.cBasis[i]!.toList, x < 4096 := by decide +kernel

theorem subsetProducts_toList (gens : List (Array ℕ))
    (hg : ∀ g ∈ gens, g.toList.length = 12 ∧ ∀ x ∈ g.toList, x < 4096) :
    (CFSG.GammaU.Native.subsetProducts gens).map Array.toList =
      subsetProductsL (gens.map Array.toList) := by
  unfold CFSG.GammaU.Native.subsetProducts subsetProductsL
  rw [show [idL] = [CFSG.GammaU.Native.idR].map Array.toList from rfl]
  generalize [CFSG.GammaU.Native.idR] = acc
  induction gens generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have ⟨hl, hb⟩ := hg g List.mem_cons_self
    rw [List.foldl_cons, List.map_cons, List.foldl_cons,
      ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg')), List.map_append, List.map_map,
      List.map_map]
    congr 2
    exact List.map_congr_left fun a _ => mulR_toList hl hb a

theorem compOf_toList (c : ℕ) :
    (CFSG.GammaU.Native.compOf c).map Array.toList = compOfL c := by
  unfold CFSG.GammaU.Native.compOf compOfL
  rw [subsetProducts_toList, List.map_map]
  · congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi5 := List.mem_range.1 hi
    simp only [Function.comp_apply]
    split
    · exact mulR_toList k0_rows.1 k0_rows.2 _
    · rfl
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi5 := List.mem_range.1 hi
    obtain ⟨hl, hb⟩ := cBasis_rows i hi5
    split
    · refine ⟨?_, ?_⟩
      · rw [mulR_toList k0_rows.1 k0_rows.2, mulL, List.length_map, hl]
      · rw [mulR_toList k0_rows.1 k0_rows.2]
        exact mulL_lt k0_rows.2 _
    · exact ⟨hl, hb⟩

theorem resConjCheck_of (h : resConjCheckL = true) : resConjCheck () = true := by
  simp only [resConjCheckL, List.all_eq_true, Bool.and_eq_true] at h
  simp only [resConjCheck, List.all_eq_true]
  intro i hi
  obtain ⟨⟨hinv, hlen⟩, hnl⟩ := h i hi
  have hW : ((CFSG.GammaU.Native.resConj i).map fun c => (c, CFSG.GammaU.Native.invR c)) =
      (CFSG.GammaU.Native.resConj i).map fun c => (c, (invL c.toList).toArray) := by
    refine List.map_congr_left fun c hc => ?_
    have := invR_eq (hinv c.toList (List.mem_map_of_mem hc))
    rw [Array.toArray_toList] at this
    rw [this]
  rw [hW]
  refine nlOKAt_of _ _ _ (fun x hx => ?_) ?_
  · rw [← compOf_toList] at hlen
    exact beq_iff_eq.1 (hlen _ (List.mem_map_of_mem hx))
  · rw [compOf_toList, List.map_map]
    convert hnl using 2
    rw [List.map_map]
    rfl

end Certificates.Kernel.GammaUList
