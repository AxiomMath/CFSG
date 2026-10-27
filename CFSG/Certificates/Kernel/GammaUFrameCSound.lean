module

public import Certificates.Data.Kernel.GammaUFrameCK
public import CFSG.Certificates.Kernel.GammaUNormSound
public import CFSG.Certificates.Kernel.GammaUSigmaSound
public import CFSG.GF2Type.Smith1979.GammaU.StepA2
public import CFSG.Certificates.Kernel.GammaUOrbSound

public section

namespace CFSG.KC.GUF

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.IdxFour

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

@[expose] def FrT (E : Nat → Nat) (Lc : List (Array ℕ)) : Prop :=
  (∀ m < 32, (∃ V : GL, IsP V (E m)) ∧ ∃ g h, E m = mulP g h) ∧
    ∀ l : GL, RowsSet Lc l ↔ ∃ m < 32, IsP l (E m)

theorem rdBit_le (B v b : Nat) : rdBit B v b ≤ b := by
  unfold rdBit
  cases Nat.beq (ap12 B v) v <;> simp

theorem rd_lt (B : Nat) : rd B < 32 := by
  have h1 := rdBit_le B 971 1
  have h2 := rdBit_le B 973 2
  have h3 := rdBit_le B 974 4
  have h4 := rdBit_le B 15 8
  have h5 := rdBit_le B 48 16
  unfold rd
  simp only [Nat.add_eq]
  omega

theorem ltOK_spec {TB i LT : Nat} (h : ltOK TB i LT = true) :
    ∀ m < 32, look LT m = look TB (32 * i + m) ∧ rd (look LT m) = m := by
  intro m hm
  have := (allBelow_iff _ _).1 h m hm
  simp only [Bool.and_eq_true, Nat.beq_eq] at this
  exact this

theorem outL_false {LT B : Nat} (h : outL LT B = false) : B = look LT (rd B) := by
  unfold outL at h
  cases hb : Nat.beq B (look LT (rd B))
  · rw [hb] at h
    exact absurd h (by decide)
  · exact Nat.eq_of_beq_eq_true hb

theorem outL_of_eq {LT B m : Nat} (hrd : rd (look LT m) = m) (hB : B = look LT m) :
    outL LT B = false := by
  subst hB
  unfold outL
  simp [hrd, Nat.beq_refl]

theorem bltT {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem bltF {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
  exact h

theorem eq_of_frT {E : Nat → Nat} {Lc : List (Array ℕ)} (hF : FrT E Lc) {U : GL} {a b : Nat}
    (hU : IsP U (mulP a b)) (hr : RowsSet Lc U) : ∃ m < 32, mulP a b = E m := by
  obtain ⟨m, hm, hUm⟩ := (hF.2 U).1 hr
  obtain ⟨g, h, hgh⟩ := (hF.1 m hm).2
  refine ⟨m, hm, ?_⟩
  rw [hgh] at hUm ⊢
  exact CFSG.KC.GUS.mulP_eq_of_linP fun v => by rw [← hU, ← hUm]

theorem row_of_frT {E : Nat → Nat} {Lc : List (Array ℕ)} (hF : FrT E Lc) {m : Nat} (hm : m < 32) :
    ∃ V : GL, IsP V (E m) ∧ ∃ r ∈ Lc, ∀ x, V x = linOfRows r x := by
  obtain ⟨V, hV⟩ := (hF.1 m hm).1
  exact ⟨V, hV, (hF.2 V).2 ⟨m, hm, hV⟩⟩

theorem frT_congr {E E' : Nat → Nat} {Lc : List (Array ℕ)} (hF : FrT E Lc)
    (hE : ∀ m < 32, E' m = E m) : FrT E' Lc := by
  refine ⟨fun m hm => by rw [hE m hm]; exact hF.1 m hm, fun l => ?_⟩
  rw [hF.2 l]
  exact ⟨fun ⟨m, hm, h⟩ => ⟨m, hm, by rw [hE m hm]; exact h⟩,
    fun ⟨m, hm, h⟩ => ⟨m, hm, by rw [← hE m hm]; exact h⟩⟩

theorem comm_bif {g h : Nat} (H : ∀ v, linP g (linP h v) = linP h (linP g v)) (b : Bool) (v : V12) :
    linP g (linP (bif b then h else idP) v) = linP (bif b then h else idP) (linP g v) := by
  cases b
  · simp only [cond_false, linP_idP]
  · exact H v

theorem comm_subQ {g : Nat} : ∀ {L : List Nat}, (∀ h ∈ L, ∀ v, linP g (linP h v) = linP h (linP g v)) →
    ∀ m v, linP g (linP (subQ L m) v) = linP (subQ L m) (linP g v)
  | [], _, m, v => by rw [subQ_nil, linP_idP, linP_idP]
  | h :: L, H, m, v => by
    rw [subQ_cons, linP_mulP, linP_mulP,
      comm_subQ (fun h' hh' => H h' (List.mem_cons_of_mem h hh')) (m / 2),
      comm_bif (H h List.mem_cons_self)]

theorem linP_subP_subQ : ∀ {L : List Nat}, (∀ g ∈ L, ∀ h ∈ L, ∀ v, linP g (linP h v) = linP h (linP g v)) →
    ∀ m v, linP (CFSG.KC.IF4R.subP L m) v = linP (subQ L m) v
  | [], _, _, _ => rfl
  | g :: L, H, m, v => by
    change linP (mulP (bif Nat.beq (m % 2) 1 then g else idP)
      (CFSG.KC.IF4R.subP L (m / 2))) v = _
    rw [subQ_cons, linP_mulP, linP_mulP,
      linP_subP_subQ (fun a ha b hb => H a (List.mem_cons_of_mem g ha) b (List.mem_cons_of_mem g hb)),
      ← comm_bif (fun w => (comm_subQ (fun h hh => H g List.mem_cons_self h
        (List.mem_cons_of_mem g hh)) (m / 2) w).symm)]

theorem ha0 : vecOf a0 = vecOf 3072 := rfl

theorem shiftLeft_lt {k : Nat} (hk : k < 5) : Nat.shiftLeft 1 k < 32 := by
  interval_cases k <;> decide

theorem d1R_spec {NA NN2 LT PT W Wi : Nat} {hd w : List Nat}
    (h : d1R NA NN2 LT PT W Wi hd w = true) {K : Subgroup GL}
    (hf : ∀ e < Nat.succ NN2, ∃ U ∈ K,
      IsP U (letD NA NN2 (mulP W (mulP (look PT (nthD 0 hd 1)) Wi)) e))
    {Lc H : List (Array ℕ)} (hF : FrT (look LT) Lc) (hLT : ∀ m < 32, rd (look LT m) = m) :
    Viol.Violation K Lc H := by
  unfold d1R d1At at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨-, hk⟩, hw⟩, ⟨hinv, hfix⟩, hout⟩ := h
  obtain ⟨U, hU, hUP⟩ := isP_wordF hf _ hw
  have hUi := hUP.inv (Nat.eq_of_beq_eq_true hinv)
  obtain ⟨L, hL, r, hr, hLr⟩ := row_of_frT hF (shiftLeft_lt hk)
  refine Or.inl ⟨U, hU, ?_, r, hr, ?_⟩
  · rw [ha0, hUP.apply_code, Nat.eq_of_beq_eq_true hfix]
  · rintro ⟨r', hr', hr'v⟩
    have hV : RowsSet Lc (U * (L * U⁻¹)) := ⟨r', hr', fun x => by
      rw [← hr'v, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hLr]⟩
    obtain ⟨m, hm, he⟩ := eq_of_frT hF (hUP.mul (hL.mul hUi)) hV
    rw [outL_of_eq (hLT m hm) he] at hout
    exact absurd hout (by decide)

theorem eqR_spec {TB LT W Wi : Nat} {hd : List Nat} (h : eqR TB LT W Wi hd = true) {Wg : GL}
    (hW : IsP Wg W) (hWi : mulP W Wi = idP) {Li Lc : List (Array ℕ)} (hLi : FrT (look LT) Li)
    (hLc : FrT (fun m => look TB (32 * nthD 0 hd 1 + m)) Lc) :
    Wg (vecOf a0) = vecOf a0 ∧ ∀ l, RowsSet Li l ↔ RowsSet Lc (Wg⁻¹ * l * Wg) := by
  unfold eqR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hfix⟩, hall⟩ := h
  have hWi' := hW.inv hWi
  refine ⟨by rw [ha0, hW.apply_code, Nat.eq_of_beq_eq_true hfix], fun l => ⟨fun hl => ?_, fun hl => ?_⟩⟩
  · obtain ⟨m, hm, hlm⟩ := (hLi.2 l).1 hl
    have he := (allBelow_iff _ _).1 hall m hm
    unfold eqAt at he
    simp only [Bool.and_eq_true] at he
    have hP : IsP (Wg⁻¹ * l * Wg) (mulP Wi (mulP (look LT m) W)) := by
      rw [mul_assoc]
      exact hWi'.mul (hlm.mul hW)
    rw [Nat.eq_of_beq_eq_true he.2] at hP
    exact (hLc.2 _).2 ⟨_, rd_lt _, hP⟩
  · obtain ⟨m, hm, hlm⟩ := (hLc.2 _).1 hl
    have he := (allBelow_iff _ _).1 hall m hm
    unfold eqAt at he
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
    have hP : IsP l (mulP W (mulP (look TB (Nat.add (Nat.mul 32 (nthD 0 hd 1)) m)) Wi)) := by
      have h1 := hW.mul (hlm.mul hWi')
      have h2 : Wg * ((Wg⁻¹ * l * Wg) * Wg⁻¹) = l := by group
      rw [h2] at h1
      exact h1
    rw [outL_false he.1] at hP
    exact (hLi.2 l).2 ⟨_, rd_lt _, hP⟩

theorem notH_spec {LT A : Nat} : ∀ {HM : List Nat}, notH LT A HM = true → ∀ q ∈ HM, A ≠ look LT q
  | [], _, q, hq => absurd hq List.not_mem_nil
  | h :: HM, hn, q, hq => by
    change (!(Nat.beq A (look LT h)) && notH LT A HM) = true at hn
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hn
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Nat.ne_of_beq_eq_false hn.1
    · exact notH_spec hn.2 q hq

theorem mulP_id_id : mulP idP idP = idP := by decide +kernel

theorem ap12_TH {TH : Nat} (hTH : ∀ v, linP TH v = theta0 v) {x : Nat} (hx : x < 4096) :
    ap12 TH x = theta0N x := by
  refine vecOf_inj (ap12_lt _ _) (theta0N_lt hx) ?_
  rw [vecOf_ap12, hTH, vecOf_theta0N hx]

theorem f4I_spec {TH : Nat} (hTH : ∀ v, linP TH v = theta0 v) {x y : Nat} (hx : x < 4096)
    (hy : y < 4096) (h : f4I TH x y = true) : Viol.F4Indep (vecOf x) (vecOf y) := by
  refine Viol.f4Indep_spec hx hy ?_
  unfold f4I at h
  rw [ap12_TH hTH hx] at h
  simp only [not_beq_eq] at h
  exact h

theorem d2uR_spec {TH NA NN2 : Nat} {HM : List Nat} {CG LT W Wi : Nat} {rec : List (List Nat)}
    (h : d2uR TH NA NN2 HM CG LT W Wi rec = true) (hTH : ∀ v, linP TH v = theta0 v)
    {K : Subgroup GL}
    (hf : ∀ e < NN2 + 5, ∃ U ∈ K, IsP U (letU NA NN2 CG W Wi (nthD 0 (nthD [] rec 0) 1) e))
    {Lc H : List (Array ℕ)} (hF : FrT (look LT) Lc) (hHM : ∀ q ∈ HM, q < 32)
    (hH : ∀ r ∈ H, (∀ v, linOfRows r v = v) ∨ ∃ q ∈ HM, ∀ v, linOfRows r v = linP (look LT q) v) :
    Viol.Violation K Lc H := by
  unfold d2uR d2uAt at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨-, ha⟩, hw₁⟩, hw₂⟩, ⟨⟨⟨⟨⟨⟨⟨hu, hne⟩, hnh⟩, hm₁⟩, hm₂⟩, he₁⟩, he₂⟩, hI⟩⟩ := h
  obtain ⟨VA, hVA, r, hr, hVr⟩ := row_of_frT hF ha
  obtain ⟨U₁, hU₁, hP₁⟩ := isP_wordF hf _ hw₁
  obtain ⟨U₂, hU₂, hP₂⟩ := isP_wordF hf _ hw₂
  obtain ⟨g, k, hgk⟩ := (hF.1 _ ha).2
  have hfr : ∀ (U : GL) (u m : Nat), IsP U u → m < 32 →
      mulP (look LT (nthD 0 (nthD [] rec 0) 2)) u = mulP u (look LT m) → Viol.InFrame Lc U r := by
    intro U u m hU hm heq
    obtain ⟨V, hV, r', hr', hVr'⟩ := row_of_frT hF hm
    refine ⟨r', hr', fun x => ?_⟩
    have h1 : VA (U x) = U (V x) := by
      rw [hVA, hU, hU, ← linP_mulP, heq, linP_mulP, ← hV]
    rw [← hVr, h1, inv_apply_apply, hVr']
  refine Or.inr (Or.inl ⟨r, hr, fun x => ?_, fun hrH => ?_, U₁, hU₁, U₂, hU₂,
    hfr _ _ _ hP₁ hm₁ (Nat.eq_of_beq_eq_true he₁), hfr _ _ _ hP₂ hm₂ (Nat.eq_of_beq_eq_true he₂), ?_⟩)
  · rw [← hVr, ← hVr, hVA, hVA]
    exact unitP_spec hTH hu x
  · rcases hH r hrH with hid | ⟨q, hq, hqv⟩
    · have heq : look LT (nthD 0 (nthD [] rec 0) 2) = idP := by
        rw [hgk, ← mulP_id_id]
        refine CFSG.KC.GUS.mulP_eq_of_linP fun v => ?_
        rw [← hgk, ← hVA, hVr, hid, mulP_id_id, linP_idP]
      rw [heq, Nat.beq_refl] at hne
      exact absurd hne (by decide)
    · obtain ⟨g', k', hgk'⟩ := (hF.1 _ (hHM q hq)).2
      have heq : look LT (nthD 0 (nthD [] rec 0) 2) = look LT q := by
        rw [hgk, hgk']
        refine CFSG.KC.GUS.mulP_eq_of_linP fun v => ?_
        rw [← hgk, ← hgk', ← hVA, hVr, hqv]
      exact notH_spec hnh q hq heq
  · rw [ha0, hP₁.apply_code, hP₂.apply_code]
    exact f4I_spec hTH (ap12_lt _ _) (ap12_lt _ _) hI

theorem rec_and {α : Type} {p : α → Bool} : ∀ {l : List α},
    List.rec (motive := fun _ => Bool) true (fun r _ ih => p r && ih) l = true → ∀ r ∈ l, p r = true
  | [], _, r, hr => absurd hr List.not_mem_nil
  | a :: l, h, r, hr => by
    change (p a && List.rec (motive := fun _ => Bool) true (fun r _ ih => p r && ih) l) = true at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h.1
    · exact rec_and h.2 r hr

theorem anyCov_spec {CM : List Nat} {c : Nat} : ∀ {rs : List (List (List Nat))},
    anyCov CM rs c = true → ∃ r ∈ rs, covers CM r c = true
  | [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | r :: rs, h => by
    change (covers CM r c || anyCov CM rs c) = true at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact ⟨r, List.mem_cons_self, h⟩
    · obtain ⟨r', hr', h'⟩ := anyCov_spec h
      exact ⟨r', List.mem_cons_of_mem r hr', h'⟩

theorem pcOK_spec {TB PT : Nat} {CM : List Nat} (h : pcOK TB PT CM = true) {e c : Nat}
    (he : e < 64) (hc : c < 32) (hb : Nat.land (Nat.shiftRight (nthD 0 CM e) c) 1 = 1) :
    look PT e = look TB (32 * c + e % 32) := by
  unfold pcOK at h
  rw [Bool.and_eq_true] at h
  have h1 := (allBelow_iff _ _).1 ((allBelow_iff _ _).1 h.2 e he) c hc
  simp only [Bool.or_eq_true, Nat.beq_eq, hb] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by decide)
  · exact h1

theorem conj_mem {Lc : List (Array ℕ)} {F : Subgroup GL} {Wg : GL}
    (hF : ∀ l, l ∈ F ↔ RowsSet Lc (Wg⁻¹ * l * Wg)) {P : GL} (hP : RowsSet Lc P) :
    Wg * (P * Wg⁻¹) ∈ F := by
  rw [hF]
  have : Wg⁻¹ * (Wg * (P * Wg⁻¹)) * Wg = P := by group
  rw [this]
  exact hP

theorem repAt_spec {TH NA NN2 : Nat} {HM : List Nat} {TB CG LT PT : Nat} {CM : List Nat}
    {W Wi : Nat} {rs : List (List (List Nat))}
    (h : repAt TH NA NN2 HM TB CG LT PT CM W Wi rs = true) (hTH : ∀ v, linP TH v = theta0 v)
    (hpc : pcOK TB PT CM = true) {N : Subgroup GL} (hN : ∀ e < NN2, ∃ U ∈ N, IsP U (look NA e))
    {Wg : GL} (hW : IsP Wg W) {Li : List (Array ℕ)} {Lc : Nat → List (Array ℕ)} {H : List (Array ℕ)}
    (hLi : FrT (look LT) Li) (hLT : ∀ m < 32, rd (look LT m) = m)
    (hLc : ∀ c < 32, FrT (fun m => look TB (32 * c + m)) (Lc c))
    (hCG : ∀ c < 32, ∀ l < 5, ∃ V : GL, IsP V (look CG (5 * c + l)) ∧ RowsSet (Lc c) V)
    (hHM : ∀ q ∈ HM, q < 32)
    (hH : ∀ r ∈ H, (∀ v, linOfRows r v = v) ∨ ∃ q ∈ HM, ∀ v, linOfRows r v = linP (look LT q) v) :
    ∀ c < 32, (Wg (vecOf a0) = vecOf a0 ∧ ∀ l, RowsSet Li l ↔ RowsSet (Lc c) (Wg⁻¹ * l * Wg)) ∨
      ∀ F : Subgroup GL, (∀ l, l ∈ F ↔ RowsSet (Lc c) (Wg⁻¹ * l * Wg)) →
        Viol.Violation (N ⊔ F) Li H := by
  intro c hc
  unfold repAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hinv, hrecs⟩, hcov⟩ := h
  have hWi := Nat.eq_of_beq_eq_true hinv
  have hWi' := hW.inv hWi
  obtain ⟨rc, hrc, hcv⟩ := anyCov_spec ((allBelow_iff _ _).1 hcov c hc)
  have hok := rec_and hrecs rc hrc
  have hNle : ∀ F : Subgroup GL, ∀ e < NN2, ∃ U ∈ N ⊔ F, IsP U (look NA e) := fun F e he => by
    obtain ⟨U, hU, hUP⟩ := hN e he
    exact ⟨U, Subgroup.mem_sup_left hU, hUP⟩
  unfold recOK at hok
  unfold covers at hcv
  cases h0 : Nat.beq (nthD 0 (nthD [] rc 0) 0) 0
  · rw [h0, cond_false] at hok hcv
    have hc' : nthD 0 (nthD [] rc 0) 1 = c := Nat.eq_of_beq_eq_true hcv
    cases h1 : Nat.beq (nthD 0 (nthD [] rc 0) 0) 1
    · rw [h1, cond_false, Bool.and_eq_true] at hok
      refine Or.inr fun F hF => d2uR_spec hok.2 hTH (fun e he => ?_) hLi hHM hH
      unfold letU
      by_cases hlt : e < NN2
      · rw [bltT hlt, cond_true]
        exact hNle F e hlt
      · rw [bltF hlt, cond_false, hc']
        obtain ⟨V, hV, hVr⟩ := hCG c hc (e - NN2) (by omega)
        exact ⟨_, Subgroup.mem_sup_right (conj_mem hF hVr), hW.mul (hV.mul hWi')⟩
    · rw [h1, cond_true] at hok
      exact Or.inl (eqR_spec hok hW hWi hLi (by rw [hc']; exact hLc c hc))
  · rw [h0, cond_true] at hok hcv
    refine Or.inr fun F hF => d1R_spec hok (fun e he => ?_) hLi hLT
    have he64 : nthD 0 (nthD [] rc 0) 1 < 64 := by
      unfold d1R at hok
      simp only [Bool.and_eq_true, Nat.blt_eq] at hok
      exact hok.1.1.1
    unfold letD
    by_cases hlt : e < NN2
    · rw [bltT hlt, cond_true]
      exact hNle F e hlt
    · rw [bltF hlt, cond_false]
      have hpe := pcOK_spec hpc he64 hc (Nat.eq_of_beq_eq_true hcv)
      obtain ⟨V, hV, hVr⟩ := row_of_frT (hLc c hc)
        (Nat.mod_lt (nthD 0 (nthD [] rc 0) 1) (by norm_num : 0 < 32))
      refine ⟨_, Subgroup.mem_sup_right (conj_mem hF hVr), ?_⟩
      rw [hpe]
      exact hW.mul (hV.mul hWi')

theorem repOK_spec {TH NA NN2 : Nat} {HM : List Nat} {TB CG LT PT : Nat} {CM PG : List Nat}
    {DT : Nat} {RP RJ : List Nat} {RW RWi : Nat} {SR : List (List (List (List Nat)))} {r : Nat}
    (h : repOK TH NA NN2 HM TB CG LT PT CM PG DT RP RJ RW RWi SR r = true) :
    nthD 0 RJ r < 108 ∧ nthD 0 RP r < PG.length ∧
      look RW r = mulP (nthD 0 PG (nthD 0 RP r)) (look DT (nthD 0 RJ r)) ∧
      repAt TH NA NN2 HM TB CG LT PT CM (look RW r) (look RWi r) (nthD [] SR r) = true := by
  unfold repOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, lenN_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem n2OK_spec {TH : Nat} {N2 : List Nat} {NA NN : Nat} (h : n2OK TH N2 NA NN = true) :
    N2.length = NN ∧ ∀ q < NN, look NA q = nthD 0 N2 q ∧ guOK TH (look NA q) = true ∧
      mulP (look NA q) (look NA (NN + q)) = idP := by
  unfold n2OK at h
  rw [Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h
  refine ⟨h.1, fun q hq => ?_⟩
  have := (allBelow_iff _ _).1 h.2 q hq
  simp only [Bool.and_eq_true, Nat.beq_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem pgOK_spec {TH : Nat} {PG : List Nat} (h : pgOK TH PG = true) : ∀ g ∈ PG, guOK TH g = true := by
  unfold pgOK at h
  exact rec_and h

theorem wordV_spec {NA n : Nat} {N : Subgroup GL} (hN : ∀ e < n, ∃ U ∈ N, IsP U (look NA e)) :
    ∀ w : List Nat, ltAll n w = true → ∃ M ∈ N, ∀ v, vecOf (wordV NA w v) = M (vecOf v)
  | [], _ => ⟨1, N.one_mem, fun _ => rfl⟩
  | e :: w, hw => by
    rw [ltAll_iff, List.forall_mem_cons] at hw
    obtain ⟨U, hU, hUP⟩ := hN e hw.1
    obtain ⟨M, hM, hMv⟩ := wordV_spec hN w ((ltAll_iff n w).2 hw.2)
    refine ⟨U * M, N.mul_mem hU hM, fun v => ?_⟩
    change vecOf (ap12 (look NA e) (wordV NA w v)) = _
    rw [← hUP.apply_code, hMv]
    rfl

theorem orth_spec : ∀ {ys : List Nat} {zs : List Nat}, orth ys zs = true →
    ∀ y ∈ ys, ∀ z ∈ zs, f0 (vecOf y) (vecOf z) = 0
  | [], _, _, y, hy, _, _ => absurd hy List.not_mem_nil
  | a :: ys, zs, h, y, hy, z, hz => by
    change (List.rec (motive := fun _ => Bool) true
      (fun z _ ih' => Nat.beq (CFSG.KC.GUO.f0k a z) 0 && ih') zs && orth ys zs) = true at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact (CFSG.KC.GUO.f0k_zero_iff _ _).1 (Nat.eq_of_beq_eq_true (rec_and h.1 z hz))
    · exact orth_spec h.2 y hy z hz

theorem cvList_spec {P : Nat → List Nat → Bool} : ∀ (l : List (List Nat)) (j : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun rec _ ih j => P j rec && ih (Nat.succ j)) l j = true →
    ∀ k < l.length, P (j + k) (l.getD k []) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | a :: l, j, h, k, hk => by
    change (P j a && List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun rec _ ih j => P j rec && ih (Nat.succ j)) l (Nat.succ j)) = true at h
    rw [Bool.and_eq_true] at h
    cases k with
    | zero =>
      rw [List.getD_cons_zero, Nat.add_zero]
      exact h.1
    | succ k =>
      have := cvList_spec l (Nat.succ j) h.2 k (by simpa using hk)
      have e : j + (k + 1) = Nat.succ j + k := by omega
      rw [List.getD_cons_succ, e]
      exact this

theorem cvOK_spec {NA NN2 DT : Nat} {RP : List Nat} {RW : Nat} {PG : List Nat}
    {CV : List (List (List Nat))} {p : Nat} (h : cvOK NA NN2 DT RP RW PG CV p = true) :
    ∀ j < 108, ∃ rec : List Nat, nthD 0 rec 0 < RP.length ∧ nthD 0 RP (nthD 0 rec 0) = p ∧
      ltAll NN2 (dropN 1 rec) = true ∧
      cvAt NA (dropN 1 rec) (ap12 (nthD 0 PG p) 3072) (look RW (nthD 0 rec 0)) (nthD 0 PG p)
        (look DT j) = true := by
  intro j hj
  unfold cvOK at h
  rw [Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h
  have hc := cvList_spec (P := fun j rec => cvRec NA NN2 DT RP RW p (nthD 0 PG p) j rec) _ 0 h.2 j
    (by rw [h.1]; exact hj)
  simp only [Nat.zero_add, cvRec, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, lenN_eq] at hc
  exact ⟨_, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

theorem mem_d0 {d : Nat} (hd : d ∈ d0) :
    d = 961 ∨ d = 48 ∨ d = 9 ∨ d = 5 ∨ d = 3 ∨ d = 3072 := by
  simpa [d0] using hd

theorem f0_span_left {S : Set V12} {g : GL} (hg : g ∈ gammaU) {z : V12}
    (h : ∀ s ∈ S, f0 (g s) z = 0) : ∀ y ∈ Submodule.span (ZMod 2) S, f0 (g y) z = 0 := by
  intro y hy
  have e : ∀ x, f0 (g x) z = f0 x (g⁻¹ z) := fun x => by
    rw [← CFSG.KC.GUO.f0_map hg x (g⁻¹ z), apply_inv_apply]
  rw [e]
  exact CFSG.KC.GUO.perp_span_of (fun s hs => by rw [← e]; exact h s hs) y hy

theorem cvAt_spec {NA : Nat} {w : List Nat} {x R G T : Nat} (h : cvAt NA w x R G T = true)
    {N : Subgroup GL} {n : Nat} (hN : ∀ e < n, ∃ U ∈ N, IsP U (look NA e)) (hw : ltAll n w = true)
    (hNg : N ≤ gammaU) {Rg A : GL} (hR : IsP Rg R) (hA : ∀ v, A v = linP G (linP T v))
    (hRg : Rg ∈ gammaU) (hAg : A ∈ gammaU)
    (hD0 : (∀ y ∈ spanOf d0, q0 y = 0) ∧ Module.finrank (ZMod 2) (spanOf d0) = 6) :
    ∃ M ∈ N, M (vecOf x) = vecOf x ∧
      (spanOf d0).map (A : V12 →ₗ[ZMod 2] V12) =
        ((spanOf d0).map (Rg : V12 →ₗ[ZMod 2] V12)).map (M : V12 →ₗ[ZMod 2] V12) := by
  unfold cvAt at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hfix, hor⟩ := h
  obtain ⟨M, hM, hMv⟩ := wordV_spec hN w hw
  refine ⟨M, hM, by rw [← hMv, Nat.eq_of_beq_eq_true hfix], ?_⟩
  have hMR : M * Rg ∈ gammaU := mul_mem (hNg hM) hRg
  have h36 : ∀ d ∈ d0, ∀ d' ∈ d0, f0 ((M * Rg) (vecOf d)) (A (vecOf d')) = 0 := by
    intro d hd d' hd'
    have hy : wordV NA w (ap12 R d) ∈ imW NA w R := by
      rcases mem_d0 hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [imW]
    have hz : ap12 G (ap12 T d') ∈ imG G T := by
      rcases mem_d0 hd' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [imG]
    have e := orth_spec hor _ hy _ hz
    rw [hMv, ← hR.apply_code, vecOf_ap12, vecOf_ap12] at e
    rw [LinearEquiv.mul_apply, hA]
    exact e
  rw [CFSG.KC.GUO.map_mul_eq]
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by
    rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq])
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap]
  have hy' : ∀ d' ∈ d0, f0 ((M * Rg) y) (A (vecOf d')) = 0 := fun d' hd' =>
    f0_span_left hMR (by rintro _ ⟨d, hd, rfl⟩; exact h36 d hd d' hd') y hy
  refine Submodule.mem_map.2 ⟨A⁻¹ ((M * Rg) y), ?_, apply_inv_apply A _⟩
  rw [← CFSG.KC.GUO.perp_eq hD0.1 hD0.2]
  refine CFSG.KC.GUO.mem_perp.2 (CFSG.KC.GUO.perp_span_of ?_)
  rintro _ ⟨d', hd', rfl⟩
  rw [← CFSG.KC.GUO.f0_map hAg, apply_inv_apply, FLCheck.f0_comm]
  exact hy' d' hd'

theorem ptMask_spec : ∀ {PG : List Nat} {n : Nat}, (ptMask PG).testBit n = true →
    ∃ g ∈ PG, ap12 g 3072 = n
  | [], n, h => by
    change (0 : Nat).testBit n = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | g :: PG, n, h => by
    change (Nat.lor (Nat.shiftLeft 1 (ap12 g 3072)) (ptMask PG)).testBit n = true at h
    simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.testBit_or, Nat.shiftLeft_eq, one_mul,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨g, List.mem_cons_self, h⟩
    · obtain ⟨g', hg', e⟩ := ptMask_spec h
      exact ⟨g', List.mem_cons_of_mem g hg', e⟩

theorem treeN_spec {NA NN SM : Nat} {N : Subgroup GL} (hN : ∀ l < NN, ∃ U ∈ N, IsP U (look NA l))
    {S : V12 → Prop} (hS : ∀ U ∈ N, ∀ x, S x → S (U x)) :
    ∀ (es : List (List Nat)) (mask : Nat), treeN NA NN SM es mask = true →
      (∀ n, mask.testBit n = true → S (vecOf n)) → ∀ n, SM.testBit n = true → S (vecOf n)
  | [], mask, h, hm => by
    have e : mask = SM := Nat.eq_of_beq_eq_true h
    rw [← e]
    exact hm
  | e :: es, mask, h, hm => by
    have h' : (Nat.blt (nthD 0 e 1) NN &&
        Nat.beq (Nat.land (Nat.shiftRight mask (nthD 0 e 2)) 1) 1 &&
        Nat.beq (ap12 (look NA (nthD 0 e 1)) (nthD 0 e 2)) (nthD 0 e 0) &&
        treeN NA NN SM es (Nat.lor mask (Nat.shiftLeft 1 (nthD 0 e 0)))) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨⟨⟨hl, hp⟩, hap⟩, hrest⟩ := h'
    refine treeN_spec hN hS es _ hrest fun n hn => ?_
    simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.testBit_or, Nat.shiftLeft_eq, one_mul,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hn
    rcases hn with hn | rfl
    · exact hm n hn
    · obtain ⟨U, hU, hUP⟩ := hN _ hl
      have := hS U hU _ (hm _ (CFSG.KC.GUO.testBit_of_land hp))
      rw [hUP.apply_code, hap] at this
      exact this

end CFSG.KC.GUF

end
