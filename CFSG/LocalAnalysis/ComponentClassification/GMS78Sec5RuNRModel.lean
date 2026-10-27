module

public import Certificates.Certificate15109
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAct

public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN
open CFSG.ComponentClassification.GMS78.RuSimCode CFSG.CosetTable
open CFSG.ComponentClassification.GMS78.RuPi7 CFSG.ComponentClassification.GMS78.RuAsm

local instance : Std.Associative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

local instance : Std.Commutative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

theorem ite_fxor (b : Bool) (x y : Fin 8) :
    (if b = true then x ^^^ y else 0) =
      (if b = true then x else 0) ^^^ (if b = true then y else 0) := by
  cases b <;> simp

theorem xs8_xor (c c' : Nat) (f : Nat → Fin 8) : xs8 (c ^^^ c') f = xs8 c f ^^^ xs8 c' f := by
  simp only [xs8, Nat.testBit_xor, ite_xor]
  ac_rfl

theorem xs8_fun_xor (c : Nat) (f g : Nat → Fin 8) :
    xs8 c (fun i => f i ^^^ g i) = xs8 c f ^^^ xs8 c g := by
  simp only [xs8, ite_fxor]
  ac_rfl

theorem xs8_zero (f : Nat → Fin 8) : xs8 0 f = 0 := by
  simp [xs8]

theorem xs8_fun_zero (c : Nat) : xs8 c (fun _ => 0) = 0 := by
  simp [xs8]

theorem xs8_congr (c : Nat) {f g : Nat → Fin 8} (h : ∀ i < 8, f i = g i) : xs8 c f = xs8 c g := by
  simp only [xs8, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem maskApply_zero (cols : List Nat) : maskApply cols 0 = 0 := by
  simp [maskApply, sel]

theorem nCo_xor (m n : Nat) : nCo (m ^^^ n) = nCo m ^^^ nCo n := maskApply_xor _ _ _

theorem nCo_zero : nCo 0 = 0 := maskApply_zero _

theorem nBeta_xor_left (m m' n : Nat) : nBeta (m ^^^ m') n = nBeta m n ^^^ nBeta m' n := by
  simp only [nBeta, nCo_xor, xs8_xor]

theorem nBeta_xor_right (m n n' : Nat) : nBeta m (n ^^^ n') = nBeta m n ^^^ nBeta m n' := by
  simp only [nBeta, nCo_xor, xs8_xor, xs8_fun_xor]

theorem nBeta_zero_left (n : Nat) : nBeta 0 n = 0 := by
  simp only [nBeta, nCo_zero, xs8_zero]

theorem nBeta_zero_right (m : Nat) : nBeta m 0 = 0 := by
  simp only [nBeta, nCo_zero, xs8_zero, xs8_fun_zero]

theorem nAd_xor (r : Lin8) (m n : Nat) : nAd r (m ^^^ n) = nAd r m ^^^ nAd r n :=
  maskApply_xor _ _ _

theorem nAd_zero (r : Lin8) : nAd r 0 = 0 := maskApply_zero _

theorem nAd_lt (r : Lin8) (m : Nat) : nAd r m < 256 := maskApply_lt (adMat_lt r) m

theorem nGam_xor_left (r : Lin8) (m m' n : Nat) :
    nGam r (m ^^^ m') n = nGam r m n ^^^ nGam r m' n := by
  simp only [nGam, nAd_xor, nBeta_xor_left, linApply_xor]
  ac_rfl

theorem nGam_xor_right (r : Lin8) (m n n' : Nat) :
    nGam r m (n ^^^ n') = nGam r m n ^^^ nGam r m n' := by
  simp only [nGam, nAd_xor, nBeta_xor_right, linApply_xor]
  ac_rfl

theorem nGam_zero_right (r : Lin8) (m : Nat) : nGam r m 0 = 0 := by
  simp only [nGam, nAd_zero, nBeta_zero_right, linApply_zero, fin8_xor_zero]

theorem nTau_zero (r : Lin8) : nTau r 0 = 0 := by
  simp only [nTau, nQuad, nCo_zero, xs8_zero, fin8_xor_zero]

theorem fin256_val_xor (a b : Fin 256) : (a ^^^ b).val = a.val ^^^ b.val := by
  rw [Fin.xor_val, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt)]

@[ext] structure RuR where
  m : Fin 256
  t : Fin 8
  deriving DecidableEq, Fintype

instance : Group RuR where
  mul x y := ⟨x.m ^^^ y.m, x.t ^^^ y.t ^^^ nBeta x.m.val y.m.val⟩
  one := ⟨0, 0⟩
  inv x := ⟨x.m, x.t ^^^ nBeta x.m.val x.m.val⟩
  mul_assoc x y z := by
    refine RuR.ext (Fin.ext ?_) ?_
    · change ((x.m ^^^ y.m) ^^^ z.m).val = (x.m ^^^ (y.m ^^^ z.m)).val
      simp only [fin256_val_xor, Nat.xor_assoc]
    · change (x.t ^^^ y.t ^^^ nBeta x.m.val y.m.val) ^^^ z.t ^^^ nBeta (x.m ^^^ y.m).val z.m.val =
        x.t ^^^ (y.t ^^^ z.t ^^^ nBeta y.m.val z.m.val) ^^^ nBeta x.m.val (y.m ^^^ z.m).val
      simp only [fin256_val_xor, nBeta_xor_left, nBeta_xor_right]
      ac_rfl
  one_mul x := by
    refine RuR.ext (Fin.ext ?_) ?_
    · change ((0 : Fin 256) ^^^ x.m).val = x.m.val
      simp
    · change (0 : Fin 8) ^^^ x.t ^^^ nBeta (0 : Fin 256).val x.m.val = x.t
      simp [nBeta_zero_left, fin8_zero_xor]
  mul_one x := by
    refine RuR.ext (Fin.ext ?_) ?_
    · change (x.m ^^^ (0 : Fin 256)).val = x.m.val
      simp
    · change x.t ^^^ (0 : Fin 8) ^^^ nBeta x.m.val (0 : Fin 256).val = x.t
      simp [nBeta_zero_right]
  inv_mul_cancel x := by
    refine RuR.ext (Fin.ext ?_) ?_
    · change (x.m ^^^ x.m).val = (0 : Fin 256).val
      simp
    · change x.t ^^^ nBeta x.m.val x.m.val ^^^ x.t ^^^ nBeta x.m.val x.m.val = 0
      have h : ∀ a b : Fin 8, a ^^^ b ^^^ a ^^^ b = 0 := by decide
      exact h _ _

theorem RuR.mul_def (x y : RuR) :
    x * y = ⟨x.m ^^^ y.m, x.t ^^^ y.t ^^^ nBeta x.m.val y.m.val⟩ := rfl

theorem RuR.one_def : (1 : RuR) = ⟨0, 0⟩ := rfl

@[expose] def RuR.equivProd : RuR ≃ Fin 256 × Fin 8 :=
  ⟨fun x => (x.m, x.t), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem card_RuR : Nat.card RuR = 2048 := by
  rw [Nat.card_congr RuR.equivProd, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def nAut (r : Lin8) (x : RuR) : RuR :=
  ⟨⟨nAd r x.m.val, nAd_lt r _⟩, linApply r x.t ^^^ nTau r x.m.val⟩

theorem getElem!_ofFn {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (h : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using h)]
  simp

theorem nB_lt {j : Nat} (hj : j < 8) : nB j < 256 := by
  interval_cases j <;> decide

theorem nCoArr_get {m : Nat} (hm : m < 256) : nCoArr[m]! = nCo m := by
  rw [nCoArr, getElem!_ofFn _ hm]

theorem nRowArr_get {j n : Nat} (hj : j < 8) (hn : n < 256) :
    nRowArr[256 * j + n]! = xs8 (nCo n) (nBT j) := by
  rw [nRowArr, getElem!_ofFn _ (by omega)]
  have h1 : (256 * j + n) % 256 = n := by omega
  have h2 : (256 * j + n) / 256 = j := by omega
  simp only [h1, h2, nCoArr_get hn]

theorem nBetaF_eq {m n : Nat} (hm : m < 256) (hn : n < 256) : nBetaF m n = nBeta m n := by
  rw [nBetaF, nCoArr_get hm, nBeta]
  exact xs8_congr _ fun j hj => nRowArr_get hj hn

theorem nBetaArr_get {m n : Nat} (hm : m < 256) (hn : n < 256) :
    nBetaArr[m * 256 + n]! = nBeta m n := by
  rw [nBetaArr, getElem!_ofFn _ (by omega)]
  have h1 : (m * 256 + n) % 256 = n := by omega
  have h2 : (m * 256 + n) / 256 = m := by omega
  simp only [h1, h2]
  exact nBetaF_eq hm hn

theorem nAdArr_get (r : Lin8) {m : Nat} (hm : m < 256) : (nAdArr r)[m]! = nAd r m := by
  rw [nAdArr, getElem!_ofFn _ hm, nAd]

theorem nCode_nIdx (r : Lin8) : nCode (nIdx r) = r := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := r
  simp only [nCode, nIdx]
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> simp <;> omega

theorem nIdx_lt (r : Lin8) : nIdx r < 512 := by
  have h1 := r.1.isLt
  have h2 := r.2.1.isLt
  have h3 := r.2.2.isLt
  simp only [nIdx]
  omega

theorem nAdTab_get {r : Lin8} (hr : r ∈ glList) : nAdTab[nIdx r]! = nAdArr r := by
  rw [nAdTab, getElem!_ofFn _ (nIdx_lt r)]
  simp only [nCode_nIdx, mem_glList.mp hr, ↓reduceIte]

theorem nGamBArr_get {r : Lin8} {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (nGamBArr r (nAdArr r))[8 * i + j]! = nGam r (nB i) (nB j) := by
  rw [nGamBArr, getElem!_ofFn _ (by omega)]
  have h1 : (8 * i + j) % 8 = j := by omega
  have h2 : (8 * i + j) / 8 = i := by omega
  simp only [h1, h2, nAdArr_get r (nB_lt hi), nAdArr_get r (nB_lt hj),
    nBetaArr_get (nAd_lt r _) (nAd_lt r _), nBetaArr_get (nB_lt hi) (nB_lt hj), nGam]

theorem nTauTab_get {r : Lin8} (hr : r ∈ glList) {m : Nat} (hm : m < 256) :
    (nTauTab[nIdx r]!)[m]! = nTau r m := by
  rw [nTauTab, getElem!_ofFn _ (nIdx_lt r)]
  simp only [nCode_nIdx, mem_glList.mp hr, ↓reduceIte, nAdTab_get hr]
  have h : (xs8 (nCo m) fun j => xs8 (nCo m) fun i =>
      if i < j then (nGamBArr r (nAdArr r))[8 * i + j]! else 0) = nQuad r m := by
    rw [nQuad]
    refine xs8_congr _ fun j hj => xs8_congr _ fun i hi => ?_
    split_ifs
    · exact nGamBArr_get hi hj
    · rfl
  simp only [nTauArrW, getElem!_ofFn _ hm, nCoArr_get hm]
  rw [h, nTau]

theorem maskApply_two_pow (cols : List Nat) {k : Nat} (hk : k < 8) :
    maskApply cols (2 ^ k) = cols.getD k 0 := by
  simp only [maskApply, sel, Nat.testBit_two_pow]
  interval_cases k <;> simp

theorem sel_map {f : Nat → Nat} (hf0 : f 0 = 0) (m k c : Nat) : f (sel m k c) = sel m k (f c) := by
  unfold sel
  split_ifs <;> simp [hf0]

theorem getD_map_zero {f : Nat → Nat} (hf0 : f 0 = 0) (l : List Nat) (k : Nat) :
    (l.map f).getD k 0 = f (l.getD k 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> simp [hf0]

theorem maskApply_map {f : Nat → Nat} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (hf0 : f 0 = 0)
    (cols : List Nat) (m : Nat) : f (maskApply cols m) = maskApply (cols.map f) m := by
  simp only [maskApply, hf, sel_map hf0, getD_map_zero hf0]

theorem nAut_m (r : Lin8) (x : RuR) : (nAut r x).m.val = nAd r x.m.val := rfl

theorem nAut_t (r : Lin8) (x : RuR) : (nAut r x).t = linApply r x.t ^^^ nTau r x.m.val := rfl

theorem fin8_cancel (a b c d e f : Fin 8) :
    a ^^^ b ^^^ c ^^^ (d ^^^ e ^^^ (f ^^^ c)) = a ^^^ d ^^^ (b ^^^ e) ^^^ f := by
  calc a ^^^ b ^^^ c ^^^ (d ^^^ e ^^^ (f ^^^ c)) = (a ^^^ d ^^^ (b ^^^ e) ^^^ f) ^^^ (c ^^^ c) := by
        ac_rfl
    _ = a ^^^ d ^^^ (b ^^^ e) ^^^ f := by rw [fin8_xor_self, fin8_xor_zero]

theorem linApply_linId (t : Fin 8) : linApply linId t = t := by
  revert t
  decide

theorem linId_mem : linId ∈ glList := by decide

theorem nAut_A1 (r : Lin8) (t : Fin 8) : nAut r ⟨0, t⟩ = ⟨0, linApply r t⟩ := by
  refine RuR.ext (Fin.ext ?_) ?_
  · rw [nAut_m]
    exact nAd_zero r
  · rw [nAut_t]
    change linApply r t ^^^ nTau r 0 = linApply r t
    rw [nTau_zero, fin8_xor_zero]

theorem eq_of_nAut_eq {r s : Lin8} (h : ∀ x, nAut r x = nAut s x) : r = s := by
  have e : ∀ t : Fin 8, linApply r t = linApply s t := fun t => by
    have := congrArg RuR.t (h ⟨0, t⟩)
    rwa [nAut_A1, nAut_A1] at this
  have e1 := e 1
  have e2 := e 2
  have e4 := e 4
  rw [linApply_one, linApply_one] at e1
  rw [linApply_two, linApply_two] at e2
  rw [linApply_four, linApply_four] at e4
  exact Prod.ext e1 (Prod.ext e2 e4)

section Cert


theorem nIdCheck_parts :
    (∀ m < 256, nAd linId m = m ∧ nTau linId m = 0 ∧ maskApply nBasis (nCo m) = m) ∧
    (∀ r ∈ glList, linInv r ∈ glList ∧ linComp (linInv r) r = linId ∧
      linComp r (linInv r) = linId) ∧
    ∀ r ∈ glList, ∀ s ∈ glList, linComp r s ∈ glList := by
  have h := Certificates.certificate15109.2.2.1
  have hid : linId ∈ glList := by decide
  simp only [nIdCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun m hm => ?_, fun r hr => ?_, h3⟩
  · obtain ⟨⟨ha, hb⟩, hc⟩ := h1 m hm
    rw [nAdTab_get hid, nAdArr_get _ hm] at ha
    rw [nTauTab_get hid hm] at hb
    rw [nCoArr_get hm] at hc
    exact ⟨ha, hb, hc⟩
  · obtain ⟨⟨ha, hb⟩, hc⟩ := h2 r hr
    exact ⟨ha, hb, hc⟩

theorem linComp_mem {r s : Lin8} (hr : r ∈ glList) (hs : s ∈ glList) : linComp r s ∈ glList :=
  nIdCheck_parts.2.2 r hr s hs

theorem linInv_mem {r : Lin8} (hr : r ∈ glList) : linInv r ∈ glList :=
  (nIdCheck_parts.2.1 r hr).1

theorem linComp_linInv_self {r : Lin8} (hr : r ∈ glList) : linComp (linInv r) r = linId :=
  (nIdCheck_parts.2.1 r hr).2.1

theorem linComp_self_linInv {r : Lin8} (hr : r ∈ glList) : linComp r (linInv r) = linId :=
  (nIdCheck_parts.2.1 r hr).2.2

theorem nTau_xor_basis {r : Lin8} (hr : r ∈ glList) {m j : Nat} (hm : m < 256) (hj : j < 8) :
    nTau r (m ^^^ nB j) = nTau r m ^^^ nTau r (nB j) ^^^ nGam r m (nB j) := by
  have h := Certificates.certificate15109.1
  simp only [nQuadCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h1 := h r hr m hm j hj
  rw [nTauTab_get hr (xor_lt hm (nB_lt hj)), nTauTab_get hr hm, nTauTab_get hr (nB_lt hj),
    nAdTab_get hr, nAdArr_get r hm, nAdArr_get r (nB_lt hj),
    nBetaArr_get (nAd_lt r _) (nAd_lt r _), nBetaArr_get hm (nB_lt hj)] at h1
  exact h1

theorem nComp_basis {r s : Lin8} (hr : r ∈ glList) (hs : s ∈ glList) {k : Nat} (hk : k < 8) :
    nAd (linComp r s) (2 ^ k) = nAd r (nAd s (2 ^ k)) ∧
      nTau (linComp r s) (nB k) = nTau r (nAd s (nB k)) ^^^ linApply r (nTau s (nB k)) := by
  have h := Certificates.certificate15109.2.1
  simp only [nCompCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h r hr s hs k hk
  have hrs := linComp_mem hr hs
  have hpow : 2 ^ k < 256 := by
    calc 2 ^ k < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hk
      _ = 256 := by norm_num
  rw [nAdTab_get hrs, nAdTab_get hr, nAdTab_get hs, nAdArr_get _ hpow, nAdArr_get _ hpow,
    nAdArr_get _ (nAd_lt s _)] at h1
  rw [nAdTab_get hs, nAdArr_get _ (nB_lt hk), nTauTab_get hrs (nB_lt hk),
    nTauTab_get hr (nAd_lt s _), nTauTab_get hs (nB_lt hk)] at h2
  exact ⟨h1, h2⟩

theorem mask_induction {P : Nat → Prop} (h0 : P 0)
    (hstep : ∀ m < 256, ∀ j < 8, P m → P (m ^^^ nB j)) {m : Nat} (hm : m < 256) : P m := by
  have hm' := (nIdCheck_parts.1 m hm).2.2
  have step : ∀ x < 256, ∀ k < 8, P x → P (x ^^^ sel (nCo m) k (nB k)) := by
    intro x hx k hk hP
    unfold sel
    split_ifs
    · exact hstep x hx k hk hP
    · simpa using hP
  have hb : ∀ k < 8, nB k < 256 := fun k hk => nB_lt hk
  rw [← hm']
  have e : maskApply nBasis (nCo m) = 0 ^^^ sel (nCo m) 0 (nB 0) ^^^ sel (nCo m) 1 (nB 1) ^^^
      sel (nCo m) 2 (nB 2) ^^^ sel (nCo m) 3 (nB 3) ^^^ sel (nCo m) 4 (nB 4) ^^^
      sel (nCo m) 5 (nB 5) ^^^ sel (nCo m) 6 (nB 6) ^^^ sel (nCo m) 7 (nB 7) := by
    simp [maskApply, nB]
  rw [e]
  have l0 := sel_lt (nCo m) 0 (hb 0 (by decide))
  have l1 := sel_lt (nCo m) 1 (hb 1 (by decide))
  have l2 := sel_lt (nCo m) 2 (hb 2 (by decide))
  have l3 := sel_lt (nCo m) 3 (hb 3 (by decide))
  have l4 := sel_lt (nCo m) 4 (hb 4 (by decide))
  have l5 := sel_lt (nCo m) 5 (hb 5 (by decide))
  have l6 := sel_lt (nCo m) 6 (hb 6 (by decide))
  refine step _ ?_ 7 (by decide) (step _ ?_ 6 (by decide) (step _ ?_ 5 (by decide)
    (step _ ?_ 4 (by decide) (step _ ?_ 3 (by decide) (step _ ?_ 2 (by decide)
    (step _ ?_ 1 (by decide) (step _ (by decide) 0 (by decide) h0))))))) <;>
    repeat (first | exact xor_lt ‹_› ‹_› | apply xor_lt)
  all_goals first | assumption | decide

theorem nTau_xor {r : Lin8} (hr : r ∈ glList) {m n : Nat} (hm : m < 256) (hn : n < 256) :
    nTau r (m ^^^ n) = nTau r m ^^^ nTau r n ^^^ nGam r m n := by
  revert m
  refine mask_induction (P := fun n => ∀ {m}, m < 256 →
    nTau r (m ^^^ n) = nTau r m ^^^ nTau r n ^^^ nGam r m n) ?_ ?_ hn
  · intro m hm
    rw [Nat.xor_zero, nTau_zero, nGam_zero_right, fin8_xor_zero, fin8_xor_zero]
  · intro n hn j hj ih m hm
    have hmn : m ^^^ n < 256 := xor_lt hm hn
    rw [← Nat.xor_assoc, nTau_xor_basis hr hmn hj, ih hm, nTau_xor_basis hr hn hj,
      nGam_xor_left, nGam_xor_right]
    ac_rfl

theorem nAd_linComp {r s : Lin8} (hr : r ∈ glList) (hs : s ∈ glList) (m : Nat) :
    nAd (linComp r s) m = nAd r (nAd s m) := by
  have e : nAd r (nAd s m) = maskApply ((adMat s).map (nAd r)) m :=
    maskApply_map (nAd_xor r) (nAd_zero r) _ _
  rw [e, nAd]
  have hcol : ∀ k < 8, (adMat (linComp r s)).getD k 0 = ((adMat s).map (nAd r)).getD k 0 := by
    intro k hk
    have h := (nComp_basis hr hs hk).1
    simp only [nAd] at h
    rw [maskApply_two_pow _ hk, maskApply_two_pow _ hk] at h
    rw [h, getD_map_zero (nAd_zero r), nAd]
  simp only [maskApply, hcol 0 (by decide), hcol 1 (by decide), hcol 2 (by decide),
    hcol 3 (by decide), hcol 4 (by decide), hcol 5 (by decide), hcol 6 (by decide),
    hcol 7 (by decide)]

theorem nTau_linComp {r s : Lin8} (hr : r ∈ glList) (hs : s ∈ glList) {m : Nat} (hm : m < 256) :
    nTau (linComp r s) m = nTau r (nAd s m) ^^^ linApply r (nTau s m) := by
  have hrs := linComp_mem hr hs
  refine mask_induction (P := fun m => nTau (linComp r s) m =
    nTau r (nAd s m) ^^^ linApply r (nTau s m)) ?_ ?_ hm
  · rw [nTau_zero, nAd_zero, nTau_zero, nTau_zero, linApply_zero, fin8_xor_zero]
  · intro m hm j hj ih
    have hb := nB_lt hj
    have hgam : nGam (linComp r s) m (nB j) =
        nGam r (nAd s m) (nAd s (nB j)) ^^^ linApply r (nGam s m (nB j)) := by
      have h4 : ∀ a b c : Fin 8, a ^^^ b ^^^ (b ^^^ c) = a ^^^ c := by decide
      simp only [nGam, nAd_linComp hr hs, linApply_linComp, linApply_xor]
      exact (h4 _ _ _).symm
    rw [nTau_xor hrs hm hb, ih, (nComp_basis hr hs hj).2, hgam, nAd_xor,
      nTau_xor hr (nAd_lt s m) (nAd_lt s _), nTau_xor hs hm hb, linApply_xor, linApply_xor]
    ac_rfl

theorem nAut_mul {r : Lin8} (hr : r ∈ glList) (x y : RuR) :
    nAut r (x * y) = nAut r x * nAut r y := by
  refine RuR.ext (Fin.ext ?_) ?_
  · change nAd r (x.m ^^^ y.m).val = ((nAut r x).m ^^^ (nAut r y).m).val
    rw [fin256_val_xor, fin256_val_xor, nAut_m, nAut_m, nAd_xor]
  · change linApply r (x.t ^^^ y.t ^^^ nBeta x.m.val y.m.val) ^^^ nTau r (x.m ^^^ y.m).val =
      (nAut r x).t ^^^ (nAut r y).t ^^^ nBeta (nAut r x).m.val (nAut r y).m.val
    rw [nAut_t, nAut_t, nAut_m, nAut_m, fin256_val_xor, nTau_xor hr x.m.isLt y.m.isLt, nGam,
      linApply_xor, linApply_xor]
    exact fin8_cancel _ _ _ _ _ _

theorem nAut_linId (x : RuR) : nAut linId x = x := by
  have h := nIdCheck_parts.1 x.m.val x.m.isLt
  refine RuR.ext (Fin.ext ?_) ?_
  · rw [nAut_m, h.1]
  · rw [nAut_t, h.2.1, linApply_linId, fin8_xor_zero]

theorem nAut_linComp {r s : Lin8} (hr : r ∈ glList) (hs : s ∈ glList) (x : RuR) :
    nAut r (nAut s x) = nAut (linComp r s) x := by
  refine RuR.ext (Fin.ext ?_) ?_
  · rw [nAut_m, nAut_m, nAut_m, nAd_linComp hr hs]
  · rw [nAut_t, nAut_t, nAut_t, nAut_m, nTau_linComp hr hs x.m.isLt, linApply_xor,
      linApply_linComp]
    ac_rfl

@[expose] noncomputable def nAutE {r : Lin8} (hr : r ∈ glList) : RuR ≃* RuR where
  toFun := nAut r
  invFun := nAut (linInv r)
  left_inv x := by
    rw [nAut_linComp (linInv_mem hr) hr, linComp_linInv_self hr, nAut_linId]
  right_inv x := by
    rw [nAut_linComp hr (linInv_mem hr), linComp_self_linInv hr, nAut_linId]
  map_mul' := nAut_mul hr

theorem nAutE_apply {r : Lin8} (hr : r ∈ glList) (x : RuR) : nAutE hr x = nAut r x := rfl

@[expose] noncomputable def nK : Subgroup (MulAut RuR) where
  carrier := {f | ∃ r ∈ glList, ∀ x, f x = nAut r x}
  mul_mem' := by
    rintro f g ⟨r, hr, hf⟩ ⟨s, hs, hg⟩
    exact ⟨linComp r s, linComp_mem hr hs, fun x => by
      rw [MulAut.mul_apply, hf, hg, nAut_linComp hr hs]⟩
  one_mem' := ⟨linId, linId_mem, fun x => by rw [MulAut.one_apply, nAut_linId]⟩
  inv_mem' := by
    rintro f ⟨r, hr, hf⟩
    refine ⟨linInv r, linInv_mem hr, fun x => ?_⟩
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hf, nAut_linComp hr (linInv_mem hr),
      linComp_self_linInv hr, nAut_linId]

theorem mem_nK_iff (f : MulAut RuR) : f ∈ nK ↔ ∃ r ∈ glList, ∀ x, f x = nAut r x := Iff.rfl

theorem card_nK : Nat.card nK = 168 := by
  classical
  let F : {r // r ∈ glList} → nK := fun r => ⟨nAutE r.2, r.1, r.2, fun _ => rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun r s h => Subtype.ext (eq_of_nAut_eq fun x => ?_), fun f => ?_⟩
    · have := congrArg (fun f : nK => (f : MulAut RuR) x) h
      exact this
    · obtain ⟨r, hr, hf⟩ := f.2
      exact ⟨⟨r, hr⟩, Subtype.ext (MulEquiv.ext fun x => (hf x).symm)⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e : (Finset.univ.filter fun r : Lin8 => r ∈ glList) = glList.toFinset := by
    ext r
    simp
  rw [e, List.toFinset_card_of_nodup RuQCode.glList_nodup, RuQCode.glList_length]

abbrev RuNModel : Type := RuR ⋊[nK.subtype] nK

theorem card_RuNModel : Nat.card RuNModel = 344064 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, card_RuR, card_nK]

end Cert

@[expose] def A1R : Subgroup RuR where
  carrier := {x | x.m = 0}
  mul_mem' := by
    intro x y hx hy
    change x.m ^^^ y.m = 0
    rw [show x.m = 0 from hx, show y.m = 0 from hy]
    rfl
  one_mem' := rfl
  inv_mem' := fun hx => hx

theorem mem_A1R_iff (x : RuR) : x ∈ A1R ↔ x.m = 0 := Iff.rfl

theorem card_A1R : Nat.card A1R = 8 := by
  let F : Fin 8 → A1R := fun t => ⟨⟨0, t⟩, rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun s t h => congrArg (fun x : A1R => (x : RuR).t) h, fun x => ⟨(x : RuR).t, ?_⟩⟩
    exact Subtype.ext (RuR.ext x.2.symm rfl)
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isPGroup_RuR : IsPGroup 2 RuR := IsPGroup.of_card (n := 11) card_RuR

theorem nBeta_comm_of_mem_center {x : RuR} (hx : x ∈ center RuR) (y : RuR) :
    nBeta x.m.val y.m.val = nBeta y.m.val x.m.val := by
  have h := congrArg RuR.t ((mem_center_iff.mp hx y).symm)
  change x.t ^^^ y.t ^^^ nBeta x.m.val y.m.val = y.t ^^^ x.t ^^^ nBeta y.m.val x.m.val at h
  have h2 : ∀ a b c d : Fin 8, a ^^^ b ^^^ c = b ^^^ a ^^^ d → c = d := by decide
  exact h2 _ _ _ _ h

section Cert


@[expose] noncomputable def A1model : Subgroup RuNModel :=
  A1R.map (SemidirectProduct.inl : RuR →* RuNModel)

theorem card_A1model : Nat.card A1model = 8 := by
  rw [A1model, Subgroup.card_map_of_injective SemidirectProduct.inl_injective, card_A1R]

theorem center_RuR : center RuR = A1R := by
  have h := Certificates.certificate15109.2.2.2.1
  simp only [nFaithCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    bne_iff_ne, ne_eq] at h
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_center_iff.mpr fun y => ?_)
  · by_contra hm
    have hm0 : x.m.val ≠ 0 := fun e => hm (Fin.ext e)
    obtain ⟨n, hn, hne⟩ := h.1 (x.m.val - 1) (by omega)
    have e1 : x.m.val - 1 + 1 = x.m.val := by omega
    rw [e1, nBetaArr_get x.m.isLt hn, nBetaArr_get hn x.m.isLt] at hne
    exact hne (nBeta_comm_of_mem_center hx ⟨⟨n, hn⟩, 0⟩)
  · have hx0 : x.m = 0 := hx
    refine RuR.ext ?_ ?_
    · change y.m ^^^ x.m = x.m ^^^ y.m
      rw [hx0]
      exact Fin.ext (by simp)
    · change y.t ^^^ x.t ^^^ nBeta y.m.val x.m.val = x.t ^^^ y.t ^^^ nBeta x.m.val y.m.val
      rw [hx0]
      change y.t ^^^ x.t ^^^ nBeta y.m.val 0 = x.t ^^^ y.t ^^^ nBeta 0 y.m.val
      rw [nBeta_zero_left, nBeta_zero_right]
      ac_rfl

theorem exists_linApply_eq {t t' : Fin 8} (ht : t ≠ 0) (ht' : t' ≠ 0) :
    ∃ s ∈ glList, linApply s t = t' := by
  have h := Certificates.certificate15109.2.2.2.1
  simp only [nFaithCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    Bool.or_eq_true, beq_iff_eq, forall_const] at h
  rcases h.2 t t' with (h0 | h0) | ⟨s, hs, e⟩
  · exact absurd h0 ht
  · exact absurd h0 ht'
  · exact ⟨s, hs, e⟩

theorem le_of_normal_ne_bot (M : Subgroup RuNModel) [hMn : M.Normal] (hM : M ≠ ⊥) :
    A1model ≤ M := by
  classical
  set Rt := (SemidirectProduct.inl : RuR →* RuNModel).range with hRt
  have hRtn : Rt.Normal := by
    rw [hRt, SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have h1 : ∃ x : RuR, x ≠ 1 ∧ SemidirectProduct.inl x ∈ M := by
    by_contra hno
    push Not at hno
    apply hM
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    have hc : ∀ x : RuR, g * SemidirectProduct.inl x = SemidirectProduct.inl x * g := by
      intro x
      have hmem : g * SemidirectProduct.inl x * g⁻¹ * (SemidirectProduct.inl x)⁻¹ ∈ M := by
        have := hMn.conj_mem _ (inv_mem hg) (SemidirectProduct.inl x)
        have e : g * SemidirectProduct.inl x * g⁻¹ * (SemidirectProduct.inl x)⁻¹ =
            g * (SemidirectProduct.inl x * g⁻¹ * (SemidirectProduct.inl x)⁻¹) := by group
        rw [e]
        exact mul_mem hg this
      have hmemR : g * SemidirectProduct.inl x * g⁻¹ * (SemidirectProduct.inl x)⁻¹ ∈ Rt :=
        mul_mem (hRtn.conj_mem _ ⟨x, rfl⟩ g) (inv_mem ⟨x, rfl⟩)
      obtain ⟨y, hy⟩ := hmemR
      have hy1 : y = 1 := by
        by_contra hy1
        exact hno y hy1 (hy ▸ hmem)
      rw [hy1, map_one] at hy
      have := hy.symm
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this
    have hk : ∀ x : RuR, g.left * (g.right : MulAut RuR) x = x * g.left := by
      intro x
      have := congrArg SemidirectProduct.left (hc x)
      simpa using this
    obtain ⟨r₀, hr₀, hf⟩ := g.right.2
    have hlin : ∀ t : Fin 8, linApply r₀ t = t := by
      intro t
      have hA : ((g.right : MulAut RuR) ⟨0, t⟩) = ⟨0, t⟩ := by
        have hcen : (⟨0, t⟩ : RuR) ∈ center RuR := by
          rw [center_RuR]
          rfl
        have := hk ⟨0, t⟩
        rw [(mem_center_iff.mp hcen g.left).symm] at this
        exact mul_left_cancel this
      rw [hf, nAut_A1] at hA
      exact congrArg RuR.t hA
    have hr₀1 : r₀ = linId := by
      have e1 := hlin 1
      have e2 := hlin 2
      have e4 := hlin 4
      rw [linApply_one] at e1
      rw [linApply_two] at e2
      rw [linApply_four] at e4
      exact Prod.ext e1 (Prod.ext e2 e4)
    have hright : g.right = 1 := by
      refine Subtype.ext (MulEquiv.ext fun x => ?_)
      rw [hf, hr₀1, nAut_linId]
      rfl
    have hleft : g.left ∈ center RuR := by
      refine mem_center_iff.mpr fun x => ?_
      have := hk x
      rw [hright] at this
      exact this.symm
    rw [center_RuR] at hleft
    have hg' : g = SemidirectProduct.inl g.left := by
      rw [← SemidirectProduct.inl_left_mul_inr_right g, hright, map_one, mul_one]
      rfl
    by_contra hg1
    have hl1 : g.left ≠ 1 := by
      intro e
      rw [e, map_one] at hg'
      exact hg1 hg'
    exact hno g.left hl1 (hg' ▸ hg)
  obtain ⟨x, hx1, hxM⟩ := h1
  have hM' : M.comap (SemidirectProduct.inl : RuR →* RuNModel) ≠ ⊥ := by
    intro e
    have : x ∈ M.comap SemidirectProduct.inl := hxM
    rw [e, mem_bot] at this
    exact hx1 this
  have : Group.IsNilpotent RuR := isPGroup_RuR.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hM'
  rw [center_RuR, Ne, eq_bot_iff, IsConcreteLE.le_iff] at hne
  push Not at hne
  obtain ⟨a, ⟨haM, haA⟩, ha1⟩ := hne
  rw [mem_bot] at ha1
  have hat : a.t ≠ 0 := by
    intro e
    exact ha1 (RuR.ext haA e)
  rintro _ ⟨b, hb, rfl⟩
  by_cases hbt : b.t = 0
  · have : b = 1 := RuR.ext hb hbt
    rw [this, map_one]
    exact one_mem M
  · obtain ⟨s, hs, hst⟩ := exists_linApply_eq hat hbt
    let k : nK := ⟨nAutE hs, s, hs, fun _ => rfl⟩
    have e : (SemidirectProduct.inl b : RuNModel) =
        SemidirectProduct.inr k * SemidirectProduct.inl a * (SemidirectProduct.inr k)⁻¹ := by
      rw [← map_inv, ← SemidirectProduct.inl_aut]
      congr 1
      change b = nAut s a
      have ea : a = ⟨0, a.t⟩ := RuR.ext haA rfl
      rw [ea, nAut_A1, hst]
      exact RuR.ext hb rfl
    rw [e]
    exact hMn.conj_mem _ haM _

theorem nValid_iff (p : NTrip) : nValid p = true ↔ p.1 < 256 ∧ p.2.2 ∈ glList := by
  simp [nValid]

@[expose] noncomputable def toModel (p : NTrip) : RuNModel :=
  if h : p.1 < 256 ∧ p.2.2 ∈ glList then
    ⟨⟨⟨p.1, h.1⟩, p.2.1⟩, ⟨nAutE h.2, p.2.2, h.2, fun _ => rfl⟩⟩
  else 1

theorem toModel_of_valid {p : NTrip} (h : p.1 < 256 ∧ p.2.2 ∈ glList) :
    toModel p = ⟨⟨⟨p.1, h.1⟩, p.2.1⟩, ⟨nAutE h.2, p.2.2, h.2, fun _ => rfl⟩⟩ := by
  unfold toModel
  split_ifs
  rfl

theorem nOneT_valid : nOneT.1 < 256 ∧ nOneT.2.2 ∈ glList := ⟨by decide, linId_mem⟩

theorem toModel_one : toModel nOneT = 1 := by
  rw [toModel_of_valid nOneT_valid]
  refine SemidirectProduct.ext rfl (Subtype.ext (MulEquiv.ext fun x => ?_))
  exact nAut_linId x

theorem nMulT_valid {p q : NTrip} (hp : p.1 < 256 ∧ p.2.2 ∈ glList)
    (hq : q.1 < 256 ∧ q.2.2 ∈ glList) : (nMulT p q).1 < 256 ∧ (nMulT p q).2.2 ∈ glList := by
  refine ⟨?_, linComp_mem hp.2 hq.2⟩
  simp only [nMulT, nAdTab_get hp.2, nAdArr_get _ hq.1]
  exact xor_lt hp.1 (nAd_lt _ _)

theorem toModel_mul {p q : NTrip} (hp : p.1 < 256 ∧ p.2.2 ∈ glList)
    (hq : q.1 < 256 ∧ q.2.2 ∈ glList) : toModel (nMulT p q) = toModel p * toModel q := by
  rw [toModel_of_valid (nMulT_valid hp hq), toModel_of_valid hp, toModel_of_valid hq,
    SemidirectProduct.mul_def]
  refine SemidirectProduct.ext ?_ (Subtype.ext (MulEquiv.ext fun x => ?_))
  · refine RuR.ext (Fin.ext ?_) ?_
    · change (nMulT p q).1 = (⟨p.1, hp.1⟩ ^^^ (nAut p.2.2 ⟨⟨q.1, hq.1⟩, q.2.1⟩).m).val
      rw [fin256_val_xor, nAut_m]
      simp only [nMulT, nAdTab_get hp.2, nAdArr_get _ hq.1]
    · change (nMulT p q).2.1 = p.2.1 ^^^ (nAut p.2.2 ⟨⟨q.1, hq.1⟩, q.2.1⟩).t ^^^
        nBeta p.1 (nAut p.2.2 ⟨⟨q.1, hq.1⟩, q.2.1⟩).m.val
      rw [nAut_t, nAut_m]
      simp only [nMulT, nAdTab_get hp.2, nAdArr_get _ hq.1, nTauTab_get hp.2 hq.1,
        nBetaArr_get hp.1 (nAd_lt _ _)]
  · exact (nAut_linComp hp.2 hq.2 x).symm

@[expose] noncomputable def ruNImg (i : Fin 7) : RuNModel := toModel (nImg.getD i nOneT)

theorem nImg_parts (i : Fin 7) :
    ((nImg.getD i nOneT).1 < 256 ∧ (nImg.getD i nOneT).2.2 ∈ glList) ∧
    ((nImgInv.getD i nOneT).1 < 256 ∧ (nImgInv.getD i nOneT).2.2 ∈ glList) ∧
    toModel (nImgInv.getD i nOneT) = (ruNImg i)⁻¹ := by
  have h := Certificates.certificate15109.2.2.2.2.1
  simp only [nImgCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    nValid_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h i.val i.isLt
  refine ⟨h1, h2, ?_⟩
  have e := toModel_mul h1 h2
  rw [h3, toModel_one] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem toModel_nSign (p : Fin 7 × Bool) :
    ((nSign p).1 < 256 ∧ (nSign p).2.2 ∈ glList) ∧
      toModel (nSign p) = bif p.2 then ruNImg p.1 else (ruNImg p.1)⁻¹ := by
  obtain ⟨i, b⟩ := p
  cases b
  · exact ⟨(nImg_parts i).2.1, (nImg_parts i).2.2⟩
  · exact ⟨(nImg_parts i).1, rfl⟩

theorem toModel_foldl (w : List (Fin 7 × Bool)) {x : NTrip} (hx : x.1 < 256 ∧ x.2.2 ∈ glList) :
    ((w.foldl (fun x p => nMulT x (nSign p)) x).1 < 256 ∧
      (w.foldl (fun x p => nMulT x (nSign p)) x).2.2 ∈ glList) ∧
    toModel (w.foldl (fun x p => nMulT x (nSign p)) x) =
      toModel x * (w.map fun p => bif p.2 then ruNImg p.1 else (ruNImg p.1)⁻¹).prod := by
  induction w generalizing x with
  | nil => exact ⟨hx, by simp⟩
  | cons p w ih =>
    have hs := toModel_nSign p
    obtain ⟨h1, h2⟩ := ih (nMulT_valid hx hs.1)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, toModel_mul hx hs.1, hs.2, List.map_cons, List.prod_cons, mul_assoc]

theorem lift_ruNImg (w : List (Fin 7 × Bool)) :
    ((nEvalW w).1 < 256 ∧ (nEvalW w).2.2 ∈ glList) ∧
      FreeGroup.lift ruNImg (FreeGroup.mk w) = toModel (nEvalW w) := by
  obtain ⟨h1, h2⟩ := toModel_foldl w nOneT_valid
  refine ⟨h1, ?_⟩
  rw [FreeGroup.lift_mk, nEvalW, h2, toModel_one, one_mul]

theorem ruNImg_relsA :
    ∀ r ∈ relsA.map (wordOfCodes 7), FreeGroup.lift ruNImg (FreeGroup.mk r) = 1 := by
  have h := Certificates.certificate15109.2.2.2.2.2.1
  simp only [nRelCheck, List.all_eq_true, beq_iff_eq] at h
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  rw [(lift_ruNImg _).2, h r' hr', toModel_one]

theorem toModel_inl {m : Nat} (hm : m < 256) (t : Fin 8) :
    toModel (m, t, linId) = SemidirectProduct.inl ⟨⟨m, hm⟩, t⟩ := by
  rw [toModel_of_valid ⟨hm, linId_mem⟩]
  refine SemidirectProduct.ext rfl (Subtype.ext (MulEquiv.ext fun x => ?_))
  exact nAut_linId x

theorem ruNImg_A0 :
    ∀ w ∈ ruA0Words, FreeGroup.lift ruNImg (FreeGroup.mk w) ∈ A1model := by
  have h := Certificates.certificate15109.2.2.2.2.2.2.2
  simp only [nA0Check, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  intro w hw
  obtain ⟨⟨hv1, -⟩, e⟩ := lift_ruNImg w
  obtain ⟨h0, hid⟩ := h w hw
  have ep : nEvalW w = ((nEvalW w).1, (nEvalW w).2.1, linId) := by
    rw [← hid]
  rw [e, ep, toModel_inl hv1]
  exact ⟨_, Fin.ext h0, rfl⟩

theorem toModel_nEvalW_mem (w : List (Fin 7 × Bool)) :
    toModel (nEvalW w) ∈ closure (ruNImg '' {i | i ∈ [0, 1, 2, 3, 4, 6]}) := by
  set H := closure (ruNImg '' {i | i ∈ [0, 1, 2, 3, 4, 6]})
  have hlet : ∀ i : Fin 7, ruNImg i ∈ H := by
    intro i
    by_cases hi : i ∈ [0, 1, 2, 3, 4, 6]
    · exact subset_closure ⟨i, hi, rfl⟩
    · have h5 : i = 5 := by
        fin_cases i <;> simp_all
      have e : ruNImg i = 1 := by
        rw [h5, ruNImg]
        exact toModel_one
      rw [e]
      exact one_mem H
  rw [← (lift_ruNImg w).2, FreeGroup.lift_mk]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
  cases p.2
  · exact inv_mem (hlet p.1)
  · exact hlet p.1

theorem eq_top_of_gens (H : Subgroup RuR) (h1 : ∀ j (hj : j < 8), (⟨⟨nB j, nB_lt hj⟩, 0⟩ : RuR) ∈ H)
    (h2 : (⟨0, 1⟩ : RuR) ∈ H) (h3 : (⟨0, 2⟩ : RuR) ∈ H) (h4 : (⟨0, 4⟩ : RuR) ∈ H) : H = ⊤ := by
  have hA : ∀ a b : Fin 8, (⟨0, a⟩ : RuR) ∈ H → (⟨0, b⟩ : RuR) ∈ H → (⟨0, a ^^^ b⟩ : RuR) ∈ H := by
    intro a b ha hb
    have e : (⟨0, a ^^^ b⟩ : RuR) = ⟨0, a⟩ * ⟨0, b⟩ := by
      rw [RuR.mul_def]
      refine RuR.ext rfl ?_
      change a ^^^ b = a ^^^ b ^^^ nBeta 0 0
      rw [nBeta_zero_left, fin8_xor_zero]
    rw [e]
    exact mul_mem ha hb
  have hA0 : ∀ t : Fin 8, (⟨0, t⟩ : RuR) ∈ H := by
    have h0 : (⟨0, 0⟩ : RuR) ∈ H := one_mem H
    have h3' := hA 1 2 h2 h3
    have h5 := hA 1 4 h2 h4
    have h6 := hA 2 4 h3 h4
    have h7 := hA 3 4 h3' h4
    intro t
    fin_cases t <;> assumption
  refine eq_top_iff.mpr fun x _ => ?_
  have key : ∀ t : Fin 8, ∀ h : x.m.val < 256, (⟨⟨x.m.val, h⟩, t⟩ : RuR) ∈ H := by
    refine mask_induction (P := fun m => ∀ t : Fin 8, ∀ h : m < 256,
      (⟨⟨m, h⟩, t⟩ : RuR) ∈ H) ?_ ?_ x.m.isLt
    · intro t h
      exact hA0 t
    · intro m hm j hj ih t h
      have e : (⟨⟨m ^^^ nB j, h⟩, t⟩ : RuR) =
          ⟨⟨m, hm⟩, t ^^^ nBeta m (nB j)⟩ * ⟨⟨nB j, nB_lt hj⟩, 0⟩ := by
        rw [RuR.mul_def]
        refine RuR.ext (Fin.ext ?_) ?_
        · change m ^^^ nB j = (⟨m, hm⟩ ^^^ ⟨nB j, nB_lt hj⟩ : Fin 256).val
          rw [fin256_val_xor]
        · change t = t ^^^ nBeta m (nB j) ^^^ 0 ^^^ nBeta m (nB j)
          have h4 : ∀ a b : Fin 8, a = a ^^^ b ^^^ 0 ^^^ b := by decide
          exact h4 _ _
      rw [e]
      exact mul_mem (ih _ hm) (h1 j hj)
  exact key x.t x.m.isLt

theorem ruNImg_closure : closure (ruNImg '' {i | i ∈ [0, 1, 2, 3, 4, 6]}) = ⊤ := by
  set H := closure (ruNImg '' {i | i ∈ [0, 1, 2, 3, 4, 6]}) with hH
  have h := Certificates.certificate15109.2.2.2.2.2.2.1
  simp only [nCloCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hR, hK⟩ := h
  have hRmem : ∀ i < 11, toModel (nRTargets.getD i nOneT) ∈ H := fun i hi =>
    (hR i hi) ▸ toModel_nEvalW_mem _
  have hinl : ∀ x : RuR, SemidirectProduct.inl x ∈ H := by
    have htop : H.comap (SemidirectProduct.inl : RuR →* RuNModel) = ⊤ := by
      refine eq_top_of_gens _ (fun j hj => ?_) ?_ ?_ ?_
      · have := hRmem j (by omega)
        interval_cases j <;> simpa [nRTargets, toModel_inl, nB, nBasis] using this
      · simpa [nRTargets, toModel_inl] using hRmem 8 (by decide)
      · simpa [nRTargets, toModel_inl] using hRmem 9 (by decide)
      · simpa [nRTargets, toModel_inl] using hRmem 10 (by decide)
    intro x
    have : x ∈ H.comap (SemidirectProduct.inl : RuR →* RuNModel) := by
      rw [htop]
      exact mem_top x
    exact this
  have hinr : ∀ k : nK, SemidirectProduct.inr k ∈ H := by
    intro k
    obtain ⟨r, hr, hf⟩ := k.2
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < 168 := by rwa [RuQCode.glList_length] at hi
    have hmem := (hK i hi') ▸ toModel_nEvalW_mem (wordOfCodes 7 (nKWords.getD i []))
    rw [List.getD_eq_getElem _ _ hi] at hmem
    rw [toModel_of_valid ⟨Nat.zero_lt_succ 255, hr⟩] at hmem
    convert hmem using 1
    refine SemidirectProduct.ext rfl (Subtype.ext (MulEquiv.ext fun x => ?_))
    exact hf x
  refine eq_top_iff.mpr fun g _ => ?_
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact mul_mem (hinl _) (hinr _)

end Cert

end CFSG.ComponentClassification.GMS78.RuN
