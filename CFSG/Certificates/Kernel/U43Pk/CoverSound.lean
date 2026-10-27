module

public import CFSG.Certificates.Kernel.U43Pk.Sound
public import Certificates.Data.Kernel.U43Pk.Cover
public import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.U43Pk

open CFSG.KD.U43Pk CFSG.KC.Enum CFSG.KC.Pack
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

theorem shl64 (e : ℕ) : Nat.shiftLeft e 64 = 16 ^ 16 * e := by
  have := shl_eq e 16
  rwa [show Nat.shiftLeft 16 2 = 64 from rfl] at this

theorem add_shl_lt {a e : ℕ} (ha : a < 16 ^ 16) (he : e < 16) :
    Nat.add a (Nat.shiftLeft e 64) < 16 ^ 17 := by
  rw [Nat.add_eq, shl64]
  have h : 16 ^ 16 * e ≤ 16 ^ 16 * 15 := Nat.mul_le_mul_left _ (by omega)
  have e17 : (16 : ℕ) ^ 17 = 16 ^ 16 * 16 := by rw [pow_succ]
  rw [e17]
  generalize 16 ^ 16 * e = Y at *
  generalize (16 : ℕ) ^ 16 = X at *
  omega

theorem mulK_lt (G P : ℕ) : mulK G P < 16 ^ 17 := by
  rw [mulK_eq]
  exact add_shl_lt (matK_lt _ _) (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))

theorem nrmK_lt (R : ℕ) : nrmK R < 16 ^ 17 := by
  unfold nrmK
  rw [strictN_eq]
  exact add_shl_lt (packK_lt fun k => dg_lt _ _) (dg_lt _ _)

theorem dec_inj {P Q : ℕ} (hP : P < 16 ^ 17) (hQ : Q < 16 ^ 17) (h : dec P = dec Q) : P = Q :=
  digits_eq 17 P Q hP hQ fun j hj => by rw [← dec_get P hj, ← dec_get Q hj, h]

theorem dec_beq {P Q : ℕ} (hP : P < 16 ^ 17) (hQ : Q < 16 ^ 17) : (dec P == dec Q) = Nat.beq P Q := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨dec_inj hP hQ, fun h => h ▸ rfl⟩

theorem scal3 : scal 3 = dec 3458767812358569987 := by decide +kernel

theorem scal6 : scal 6 = dec 6917535624717139974 := by decide +kernel

theorem scal1 : scal 1 = dec 1152922604119523329 := by decide +kernel

theorem scal2 : scal 2 = dec 2305845208239046658 := by decide +kernel

theorem isZ_dec {P : ℕ} (hP : P < 16 ^ 17) : isZ (dec P) = isZK P := by
  unfold isZ isZK
  rw [scal3, scal6, scal1, scal2, dec_beq hP (by norm_num), dec_beq hP (by norm_num),
    dec_beq hP (by norm_num), dec_beq hP (by norm_num)]
  generalize Nat.beq P 3458767812358569987 = a
  generalize Nat.beq P 6917535624717139974 = b
  generalize Nat.beq P 1152922604119523329 = c
  generalize Nat.beq P 2305845208239046658 = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem eqZ_dec {A B : ℕ} (hA : Dig A) (hB : Dig B) :
    eqZ (dec A) (dec B) = Nat.beq (nrmK A) (nrmK B) := by
  unfold eqZ
  rw [normalize_dec hA, normalize_dec hB, dec_beq (nrmK_lt A) (nrmK_lt B)]

theorem notK_eq (b : Bool) : notK b = !b := by cases b <;> rfl

theorem cls_flags (a b : Bool) :
    Nat.beq (Nat.mod (Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 a)
      (Bool.rec (motive := fun _ => ℕ) 0 2 b)) 2) 1 = a ∧
    Nat.beq (Nat.div (Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 a)
      (Bool.rec (motive := fun _ => ℕ) 0 2 b)) 2) 1 = b := by
  cases a <;> cases b <;> exact ⟨rfl, rfl⟩

theorem band_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem clsK_o8 (P : ℕ) : Nat.beq (Nat.mod (clsK P) 2) 1 =
    (isZK (mulK (mulK (mulK P P) (mulK P P)) (mulK (mulK P P) (mulK P P))) &&
      !isZK (mulK (mulK P P) (mulK P P))) := by
  unfold clsK
  simp only [strictN_eq]
  rw [(cls_flags _ _).1, band_eq, notK_eq]

theorem clsK_inv (P : ℕ) : Nat.beq (Nat.div (clsK P) 2) 1 = (isZK (mulK P P) && !isZK P) := by
  unfold clsK
  simp only [strictN_eq]
  rw [(cls_flags _ _).2, band_eq, notK_eq]

theorem dg_mapK (B P : ℕ) {m : ℕ} (hm : m < 16) : dg (mapK B P) m = dg B (dg P m) := by
  unfold mapK
  rw [dg_packK (fun k => dg_lt _ _), if_pos hm]

theorem ydK_eq (G P : ℕ) {m : ℕ} (hm : m < 16) :
    ydK G P m = dg (if dg G 16 = 1 then mapK BT P else P) m := by
  unfold ydK
  by_cases h : dg G 16 = 1
  · rw [if_pos h, dg_mapK _ _ hm, h]
    rfl
  · rw [if_neg h]
    have : Nat.beq (dg G 16) 1 = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    rw [this]

theorem enK_eq (G P : ℕ) {k : ℕ} (hk : k < 16) : enK G P k = dg (mulK G P) k := by
  set Y := if dg G 16 = 1 then mapK BT P else P
  have hm : mulK G P = Nat.add (packK fun k => entK G Y (Nat.div k 4) (Nat.mod k 4))
      (Nat.shiftLeft ((dg G 16 + dg P 16) % 2) 64) := by
    rw [mulK_eq]
    rfl
  rw [hm, dg_pack16 (fun k => entK_lt _ _ _ _) (by omega), if_pos hk]
  unfold enK enIJ entK
  have hj : Nat.mod k 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e0 : ∀ c, c ≤ 12 → ydK G P (Nat.add c (Nat.mod k 4)) = dg Y (Nat.add c (Nat.mod k 4)) :=
    fun c hc => ydK_eq G P (by rw [Nat.add_eq]; omega)
  have e1 : ydK G P (Nat.mod k 4) = dg Y (Nat.mod k 4) := ydK_eq G P (by omega)
  rw [e1, e0 4 (by norm_num), e0 8 (by norm_num), e0 12 (by norm_num)]

theorem mT_lt : ∀ a < 9, ∀ b < 9, mT a b < 9 := by decide +kernel

theorem mT_rearr : ∀ a < 9, ∀ b < 9, ∀ c < 9, ∀ d < 9,
    mT (mT a b) (mT c d) = mT (mT a c) (mT b d) := by decide +kernel

theorem mT_comm : ∀ a < 9, ∀ b < 9, mT a b = mT b a := by decide +kernel

theorem mT_cancel : ∀ c < 9, c ≠ 0 → ∀ a < 9, ∀ b < 9, mT c a = mT c b → a = b := by
  decide +kernel

theorem mT_nz : ∀ a < 9, ∀ b < 9, a ≠ 0 → b ≠ 0 → mT a b ≠ 0 := by decide +kernel

theorem mT_zero : ∀ a < 9, mT 0 a = 0 ∧ mT a 0 = 0 := by decide +kernel

theorem mcT_zero : ∀ u < 9, dg MCT u = 0 → u = 0 := by decide +kernel

theorem fnz_zero {R : ℕ} (h : fnzK R = 0) {k : ℕ} (hk : k < 16) : dg R k = 0 := by
  rw [fnzK_go, Nat.sub_self, ← List.range_eq_range'] at h
  cases hf : ((List.range 16).map (dg R)).find? fun w => decide (w ≠ 0) with
  | some v =>
    rw [hf] at h
    have hv := List.find?_some hf
    simp only [Option.getD_some] at h
    simp [h] at hv
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf (dg R k) (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
    simpa using this

theorem dg_nrmK {R : ℕ} {k : ℕ} (hk : k < 16) : dg (nrmK R) k = mT (dg MCT (fnzK R)) (dg R k) := by
  unfold nrmK
  simp only [strictN_eq]
  unfold mapK
  rw [dg_pack16 (fun k => dg_lt _ _) (dg_lt _ _), if_pos hk, dg_shr]
  rfl

theorem dig_lt16 {R : ℕ} (hR : Dig R) {k : ℕ} (hk : k < 16) : dg R k < 9 := hR k hk

theorem cross_of_nrm {A B : ℕ} (hA : Dig A) (hB : Dig B) (h : nrmK A = nrmK B) {p q : ℕ}
    (hp : p < 16) (hq : q < 16) : mT (dg A p) (dg B q) = mT (dg A q) (dg B p) := by
  have e : ∀ k < 16, mT (dg MCT (fnzK A)) (dg A k) = mT (dg MCT (fnzK B)) (dg B k) :=
    fun k hk => by rw [← dg_nrmK hk, ← dg_nrmK hk, h]
  have hfA := fnzK_lt hA
  have hfB := fnzK_lt hB
  have hcA : dg MCT (fnzK A) < 9 := by rw [mcT_eq _ hfA]; exact mC_lt _ hfA
  have hcB : dg MCT (fnzK B) < 9 := by rw [mcT_eq _ hfB]; exact mC_lt _ hfB
  by_cases zA : dg MCT (fnzK A) = 0
  · have h0 := mcT_zero _ hfA zA
    rw [fnz_zero h0 hp, fnz_zero h0 hq, (mT_zero _ (hB q hq)).1, (mT_zero _ (hB p hp)).1]
  by_cases zB : dg MCT (fnzK B) = 0
  · have h0 := mcT_zero _ hfB zB
    rw [fnz_zero h0 hp, fnz_zero h0 hq, (mT_zero _ (hA q hq)).2, (mT_zero _ (hA p hp)).2]
  set cA := dg MCT (fnzK A)
  set cB := dg MCT (fnzK B)
  have ap := hA p hp
  have aq := hA q hq
  have bp := hB p hp
  have bq := hB q hq
  apply mT_cancel (mT cA cB) (mT_lt _ hcA _ hcB) (mT_nz _ hcA _ hcB zA zB) _ (mT_lt _ ap _ bq) _
    (mT_lt _ aq _ bp)
  rw [mT_rearr _ hcA _ hcB _ ap _ bq, e p hp, ← e q hq, mT_rearr _ hcB _ bp _ hcA _ aq,
    mT_comm _ hcB _ hcA, mT_comm _ bp _ aq]

theorem pairK_spec {W x t : ℕ} (hx : Dig x) (ht : Dig t) (h : pairK W x t = true) :
    eqZ (mulRaw (dec x) (dec t)) (mulRaw (dec t) (dec x)) = Nat.beq W 65535 := by
  rw [mulRaw_dec hx ht, mulRaw_dec ht hx, eqZ_dec (mulK_dig hx ht) (mulK_dig ht hx)]
  unfold pairK at h
  rw [bIf_eq] at h
  by_cases hw : Nat.beq W 65535 = true
  · rw [if_pos hw] at h
    rw [hw]
    unfold commK at h
    rwa [strictB_eq] at h
  · rw [if_neg hw] at h
    rw [Bool.not_eq_true] at hw
    rw [hw]
    obtain ⟨hlt, hc⟩ := bAnd_spec h
    have hW : W < 256 := Eq.mp Nat.blt_eq hlt
    unfold crossK at hc
    simp only [strictB_eq, notK_eq, Bool.not_eq_true'] at hc
    have hp : Nat.div W 16 < 16 := by change W / 16 < 16; omega
    have hq : Nat.mod W 16 < 16 := Nat.mod_lt _ (by norm_num)
    rw [enK_eq _ _ hp, enK_eq _ _ hq, enK_eq _ _ hq, enK_eq _ _ hp] at hc
    apply Bool.eq_false_iff.2
    intro he
    have := cross_of_nrm (mulK_dig hx ht) (mulK_dig ht hx) (Nat.eq_of_beq_eq_true he) hp hq
    rw [this, Nat.beq_refl] at hc
    exact absurd hc (by decide)

theorem conjK_spec {s i j x t : ℕ} (hs : Dig s) (hi : Dig i) (hj : Dig j) (hx : Dig x) (ht : Dig t)
    (h : conjK s i j x t = true) :
    eqZ (mulRaw (dec s) (dec i)) (mulRaw (dec x) (dec s)) = true ∧
      eqZ (mulRaw (dec s) (dec j)) (mulRaw (dec t) (dec s)) = true := by
  unfold conjK at h
  obtain ⟨h1, h2⟩ := bAnd_spec h
  rw [mulRaw_dec hs hi, mulRaw_dec hx hs, mulRaw_dec hs hj, mulRaw_dec ht hs,
    eqZ_dec (mulK_dig hs hi) (mulK_dig hx hs), eqZ_dec (mulK_dig hs hj) (mulK_dig ht hs)]
  exact ⟨h1, h2⟩

theorem digK_spec {P : ℕ} (h : digK P = true) : Dig P := fun j hj => by
  have := allBlk_spec h j hj
  rw [Nat.add_eq, Nat.zero_add] at this
  exact Eq.mp Nat.blt_eq this

theorem tabOfString_ofList (cs : List Char)
    (hd : ((cs.splitOn ' ').filter fun l => !l.isEmpty).all (fun l => l.all Char.isDigit) = true) :
    tabOfString (String.ofList cs) =
      (pairUp (((cs.splitOn ' ').filter fun l => !l.isEmpty).map CFSG.KC.Str.decVal)).toArray := by
  have hs : (" " : String) = String.singleton ' ' := by rw [String.singleton_eq_ofList]
  unfold tabOfString
  rw [hs, CFSG.KC.Str.splitOn_ofList, List.filter_map, List.map_map]
  have hf : List.filter ((fun x => decide (x ≠ "")) ∘ String.ofList) (cs.splitOn ' ') =
      (cs.splitOn ' ').filter fun l => !l.isEmpty := by
    apply List.filter_congr
    intro l _
    simp only [Function.comp, ne_eq, String.ofList_eq_empty_iff]
    cases l <;> rfl
  rw [hf]
  congr 2
  apply List.map_congr_left
  intro l hl
  rw [List.all_eq_true] at hd
  have hl' := List.mem_filter.1 hl
  have hne : l ≠ [] := by
    intro e
    subst e
    exact absurd hl'.2 (by decide)
  have hdig := hd l hl
  rw [List.all_eq_true] at hdig
  exact CFSG.KC.Str.toNat!_ofList hne hdig

end CFSG.KS.U43Pk

end
