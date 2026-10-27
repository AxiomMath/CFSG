module

public import Certificates.Data.SMod20UaData
public import Certificates.Data.Kernel.SmithEKU
public import CFSG.Certificates.Kernel.SmithEK.WSound
public import CFSG.Certificates.Kernel.Spor.PK.F4Code
public import CFSG.Fischer.Polar.Search
public import CFSG.Fischer.Polar.Span
public import CFSG.Sporadic.Th.CertificateChunks
import all CFSG.Fischer.F4

public section

namespace CFSG.SmithE.KU

open CFSG.Fischer CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.SmithE CFSG.SmithE.K

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos tvTabs perpTab

theorem dualK_cons (x : ℕ) (D Y : List ℕ) : dualK (x :: D) Y =
    (Nat.blt (Y.headD 0) 68719476736 && dualRow (decW x) (decW (Y.headD 0)) && dualK D Y.tail) :=
  rfl

theorem dualK_sound : ∀ (D Y : List ℕ), dualK D Y = true →
    ∀ r < D.length, dualRow (decW (D.getD r 0)) (decW (Y.getD r 0)) = true
  | [], _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | x :: D, Y, h, r, hr => by
    rw [dualK_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    cases r with
    | zero => rw [getD_zero, getD_zero]; exact h.1.2
    | succ r =>
      rw [getD_succ, getD_succ Y]
      exact dualK_sound D Y.tail h.2 r (by simp at hr; omega)

theorem keyK_sound {M : List ℕ} {R : ℕ} (h : keyK M R = true) {i j : ℕ} (hi : i < M.length)
    (hj : j < M.length) (he : M.getD i 0 % R = M.getD j 0 % R) : i = j := by
  unfold keyK at h
  have hnd := (nodupK_sound _ 0 h).1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at he
  have hp := List.pairwise_iff_getElem.mp hnd
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd (by rw [List.getElem_map, List.getElem_map]; exact he)
      (hp i j (by simpa using hi) (by simpa using hj) hij)
  · exact hij
  · exact absurd (by rw [List.getElem_map, List.getElem_map]; exact he.symm)
      (hp j i (by simpa using hj) (by simpa using hi) hij)

theorem wMask_of_pin {i x w m : ℕ} (hx : wB i = decW x) (h : pinRow (decW x) w m = true) :
    wMask i = m := by
  unfold pinRow at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold wMask
  rw [vecMask_eq, hx, h.1.2]

@[expose] def f4of (n : ℕ) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by decide)⟩⟩

theorem code_f4of {n : ℕ} (h : n < 4) : (f4of n).code.val = n := Nat.mod_eq_of_lt h

theorem coord_cv (c : ℕ) {i : ℕ} (hi : i < 6) : coord (codeOf (vecOfCode c)) i = coord c i :=
  coord_codeOf (vecOfCode c) ⟨i, hi⟩

theorem scaleC_vec {n : ℕ} (hn : n < 4) (c : ℕ) :
    scaleC n c = codeOf (f4of n • vecOfCode c) := by
  rw [← scaleC_codeOf, code_f4of hn]
  unfold scaleC
  rw [foldl_add_six, foldl_add_six, coord_cv c (by norm_num : 0 < 6),
    coord_cv c (by norm_num : 1 < 6), coord_cv c (by norm_num : 2 < 6),
    coord_cv c (by norm_num : 3 < 6), coord_cv c (by norm_num : 4 < 6),
    coord_cv c (by norm_num : 5 < 6)]

theorem hermC_vec (c d : ℕ) : hermC c d = (hermStd (vecOfCode c) (vecOfCode d)).code.val := by
  rw [← hermC_codeOf]
  unfold hermC
  rw [foldl_xor_six, foldl_xor_six, coord_cv c (by norm_num : 0 < 6),
    coord_cv c (by norm_num : 1 < 6), coord_cv c (by norm_num : 2 < 6),
    coord_cv c (by norm_num : 3 < 6), coord_cv c (by norm_num : 4 < 6),
    coord_cv c (by norm_num : 5 < 6), coord_cv d (by norm_num : 0 < 6),
    coord_cv d (by norm_num : 1 < 6), coord_cv d (by norm_num : 2 < 6),
    coord_cv d (by norm_num : 3 < 6), coord_cv d (by norm_num : 4 < 6),
    coord_cv d (by norm_num : 5 < 6)]

theorem herm0 {c d : ℕ} (h : (hermC c d == 0) = true) :
    hermStd (vecOfCode c) (vecOfCode d) = 0 := by
  rw [beq_iff_eq, hermC_vec] at h
  exact (code_eq_zero_iff _).1 h

theorem hermK0 {c d : ℕ} (h : (CFSG.KC.Misc.T46.hermK c d == 0) = true) :
    hermStd (vecOfCode c) (vecOfCode d) = 0 := by
  rw [CFSG.KS.PK.hermK_eq] at h
  exact herm0 h

theorem hermK1 {c d : ℕ} (h : (CFSG.KC.Misc.T46.hermK c d == 1) = true) :
    hermStd (vecOfCode c) (vecOfCode d) = 1 := by
  rw [beq_iff_eq, CFSG.KS.PK.hermK_eq, hermC_vec] at h
  exact code_inj h

theorem herm_swap0 {x z : Fin 6 → F4} (h : hermStd x z = 0) : hermStd z x = 0 := by
  rw [hermStd_swap, h]
  ring

theorem herm_zero_left (x : Fin 6 → F4) : hermStd 0 x = 0 := by
  unfold hermStd
  simp

@[expose] def wv (W : ℕ × ℕ × ℕ) : Fin 3 → Fin 6 → F4 :=
  ![vecOfCode W.1, vecOfCode W.2.1, vecOfCode W.2.2]

@[expose] def comb (w : Fin 3 → Fin 6 → F4) (c : Fin 3 → F4) : Fin 6 → F4 :=
  c 0 • w 0 + c 1 • w 1 + c 2 • w 2

@[expose] def alv (a : ℕ) : Fin 3 → F4 := ![f4of (a % 4), f4of (a / 4 % 4), f4of (a / 16)]

@[expose] def enc (c : Fin 3 → F4) : ℕ := (c 0).code.val + 4 * (c 1).code.val + 16 * (c 2).code.val

theorem enc_lt (c : Fin 3 → F4) : enc c < 64 := by
  have := code_lt (c 0); have := code_lt (c 1); have := code_lt (c 2)
  unfold enc; omega

theorem alv_enc (c : Fin 3 → F4) : alv (enc c) = c := by
  have h0 := code_lt (c 0); have h1 := code_lt (c 1); have h2 := code_lt (c 2)
  funext a
  apply code_inj
  match a with
  | 0 => change (enc c % 4) % 4 = (c 0).code.val; unfold enc; omega
  | 1 => change (enc c / 4 % 4) % 4 = (c 1).code.val; unfold enc; omega
  | 2 => change (enc c / 16) % 4 = (c 2).code.val; unfold enc; omega

theorem uaVec_eq (W : ℕ × ℕ × ℕ) {a : ℕ} (ha : a < 64) :
    uaVec W a = codeOf (comb (wv W) (alv a)) := by
  unfold uaVec
  rw [scaleC_vec (Nat.mod_lt a (by norm_num : 4 > 0)),
    scaleC_vec (Nat.mod_lt (a / 4) (by norm_num : 4 > 0)), scaleC_vec (by omega : a / 16 < 4),
    ← codeOf_add, ← codeOf_add]
  rfl

theorem foldl_or_testBit (f : ℕ → ℕ) (v : ℕ) : ∀ (l : List ℕ) (s : ℕ),
    (l.foldl (fun acc d => acc ||| 2 ^ f d) s).testBit v = true ↔
      s.testBit v = true ∨ ∃ d ∈ l, f d = v
  | [], s => by simp
  | d :: l, s => by
    rw [List.foldl_cons, foldl_or_testBit f v l, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem vecMask_testBit (W : ℕ × ℕ × ℕ) (v : ℕ) :
    (vecMask W).testBit v = true ↔ ∃ d < 64, uaVec W d = v := by
  have e := foldl_or_testBit (uaVec W) v (List.range 64) 0
  rw [Nat.zero_testBit] at e
  simp only [Bool.false_eq_true, false_or, List.mem_range] at e
  exact e

@[expose] def alK (k : ℕ) : Fin 3 → F4 := alv uaAl[k]!

@[expose] def hm (α : Fin 3 → F4) : Fin 3 → Fin 3 → F4 := fun a b => α a * α b ^ 2

@[expose] def bitS (a : ℕ) : ℕ → Fin 3 → Fin 3 → F4
  | 0 => 0
  | n + 1 => bitS a n + if a.testBit n then hm (alK n) else 0

theorem uaAl_lt : ∀ k < 21, uaAl[k]! < 64 := by decide

theorem alK_ne_zero : ∀ k < 21, alK k ≠ 0 := by decide +kernel

theorem alK_inj : ∀ k < 21, ∀ l < 21, ∀ c : F4, alK l = c • alK k → k = l := by decide +kernel

theorem alK_cover' : ∀ d < 64, alv d ≠ 0 → ∃ k < 21, ∃ e : F4, e ≠ 0 ∧ alv d = e • alK k := by
  decide +kernel

theorem alK_cover {c : Fin 3 → F4} (hc : c ≠ 0) : ∃ k < 21, ∃ e : F4, e ≠ 0 ∧ c = e • alK k := by
  have := alK_cover' (enc c) (enc_lt c)
  rw [alv_enc] at this
  exact this hc

theorem alv_cover (c : Fin 3 → F4) : ∃ d < 64, alv d = c := ⟨enc c, enc_lt c, alv_enc c⟩

theorem alv_zero : alv 0 = 0 := by decide +kernel

theorem alK_basis : alK 0 = ![1, 0, 0] ∧ alK 1 = ![0, 1, 0] ∧ alK 4 = ![0, 0, 1] := by
  decide +kernel

theorem bitS_co : ∀ k < 21, bitS uaCo[k]! 9 = hm (alK k) := by decide +kernel

theorem bitS_ne : ∀ a < 512, a ≠ 0 → bitS a 9 ≠ 0 := by decide +kernel

private theorem cube : ∀ c : F4, c ≠ 0 → c ^ 2 * c = 1 := by decide

section Plane

variable {w y : Fin 3 → Fin 6 → F4}

structure PlaneOK (w y : Fin 3 → Fin 6 → F4) : Prop where
  ww : ∀ a b, hermStd (w a) (w b) = 0
  yy : ∀ a b, hermStd (y a) (y b) = 0
  yw : ∀ a b, hermStd (y a) (w b) = if a = b then 1 else 0

theorem herm_comb_left (c : Fin 3 → F4) (v : Fin 6 → F4) : hermStd (comb w c) v =
    c 0 * hermStd (w 0) v + c 1 * hermStd (w 1) v + c 2 * hermStd (w 2) v := by
  unfold comb
  rw [hermStd_add_left, hermStd_add_left, hermStd_smul_left, hermStd_smul_left, hermStd_smul_left]

theorem herm_comb_right (x : Fin 6 → F4) (c : Fin 3 → F4) : hermStd x (comb w c) =
    c 0 ^ 2 * hermStd x (w 0) + c 1 ^ 2 * hermStd x (w 1) + c 2 ^ 2 * hermStd x (w 2) := by
  unfold comb
  rw [hermStd_add_right, hermStd_add_right, hermStd_smul_right, hermStd_smul_right,
    hermStd_smul_right]

theorem comb_smul (k : F4) (c : Fin 3 → F4) : comb w (k • c) = k • comb w c := by
  unfold comb
  simp only [Pi.smul_apply, smul_eq_mul, smul_add, mul_smul]

theorem comb_zero : comb w 0 = 0 := by
  unfold comb
  simp only [Pi.zero_apply, zero_smul, add_zero]

theorem comb_basis : comb w ![1, 0, 0] = w 0 ∧ comb w ![0, 1, 0] = w 1 ∧
    comb w ![0, 0, 1] = w 2 := by
  unfold comb
  simp

theorem herm_w_y (h : PlaneOK w y) (a b : Fin 3) :
    hermStd (w b) (y a) = if a = b then 1 else 0 := by
  rw [hermStd_swap, h.yw]
  split <;> simp

theorem comb_y (h : PlaneOK w y) (c : Fin 3 → F4) (d : Fin 3) : hermStd (comb w c) (y d) = c d := by
  rw [herm_comb_left, herm_w_y h, herm_w_y h, herm_w_y h]
  fin_cases d <;> simp

theorem comb_w (h : PlaneOK w y) (c : Fin 3 → F4) (b : Fin 3) : hermStd (comb w c) (w b) = 0 := by
  rw [herm_comb_left, h.ww, h.ww, h.ww]
  simp

theorem combY_w (h : PlaneOK w y) (d : Fin 3 → F4) (b : Fin 3) :
    hermStd (comb y d) (w b) = d b := by
  rw [herm_comb_left, h.yw, h.yw, h.yw]
  fin_cases b <;> simp

theorem combY_y (h : PlaneOK w y) (d : Fin 3 → F4) (b : Fin 3) : hermStd (comb y d) (y b) = 0 := by
  rw [herm_comb_left, h.yy, h.yy, h.yy]
  simp

theorem comb_iso (h : PlaneOK w y) (c c' : Fin 3 → F4) : hermStd (comb w c) (comb w c') = 0 := by
  rw [herm_comb_left, herm_comb_right, herm_comb_right, herm_comb_right]
  simp [h.ww]

theorem comb_inj (h : PlaneOK w y) {c c' : Fin 3 → F4} (e : comb w c = comb w c') : c = c' := by
  funext d
  have e' : hermStd (comb w c) (y d) = hermStd (comb w c') (y d) := by rw [e]
  rwa [comb_y h, comb_y h] at e'

theorem exists_comb (h : PlaneOK w y) (x : Fin 6 → F4) (hx : ∀ b, hermStd x (w b) = 0) :
    ∃ c, x = comb w c := by
  let F : (Fin 3 → F4) × (Fin 3 → F4) → (Fin 6 → F4) := fun p => comb w p.1 + comb y p.2
  have hy' : ∀ p d, hermStd (F p) (y d) = p.1 d := fun p d => by
    simp only [F]
    rw [hermStd_add_left, comb_y h, combY_y h, add_zero]
  have hw' : ∀ p b, hermStd (F p) (w b) = p.2 b := fun p b => by
    simp only [F]
    rw [hermStd_add_left, comb_w h, combY_w h, zero_add]
  have hinj : Function.Injective F := by
    intro p q e
    refine Prod.ext (funext fun d => ?_) (funext fun b => ?_)
    · rw [← hy' p d, ← hy' q d, e]
    · rw [← hw' p b, ← hw' q b, e]
  have hbij := (Fintype.bijective_iff_injective_and_card F).2
    ⟨hinj, by simp [Fintype.card_prod, Fintype.card_fun, F4.card]⟩
  obtain ⟨⟨c, d⟩, hp⟩ := hbij.2 x
  have hd : d = 0 := funext fun b => by
    have := hw' (c, d) b
    rw [hp, hx] at this
    exact this.symm
  refine ⟨c, ?_⟩
  rw [← hp]
  simp only [F, hd, comb_zero, add_zero]

@[expose] def nmap (w : Fin 3 → Fin 6 → F4) (H : Fin 3 → Fin 3 → F4) (x : Fin 6 → F4) :
    Fin 6 → F4 :=
  comb w fun a => H a 0 * hermStd x (w 0) + H a 1 * hermStd x (w 1) + H a 2 * hermStd x (w 2)

@[expose] def am (w : Fin 3 → Fin 6 → F4) (H : Fin 3 → Fin 3 → F4) (x : Fin 6 → F4) :
    Fin 6 → F4 :=
  x + nmap w H x

theorem nmap_hm (α : Fin 3 → F4) (x : Fin 6 → F4) :
    hermStd x (comb w α) • comb w α = nmap w (hm α) x := by
  rw [herm_comb_right]
  unfold nmap comb hm
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem nmap_addH (H H' : Fin 3 → Fin 3 → F4) (x : Fin 6 → F4) :
    nmap w (H + H') x = nmap w H x + nmap w H' x := by
  unfold nmap comb
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem nmap_zeroH (x : Fin 6 → F4) : nmap w 0 x = 0 := by
  unfold nmap comb
  funext i
  simp

theorem nmap_add (H : Fin 3 → Fin 3 → F4) (x x' : Fin 6 → F4) :
    nmap w H (x + x') = nmap w H x + nmap w H x' := by
  unfold nmap comb
  simp only [hermStd_add_left]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem nmap_smul (H : Fin 3 → Fin 3 → F4) (k : F4) (x : Fin 6 → F4) :
    nmap w H (k • x) = k • nmap w H x := by
  unfold nmap comb
  simp only [hermStd_smul_left]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem nmap_nmap (h : PlaneOK w y) (H H' : Fin 3 → Fin 3 → F4) (x : Fin 6 → F4) :
    nmap w H (nmap w H' x) = 0 := by
  have e : ∀ b, hermStd (nmap w H' x) (w b) = 0 := fun b => comb_w h _ b
  have hd : nmap w H (nmap w H' x) = comb w fun a => H a 0 * hermStd (nmap w H' x) (w 0) +
      H a 1 * hermStd (nmap w H' x) (w 1) + H a 2 * hermStd (nmap w H' x) (w 2) := rfl
  rw [hd, e, e, e]
  unfold comb
  funext i
  simp

theorem nmap_y (h : PlaneOK w y) (H : Fin 3 → Fin 3 → F4) (d : Fin 3) :
    nmap w H (y d) = comb w fun a => H a d := by
  unfold nmap
  rw [h.yw, h.yw, h.yw]
  congr 1
  funext a
  fin_cases d <;> simp

theorem am_smul (H : Fin 3 → Fin 3 → F4) (k : F4) (x : Fin 6 → F4) :
    am w H (k • x) = k • am w H x := by
  unfold am
  rw [nmap_smul, smul_add]

end Plane

section Points

variable {w y : Fin 3 → Fin 6 → F4}

theorem smul_of_ptIdx_eq' {u v : Fin 6 → F4} (hv : v ≠ 0) (hvi : hermStd v v = 0)
    (h : ptIdx u = ptIdx v) : ∃ c : F4, c ≠ 0 ∧ u = c • v := by
  have hmv := normC_mem ptsFacts hv hvi
  have hlt := ptIdx_lt ptsFacts hv hvi
  unfold ptIdx at h hlt
  have hlt' : uPts.toList.idxOf (normC (codeOf u)) < uPts.toList.length := by
    rw [h, Array.length_toList, ptsFacts.size]
    exact hlt
  have hmu : normC (codeOf u) ∈ uPts.toList := List.idxOf_lt_length_iff.1 hlt'
  have e : normC (codeOf u) = normC (codeOf v) :=
    (List.idxOf_inj hmu).1 h
  rw [normC_codeOf, normC_codeOf] at e
  have e' := codeOf_injective e
  obtain ⟨b, hb, hbv⟩ := normV_eq_smul hv
  have hu : u ≠ 0 := by
    rintro rfl
    have h0 : normV (0 : Fin 6 → F4) = 0 := by
      unfold normV
      simp
    rw [h0, hbv] at e'
    exact smul_ne_zero hb hv e'.symm
  obtain ⟨a, ha, hau⟩ := normV_eq_smul hu
  refine ⟨a⁻¹ * b, mul_ne_zero (inv_ne_zero ha) hb, ?_⟩
  rw [mul_smul, ← hbv, ← e', hau, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem ap_tv {p x : ℕ} (hp : p < 693) (hx : x < 693) :
    ap tvTabs[p]! x = ptIdx (uVec x + hermStd (uVec x) (uVec p) • uVec p) := by
  have e : tvTabs[p]! = tvTable uPts[p]! := tvTabs_get ⟨p, hp⟩
  rw [e]
  unfold ptIdx
  refine ap_tvTable _ hx ?_ (by rw [normC_codeOf]; exact codeOf_lt _)
  rw [← codeOf_uVec ptsFacts hp, ← codeOf_uVec ptsFacts hx, tvC_codeOf]

theorem tv_ne_zero_iso {u v : Fin 6 → F4} (hv : hermStd v v = 0) (hu : u ≠ 0)
    (hui : hermStd u u = 0) :
    u + hermStd u v • v ≠ 0 ∧ hermStd (u + hermStd u v • v) (u + hermStd u v • v) = 0 := by
  have hw := mulVec_ne_zero (tvGL v hv) hu
  rw [tvGL_val, tvM_mulVec] at hw
  refine ⟨hw, ?_⟩
  have := isIsom_tvM hv u u
  rwa [herm_eq_std, herm_eq_std, tvM_mulVec, hui] at this

theorem pt_eq {i k : ℕ} (hi : i < 891) (hk : k < 21) :
    (uaPts[i]!)[k]! = ptIdx (comb (wv (wB i)) (alK k)) := by
  unfold uaPts
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hi, CFSG.SmithL6.Kernel.ofFn_get! _ hk]
  unfold uaPt alK
  rw [uaVec_eq _ (uaAl_lt k hk)]
  exact uPos_normC _

theorem pts_size {i : ℕ} (hi : i < 891) : (uaPts[i]!).size = 21 := by
  unfold uaPts
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hi]
  exact Array.size_ofFn

theorem uaPts_size : uaPts.size = 891 := by
  unfold uaPts
  exact Array.size_ofFn

theorem uaMem_iff {i : ℕ} (hi : i < 891) (q : ℕ) :
    uaMem uaPts[i]! q = true ↔ ∃ k < 21, ptIdx (comb (wv (wB i)) (alK k)) = q := by
  unfold uaMem
  rw [anyIn_eq_true]
  refine exists_congr fun k => and_congr_right fun hk => ?_
  rw [beq_iff_eq, pt_eq hi hk]

theorem vk_ne (h : PlaneOK w y) {k : ℕ} (hk : k < 21) : comb w (alK k) ≠ 0 := fun e =>
  alK_ne_zero k hk (comb_inj h (e.trans comb_zero.symm))

theorem uVec_vk (h : PlaneOK w y) {k : ℕ} (hk : k < 21) :
    ∃ μ : F4, μ ≠ 0 ∧ uVec (ptIdx (comb w (alK k))) = μ • comb w (alK k) := by
  rw [uVec_ptIdx ptsFacts (vk_ne h hk) (comb_iso h _ _)]
  exact normV_eq_smul (vk_ne h hk)

theorem pt_lt (h : PlaneOK w y) {k : ℕ} (hk : k < 21) : ptIdx (comb w (alK k)) < 693 :=
  ptIdx_lt ptsFacts (vk_ne h hk) (comb_iso h _ _)

theorem pt_inj (h : PlaneOK w y) {k l : ℕ} (hk : k < 21) (hl : l < 21)
    (e : ptIdx (comb w (alK k)) = ptIdx (comb w (alK l))) : k = l := by
  obtain ⟨c, -, hce⟩ := smul_of_ptIdx_eq' (vk_ne h hl) (comb_iso h _ _) e
  rw [← comb_smul] at hce
  exact (alK_inj l hl k hk c (comb_inj h hce)).symm

theorem tv_pt (h : PlaneOK w y) {k x : ℕ} (hk : k < 21) (hx : x < 693) :
    ap tvTabs[ptIdx (comb w (alK k))]! x = ptIdx (am w (hm (alK k)) (uVec x)) := by
  rw [ap_tv (pt_lt h hk) hx]
  obtain ⟨μ, hμ, eμ⟩ := uVec_vk h hk
  rw [eμ, hermStd_smul_right, smul_smul, mul_comm (μ ^ 2), mul_assoc, cube μ hμ, mul_one,
    nmap_hm]
  rfl

theorem uaAp_eq {i : ℕ} (hi : i < 891) (h : PlaneOK (wv (wB i)) y) (a : ℕ) :
    ∀ n ≤ 21, ∀ u : Fin 6 → F4, u ≠ 0 → hermStd u u = 0 →
      uaAp tvTabs uaPts[i]! a n (ptIdx u) = ptIdx (am (wv (wB i)) (bitS a n) u)
  | 0, _, u, _, _ => by
    simp only [uaAp, bitS, am, nmap_zeroH, add_zero]
  | n + 1, hn, u, hu, hui => by
    simp only [uaAp, bitS]
    by_cases hb : a.testBit n = true
    · rw [if_pos hb, if_pos hb]
      have hk : n < 21 := by omega
      obtain ⟨hne, hiso⟩ := tv_ne_zero_iso (comb_iso h (alK n) (alK n)) hu hui
      have e1 : ap tvTabs[(uaPts[i]!)[n]!]! (ptIdx u) = ptIdx (u + hermStd u
          (comb (wv (wB i)) (alK n)) • comb (wv (wB i)) (alK n)) := by
        rw [pt_eq hi hk, tv_pt h hk (ptIdx_lt ptsFacts hu hui), uVec_ptIdx ptsFacts hu hui]
        obtain ⟨c, hc, hcu⟩ := normV_eq_smul hu
        rw [hcu, am_smul, ptIdx_smul hc, am, nmap_hm]
      rw [e1, uaAp_eq hi h a n (by omega) _ hne hiso, nmap_hm]
      congr 1
      unfold am
      rw [nmap_add, nmap_nmap h, nmap_addH]
      abel
    · rw [if_neg hb, if_neg hb, add_zero]
      exact uaAp_eq hi h a n (by omega) u hu hui

theorem uaAp_pt {i : ℕ} (hi : i < 891)
    (h : PlaneOK (wv (wB i)) y) (a : ℕ) {x : ℕ} (hx : x < 693) :
    uaAp tvTabs uaPts[i]! a 9 x = ptIdx (am (wv (wB i)) (bitS a 9) (uVec x)) := by
  have e := uaAp_eq hi h a 9 (by norm_num) (uVec x) (uVec_ne_zero ptsFacts hx)
    (uVec_iso ptsFacts hx)
  rwa [ptIdx_uVec ptsFacts hx] at e

theorem pt_perp {p q : ℕ} (hp : p < 693) (hq : q < 693) :
    ((perpTab ())[p]!)[q]! = true ↔ hermStd (uVec p) (uVec q) = 0 :=
  perpTab_spec ⟨p, hp⟩ ⟨q, hq⟩

theorem planeOK_of {i : ℕ} (hi : i < 891)
    (h : PlaneOK (wv (wB i)) y) : uaPlaneOK (perpTab ()) tvTabs uaPts[i]! = true := by
  have hP : ∀ k < 21, (uaPts[i]!)[k]! = ptIdx (comb (wv (wB i)) (alK k)) := fun k hk => pt_eq hi hk
  have hlt : ∀ k < 21, (uaPts[i]!)[k]! < 693 := fun k hk => by rw [hP k hk]; exact pt_lt h hk
  have hA : (uaPts[i]!.size == 21) = true := by rw [beq_iff_eq]; exact pts_size hi
  have hB : allIn 0 21 (fun k => decide ((uaPts[i]!)[k]! < 693)) = true :=
    allIn_eq_true.2 fun k _ hk => decide_eq_true (hlt k hk)
  have hC : allIn 0 21 (fun k => allIn 0 21 fun l =>
      k == l || (uaPts[i]!)[k]! != (uaPts[i]!)[l]!) = true := by
    refine allIn_eq_true.2 fun k _ hk => allIn_eq_true.2 fun l _ hl => ?_
    rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
    by_cases hkl : k = l
    · exact Or.inl hkl
    · refine Or.inr fun e => hkl ?_
      rw [hP k hk, hP l hl] at e
      exact pt_inj h hk hl e
  have hD : allIn 0 21 (fun k => allIn 0 21 fun l =>
      ((perpTab ())[(uaPts[i]!)[k]!]!)[(uaPts[i]!)[l]!]!) = true := by
    refine allIn_eq_true.2 fun k _ hk => allIn_eq_true.2 fun l _ hl => ?_
    rw [pt_perp (hlt k hk) (hlt l hl), hP k hk, hP l hl]
    obtain ⟨μ, -, eμ⟩ := uVec_vk h hk
    obtain ⟨ν, -, eν⟩ := uVec_vk h hl
    rw [eμ, eν, hermStd_smul_left, hermStd_smul_right, comb_iso h, mul_zero, mul_zero]
  have hE : allIn 0 693 (fun q => !(allIn 0 21 fun k => ((perpTab ())[(uaPts[i]!)[k]!]!)[q]!) ||
      uaMem uaPts[i]! q) = true := by
    refine allIn_eq_true.2 fun q _ hq => ?_
    cases hall : allIn 0 21 (fun k => ((perpTab ())[(uaPts[i]!)[k]!]!)[q]!) with
    | false => rfl
    | true =>
      rw [Bool.not_true, Bool.false_or]
      have hk := allIn_eq_true.1 hall
      have hpk : ∀ k < 21, hermStd (uVec q) (comb (wv (wB i)) (alK k)) = 0 := fun k hk' => by
        have e := (pt_perp (hlt k hk') hq).1 (hk k (Nat.zero_le _) hk')
        rw [hP k hk'] at e
        obtain ⟨μ, hμ, eμ⟩ := uVec_vk h hk'
        rw [eμ, hermStd_smul_left] at e
        exact herm_swap0 ((mul_eq_zero.1 e).resolve_left hμ)
      have hxw : ∀ b, hermStd (uVec q) (wv (wB i) b) = 0 := by
        have h0 := hpk 0 (by norm_num)
        have h1 := hpk 1 (by norm_num)
        have h4 := hpk 4 (by norm_num)
        rw [alK_basis.1, comb_basis.1] at h0
        rw [alK_basis.2.1, comb_basis.2.1] at h1
        rw [alK_basis.2.2, comb_basis.2.2] at h4
        intro b
        match b with
        | 0 => exact h0
        | 1 => exact h1
        | 2 => exact h4
      obtain ⟨c, hc⟩ := exists_comb h (uVec q) hxw
      have hc0 : c ≠ 0 := fun e => uVec_ne_zero ptsFacts hq (by rw [hc, e, comb_zero])
      obtain ⟨k, hk, e, he, hce⟩ := alK_cover hc0
      rw [uaMem_iff hi]
      refine ⟨k, hk, ?_⟩
      rw [← ptIdx_uVec ptsFacts hq, hc, hce, comb_smul, ptIdx_smul he]
  have hF : allIn 0 21 (fun k => allIn 0 693 fun x =>
      uaAp tvTabs uaPts[i]! uaCo[k]! 9 x == ap (tvTabs[(uaPts[i]!)[k]!]!) x) = true := by
    refine allIn_eq_true.2 fun k _ hk => allIn_eq_true.2 fun x _ hx => ?_
    rw [beq_iff_eq, uaAp_pt hi h _ hx, bitS_co k hk, hP k hk, tv_pt h hk hx]
  have hG : allIn 1 512 (fun a => anyIn 693 fun x => uaAp tvTabs uaPts[i]! a 9 x != x) = true := by
    refine allIn_eq_true.2 fun a ha1 ha2 => anyIn_eq_true.2 ?_
    have hS := bitS_ne a ha2 (by omega)
    obtain ⟨a', d, had⟩ : ∃ a' d, bitS a 9 a' d ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hS (funext fun a' => funext fun d => hc a' d)
    have hyd : y d ≠ 0 := fun e => by
      have := h.yw d d
      rw [if_pos rfl, e, herm_zero_left] at this
      exact zero_ne_one this
    have hydi := h.yy d d
    refine ⟨ptIdx (y d), ptIdx_lt ptsFacts hyd hydi, ?_⟩
    rw [bne_iff_ne]
    intro e
    rw [uaAp_eq hi h a 9 (by norm_num) (y d) hyd hydi] at e
    obtain ⟨c, -, hce⟩ := smul_of_ptIdx_eq' hyd hydi e
    unfold am at hce
    rw [nmap_y h] at hce
    have e1 : hermStd (y d + comb (wv (wB i)) fun b => bitS a 9 b d) (wv (wB i) d) =
        hermStd (c • y d) (wv (wB i) d) := by rw [hce]
    rw [hermStd_add_left, comb_w h, add_zero, hermStd_smul_left, h.yw, if_pos rfl,
      mul_one] at e1
    have e2 : y d + (comb (wv (wB i)) fun b => bitS a 9 b d) = y d + 0 := by
      rw [hce, ← e1, one_smul, add_zero]
    have e3 := comb_inj h ((add_left_cancel e2).trans comb_zero.symm)
    exact had (congrFun e3 a')
  unfold uaPlaneOK
  simp only [hA, hB, hC, hD, hE, hF, hG, Bool.and_self]

theorem mask_iff {i : ℕ} (h : PlaneOK (wv (wB i)) y) {q : ℕ} (hq : q < 693) :
    (wMask i).testBit uPts[q]! = true ↔ ∃ k < 21, ptIdx (comb (wv (wB i)) (alK k)) = q := by
  unfold wMask
  rw [vecMask_testBit, ← codeOf_uVec ptsFacts hq]
  constructor
  · rintro ⟨d, hd, e⟩
    rw [uaVec_eq _ hd] at e
    have e' := codeOf_injective e
    have hd0 : alv d ≠ 0 := fun h0 => uVec_ne_zero ptsFacts hq (by rw [← e', h0, comb_zero])
    obtain ⟨k, hk, c, hc, hce⟩ := alK_cover hd0
    refine ⟨k, hk, ?_⟩
    rw [← ptIdx_uVec ptsFacts hq, ← e', hce, comb_smul, ptIdx_smul hc]
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨μ, -, eμ⟩ := uVec_vk h hk
    obtain ⟨d, hd, hdv⟩ := alv_cover (μ • alK k)
    refine ⟨d, hd, ?_⟩
    rw [uaVec_eq _ hd, hdv, comb_smul, eμ]

theorem hypOK : uaHypOK (perpTab ()) tvTabs = true := by
  unfold uaHypOK
  refine allIn_eq_true.2 fun p _ hp => allIn_eq_true.2 fun q _ hq => ?_
  rw [Bool.or_eq_true]
  by_cases hpq : ((perpTab ())[p]!)[q]! = true
  · exact Or.inl hpq
  right
  have hc : hermStd (uVec q) (uVec p) ≠ 0 := fun e => hpq ((pt_perp hp hq).2 (herm_swap0 e))
  obtain ⟨hz, hzi⟩ := tv_ne_zero_iso (uVec_iso ptsFacts hp) (uVec_ne_zero ptsFacts hq)
    (uVec_iso ptsFacts hq)
  rw [ap_tv hp hq, Bool.not_eq_true', Bool.eq_false_iff]
  intro e
  rw [pt_perp hq (ptIdx_lt ptsFacts hz hzi), uVec_ptIdx ptsFacts hz hzi] at e
  obtain ⟨l, hl, hle⟩ := normV_eq_smul hz
  rw [hle, hermStd_smul_right, hermStd_add_right, hermStd_smul_right, uVec_iso ptsFacts hq,
    zero_add, cube _ hc, mul_one] at e
  exact hl ((pow_eq_zero_iff (by norm_num)).1 e)

theorem maskOK (hpl : ∀ i < 891, ∃ y, PlaneOK (wv (wB i)) y) : uaMaskOK uaPts = true := by
  unfold uaMaskOK
  refine allIn_eq_true.2 fun i _ hi => allIn_eq_true.2 fun q _ hq => ?_
  obtain ⟨y, h⟩ := hpl i hi
  rw [beq_iff_eq, maskArr_get hi]
  apply Bool.eq_iff_iff.2
  rw [mask_iff h hq, uaMem_iff hi]

theorem mask_incl {i j : ℕ} {yi yj : Fin 3 → Fin 6 → F4} (hpi : PlaneOK (wv (wB i)) yi)
    (hpj : PlaneOK (wv (wB j)) yj)
    (hsub : ∀ k < 21, ∃ l < 21, ptIdx (comb (wv (wB j)) (alK l)) = ptIdx (comb (wv (wB i)) (alK k)))
    (v : ℕ) (hv : (wMask i).testBit v = true) : (wMask j).testBit v = true := by
  unfold wMask at hv ⊢
  rw [vecMask_testBit] at hv ⊢
  obtain ⟨d, hd, rfl⟩ := hv
  rw [uaVec_eq _ hd]
  by_cases hd0 : alv d = 0
  · refine ⟨0, by norm_num, ?_⟩
    rw [uaVec_eq (wB j) (by norm_num : (0 : ℕ) < 64), hd0, alv_zero, comb_zero, comb_zero]
  obtain ⟨k, hk, c, -, hce⟩ := alK_cover hd0
  obtain ⟨l, hl, hkl⟩ := hsub k hk
  obtain ⟨μ, hμ, eμ⟩ := uVec_vk hpi hk
  obtain ⟨ν, -, eν⟩ := uVec_vk hpj hl
  have e : comb (wv (wB i)) (alK k) = (μ⁻¹ * ν) • comb (wv (wB j)) (alK l) := by
    rw [mul_smul, ← eν, hkl, eμ, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  obtain ⟨d', hd', hdv⟩ := alv_cover ((c * (μ⁻¹ * ν)) • alK l)
  refine ⟨d', hd', ?_⟩
  rw [uaVec_eq _ hd', hdv, hce, comb_smul, comb_smul, e, smul_smul]

theorem mask_eq {i j : ℕ} {yi yj : Fin 3 → Fin 6 → F4} (hpi : PlaneOK (wv (wB i)) yi)
    (hpj : PlaneOK (wv (wB j)) yj)
    (hsub : ∀ k < 21, ∃ l < 21, ptIdx (comb (wv (wB j)) (alK l)) = ptIdx (comb (wv (wB i)) (alK k))) :
    wMask i = wMask j := by
  have hcard : ∀ {i' : ℕ} {y' : Fin 3 → Fin 6 → F4}, PlaneOK (wv (wB i')) y' →
      ((Finset.range 21).image fun k => ptIdx (comb (wv (wB i')) (alK k))).card = 21 := by
    intro i' y' h
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl e
    exact pt_inj h (Finset.mem_range.1 hk) (Finset.mem_range.1 hl) e
  have hss : ((Finset.range 21).image fun k => ptIdx (comb (wv (wB i)) (alK k))) ⊆
      ((Finset.range 21).image fun k => ptIdx (comb (wv (wB j)) (alK k))) := by
    intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨l, hl, e⟩ := hsub k (Finset.mem_range.1 hk)
    exact ⟨l, Finset.mem_range.2 hl, e⟩
  have heq := Finset.eq_of_subset_of_card_le hss (by rw [hcard hpi, hcard hpj])
  have hsub' : ∀ l < 21, ∃ k < 21,
      ptIdx (comb (wv (wB i)) (alK k)) = ptIdx (comb (wv (wB j)) (alK l)) := by
    intro l hl
    have hm : ptIdx (comb (wv (wB j)) (alK l)) ∈
        ((Finset.range 21).image fun k => ptIdx (comb (wv (wB j)) (alK k))) :=
      Finset.mem_image.2 ⟨l, Finset.mem_range.2 hl, rfl⟩
    rw [← heq, Finset.mem_image] at hm
    obtain ⟨k, hk, e⟩ := hm
    exact ⟨k, Finset.mem_range.1 hk, e⟩
  apply Nat.eq_of_testBit_eq
  intro v
  apply Bool.eq_iff_iff.2
  exact ⟨mask_incl hpi hpj hsub v, mask_incl hpj hpi hsub' v⟩

theorem distinctOK (hpl : ∀ i < 891, ∃ y, PlaneOK (wv (wB i)) y)
    (hkey : ∀ i < 891, ∀ j < 891, wMask i = wMask j → i = j) : uaDistinctOK uaPts = true := by
  unfold uaDistinctOK
  refine allIn_eq_true.2 fun i _ hi => allIn_eq_true.2 fun j _ hj => ?_
  rw [Bool.or_eq_true, beq_iff_eq]
  by_cases hij : i = j
  · exact Or.inl hij
  right
  by_contra hc
  obtain ⟨yi, hpi⟩ := hpl i hi
  obtain ⟨yj, hpj⟩ := hpl j hj
  have hsub : ∀ k < 21, ∃ l < 21,
      ptIdx (comb (wv (wB j)) (alK l)) = ptIdx (comb (wv (wB i)) (alK k)) := fun k hk => by
    by_contra hn
    apply hc
    refine anyIn_eq_true.2 ⟨k, hk, ?_⟩
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hm
    rw [pt_eq hi hk, uaMem_iff hj] at hm
    exact hn hm
  exact hij (hkey i hi j hj (mask_eq hpi hpj hsub))

theorem planeOK_of_checks {i : ℕ} {Y : ℕ × ℕ × ℕ} (hm : modelOK i = true)
    (hd : dualRow (wB i) Y = true) : PlaneOK (wv (wB i)) (wv Y) := by
  unfold modelOK at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h11, h22⟩, h33⟩, h12⟩, h13⟩, h23⟩, -⟩, -⟩, -⟩, -⟩ := hm
  unfold dualRow at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨y11, y22⟩, y33⟩, y12⟩, y13⟩, y23⟩, a11⟩, a12⟩, a13⟩, a21⟩, a22⟩, a23⟩,
    a31⟩, a32⟩, a33⟩ := hd
  have w11 : hermStd (wv (wB i) 0) (wv (wB i) 0) = 0 := herm0 h11
  have w22 : hermStd (wv (wB i) 1) (wv (wB i) 1) = 0 := herm0 h22
  have w33 : hermStd (wv (wB i) 2) (wv (wB i) 2) = 0 := herm0 h33
  have w12 : hermStd (wv (wB i) 0) (wv (wB i) 1) = 0 := herm0 h12
  have w13 : hermStd (wv (wB i) 0) (wv (wB i) 2) = 0 := herm0 h13
  have w23 : hermStd (wv (wB i) 1) (wv (wB i) 2) = 0 := herm0 h23
  have z11 : hermStd (wv Y 0) (wv Y 0) = 0 := hermK0 y11
  have z22 : hermStd (wv Y 1) (wv Y 1) = 0 := hermK0 y22
  have z33 : hermStd (wv Y 2) (wv Y 2) = 0 := hermK0 y33
  have z12 : hermStd (wv Y 0) (wv Y 1) = 0 := hermK0 y12
  have z13 : hermStd (wv Y 0) (wv Y 2) = 0 := hermK0 y13
  have z23 : hermStd (wv Y 1) (wv Y 2) = 0 := hermK0 y23
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · match a, b with
    | 0, 0 => exact w11
    | 0, 1 => exact w12
    | 0, 2 => exact w13
    | 1, 0 => exact herm_swap0 w12
    | 1, 1 => exact w22
    | 1, 2 => exact w23
    | 2, 0 => exact herm_swap0 w13
    | 2, 1 => exact herm_swap0 w23
    | 2, 2 => exact w33
  · match a, b with
    | 0, 0 => exact z11
    | 0, 1 => exact z12
    | 0, 2 => exact z13
    | 1, 0 => exact herm_swap0 z12
    | 1, 1 => exact z22
    | 1, 2 => exact z23
    | 2, 0 => exact herm_swap0 z13
    | 2, 1 => exact herm_swap0 z23
    | 2, 2 => exact z33
  · match a, b with
    | 0, 0 => exact hermK1 a11
    | 0, 1 => exact hermK0 a12
    | 0, 2 => exact hermK0 a13
    | 1, 0 => exact hermK0 a21
    | 1, 1 => exact hermK1 a22
    | 1, 2 => exact hermK0 a23
    | 2, 0 => exact hermK0 a31
    | 2, 1 => exact hermK0 a32
    | 2, 2 => exact hermK1 a33

theorem chkUA_of (Y : ℕ → ℕ)
    (hmodel : ∀ i < 891, modelOK i = true) (hdual : ∀ i < 891, dualRow (wB i) (decW (Y i)) = true)
    (hkey : ∀ i < 891, ∀ j < 891, wMask i = wMask j → i = j) : chkUA () = true := by
  have hpl : ∀ i < 891, PlaneOK (wv (wB i)) (wv (decW (Y i))) := fun i hi =>
    planeOK_of_checks (hmodel i hi) (hdual i hi)
  have hpl' : ∀ i < 891, ∃ y, PlaneOK (wv (wB i)) y := fun i hi => ⟨_, hpl i hi⟩
  have e : chkUA () = (uaPts.size == 891 &&
      parAll 891 7 (fun i => uaPlaneOK (perpTab ()) tvTabs uaPts[i]!) &&
      uaHypOK (perpTab ()) tvTabs && uaDistinctOK uaPts && uaMaskOK uaPts) := rfl
  have hA : (uaPts.size == 891) = true := by rw [beq_iff_eq]; exact uaPts_size
  simp only [e, hA, parAll_eq_true_of (fun i hi => planeOK_of hi (hpl i hi)), hypOK,
    distinctOK hpl' hkey, maskOK hpl', Bool.and_self]

end Points

end CFSG.SmithE.KU
