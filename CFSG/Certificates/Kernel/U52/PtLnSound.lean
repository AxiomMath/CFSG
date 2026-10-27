module

public import Certificates.Data.Kernel.U52.PtLn
public import CFSG.Certificates.Kernel.TreeKSound
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs3
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.U52.PackEq

public section

namespace CFSG.KC.U52PL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.ASVolI

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem beq_t {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem bIf_ite (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem f2_eq (p j : Nat) : f2 p j = p / 4 ^ j % 4 := by
  unfold f2 pg
  change (p >>> (2 * j)) &&& mask 2 = _
  rw [PackFld.mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem f2_lt (p j : Nat) : f2 p j < 4 := by
  rw [f2_eq]
  omega

theorem mulK_lt (a b : Nat) : mulK a b < 4 := by
  unfold mulK
  change _ &&& 3 < 4
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem mulK_eq : ∀ a < 4, ∀ b < 4, mulK a b = burnsideF48t_gf4Mul a b := by
  decide +kernel

theorem sq_eq : ∀ a < 4, mulK a a = burnsideF48t_gf4Sq a := by
  decide +kernel

theorem mulK_one : ∀ b < 4, mulK 1 b = b := by
  decide +kernel

theorem xor_lt {a b : Nat} (ha : a < 4) (hb : b < 4) : Nat.xor a b < 4 :=
  Nat.xor_lt_two_pow (n := 2) ha hb

theorem dotK_lt (a b : Nat) : dotK a b < 4 := by
  unfold dotK
  exact xor_lt (xor_lt (xor_lt (xor_lt (mulK_lt _ _) (mulK_lt _ _)) (mulK_lt _ _)) (mulK_lt _ _))
    (mulK_lt _ _)

theorem f2_mk5 {a b c d e : Nat} (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (he : e < 4) :
    f2 (mk5 a b c d e) 0 = a ∧ f2 (mk5 a b c d e) 1 = b ∧ f2 (mk5 a b c d e) 2 = c ∧
      f2 (mk5 a b c d e) 3 = d ∧ f2 (mk5 a b c d e) 4 = e ∧ mk5 a b c d e >>> 10 = 0 := by
  simp only [f2_eq, mk5, Nat.shiftRight_eq_div_pow]
  change (a + 4 * (b + 4 * (c + 4 * (d + 4 * e)))) / 4 ^ 0 % 4 = a ∧ _
  norm_num
  omega

theorem eq_mk5 {x : Nat} (hx : x >>> 10 = 0) :
    x = mk5 (f2 x 0) (f2 x 1) (f2 x 2) (f2 x 3) (f2 x 4) := by
  rw [Nat.shiftRight_eq_div_pow] at hx
  simp only [f2_eq, mk5]
  change x = x / 4 ^ 0 % 4 + 4 * (x / 4 ^ 1 % 4 + 4 * (x / 4 ^ 2 % 4 + 4 * (x / 4 ^ 3 % 4 +
    4 * (x / 4 ^ 4 % 4))))
  norm_num at hx ⊢
  omega

theorem f2_ext {x y : Nat} (hx : x >>> 10 = 0) (hy : y >>> 10 = 0)
    (h : ∀ j < 5, f2 x j = f2 y j) : x = y := by
  rw [eq_mk5 hx, eq_mk5 hy, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
    h 3 (by norm_num), h 4 (by norm_num)]

theorem unpack_f2 (x : Nat) {j : Nat} (hj : j < 5) : (unpack 5 2 x)[j]! = f2 x j := by
  rw [CFSG.KS.WordF.getElem!_unpack, if_pos hj]
  rfl

theorem unpack_f8 (q : Nat) {a : Nat} (ha : a < 5) : (unpack 5 8 q)[a]! = f8 q a := by
  rw [CFSG.KS.WordF.getElem!_unpack, if_pos ha]
  rfl

theorem unpack_size5 (w x : Nat) : (unpack 5 w x).size = 5 := by
  simp [unpack]

private theorem ofFn5 (f : Fin 5 → Nat) {j : Nat} (hj : j < 5) :
    (Array.ofFn (n := 5) f)[j]! = f ⟨j, hj⟩ := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

private theorem f2_mk5_get {g : Nat → Nat} (hg : ∀ j, g j < 4) {j : Nat} (hj : j < 5) :
    f2 (mk5 (g 0) (g 1) (g 2) (g 3) (g 4)) j = g j := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := f2_mk5 (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  interval_cases j
  exacts [e0, e1, e2, e3, e4]

theorem mk5_canon {g : Nat → Nat} (hg : ∀ j, g j < 4) :
    mk5 (g 0) (g 1) (g 2) (g 3) (g 4) >>> 10 = 0 :=
  (f2_mk5 (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)).2.2.2.2.2

theorem dot_eq (a b : Nat) :
    burnsideF48t_u52Dot (unpack 5 2 a) (unpack 5 2 b) = dotK a b := by
  unfold burnsideF48t_u52Dot dotK
  rw [unpack_f2 a (by norm_num : 0 < 5), unpack_f2 a (by norm_num : 1 < 5),
    unpack_f2 a (by norm_num : 2 < 5), unpack_f2 a (by norm_num : 3 < 5),
    unpack_f2 a (by norm_num : 4 < 5), unpack_f2 b (by norm_num : 0 < 5),
    unpack_f2 b (by norm_num : 1 < 5), unpack_f2 b (by norm_num : 2 < 5),
    unpack_f2 b (by norm_num : 3 < 5), unpack_f2 b (by norm_num : 4 < 5)]
  simp only [← mulK_eq _ (f2_lt _ _) _ (f2_lt _ _)]
  rfl

theorem bar_eq (u : Nat) : burnsideF48t_u52Bar (unpack 5 2 u) = unpack 5 2 (barK u) := by
  apply Array.ext (by simp [burnsideF48t_u52Bar, unpack])
  intro j h1 h2
  have hj : j < 5 := by simpa [unpack] using h2
  rw [← getElem!_pos _ j h1, ← getElem!_pos _ j h2, unpack_f2 _ hj]
  unfold burnsideF48t_u52Bar
  rw [ofFn5 _ hj, unpack_f2 _ hj, ← sq_eq _ (f2_lt _ _)]
  unfold barK
  exact (f2_mk5_get (g := fun j => mulK (f2 u j) (f2 u j)) (fun _ => mulK_lt _ _) hj).symm

theorem dot_bar_eq (u v : Nat) :
    burnsideF48t_u52Dot (burnsideF48t_u52Bar (unpack 5 2 u)) (unpack 5 2 v) = dotK (barK u) v := by
  rw [bar_eq, dot_eq]

theorem tv_eq (u v : Nat) :
    burnsideF48t_u52TV (unpack 5 2 u) (unpack 5 2 v) = unpack 5 2 (tvK u v) := by
  apply Array.ext (by simp [burnsideF48t_u52TV, unpack])
  intro j h1 h2
  have hj : j < 5 := by simpa [unpack] using h2
  rw [← getElem!_pos _ j h1, ← getElem!_pos _ j h2, unpack_f2 _ hj]
  unfold burnsideF48t_u52TV
  simp only
  rw [ofFn5 _ hj, unpack_f2 _ hj, unpack_f2 _ hj, dot_bar_eq,
    ← mulK_eq _ (f2_lt _ _) _ (dotK_lt _ _)]
  unfold tvK
  rw [strictN_app]
  exact (f2_mk5_get (g := fun j => Nat.xor (f2 v j) (mulK (f2 u j) (dotK (barK u) v)))
    (fun _ => xor_lt (f2_lt _ _) (mulK_lt _ _)) hj).symm

theorem scale_eq {l : Nat} (hl : l < 4) (y : Nat) :
    burnsideF48t_u52Scale l (unpack 5 2 y) = unpack 5 2 (scK l y) := by
  apply Array.ext (by simp [burnsideF48t_u52Scale, unpack])
  intro j h1 h2
  have hj : j < 5 := by simpa [unpack] using h2
  rw [← getElem!_pos _ j h1, ← getElem!_pos _ j h2, unpack_f2 _ hj]
  unfold burnsideF48t_u52Scale
  rw [ofFn5 _ hj, unpack_f2 _ hj, ← mulK_eq _ hl _ (f2_lt _ _)]
  unfold scK
  exact (f2_mk5_get (g := fun j => mulK l (f2 y j)) (fun _ => mulK_lt _ _) hj).symm

theorem tvK_canon (u v : Nat) : tvK u v >>> 10 = 0 := by
  unfold tvK
  rw [strictN_app]
  exact mk5_canon (g := fun j => Nat.xor (f2 v j) (mulK (f2 u j) (dotK (barK u) v)))
    (fun _ => xor_lt (f2_lt _ _) (mulK_lt _ _))

theorem scK_canon (l y : Nat) : scK l y >>> 10 = 0 :=
  mk5_canon (g := fun j => mulK l (f2 y j)) (fun _ => mulK_lt _ _)

theorem scK_one {y : Nat} (hy : y >>> 10 = 0) : scK 1 y = y := by
  refine f2_ext (scK_canon 1 y) hy fun j hj => ?_
  unfold scK
  rw [f2_mk5_get (g := fun j => mulK 1 (f2 y j)) (fun _ => mulK_lt _ _) hj]
  exact mulK_one _ (f2_lt _ _)

private theorem normC : allN 1024 (fun x => bIf(ptNorm (normK x),
    bAnd(Nat.beq x (scK (leadK x) (normK x)), bAnd(Nat.blt 0 (leadK x), Nat.blt (leadK x) 4)),
    true)) = true := by
  decide +kernel

private theorem scaleC : allN 1024 (fun y => allN 4 fun l =>
    bIf(bAnd(ptNorm y, bAnd(ptNorm (scK l y), Nat.blt 0 l)), Nat.beq l 1, true)) = true := by
  decide +kernel

theorem ptNorm_spec {p : Nat} (h : ptNorm p = true) : p >>> 10 = 0 ∧ leadK p = 1 := by
  unfold ptNorm at h
  rw [bAnd_iff] at h
  exact ⟨beq_t.1 h.1, beq_t.1 h.2⟩

theorem norm_spec {x : Nat} (hx : x >>> 10 = 0) (h : ptNorm (normK x) = true) :
    x = scK (leadK x) (normK x) ∧ 0 < leadK x ∧ leadK x < 4 := by
  have hx' : x < 1024 := by
    rw [Nat.shiftRight_eq_div_pow] at hx
    have : x / 1024 = 0 := by simpa using hx
    omega
  have e := allN_spec normC x hx'
  rw [bIf_ite, if_pos h, bAnd_iff, bAnd_iff] at e
  exact ⟨beq_t.1 e.1, Nat.blt_eq.mp e.2.1, Nat.blt_eq.mp e.2.2⟩

theorem scale_spec {y l : Nat} (hl : l < 4) (hl0 : 0 < l) (hy : ptNorm y = true)
    (h : ptNorm (scK l y) = true) : l = 1 := by
  have hy' : y < 1024 := by
    have hx := (ptNorm_spec hy).1
    rw [Nat.shiftRight_eq_div_pow] at hx
    have : y / 1024 = 0 := by simpa using hx
    omega
  have e := allN_spec (allN_spec scaleC y hy') l hl
  have hc : bAnd(ptNorm y, bAnd(ptNorm (scK l y), Nat.blt 0 l)) = true := by
    rw [bAnd_iff, bAnd_iff]
    exact ⟨hy, h, Nat.blt_eq.mpr hl0⟩
  rw [bIf_ite, if_pos hc] at e
  exact beq_t.1 e

theorem ptsK_spec {F : Nat → Nat} (h : ptsK F = true) :
    (∀ i < 165, ptNorm (F i) = true) ∧ ∀ i < 165, ∀ l < 165, F i = F l → i = l := by
  unfold ptsK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨allN_spec h1, fun i hi l hl e => ?_⟩
  have hd := CFSG.KC.TreeK.distinctK_sound h2
  refine hd.eq_of_getElem_eq (i := i) (j := l) (by simpa using hi) (by simpa using hl) ?_
  simpa using e

theorem lnInc_spec {q : Nat} (h : lnInc q = true) :
    q >>> 40 = 0 ∧ f8 q 0 < f8 q 1 ∧ f8 q 1 < f8 q 2 ∧ f8 q 2 < f8 q 3 ∧ f8 q 3 < f8 q 4 ∧
      f8 q 4 < 165 := by
  unfold lnInc at h
  simp only [bAnd_iff, beq_t, Nat.blt_eq] at h
  exact h

theorem lnsK_spec {L : Nat → Nat} (h : lnsK L = true) :
    (∀ l < 297, lnInc (L l) = true) ∧ ∀ l < 297, ∀ l' < 297, L l = L l' → l = l' := by
  unfold lnsK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨allN_spec h1, fun i hi l hl e => ?_⟩
  have hd := CFSG.KC.TreeK.distinctK_sound h2
  refine hd.eq_of_getElem_eq (i := i) (j := l) (by simpa using hi) (by simpa using hl) ?_
  simpa using e

theorem any5_spec {f : Nat → Nat} {x : Nat} (h : any5 f x = true) : ∃ a < 5, f a = x := by
  unfold any5 at h
  simp only [bIf_ite] at h
  split_ifs at h with h0 h1 h2 h3
  · exact ⟨0, by norm_num, beq_t.1 h0⟩
  · exact ⟨1, by norm_num, beq_t.1 h1⟩
  · exact ⟨2, by norm_num, beq_t.1 h2⟩
  · exact ⟨3, by norm_num, beq_t.1 h3⟩
  · exact ⟨4, by norm_num, beq_t.1 h⟩

theorem genPt_spec {G U F : Nat → Nat} {k i : Nat} (h : genPt G U F k i = true) :
    pg 9 (mask 9) (G k) i < 165 ∧ normK (tvK (U k) (F i)) = F (pg 9 (mask 9) (G k) i) := by
  unfold genPt at h
  rw [strictB_app, bAnd_iff] at h
  exact ⟨Nat.blt_eq.mp h.1, beq_t.1 h.2⟩

theorem genLn_spec {G L : Nat → Nat} {k l : Nat} (h : genLn G L k l = true) :
    165 ≤ pg 9 (mask 9) (G k) (165 + l) ∧ pg 9 (mask 9) (G k) (165 + l) < 462 ∧
      (∀ a < 5, ∃ b < 5, f8 (L (pg 9 (mask 9) (G k) (165 + l) - 165)) b =
        pg 9 (mask 9) (G k) (f8 (L l) a)) ∧
      (∀ b < 5, ∃ a < 5, pg 9 (mask 9) (G k) (f8 (L l) a) =
        f8 (L (pg 9 (mask 9) (G k) (165 + l) - 165)) b) := by
  unfold genLn at h
  rw [strictB_app, bAnd_iff, bAnd_iff, strictB_app, strictB_app, bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.blt_eq.mp h2, fun a ha => any5_spec (allN_spec h3 a ha),
    fun b hb => any5_spec (allN_spec h4 b hb)⟩

theorem gensK_spec {G U F L : Nat → Nat} (h : gensK G U F L = true) :
    (∀ k < 6, ∀ i < 165, genPt G U F k i = true) ∧ ∀ k < 6, ∀ l < 297, genLn G L k l = true := by
  unfold gensK at h
  rw [bAnd_iff] at h
  exact ⟨fun k hk i hi => allN_spec (allN_spec h.1 k hk) i hi,
    fun k hk l hl => allN_spec (allN_spec h.2 k hk) l hl⟩

theorem isoK_spec {U : Nat → Nat} (h : isoK U = true) {k : Nat} (hk : k < 6) :
    U k >>> 10 = 0 ∧ dotK (barK (U k)) (U k) = 0 := by
  have e := allN_spec h k hk
  rw [bAnd_iff] at e
  exact ⟨beq_t.1 e.1, beq_t.1 e.2⟩

end CFSG.KC.U52PL

end
