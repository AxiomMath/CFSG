module

public import Certificates.Data.Kernel.Spor.ONPvK
public import CFSG.Certificates.Kernel.Spor.ONNQSound
public import Mathlib.Algebra.Group.Subgroup.Defs
import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.KS.ONPv

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.ONNQ

variable {n : Nat}

@[expose] def lv (g : Nat → Equiv.Perm (Fin n)) (z : Int) : Equiv.Perm (Fin n) :=
  if 0 < z then g (z.toNat - 1) else (g ((-z).toNat - 1))⁻¹

@[expose] def wv (g : Nat → Equiv.Perm (Fin n)) (w : List Int) : Equiv.Perm (Fin n) :=
  (w.map (lv g)).prod

@[expose] def Rp (T U : Nat → Nat → Nat) (g : Nat → Equiv.Perm (Fin n)) (m : Nat) : Prop :=
  ∀ k < m, ∀ x : Fin n, T k x = (g k x : Nat) ∧ U k x = ((g k)⁻¹ x : Nat)

@[expose] abbrev Lm (m : Nat) (w : List Int) : Prop :=
  w.all (fun z => decide (z ≠ 0 ∧ z.natAbs ≤ m)) = true

@[expose] def Sep (K : Subgroup (Equiv.Perm (Fin n))) (p0 p1 p2 : Fin n) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, a p0 = b p0 → a p1 = b p1 → a p2 = b p2 → a = b

theorem Lm_cons {m : Nat} {z : Int} {w : List Int} (h : Lm m (z :: w)) :
    (z ≠ 0 ∧ z.natAbs ≤ m) ∧ Lm m w := by
  unfold Lm at h ⊢
  rw [List.all_cons, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, h.2⟩

theorem Lm_mono {m m' : Nat} (hm : m ≤ m') {w : List Int} (h : Lm m w) : Lm m' w := by
  unfold Lm at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro z hz
  have := of_decide_eq_true (h z hz)
  exact decide_eq_true ⟨this.1, by omega⟩

theorem Lm_winv {m : Nat} {w : List Int} (h : Lm m w) : Lm m (winv w) := by
  unfold Lm winv at *
  rw [List.all_eq_true] at h ⊢
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  have := of_decide_eq_true (h y (List.mem_reverse.1 hy))
  refine decide_eq_true ⟨by omega, ?_⟩
  rw [Int.natAbs_neg]
  exact this.2

theorem wv_nil (g : Nat → Equiv.Perm (Fin n)) : wv g [] = 1 := by simp [wv]

theorem wv_cons (g : Nat → Equiv.Perm (Fin n)) (z : Int) (w : List Int) :
    wv g (z :: w) = lv g z * wv g w := by simp [wv]

theorem wv_append (g : Nat → Equiv.Perm (Fin n)) (u w : List Int) :
    wv g (u ++ w) = wv g u * wv g w := by simp [wv, List.prod_append]

theorem lv_neg (g : Nat → Equiv.Perm (Fin n)) {z : Int} (hz : z ≠ 0) : lv g (-z) = (lv g z)⁻¹ := by
  unfold lv
  by_cases hp : 0 < z
  · have hn : ¬ (0 : Int) < -z := by omega
    have e : (- -z).toNat - 1 = z.toNat - 1 := by omega
    simp only [hp, hn, ↓reduceIte, e]
  · have hn : (0 : Int) < -z := by omega
    simp only [hp, hn, ↓reduceIte, inv_inv]

theorem wv_winv (g : Nat → Equiv.Perm (Fin n)) {m : Nat} :
    ∀ {w : List Int}, Lm m w → wv g (winv w) = (wv g w)⁻¹
  | [], _ => by simp [wv, winv]
  | z :: w, hw => by
    obtain ⟨hz, hw'⟩ := Lm_cons hw
    have e : winv (z :: w) = winv w ++ [-z] := by simp [winv]
    rw [e, wv_append, wv_winv g hw', wv_cons, wv_cons, wv_nil, mul_one, lv_neg g hz.1, mul_inv_rev]

theorem wv_congr {g g' : Nat → Equiv.Perm (Fin n)} {m : Nat} (h : ∀ k < m, g k = g' k) :
    ∀ {w : List Int}, Lm m w → wv g w = wv g' w
  | [], _ => rfl
  | z :: w, hw => by
    obtain ⟨hz, hw'⟩ := Lm_cons hw
    have hl : lv g z = lv g' z := by
      unfold lv
      split
      · exact h _ (by omega)
      · rw [h _ (by omega)]
    rw [wv_cons, wv_cons, hl, wv_congr h hw']

theorem lv_mem {K : Subgroup (Equiv.Perm (Fin n))} {g : Nat → Equiv.Perm (Fin n)} {m : Nat}
    (hg : ∀ k < m, g k ∈ K) {z : Int} (hz : z ≠ 0 ∧ z.natAbs ≤ m) : lv g z ∈ K := by
  unfold lv
  split
  · exact hg _ (by omega)
  · exact inv_mem (hg _ (by omega))

theorem wv_mem {K : Subgroup (Equiv.Perm (Fin n))} {g : Nat → Equiv.Perm (Fin n)} {m : Nat}
    (hg : ∀ k < m, g k ∈ K) : ∀ {w : List Int}, Lm m w → wv g w ∈ K
  | [], _ => by rw [wv_nil]; exact one_mem K
  | z :: w, hw => by
    obtain ⟨hz, hw'⟩ := Lm_cons hw
    rw [wv_cons]
    exact mul_mem (lv_mem hg hz) (wv_mem hg hw')

variable {T U : Nat → Nat → Nat} {g : Nat → Equiv.Perm (Fin n)} {m : Nat}

theorem Rp_congr (hR : Rp T U g m) {g' : Nat → Equiv.Perm (Fin n)} (h : ∀ k < m, g k = g' k) :
    Rp T U g' m := by
  intro k hk x
  rw [← h k hk]
  exact hR k hk x

theorem GZ_eq (hR : Rp T U g m) {z : Int} (hz : z ≠ 0 ∧ z.natAbs ≤ m) (x : Fin n) :
    GZ T U z x = (lv g z x : Nat) := by
  unfold GZ lv
  by_cases hp : 0 < z
  · simp only [hp, ↓reduceIte]
    exact (hR _ (by omega) x).1
  · simp only [hp, ↓reduceIte]
    exact (hR _ (by omega) x).2

theorem foldr_eq (hR : Rp T U g m) : ∀ {w : List Int}, Lm m w → ∀ x : Fin n,
    w.foldr (fun z y => GZ T U z y) (x : Nat) = (wv g w x : Nat)
  | [], _, x => by rw [wv_nil]; rfl
  | z :: w, hw, x => by
    obtain ⟨hz, hw'⟩ := Lm_cons hw
    rw [List.foldr_cons, foldr_eq hR hw' x, GZ_eq hR hz, wv_cons, Equiv.Perm.mul_apply]

theorem iT_eq (hR : Rp T U g m) {v : Nat} (hv : Lm m (wd v)) (x : Fin n) :
    iT T U v x = (wv g (wd v) x : Nat) := by
  unfold iT
  rw [trace_eq]
  exact foldr_eq hR hv x

theorem iU_eq (hR : Rp T U g m) {v : Nat} (hv : Lm m (wd v)) (x : Fin n) :
    iU T U v x = ((wv g (wd v))⁻¹ x : Nat) := by
  unfold iU
  rw [traceR_eq, ← wv_winv g hv]
  exact foldr_eq hR (Lm_winv hv) x

theorem itT_Rp (hR : Rp T U g m) {D : Nat → Nat} {o m' : Nat}
    (hL : ∀ k < m', Lm m (wd (D (o + k)))) :
    Rp (itT T U D o) (itU T U D o) (fun k => wv g (wd (D (o + k)))) m' :=
  fun k hk x => ⟨iT_eq hR (hL k hk) x, iU_eq hR (hL k hk) x⟩

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem nbeq {a b : Nat} (h : Bool.not (Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

@[expose] abbrev ItemsOK (D : Nat → Nat) : Prop :=
  (∀ j < 19, Lm 7 (wd (D j))) ∧ ∀ j < 132, Lm 7 (wd (D (77 + j)))

@[expose] def gI (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (j : Nat) :
    Equiv.Perm (Fin 245520) :=
  wv g (wd (D j))

@[expose] def hI (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (k : Nat) :
    Equiv.Perm (Fin 245520) :=
  gI g D (77 + k)

@[expose] def qI (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (k : Nat) :
    Equiv.Perm (Fin 245520) :=
  wv (hI g D) (wd (D (149 + k)))

section Vec

variable {TT UU : Nat → Nat → Nat} {D : Nat → Nat} {g : Nat → Equiv.Perm (Fin 245520)}

theorem items_hi (hI' : ItemsOK D) (j : Nat) (h1 : 77 ≤ j := by omega) (h2 : j < 209 := by omega) :
    Lm 7 (wd (D j)) := by
  have := hI'.2 (j - 77) (by omega)
  rwa [show 77 + (j - 77) = j by omega] at this

theorem items_lo (hI' : ItemsOK D) (j : Nat) (h : j < 19 := by omega) : Lm 7 (wd (D j)) :=
  hI'.1 j h

theorem rp_v (hR : Rp TT UU g 7) (hI' : ItemsOK D) :
    Rp (itT TT UU D 0) (itU TT UU D 0) (gI g D) 7 :=
  Rp_congr (itT_Rp (o := 0) hR fun k _ => items_lo hI' (0 + k)) fun k _ => by
    simp only [gI, Nat.zero_add]

theorem rp_h (hR : Rp TT UU g 7) (hI' : ItemsOK D) :
    Rp (hT TT UU D) (hU TT UU D) (hI g D) 7 :=
  itT_Rp (o := 77) hR fun k _ => items_hi hI' (77 + k)

theorem rp_q (hR : Rp TT UU g 7) (hI' : ItemsOK D) :
    Rp (qT TT UU D) (qU TT UU D) (qI g D) 7 :=
  itT_Rp (o := 149) (rp_h hR hI') fun k _ => items_hi hI' (149 + k)

theorem gsel_lt {k : Nat} (hk : k < 7) : gsel k < 7 := by
  unfold gsel
  cases Nat.beq k 3 <;> dsimp only <;> omega

theorem rp_g (hR : Rp TT UU g 7) (hI' : ItemsOK D) :
    Rp (gT TT UU D) (gU TT UU D) (fun k => qI g D (gsel k)) 7 :=
  fun k hk x => rp_q hR hI' (gsel k) (gsel_lt hk) x

variable {K : Subgroup (Equiv.Perm (Fin 245520))}

theorem gI_mem (hK : ∀ k < 7, g k ∈ K) (hI' : ItemsOK D) {j : Nat}
    (hj : j < 19 ∨ (77 ≤ j ∧ j < 209)) : gI g D j ∈ K := by
  rcases hj with hj | ⟨h1, h2⟩
  · exact wv_mem hK (items_lo hI' j)
  · exact wv_mem hK (items_hi hI' j)

theorem hI_mem (hK : ∀ k < 7, g k ∈ K) (hI' : ItemsOK D) : ∀ k < 7, hI g D k ∈ K :=
  fun k _ => gI_mem hK hI' (Or.inr ⟨by omega, by omega⟩)

theorem qI_mem (hK : ∀ k < 7, g k ∈ K) (hI' : ItemsOK D) : ∀ k < 7, qI g D k ∈ K :=
  fun k _ => wv_mem (hI_mem hK hI') (items_hi hI' (149 + k))

theorem sep_eq {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) {a b : Equiv.Perm (Fin 245520)}
    (ha : a ∈ K) (hb : b ∈ K) (h : ∀ p ∈ [p0, p1, p2], a p = b p) : a = b :=
  hS a ha b hb (h p0 (by simp)) (h p1 (by simp)) (h p2 (by simp))

theorem one_apply' (p : Fin 245520) : (1 : Equiv.Perm (Fin 245520)) p = p := rfl

theorem c502At_pt (hR : Rp TT UU g 7) (hI' : ItemsOK D) {p : Fin 245520}
    (h : c502At TT UU D p = true) :
    (∀ j < 29, wv (gI g D) (wd (D (178 + j))) p = p) ∧
      wv (gI g D) (wd (D 207)) p = gI g D 79 p ∧ wv (gI g D) (wd (D 208)) p = g 1 p := by
  have hV := rp_v hR hI'
  unfold c502At at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun j hj => Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec h1 j hj)
    exact (iT_eq hV (items_hi hI' (178 + j)) p).symm.trans e
  · have e := Nat.eq_of_beq_eq_true h2
    exact (iT_eq hV (items_hi hI' 207) p).symm.trans (e.trans (iT_eq hR (items_hi hI' 79) p))
  · have e := Nat.eq_of_beq_eq_true h3
    exact (iT_eq hV (items_hi hI' 208) p).symm.trans (e.trans (hR 1 (by omega) p).1)

theorem c502_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) (h0 : c502At TT UU D p0 = true)
    (h1 : c502At TT UU D p1 = true) (h2 : c502At TT UU D p2 = true) :
    (∀ j < 29, wv (gI g D) (wd (D (178 + j))) = 1) ∧
      wv (gI g D) (wd (D 207)) = gI g D 79 ∧ wv (gI g D) (wd (D 208)) = g 1 := by
  have hv : ∀ k < 7, gI g D k ∈ K := fun k _ => gI_mem hK hI' (Or.inl (by omega))
  have hm : ∀ j, 77 ≤ j → j < 209 → wv (gI g D) (wd (D j)) ∈ K := fun j a b =>
    wv_mem hv (items_hi hI' j a b)
  have P : ∀ p ∈ [p0, p1, p2], c502At TT UU D p = true := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  refine ⟨fun j hj => sep_eq hS (hm _ (by omega) (by omega)) (one_mem K) fun p hp =>
      ((c502At_pt hR hI' (P p hp)).1 j hj).trans (one_apply' p).symm,
    sep_eq hS (hm _ (by omega) (by omega)) (gI_mem hK hI' (Or.inr ⟨by omega, by omega⟩))
      fun p hp => (c502At_pt hR hI' (P p hp)).2.1,
    sep_eq hS (hm _ (by omega) (by omega)) (hK 1 (by omega))
      fun p hp => (c502At_pt hR hI' (P p hp)).2.2⟩

theorem c502Hd_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (h : c502Hd TT UU D = true) :
    gI g D 79 ≠ 1 := by
  unfold c502Hd at h
  rw [sB] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hx : D 19 < 245520 := Nat.blt_eq.mp h1
  intro e
  apply nbeq h2
  refine (iT_eq hR (items_hi hI' 79) ⟨D 19, hx⟩).trans ?_
  change ((gI g D 79) ⟨D 19, hx⟩ : Nat) = D 19
  rw [e]
  rfl

theorem c505At_pt (hR : Rp TT UU g 7) (hI' : ItemsOK D) {p : Fin 245520}
    (h : c505At TT UU D p = true) : ∀ j < 19, wv (qI g D) (wd (D (156 + j))) p = p := by
  intro j hj
  apply Fin.ext
  have e := Nat.eq_of_beq_eq_true (allBlk_spec h j hj)
  exact (iT_eq (rp_q hR hI') (items_hi hI' (156 + j)) p).symm.trans e

theorem c505_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) (h0 : c505At TT UU D p0 = true)
    (h1 : c505At TT UU D p1 = true) (h2 : c505At TT UU D p2 = true) :
    ∀ j < 19, wv (qI g D) (wd (D (156 + j))) = 1 := by
  intro j hj
  have P : ∀ p ∈ [p0, p1, p2], c505At TT UU D p = true := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  exact sep_eq hS (wv_mem (qI_mem hK hI') (items_hi hI' (156 + j))) (one_mem K)
    fun p hp => (c505At_pt hR hI' (P p hp) j hj).trans (one_apply' p).symm

theorem c505Hd_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (h : c505Hd TT UU D = true) :
    qI g D 0 ≠ 1 ∧ ∀ k < 4, qI g D k ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  have hq := rp_q hR hI'
  unfold c505Hd at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [sB] at h1
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h1
  have hx : D 20 < 245520 := Nat.blt_eq.mp h3
  refine ⟨fun e => nbeq h4 ((hq 0 (by omega) ⟨D 20, hx⟩).1.trans ?_), fun k hk => Fin.ext ?_⟩
  · rw [e]
    rfl
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec h2 k hk)
    rw [show Nat.add 0 k = k from Nat.zero_add k] at e
    exact (hq k (by omega) ⟨0, by omega⟩).1.symm.trans e

theorem c503At_pt (hR : Rp TT UU g 7) (hI' : ItemsOK D) {p : Fin 245520}
    (h : c503At TT UU D p = true) :
    wv (fun k => qI g D (gsel k)) (wd (D 175)) p = qI g D 3 p ∧
      wv (fun k => qI g D (gsel k)) (wd (D 176)) p = wv (fun k => qI g D (gsel k)) (wd (D 177)) p := by
  have hG := rp_g hR hI'
  unfold c503At at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · exact (iT_eq hG (items_hi hI' 175) p).symm.trans
      ((Nat.eq_of_beq_eq_true h1).trans (rp_q hR hI' 3 (by omega) p).1)
  · exact (iT_eq hG (items_hi hI' 176) p).symm.trans
      ((Nat.eq_of_beq_eq_true h2).trans (iT_eq hG (items_hi hI' 177) p))

theorem c503_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) (h0 : c503At TT UU D p0 = true)
    (h1 : c503At TT UU D p1 = true) (h2 : c503At TT UU D p2 = true) :
    wv (fun k => qI g D (gsel k)) (wd (D 175)) = qI g D 3 ∧
      wv (fun k => qI g D (gsel k)) (wd (D 176)) = wv (fun k => qI g D (gsel k)) (wd (D 177)) := by
  have hG : ∀ k < 7, qI g D (gsel k) ∈ K := fun k hk => qI_mem hK hI' _ (gsel_lt hk)
  have P : ∀ p ∈ [p0, p1, p2], c503At TT UU D p = true := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  exact ⟨sep_eq hS (wv_mem hG (items_hi hI' 175)) (qI_mem hK hI' 3 (by omega))
      fun p hp => (c503At_pt hR hI' (P p hp)).1,
    sep_eq hS (wv_mem hG (items_hi hI' 176)) (wv_mem hG (items_hi hI' 177))
      fun p hp => (c503At_pt hR hI' (P p hp)).2⟩

theorem c503Hd_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (h : c503Hd TT UU D = true) :
    qI g D 4 ⟨0, by omega⟩ ≠ ⟨0, by omega⟩ := by
  intro e
  apply nbeq h
  refine (rp_q hR hI' 4 (by omega) ⟨0, by omega⟩).1.trans ?_
  rw [e]

theorem conjAt_eq (hR : Rp TT UU g 7) (hI' : ItemsOK D) {v : Nat} (hv : Lm 7 (wd v)) {k : Nat}
    (hk : k < 2) (y : Fin 245520) :
    conjAt TT UU D v k y = ((qI g D (5 + k) * wv g (wd v) * (qI g D (5 + k))⁻¹) y : Nat) := by
  have hq := rp_q hR hI' (5 + k) (by omega)
  unfold conjAt
  rw [sN, sN]
  change qT TT UU D (Nat.add 5 k) (iT TT UU v (qU TT UU D (Nat.add 5 k) y)) = _
  have e5 : Nat.add 5 k = 5 + k := rfl
  rw [e5, (hq y).2, iT_eq hR hv, (hq _).1]
  rfl

theorem c506At_pt (hR : Rp TT UU g 7) (hI' : ItemsOK D) {p : Fin 245520}
    (h : c506At TT UU D p = true) :
    (∀ k < 2, (qI g D (5 + k) * gI g D 92 * (qI g D (5 + k))⁻¹) p = (gI g D 92 ^ 3) p) ∧
      ∀ m < 12, gI g D (80 + m) p = gI g D (7 + m) p := by
  have hv : Lm 7 (wd (D 92)) := items_hi hI' 92
  unfold c506At at h
  rw [sB] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun k hk => Fin.ext ?_, fun m hm => Fin.ext ?_⟩
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec h1 k hk)
    rw [show Nat.add 0 k = k from Nat.zero_add k, sN, sN, iT_eq hR hv p, iT_eq hR hv,
      iT_eq hR hv, conjAt_eq hR hI' hv hk] at e
    refine e.trans ?_
    rw [pow_three]
    rfl
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec h2 m hm)
    rw [show Nat.add 0 m = m from Nat.zero_add m] at e
    exact (iT_eq hR (items_hi hI' (80 + m)) p).symm.trans
      (e.trans (iT_eq hR (items_lo hI' (7 + m)) p))

theorem c506_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) (h0 : c506At TT UU D p0 = true)
    (h1 : c506At TT UU D p1 = true) (h2 : c506At TT UU D p2 = true) :
    (∀ k < 2, qI g D (5 + k) * gI g D 92 * (qI g D (5 + k))⁻¹ = gI g D 92 ^ 3) ∧
      ∀ m < 12, gI g D (80 + m) = gI g D (7 + m) := by
  have P : ∀ p ∈ [p0, p1, p2], c506At TT UU D p = true := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have hx : gI g D 92 ∈ K := gI_mem hK hI' (Or.inr ⟨by omega, by omega⟩)
  refine ⟨fun k hk => sep_eq hS ?_ (pow_mem hx 3) fun p hp => (c506At_pt hR hI' (P p hp)).1 k hk,
    fun m hm => sep_eq hS (gI_mem hK hI' (Or.inr ⟨by omega, by omega⟩))
      (gI_mem hK hI' (Or.inl (by omega))) fun p hp => (c506At_pt hR hI' (P p hp)).2 m hm⟩
  have hq := qI_mem hK hI' (5 + k) (by omega)
  exact mul_mem (mul_mem hq hx) (inv_mem hq)

theorem c506Wit_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) {j : Nat} (hj : j < 56)
    (h : c506Wit TT UU D j = true) :
    ∃ k < 2, ¬ Commute (qI g D (5 + k) * gI g D (93 + j) * (qI g D (5 + k))⁻¹) (gI g D (93 + j)) := by
  have hv : Lm 7 (wd (D (93 + j))) := items_hi hI' (93 + j)
  unfold c506Wit at h
  rw [sB, sB, sB, sB] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hp : Nat.shiftRight (D (Nat.add 21 j)) 1 < 245520 := Nat.blt_eq.mp h1
  have hk : Nat.land (D (Nat.add 21 j)) 1 < 2 := by
    have e : Nat.land (D (Nat.add 21 j)) 1 = D (Nat.add 21 j) % 2 := Nat.and_one_is_mod _
    rw [e]
    exact Nat.mod_lt _ (by omega)
  refine ⟨_, hk, fun hc => nbeq h2 ?_⟩
  have e93 : D (Nat.add 93 j) = D (93 + j) := rfl
  rw [e93]
  set x := gI g D (93 + j)
  set y := qI g D (5 + Nat.land (D (Nat.add 21 j)) 1) * x *
    (qI g D (5 + Nat.land (D (Nat.add 21 j)) 1))⁻¹
  have a1 : iT TT UU (D (93 + j)) (Nat.shiftRight (D (Nat.add 21 j)) 1) = (x ⟨_, hp⟩ : Nat) :=
    iT_eq hR hv ⟨_, hp⟩
  have a2 := conjAt_eq hR hI' hv hk ⟨_, hp⟩
  rw [a1, conjAt_eq hR hI' hv hk (x ⟨_, hp⟩), a2, iT_eq hR hv]
  change ((y * x) ⟨_, hp⟩ : Nat) = ((x * y) ⟨_, hp⟩ : Nat)
  rw [hc.eq]

theorem c506WitR_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) {lo cnt : Nat}
    (h : c506WitR TT UU D lo cnt = true) (hc : lo + cnt ≤ 56) :
    ∀ l < cnt, ∃ k < 2, ¬ Commute (qI g D (5 + k) * gI g D (93 + (lo + l)) * (qI g D (5 + k))⁻¹)
      (gI g D (93 + (lo + l))) :=
  fun l hl => c506Wit_sound hR hI' (j := lo + l) (by omega) (allBlk_spec h l hl)

end Vec

theorem twH_lt {b h : Nat} (hh : h < 8) : twH b h < 8 := by
  unfold twH
  cases Nat.beq b 0 <;> cases Nat.beq h 0 <;> cases Nat.beq h 2 <;> cases Nat.beq h 3 <;>
    dsimp only <;> omega

theorem actT_Rp {LT LU : Nat → Nat → Nat} {ℓ : Nat → Equiv.Perm (Fin n)} (hR : Rp LT LU ℓ 8)
    (b : Nat) : Rp (actT LT b) (actT LU b) (fun h => ℓ (twH b h)) 8 :=
  fun h hh x => hR (twH b h) (twH_lt hh) x

theorem c506Ln_sound {LT LU : Nat → Nat → Nat} {ℓ : Nat → Equiv.Perm (Fin 122760)} {D : Nat → Nat}
    (hR : Rp LT LU ℓ 8) (hI' : ItemsOK D) {l2 : Fin 122760} (h : c506Ln LT LU D l2 = true) :
    (∀ m < 8, wv (fun h => ℓ (twH 0 h)) (wd (D (7 + m))) ⟨0, by omega⟩ = ⟨0, by omega⟩) ∧
      (∀ m < 4, wv (fun h => ℓ (twH 1 h)) (wd (D (7 + m))) l2 = l2) ∧
      (∀ m < 4, wv (fun h => ℓ (twH 1 h)) (wd (D (15 + m))) l2 = l2) ∧
      wv (fun k => wv (fun h => ℓ (twH 1 h)) (wd (D (77 + k)))) (wd (D 154)) l2 = l2 := by
  have h0 := actT_Rp hR 0
  have h1 := actT_Rp hR 1
  have hL : ∀ j < 19, Lm 8 (wd (D j)) := fun j hj => Lm_mono (by omega) (hI'.1 j hj)
  unfold c506Ln at h
  obtain ⟨a1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨a2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨a3, a4⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun m hm => Fin.ext ?_, fun m hm => Fin.ext ?_, fun m hm => Fin.ext ?_, Fin.ext ?_⟩
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec a1 m hm)
    exact (iT_eq h0 (hL (7 + m) (by omega)) ⟨0, by omega⟩).symm.trans e
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec a2 m hm)
    exact (iT_eq h1 (hL (7 + m) (by omega)) l2).symm.trans e
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec a3 m hm)
    exact (iT_eq h1 (hL (15 + m) (by omega)) l2).symm.trans e
  · have e := Nat.eq_of_beq_eq_true a4
    have hH := itT_Rp (D := D) (o := 77) (m' := 7) h1 fun k hk =>
      Lm_mono (by omega) (hI'.2 k (by omega))
    exact (iT_eq hH (hI'.2 77 (by omega)) l2).symm.trans e

end CFSG.KS.ONPv

end
