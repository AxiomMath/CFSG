module

public import Certificates.Data.Kernel.Spor.ONPlK
public import CFSG.Certificates.Kernel.Spor.ONPvSound
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KS.ONPl

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONNQ CFSG.KS.ONPv

abbrev ItemsE (E : Nat → Nat) : Prop :=
  (∀ j < 71, Lm 2 (wd (E j))) ∧ ∀ j < 70, Lm 4 (wd (E (71 + j)))

@[expose] def aG (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (k : Nat) :
    Equiv.Perm (Fin 245520) :=
  if k = 0 then gI g D 79 else g 1

@[expose] def aI (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (k : Nat) :
    Equiv.Perm (Fin 245520) :=
  wv (aG g D) (wd (D (77 + k)))

@[expose] def cI (g : Nat → Equiv.Perm (Fin 245520)) (D E : Nat → Nat) (j : Nat) :
    Equiv.Perm (Fin 245520) :=
  (wv g (wd (E j)))⁻¹ * wv (hI g D) (wd (E (28 + j)))

section Vec

variable {TT UU : Nat → Nat → Nat} {D E : Nat → Nat} {g : Nat → Equiv.Perm (Fin 245520)}

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem nbeq {a b : Nat} (h : Bool.not (Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem itemsE_lo (hE : ItemsE E) {j : Nat} (h : j < 71) : Lm 7 (wd (E j)) :=
  Lm_mono (by omega) (hE.1 j h)

theorem itemsE_h (hE : ItemsE E) {j : Nat} (h : j < 71) : Lm 2 (wd (E j)) := hE.1 j h

theorem itemsE_q (hE : ItemsE E) {j : Nat} (h1 : 71 ≤ j) (h2 : j < 141) : Lm 7 (wd (E j)) := by
  have := hE.2 (j - 71) (by omega)
  rw [show 71 + (j - 71) = j by omega] at this
  exact Lm_mono (by omega) this

theorem rp_a (hR : Rp TT UU g 7) (hI' : ItemsOK D) : Rp (aT TT UU D) (aU TT UU D) (aG g D) 2 := by
  intro k hk x
  interval_cases k
  · exact ⟨iT_eq hR (items_hi hI' 79) x, iU_eq hR (items_hi hI' 79) x⟩
  · exact hR 1 (by omega) x

theorem rp_ah (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hA : ∀ k < 2, Lm 2 (wd (D (77 + k)))) :
    Rp (ahT TT UU D) (ahU TT UU D) (aI g D) 2 :=
  itT_Rp (o := 77) (rp_a hR hI') hA

theorem cAt_eq (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) {j : Nat} (hj : j < 28)
    (x : Fin 245520) : cAt TT UU D E j x = (cI g D E j x : Nat) := by
  unfold cAt
  rw [show Nat.add 28 j = 28 + j from rfl, iT_eq (rp_h hR hI') (itemsE_lo hE (j := 28 + j)
    (by omega)), iU_eq hR (itemsE_lo hE (j := j) (by omega))]
  rfl

theorem ciAt_eq (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) {j : Nat} (hj : j < 28)
    (x : Fin 245520) : ciAt TT UU D E j x = ((cI g D E j)⁻¹ x : Nat) := by
  unfold ciAt
  rw [show Nat.add 28 j = 28 + j from rfl, iT_eq hR (itemsE_lo hE (j := j) (by omega)),
    iU_eq (rp_h hR hI') (itemsE_lo hE (j := 28 + j) (by omega))]
  simp [cI, mul_inv_rev, Equiv.Perm.mul_apply]

theorem eAt_pt (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) {YT YU : Nat → Nat → Nat}
    {gy : Nat → Equiv.Perm (Fin 245520)} {m : Nat} (hY : Rp YT YU gy m) {v j r : Nat}
    (hv : Lm m (wd v)) (hj : j < 28) (hr1 : 71 ≤ r) (hr2 : r < 141) {p : Fin 245520}
    (h : eAt TT UU D E YT YU v j r p = true) :
    ((cI g D E j)⁻¹ * wv gy (wd v) * cI g D E j) p = wv (qI g D) (wd (E r)) p := by
  apply Fin.ext
  have e := Nat.eq_of_beq_eq_true h
  rw [cAt_eq hR hI' hE hj, iT_eq hY hv, ciAt_eq hR hI' hE hj,
    iT_eq (rp_q hR hI') (itemsE_q hE hr1 hr2)] at e
  exact e

variable {K : Subgroup (Equiv.Perm (Fin 245520))}

theorem cI_mem (hK : ∀ k < 7, g k ∈ K) (hI' : ItemsOK D) (hE : ItemsE E) {j : Nat} (hj : j < 28) :
    cI g D E j ∈ K :=
  mul_mem (inv_mem (wv_mem hK (itemsE_lo hE (j := j) (by omega))))
    (wv_mem (hI_mem hK hI') (itemsE_lo hE (j := 28 + j) (by omega)))

theorem P3 {f : Fin 245520 → Bool} {p0 p1 p2 : Fin 245520} (h0 : f p0 = true) (h1 : f p1 = true)
    (h2 : f p2 = true) : ∀ p ∈ [p0, p1, p2], f p = true := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> assumption

theorem eAt_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) {YT YU : Nat → Nat → Nat}
    {gy : Nat → Equiv.Perm (Fin 245520)} {m : Nat} (hY : Rp YT YU gy m) (hgy : ∀ k < m, gy k ∈ K)
    {v j r : Nat} (hv : Lm m (wd v)) (hj : j < 28) (hr1 : 71 ≤ r) (hr2 : r < 141)
    (h : ∀ p ∈ [p0, p1, p2], eAt TT UU D E YT YU v j r p = true) :
    (cI g D E j)⁻¹ * wv gy (wd v) * cI g D E j = wv (qI g D) (wd (E r)) := by
  have hc := cI_mem hK hI' hE hj
  exact sep_eq hS (mul_mem (mul_mem (inv_mem hc) (wv_mem hgy hv)) hc)
    (wv_mem (qI_mem hK hI') (itemsE_q hE hr1 hr2))
    fun p hp => eAt_pt hR hI' hE hY hv hj hr1 hr2 (h p hp)

theorem plLn_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2) {j : Nat} (hj : j < 14)
    (h : ∀ p ∈ [p0, p1, p2], plLn TT UU D E j p = true) :
    (cI g D E j)⁻¹ * gI g D 92 * cI g D E j = wv (qI g D) (wd (E (71 + 2 * j))) ∧
      (cI g D E j)⁻¹ * gI g D (93 + j) * cI g D E j = wv (qI g D) (wd (E (72 + 2 * j))) := by
  have e1 : Nat.add 71 (Nat.add j j) = 71 + 2 * j := by simp only [Nat.add_eq]; omega
  have e2 : Nat.add 72 (Nat.add j j) = 72 + 2 * j := by simp only [Nat.add_eq]; omega
  have hp := fun p hp => (bAnd_iff _ _).1 (h p hp)
  refine ⟨eAt_sound hR hI' hE hK hS hR hK (items_hi hI' 92) (by omega) (by omega) (by omega)
      fun p hq => ?_,
    eAt_sound hR hI' hE hK hS hR hK (items_hi hI' (93 + j)) (by omega) (by omega) (by omega)
      fun p hq => ?_⟩
  · have := (hp p hq).1
    rwa [e1] at this
  · have := (hp p hq).2
    rwa [e2, show Nat.add 93 j = 93 + j from rfl] at this

theorem plAl_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) (hK : ∀ k < 7, g k ∈ K)
    (hA : ∀ k < 2, Lm 2 (wd (D (77 + k)))) {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2)
    {j : Nat} (hj1 : 14 ≤ j) (hj : j < 28) (h : ∀ p ∈ [p0, p1, p2], plAl TT UU D E j p = true) :
    (cI g D E j)⁻¹ * wv (aI g D) (wd (E 56)) * cI g D E j = wv (qI g D) (wd (E (71 + 2 * j))) ∧
      (cI g D E j)⁻¹ * wv (aI g D) (wd (E (43 + j))) * cI g D E j =
        wv (qI g D) (wd (E (72 + 2 * j))) := by
  have e1 : Nat.add 71 (Nat.add j j) = 71 + 2 * j := by simp only [Nat.add_eq]; omega
  have e2 : Nat.add 72 (Nat.add j j) = 72 + 2 * j := by simp only [Nat.add_eq]; omega
  have hp := fun p hp => (bAnd_iff _ _).1 (h p hp)
  have hY := rp_ah (g := g) hR hI' hA
  have hag : ∀ k < 2, aG g D k ∈ K := by
    intro k hk
    unfold aG
    split_ifs
    · exact gI_mem hK hI' (Or.inr ⟨by omega, by omega⟩)
    · exact hK 1 (by omega)
  have hgy : ∀ k < 2, aI g D k ∈ K := fun k hk => wv_mem hag (hA k hk)
  refine ⟨eAt_sound hR hI' hE hK hS hY hgy (itemsE_h hE (j := 56) (by omega)) (by omega) (by omega)
      (by omega) fun p hq => ?_,
    eAt_sound hR hI' hE hK hS hY hgy (itemsE_h hE (j := 43 + j) (by omega)) (by omega) (by omega)
      (by omega) fun p hq => ?_⟩
  · have := (hp p hq).1
    rwa [e1] at this
  · have := (hp p hq).2
    rwa [e2, show Nat.add 43 j = 43 + j from rfl] at this

theorem plX_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2)
    (h : ∀ p ∈ [p0, p1, p2], plX TT UU D E p = true) :
    wv (hI g D) (wd (E 56)) = gI g D 92 ∧
      ∀ k < 14, wv (hI g D) (wd (E (57 + k))) = gI g D (107 + k) := by
  have hp := fun p hp => (bAnd_iff _ _).1 (h p hp)
  refine ⟨sep_eq hS (wv_mem (hI_mem hK hI') (itemsE_lo hE (j := 56) (by omega)))
      (gI_mem hK hI' (Or.inr ⟨by omega, by omega⟩)) fun p hq => Fin.ext ?_,
    fun k hk => sep_eq hS (wv_mem (hI_mem hK hI') (itemsE_lo hE (j := 57 + k) (by omega)))
      (gI_mem hK hI' (Or.inr ⟨by omega, by omega⟩)) fun p hq => Fin.ext ?_⟩
  · have e := Nat.eq_of_beq_eq_true (hp p hq).1
    rwa [iT_eq (rp_h hR hI') (itemsE_lo hE (j := 56) (by omega)),
      iT_eq hR (items_hi hI' 92)] at e
  · have e := Nat.eq_of_beq_eq_true (allBlk_spec (hp p hq).2 k hk)
    rwa [show Nat.add 57 (Nat.add 0 k) = 57 + k by simp only [Nat.add_eq]; omega,
      show Nat.add 107 (Nat.add 0 k) = 107 + k by simp only [Nat.add_eq]; omega,
      iT_eq (rp_h hR hI') (itemsE_lo hE (j := 57 + k) (by omega)),
      iT_eq hR (items_hi hI' (107 + k))] at e

theorem plP_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E) (hK : ∀ k < 7, g k ∈ K)
    {p0 p1 p2 : Fin 245520} (hS : Sep K p0 p1 p2)
    (h : ∀ p ∈ [p0, p1, p2], plP TT UU D E p = true) :
    ∀ i < 7, wv (qI g D) (wd (E (127 + 2 * i))) = wv (qI g D) (wd (E (128 + 2 * i))) := by
  intro i hi
  refine sep_eq hS (wv_mem (qI_mem hK hI') (itemsE_q hE (j := 127 + 2 * i) (by omega) (by omega)))
    (wv_mem (qI_mem hK hI') (itemsE_q hE (j := 128 + 2 * i) (by omega) (by omega)))
    fun p hq => Fin.ext ?_
  have e := Nat.eq_of_beq_eq_true (allBlk_spec (h p hq) i hi)
  rwa [show Nat.add 127 (Nat.add (Nat.add 0 i) (Nat.add 0 i)) = 127 + 2 * i by
      simp only [Nat.add_eq]; omega,
    show Nat.add 128 (Nat.add (Nat.add 0 i) (Nat.add 0 i)) = 128 + 2 * i by
      simp only [Nat.add_eq]; omega,
    iT_eq (rp_q hR hI') (itemsE_q hE (j := 127 + 2 * i) (by omega) (by omega)),
    iT_eq (rp_q hR hI') (itemsE_q hE (j := 128 + 2 * i) (by omega) (by omega))] at e

theorem plHd_sound (hR : Rp TT UU g 7) (hI' : ItemsOK D) (hE : ItemsE E)
    (h : plHd TT UU D E = true) : wv (qI g D) (wd (E 134)) ≠ 1 ∧ qI g D 2 ≠ 1 := by
  have hq := rp_q hR hI'
  unfold plHd at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [sB] at h1 h2
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h2
  have hx : E 141 < 245520 := Nat.blt_eq.mp h3
  have hy : E 142 < 245520 := Nat.blt_eq.mp h5
  refine ⟨fun e => nbeq h4 ?_, fun e => nbeq h6 ?_⟩
  · refine (iT_eq hq (itemsE_q hE (j := 134) (by omega) (by omega)) ⟨E 141, hx⟩).trans ?_
    rw [e]
    rfl
  · refine (hq 2 (by omega) ⟨E 142, hy⟩).1.trans ?_
    rw [e]
    rfl

end Vec

end CFSG.KS.ONPl

end
