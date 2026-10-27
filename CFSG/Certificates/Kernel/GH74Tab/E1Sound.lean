
module

public import CFSG.Certificates.Kernel.GH74Tab.SearchSound
public import Certificates.Data.Kernel.GH74Tab.E1

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def eP (D : Dat) (A i : Nat) : Bool :=
  i == D.one || i == vIK D A ||
    (bit D.IV i && bit (reachK D A 12 (1 <<< D.x0)) i && mul D i (vIK D A) == mul D (vIK D A) i &&
      bit (reachK D A 12 (1 <<< D.x0)) (mul D i (vIK D A)))

theorem eLK_eq (D : Dat) (A : Nat) : eLK D A = r64.filter (eP D A) := rfl

theorem mem_eLK {D : Dat} {A i : Nat} : i ∈ eLK D A ↔ i < 64 ∧ eP D A i = true := by
  rw [eLK_eq, r64, List.mem_filter, List.mem_range]

theorem mem_r64 {i : Nat} (hi : i < 64) : i ∈ r64 := List.mem_range.2 hi

theorem tblOf_get_eq (A : Nat) (i : Fin 64) : (tblOf A).get i = f64 (g6 A i.val) := by
  rw [tblOf, vget_ofFn]

theorem f64_eq_f64 {x y : Nat} (hx : x < 64) (hy : y < 64) : f64 x = f64 y ↔ x = y := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rwa [val_f64 hx, val_f64 hy] at this
  · rintro rfl
    rfl

theorem beq_f64 (i : Fin 64) {x : Nat} (hx : x < 64) : (i == f64 x) = (i.val == x) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Fin.ext_iff, val_f64 hx]

theorem f64_beq_f64 {x y : Nat} (hx : x < 64) (hy : y < 64) : (f64 x == f64 y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, f64_eq_f64 hx hy]

theorem vIK_lt (D : Dat) (A : Nat) : vIK D A < 64 := mul_lt D _ _

theorem card_filter_r64 (p : Nat → Bool) :
    (Finset.univ.filter fun i : Fin 64 => p i.val = true).card = (r64.filter p).length := by
  rw [r64, ← List.toFinset_card_of_nodup (List.Nodup.filter p List.nodup_range),
    ← Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_filter, r64, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.2, hi⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

section Sound

variable {D : Dat} {n : ℕ} [NeZero n] (ht : transOK D n = true) (hd : dataOK D = true)
include ht hd

theorem x0i_val : (mkTab n).x0i.val = D.x0 := by
  rw [x0i_eq D ht, val_f64 (dataOK_spec D hd).2.1]

theorem vIE1_eq (A : Nat) : (mkTab n).vIE1 (tblOf A) = f64 (vIK D A) := by
  rw [Tab.vIE1, tblOf_get_eq, mulT_eq D ht, val_f64_g6, x0i_val ht hd]
  rfl

theorem reachX (A : Nat) (j : Fin 64) :
    ((mkTab n).reach (tblOf A) (mkTab n).x0i).get j = bit (reachK D A 12 (1 <<< D.x0)) j.val := by
  rw [reach_tblOf ht hd, x0i_val ht hd]

theorem reachV (A : Nat) (j : Fin 64) :
    ((mkTab n).reach (tblOf A) ((mkTab n).vIE1 (tblOf A))).get j =
      bit (reachK D A 12 (1 <<< vIK D A)) j.val := by
  rw [reach_tblOf ht hd, vIE1_eq ht hd, val_f64 (vIK_lt D A)]

theorem eVec_get (A : Nat) (i : Fin 64) :
    ((mkTab n).eVecE1 (tblOf A)).get i = eP D A i.val := by
  have hd1 := (dataOK_spec D hd).1
  rw [Tab.eVecE1_get, isInv_eq ht hd, reachX ht hd, reachX ht hd, vIE1_eq ht hd, mulT_eq D ht,
    mulT_eq D ht, one_eq D ht, beq_f64 i hd1, beq_f64 i (vIK_lt D A),
    f64_beq_f64 (mul_lt D _ _) (mul_lt D _ _), val_f64_mul, val_f64 (vIK_lt D A)]
  rfl

theorem eVec_iff (A : Nat) (i : Fin 64) :
    ((mkTab n).eVecE1 (tblOf A)).get i = true ↔ i.val ∈ eLK D A := by
  rw [eVec_get ht hd, mem_eLK]
  exact ⟨fun h => ⟨i.2, h⟩, fun h => h.2⟩

theorem eVec_iff_f64 (A : Nat) {m : Nat} (hm : m < 64) :
    ((mkTab n).eVecE1 (tblOf A)).get (f64 m) = true ↔ m ∈ eLK D A := by
  rw [eVec_iff ht hd, val_f64 hm]

theorem e1P1_of (A : Nat) (h0 : e1K0 D = true) (h1 : e1K1 D n A = true) (u : Fin 64) :
    (mkTab n).e1P1 (tblOf A) u = true := by
  have hd1 := (dataOK_spec D hd).1
  have hx0 := (dataOK_spec D hd).2.1
  unfold e1K0 at h0
  unfold e1K1 at h1
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at h0 h1
  obtain ⟨⟨hF, hxI⟩, hxc⟩ := h0
  obtain ⟨⟨⟨⟨⟨⟨hvI, hvel⟩, hmul⟩, hsq⟩, hlen⟩, hnorm⟩, hstab⟩ := h1
  unfold Tab.e1P1
  rw [decide_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hc hne
    rw [isInv_eq ht hd] at hi hj ⊢
    rw [mulT_eq D ht, mulT_eq D ht, f64_eq_f64 (mul_lt D _ _) (mul_lt D _ _)] at hc
    rw [mulT_eq D ht, val_f64_mul]
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases hF i.val (mem_r64 i.2) j.val (mem_r64 j.2) with h | h
    · simp [hi, hj, hc, hne'] at h
    · exact h
  · rw [isInv_eq ht hd, x0i_val ht hd]
    exact hxI
  · intro i
    rw [mulT_eq D ht, mulT_eq D ht, x0i_val ht hd, hxc i.val (mem_r64 i.2)]
  · rw [vIE1_eq ht hd, isInv_eq ht hd, val_f64 (vIK_lt D A)]
    exact hvI
  · rw [vIE1_eq ht hd]
    exact hvel
  · intro i j hi hj
    rw [eVec_iff ht hd] at hi hj
    obtain ⟨hm, hc⟩ := hmul i.val hi j.val hj
    rw [mulT_eq D ht, mulT_eq D ht, eVec_iff_f64 ht hd A (mul_lt D _ _), hc]
    exact ⟨hc ▸ hm, rfl⟩
  · intro i hi
    rw [eVec_iff ht hd] at hi
    rw [mulT_eq D ht, one_eq D ht, hsq i.val hi]
  · simp only [eVec_get ht hd]
    rw [card_filter_r64, ← eLK_eq]
    exact hlen
  · intro s i hi
    rw [eVec_iff ht hd] at hi
    rw [mulT_eq D ht, mulT_eq D ht, inv_eq D ht, val_f64_mul, val_f64_g6,
      eVec_iff_f64 ht hd A (mul_lt D _ _)]
    exact hnorm s.val (mem_r64 s.2) i.val hi
  · intro i hi
    rw [eVec_iff ht hd] at hi
    rw [tblOf_get_eq, eVec_iff_f64 ht hd A (g6_lt _ _)]
    exact hstab i.val hi

theorem e1P2_of (A : Nat) (h2 : e1K2 D A = true) (u : Fin 64) :
    (mkTab n).e1P2 (tblOf A) u = true := by
  unfold e1K2 at h2
  simp only [List.all_eq_true, beq_iff_eq, List.mem_filter, r64, List.mem_range,
    Bool.and_eq_true] at h2
  unfold Tab.e1P2
  rw [decide_eq_true_iff]
  intro i j hi hj hVi hVj hXi hXj
  rw [isInv_eq ht hd] at hi hj
  rw [reachV ht hd] at hVi hVj
  rw [reachX ht hd, mulT_eq D ht, val_f64_mul, x0i_val ht hd] at hXi hXj
  rw [cls_eq D ht, cls_eq D ht, h2 i.val ⟨i.2, ⟨hi, hVi⟩, hXi⟩, h2 j.val ⟨j.2, ⟨hj, hVj⟩, hXj⟩]

theorem e1P3_of (A : Nat) (h3 : e1K3 D n A = true) (u : Fin 64) :
    (mkTab n).e1P3 (tblOf A) u = true := by
  unfold e1K3 at h3
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h3
  unfold Tab.e1P3
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro r hr i hi
  rw [eVec_iff ht hd] at hi
  obtain ⟨j, hj, hjeq⟩ := h3 r hr i.val hi
  refine ⟨f64 j, (eVec_iff_f64 ht hd A (mem_eLK.1 hj).1).2 hj, ?_⟩
  rw [f64_val] at hjeq
  exact hjeq

theorem e1OK_sound {L : List (Nat × Nat)} (h : e1OK D n L = true) {p : Nat × Nat} (hp : p ∈ L) :
    (mkTab n).e1P1 (tblOf p.1) (f64 p.2) = true ∧ (mkTab n).e1P2 (tblOf p.1) (f64 p.2) = true ∧
      (mkTab n).e1P3 (tblOf p.1) (f64 p.2) = true := by
  unfold e1OK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.2 p hp
  exact ⟨e1P1_of ht hd _ h.1 h1 _, e1P2_of ht hd _ h2 _, e1P3_of ht hd _ h3 _⟩

end Sound

end CFSG.KC.GH74Tab

end
