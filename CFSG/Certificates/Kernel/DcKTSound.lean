module

public import CFSG.Certificates.Kernel.DcKSound

public section

namespace CFSG.KC.DcK

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.KC.E64F

variable {K : DcK} {xt xti : Nat → Nat → Nat}

theorem gd_eq {f : Nat → Nat} {w : List Nat} (h : ∀ p < K.n, f p = wordF K.ab w p) :
    K.gd f w = wordF K.ab w := by
  funext q
  unfold DcK.gd
  split
  · exact h q ‹_›
  · rfl

theorem tabs_spec (ht : K.tabsOK xt xti 0 K.reps.size = true) {j : Nat} (hj : j < K.reps.size) :
    (∀ p < K.n, xt j p = wordF K.ab (K.reps.getD j []) p) ∧
      ∀ p < K.n, xti j p = wordF K.ab (invW (K.reps.getD j [])) p := by
  unfold DcK.tabsOK at ht
  have h := List.all_eq_true.1 ht j (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩ <;>
  · have hp' := List.all_eq_true.1 h p (List.mem_range.2 hp)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp'
    first | exact hp'.1 | exact hp'.2

theorem conjKeyT_eq (ht : K.tabsOK xt xti 0 K.reps.size = true) {i j : Nat}
    (hi : i < K.reps.size) (hj : j < K.reps.size) (k : Nat) :
    K.conjKeyT xt xti i j k = K.conjKey2 i j k := by
  unfold DcK.conjKeyT DcK.conjKey2
  rw [gd_eq (tabs_spec ht hj).1, gd_eq (tabs_spec ht hi).2]

theorem distOKN_of_T (ht : K.tabsOK xt xti 0 K.reps.size = true) {I : List Nat}
    {P : Nat → Nat → Nat → Nat} (h : K.distOKNT xt xti I P = true) : K.distOKN I P = true := by
  simp only [DcK.distOKNT, DcK.distOKN, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h ⊢
  obtain ⟨h1, h3⟩ := h
  refine ⟨h1, fun i hi j hj => ?_⟩
  have e : K.noHitKT xt xti i j (P i j) = K.noHitK i j (P i j) := by
    simp only [DcK.noHitKT, DcK.noHitK, conjKeyT_eq ht hi hj]
  rw [← e]
  exact h3 i hi j hj

theorem hitOK_of_T (ht : K.tabsOK xt xti 0 K.reps.size = true) {H : List Nat}
    (h : K.hitOKT xt xti H = true) : K.hitOK H = true := by
  simp only [DcK.hitOKT, DcK.hitOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun j hj => ?_⟩
  have e : K.hitT xt xti j = K.hit j := by
    simp only [DcK.hitT, DcK.hit, conjKeyT_eq ht hj hj]
    rfl
  rw [← e]
  exact h2 j hj

theorem chkAll_of_chkAllKT {D : DcData} {I H : List Nat} {P : Nat → Nat → Nat → Nat}
    (hr : Rel D K) (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true)
    (hV : ∀ V ∈ K.Vs, ∀ k < V.2.2.N, elemK K.n K.B (K.vg V.2.1) (K.nr + V.1.length) V.2.2 k = true)
    (h : chkAllKT K I H P xt xti = true) : D.chkAll = true := by
  simp only [chkAllKT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hl⟩, hd⟩, he⟩, hvs⟩, hh⟩, hm⟩, ht⟩ := h
  refine chkAll_of_chkAllKN (I := I) (H := H) (P := P) hr hR hV ?_
  simp only [chkAllKN, hi, hb, hl, distOKN_of_T ht hd, he, hvs, hitOK_of_T ht hh, hm,
    Bool.and_self]

end CFSG.KC.DcK

end
