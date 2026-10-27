module

public import Certificates.Data.Kernel.L34DCShape

public section

namespace Certificates.L34DC

open CFSG.GH74.KGroups

theorem allN5167_iff {p : Nat → Bool} : ∀ {n : Nat}, allN5167 n p = true ↔ ∀ i < n, p i = true
  | 0 => by simp [allN5167]
  | n + 1 => by
    have e : allN5167 (n + 1) p = (p n && allN5167 n p) := rfl
    rw [e, Bool.and_eq_true, allN5167_iff]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem elt_idx5167 (x : Elt) : elt (idx x) = x := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩, k⟩ := x
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hk := k.isLt
  simp only [elt, idx, idxN, Prod.mk.injEq, GF4.mk.injEq, Fin.ext_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try simp only [Fin.val_mk]) <;> omega

theorem eltN_idx5167 (x : Elt) : eltN (idx x).val = x := by
  have e : (⟨(idx x).val % 192, Nat.mod_lt _ (by decide)⟩ : Fin 192) = idx x :=
    Fin.ext (Nat.mod_eq_of_lt (idx x).isLt)
  change elt ⟨(idx x).val % 192, Nat.mod_lt _ (by decide)⟩ = x
  rw [e, elt_idx5167]

theorem idx_val5167 (x : Elt) (hk : x.2.2.2 = 0) :
    (idx x).val = 16 * x.1.val.val + 4 * x.2.1.val.val + x.2.2.1.val.val := by
  have e : x.2.2.2.val = 0 := by rw [hk]; rfl
  have := x.1.val.isLt
  have := x.2.1.val.isLt
  have := x.2.2.1.val.isLt
  simp only [idx, idxN, e]
  omega

theorem gf4_zero_iff5167 : ∀ g : GF4, g = 0 ↔ g.val.val = 0 := by decide

theorem fin3_add_self5167 : ∀ k : Fin 3, k + k = 0 → k = 0 := by decide

theorem mulE_one_one5167 : mulE one one = one := by decide

theorem elt_zero5167 : elt 0 = one := by decide

theorem sq16_5167 : mulE (elt 16) (elt 16) = one := by decide

theorem sq16_4_5167 :
    mulE (mulE (elt 16) (elt 4)) (mulE (elt 16) (elt 4)) ≠ one := by decide

theorem elt4_V2_5167 : (elt 4).1 = 0 ∧ (elt 4).2.2.2 = 0 := by decide

theorem map_one5167 (h : idemOK5167 = true) (φ : Elt → Elt)
    (hm : ∀ x y, φ (mulE x y) = mulE (φ x) (φ y)) : φ one = one := by
  have hu : mulE (φ one) (φ one) = φ one := by rw [← hm, mulE_one_one5167]
  have hi := allN5167_iff.mp h (idx (φ one)).val (idx (φ one)).isLt
  rw [eltN_idx5167, hu] at hi
  simp only [beq_self_eq_true, Bool.not_true, Bool.or_false, beq_iff_eq] at hi
  have h0 : idx (φ one) = 0 := Fin.ext hi
  rw [← elt_idx5167 (φ one), h0, elt_zero5167]

theorem shape_of_checkShape5167 (h : checkShape5167 = true) (φ : Elt → Elt)
    (hm : ∀ x y, φ (mulE x y) = mulE (φ x) (φ y)) (hi : Function.Injective φ)
    (hV : ∀ x : Elt, x.1 = 0 → x.2.2.2 = 0 → (φ x).1 = 0 ∧ (φ x).2.2.2 = 0) :
    (φ (elt 16)).2.1 = 0 ∧ (φ (elt 16)).2.2.2 = 0 ∧ (φ (elt 16)).1 ≠ 0 ∧
      (φ (elt 4)).1 = 0 ∧ (φ (elt 4)).2.2.2 = 0 ∧ (φ (elt 4)).2.1 ≠ 0 := by
  have hc : idemOK5167 = true ∧ pairsOK5167 = true := by
    simpa only [checkShape5167, Bool.and_eq_true] using h
  have h1 := map_one5167 hc.1 φ hm
  have hYY : mulE (φ (elt 16)) (φ (elt 16)) = one := by rw [← hm, sq16_5167, h1]
  have hYk : (φ (elt 16)).2.2.2 = 0 :=
    fin3_add_self5167 _ (congrArg (fun x : Elt => x.2.2.2) hYY)
  obtain ⟨hZa, hZk⟩ := hV (elt 4) elt4_V2_5167.1 elt4_V2_5167.2
  have hy := idx_val5167 _ hYk
  have hz := idx_val5167 _ hZk
  have hZa' := (gf4_zero_iff5167 _).mp hZa
  have bY1 := (φ (elt 16)).1.val.isLt
  have bY2 := (φ (elt 16)).2.1.val.isLt
  have bY3 := (φ (elt 16)).2.2.1.val.isLt
  have bZ2 := (φ (elt 4)).2.1.val.isLt
  have bZ3 := (φ (elt 4)).2.2.1.val.isLt
  have hyl : (idx (φ (elt 16))).val < 64 := by omega
  have hzl : (idx (φ (elt 4))).val < 16 := by omega
  have hp := allN5167_iff.mp (allN5167_iff.mp hc.2 _ hyl) _ hzl
  have hrel : mulE (mulE (φ (elt 16)) (φ (elt 4))) (mulE (φ (elt 16)) (φ (elt 4))) ≠ one := by
    intro he
    apply sq16_4_5167
    apply hi
    rw [hm, hm, he, h1]
  simp only [pairOK5167, eltN_idx5167, hYY, beq_self_eq_true, Bool.not_true, Bool.or_false,
    beq_eq_false_iff_ne.mpr hrel, Bool.or_false, shapeOK5167, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨hb, ha⟩, hb'⟩ := hp
  refine ⟨(gf4_zero_iff5167 _).mpr (by omega), hYk, fun h0 => ha ?_, hZa, hZk,
    fun h0 => hb' ?_⟩
  · have := (gf4_zero_iff5167 _).mp h0
    omega
  · have := (gf4_zero_iff5167 _).mp h0
    omega

end Certificates.L34DC
