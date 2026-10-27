module

public import CFSG.CGT.M24R.R3Model

public section

namespace CFSG.CGT.M24R.R3

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem card_mul_card_centralizer_le {H : Type*} [Group H] [Finite H] {k m : ℕ} (y : Fin k → H)
    (z : Fin m → H)
    (hz : ∀ i i', (∀ j, (z i)⁻¹ * y j * z i = (z i')⁻¹ * y j * z i') → i = i') :
    m * Nat.card {c : H // ∀ j, c * y j = y j * c} ≤ Nat.card H := by
  set C := {c : H // ∀ j, c * y j = y j * c}
  have hconj : ∀ (c : C) (i : Fin m) (j : Fin k),
      ((c : H) * z i)⁻¹ * y j * ((c : H) * z i) = (z i)⁻¹ * y j * z i := by
    intro c i j
    have hc := c.2 j
    calc ((c : H) * z i)⁻¹ * y j * ((c : H) * z i) = (z i)⁻¹ * ((c : H)⁻¹ * (y j * c)) * z i := by
          group
      _ = (z i)⁻¹ * ((c : H)⁻¹ * (c * y j)) * z i := by rw [hc]
      _ = (z i)⁻¹ * y j * z i := by group
  let f : Fin m × C → H := fun p => (p.2 : H) * z p.1
  have hf : Function.Injective f := by
    rintro ⟨i, c⟩ ⟨i', c'⟩ h
    have h' : (c : H) * z i = (c' : H) * z i' := h
    have hi : i = i' := hz i i' fun j => by rw [← hconj c i j, ← hconj c' i' j, h']
    subst hi
    exact Prod.ext rfl (Subtype.ext (mul_right_cancel h'))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this

@[expose] def yN (j : Fin 4) : N0 := n0 (dExp (yD j))

theorem rep_conjTab (z : N0Word) (j : Fin 4) :
    Rep 24 (compT 24 (compT 24 (wTab (inv10 z)) (wTab (dExp (yD j)))) (wTab z))
      (FreeGroup.lift n0Perm (FreeGroup.mk (inv10 z)) *
        FreeGroup.lift n0Perm (FreeGroup.mk (dExp (yD j))) *
          FreeGroup.lift n0Perm (FreeGroup.mk z)) :=
  Rep.compT (Rep.compT (rep_wTab _) (rep_wTab _)) (rep_wTab _)

theorem tupKey_map_congr {α : Type*} (l : List α) (f g : α → Table)
    (hfg : ∀ x ∈ l, ∀ i < 24, ap (f x) i = ap (g x) i) :
    tupKey (l.map f) = tupKey (l.map g) := by
  unfold tupKey tupPts
  rw [List.flatMap_map, List.flatMap_map,
    List.flatMap_congr fun x hx => List.map_congr_left fun i hi =>
      hfg x hx i (List.mem_range.1 hi)]

theorem conjKey_eq (h : relCheck = true) {z z' : N0Word}
    (hzz : ∀ j, (n0 z)⁻¹ * yN j * n0 z = (n0 z')⁻¹ * yN j * n0 z') :
    conjKey z = conjKey z' := by
  unfold conjKey
  apply tupKey_map_congr
  intro x hx i hi
  simp only [yTabs, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  rw [rep_conjTab z j i hi, rep_conjTab z' j i hi]
  congr 1
  have e := congrArg (rho h) (hzz j)
  simp only [map_mul, map_inv, yN] at e
  simp only [← rho_n0 h, n0_inv10, map_inv]
  exact e

theorem orbit_distinct (h : relCheck = true) {Z : List N0Word} (hnd : (Z.map conjKey).Nodup)
    (i i' : Fin Z.length)
    (hii : ∀ j, (n0 (Z.get i))⁻¹ * yN j * n0 (Z.get i) =
      (n0 (Z.get i'))⁻¹ * yN j * n0 (Z.get i')) : i = i' := by
  have hk := conjKey_eq h hii
  have hlen : (Z.map conjKey).length = Z.length := List.length_map _
  have e : (Z.map conjKey).get (Fin.cast hlen.symm i) =
      (Z.map conjKey).get (Fin.cast hlen.symm i') := by
    simpa using hk
  exact Fin.ext (by simpa using Fin.ext_iff.1 ((List.Nodup.get_inj_iff hnd).1 e))

theorem n0_eq_of_nEq (h : relCheck = true) (hinj : Function.Injective (rho h)) {w w' : N0Word}
    (hw : nEq w w' = true) : n0 w = n0 w' :=
  hinj (rho_eq_of_nEq h hw)

theorem identCheck_spec (h : identCheck = true) :
    nEq (thExp uD) (dExp uD) = true ∧ nEq (nW ++ dExp uD ++ inv10 nW) (dExp bD) = true ∧
      nEq (thExp bD) aW = true ∧ nEq aW [] = false ∧
      (∀ j, nEq (inv10 nW ++ thExp (yD j) ++ nW) (dExp (a1D j)) = true ∧
        nEq (nW ++ thExp (a1D j) ++ inv10 nW) (dExp (b1D j)) = true ∧
        nEq (inv10 wW ++ dExp (yD j) ++ wW) (thExp (b1D j)) = true) ∧
      ∀ i j, nEq (eW i ++ dExp (yD j)) (dExp (yD j) ++ eW i) = true := by
  simp only [identCheck, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, fun j => ⟨(h5 j).1.1, (h5 j).1.2, (h5 j).2⟩, h6⟩

theorem distinctCheck_spec (h : distinctCheck = true) :
    (∀ i i', i ≠ i' → nEq (eW i) (eW i') = false) ∧
      ∀ v v', v ≠ v' → nEq (tWordOf v) (tWordOf v') = false := by
  simp only [distinctCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true, List.mem_finRange, forall_const] at h
  exact ⟨fun i i' hne => (h.1 i i').resolve_left hne, fun v v' hne => (h.2 v v').resolve_left hne⟩

theorem mem_eW_of_commute (h : relCheck = true) (hinj : Function.Injective (rho h))
    (hid : identCheck = true) (hd : distinctCheck = true)
    (ho : ∃ Z : List N0Word, Z.length = 20160 ∧ (Z.map conjKey).Nodup) [Finite N0]
    (hcard : Nat.card N0 ≤ 322560) {c : N0} (hc : ∀ j, c * yN j = yN j * c) :
    ∃ i, c = n0 (eW i) := by
  obtain ⟨Z, hZl, hZ⟩ := ho
  have hcount := card_mul_card_centralizer_le yN
    (fun i : Fin Z.length => n0 (Z.get i)) (orbit_distinct h hZ)
  rw [hZl] at hcount
  have hC : Nat.card {c : N0 // ∀ j, c * yN j = yN j * c} ≤ 16 := by omega
  have hcomm : ∀ i j, n0 (eW i) * yN j = yN j * n0 (eW i) := fun i j => by
    rw [yN, ← n0_append, ← n0_append]
    exact n0_eq_of_nEq h hinj ((identCheck_spec hid).2.2.2.2.2 i j)
  let e : Fin 16 → {c : N0 // ∀ j, c * yN j = yN j * c} := fun i => ⟨n0 (eW i), hcomm i⟩
  have he : Function.Injective e := by
    intro i i' hii
    by_contra hne
    exact n0_ne_of_nEq h ((distinctCheck_spec hd).1 i i' hne) (congrArg Subtype.val hii)
  have hb := he.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact hC)
  obtain ⟨i, hi⟩ := hb.2 ⟨c, hc⟩
  exact ⟨i, (congrArg Subtype.val hi).symm⟩

end CFSG.CGT.M24R.R3
