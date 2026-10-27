module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCheck
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.M24Std.CU43

theorem enumOK_spec {A : Array Table} {cap size : ℕ} (h : enumOK A cap size = true) :
    (∀ x ∈ A, permOK 820 x = true ∧
      CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x) = true) ∧
    (∀ k < size, Rep 820 (mulClosureH 820 A cap).1[k]!
      (tablePerm 820 (mulClosureH 820 A cap).1[k]!)) ∧
    (∀ k < size, tablePerm 820 (mulClosureH 820 A cap).1[k]! ∈ closure (tp 820 '' {x | x ∈ A})) ∧
    (∀ x ∈ closure (tp 820 '' {x | x ∈ A}),
      ∃ k < size, Rep 820 (mulClosureH 820 A cap).1[k]! x) ∧
    Nat.card ↥(closure (tp 820 '' {x | x ∈ A})) = size ∧
    ((mulClosureH 820 A cap).1.toList.map (tablePerm 820)).Nodup ∧
    (mulClosureH 820 A cap).1.size = size := by
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hperm, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  rw [Array.all_eq_true'] at hperm
  have hperm' : ∀ x ∈ A, permOK 820 x = true ∧
      CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x) = true := fun x hx => by
    simpa only [permInvOK, Bool.and_eq_true] using hperm x hx
  obtain ⟨h1, h2, h3⟩ := enum_spec (n := 820) (by norm_num) (A := A)
    (fun x hx => (hperm' x hx).1) (fun x hx => (hperm' x hx).2) (cap := cap) htree hclosed hdist
  have hnodup := nodup_of_hkeysDistinct
    (forall₂_tablePerm (E := (mulClosureH 820 A cap).1)
      (e := fun k => tablePerm 820 (mulClosureH 820 A cap).1[k]!) fun k hk => (h1 k hk).1) hdist
  rw [hsize] at h1 h2 h3
  exact ⟨hperm', fun k hk => (h1 k hk).1, fun k hk => (h1 k hk).2, h2, h3, hnodup, hsize⟩

theorem memCos_spec
    {ks : List ℕ} {x : Table} (hx : permOK 820 x = true) (h : memCos ks x = true) :
    ∃ k ∈ ks, k < 8 ∧ tp 820 x * (tP k)⁻¹ ∈ P := by
  rw [memCos, List.any_eq_true] at h
  obtain ⟨k, hk, hkx⟩ := h
  rw [Bool.and_eq_true, decide_eq_true_eq] at hkx
  obtain ⟨hk8, hin⟩ := hkx
  have hX : CFSG.Monster.B.Co2.Rep 820 (natArr x) (tp 820 x) := co2Rep_natArr_iff.2 (rep_tp hx)
  exact ⟨k, hk, hk8, (inP_iff (CFSG.Monster.B.Co2.rep_compA hX (rep_tArr_inv hk8))).1 hin⟩

theorem mem_G_of_memCos
    {G : Subgroup (Equiv.Perm (Fin 820))} {ks : List ℕ}
    (hG : ∀ x, x ∈ G ↔ ∃ g ∈ P, ∃ k ∈ ks, k < 8 ∧ x = g * tP k) {x : Table}
    (hx : permOK 820 x = true) (h : memCos ks x = true) : tp 820 x ∈ G := by
  obtain ⟨k, hk, hk8, hP⟩ := memCos_spec hx h
  exact (hG _).2 ⟨tp 820 x * (tP k)⁻¹, hP, k, hk, hk8, by group⟩

theorem classOK_card_le {G : Subgroup (Equiv.Perm (Fin 820))} {sizeG csz cap : ℕ}
    (hG : Nat.card G = sizeG) {gG : Array Table} (hgG : ∀ x ∈ gG, tp 820 x ∈ G) {x : Table}
    {xg : Equiv.Perm (Fin 820)} (hx : Rep 820 x xg) (h : classOK gG x cap sizeG csz = true) :
    Nat.card ↥(G ⊓ centralizer ({xg} : Set (Equiv.Perm (Fin 820)))) ≤ csz := by
  simp only [classOK, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨hgp, htree⟩, hdist⟩, hle⟩ := h
  have hperm : ∀ x ∈ gG, permOK 820 x = true ∧
      CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x) = true := fun x hx => by
    simpa only [permInvOK, Bool.and_eq_true] using hgp x hx
  set gGinv := gG.map (invT 820) with hgGinv
  set o := conjClosureH 820 gG gGinv x cap with ho
  have hg : ∀ l < gG.size, Rep 820 gG[l]! (tp 820 gG[l]!) ∧
      Rep 820 gGinv[l]! (tp 820 gG[l]!)⁻¹ ∧ tp 820 gG[l]! ∈ G := by
    intro l hl
    have hmem := getElem!_mem_array hl
    have hr := rep_tp (hperm _ hmem).1
    refine ⟨hr, ?_, hgG _ hmem⟩
    rw [hgGinv, getElem!_pos (gG.map (invT 820)) l (by simpa using hl), Array.getElem_map,
      ← getElem!_pos gG l hl]
    exact rep_invT hr (hperm _ hmem).2
  have hpos : 0 < o.1.size := by
    have := htree
    simp only [conjTreeOK, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  have horb := conjTreeOK_spec G hg hx htree
  have horep : ∀ k < o.1.size, Rep 820 o.1[k]! (tablePerm 820 o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hdist
  have hclass : o.1.size ≤ (conjClass G xg).ncard := by
    have := length_le_ncard_of_nodup honodup (S := conjClass G xg) fun z hz => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hz
      obtain ⟨c, hc, hrep⟩ := horb k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩
    rwa [List.length_map, Array.length_toList] at this
  have hos := ncard_conjClass_mul_card G xg
  rw [hG] at hos
  have hnpos : 0 < (conjClass G xg).ncard := hpos.trans_le hclass
  refine Nat.le_of_mul_le_mul_left ?_ hnpos
  calc (conjClass G xg).ncard * Nat.card ↥(G ⊓ centralizer ({xg} : Set _)) = sizeG := hos
    _ ≤ csz * o.1.size := hle
    _ ≤ csz * (conjClass G xg).ncard := Nat.mul_le_mul_left _ hclass
    _ = (conjClass G xg).ncard * csz := Nat.mul_comm _ _

theorem coverOK_spec {cg : Array Table} {y0 : Table} {cap size : ℕ}
    {yg : Equiv.Perm (Fin 820)} (hy : Rep 820 y0 yg) (he : enumOK cg cap size = true)
    (h : coverOK cg y0 cap = true) :
    ∀ y ∈ closure (tp 820 '' {x | x ∈ cg}), orderOf y = 3 →
      ∃ c ∈ closure (tp 820 '' {x | x ∈ cg}), y = c * yg * c⁻¹ := by
  obtain ⟨hperm, -, -, hcov, -, -, hEsize⟩ := enumOK_spec he
  simp only [coverOK, Bool.and_eq_true, Array.all_eq_true'] at h
  obtain ⟨htree, hall⟩ := h
  set cgInv := cg.map (invT 820) with hcgInv
  set Q := conjClosureH 820 cg cgInv y0 cap with hQ
  set E := (mulClosureH 820 cg cap).1 with hE
  have hg : ∀ l < cg.size, Rep 820 cg[l]! (tp 820 cg[l]!) ∧ Rep 820 cgInv[l]! (tp 820 cg[l]!)⁻¹ ∧
      tp 820 cg[l]! ∈ closure (tp 820 '' {x | x ∈ cg}) := by
    intro l hl
    have hmem := getElem!_mem_array hl
    have hr := rep_tp (hperm _ hmem).1
    refine ⟨hr, ?_, subset_closure ⟨_, hmem, rfl⟩⟩
    rw [hcgInv, getElem!_pos (cg.map (invT 820)) l (by simpa using hl), Array.getElem_map,
      ← getElem!_pos cg l hl]
    exact rep_invT hr (hperm _ hmem).2
  have horb := conjTreeOK_spec (closure (tp 820 '' {x | x ∈ cg})) hg hy htree
  have hQrep : ∀ k < Q.1.size, Rep 820 Q.1[k]! (tablePerm 820 Q.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb k hk
    rw [tablePerm_eq hrep]
    exact hrep
  intro y hy' hy3
  obtain ⟨k, hk, hrepk⟩ := hcov y hy'
  have hmemE : E[k]! ∈ E := getElem!_mem_array (hEsize ▸ hk)
  have hord := hall _ hmemE
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hord
  rcases hord with hord | hord
  · exfalso
    have := (ordTest_iff_perm hrepk (by norm_num)).2 hy3
    rw [this] at hord
    exact Bool.noConfusion hord
  · obtain ⟨k', hk', hyk'⟩ := memT_spec (e := fun k => tablePerm 820 Q.1[k]!) hQrep hrepk hord
    obtain ⟨c, hc, hrep⟩ := horb k' hk'
    refine ⟨c, hc, ?_⟩
    rw [hyk', tablePerm_eq hrep]

end CFSG.EvenSporadicStandard.HSStd.U43
