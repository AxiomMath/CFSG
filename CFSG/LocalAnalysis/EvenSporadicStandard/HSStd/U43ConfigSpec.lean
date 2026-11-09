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

theorem mulRecArr_mem {H : Subgroup (Equiv.Perm (Fin 820))} {A : Array Table}
    (hg : ∀ l < A.size, Rep 820 A[l]! (tp 820 A[l]!) ∧ tp 820 A[l]! ∈ H) {par : Array (ℕ × ℕ)}
    (hpar : ∀ i < par.size, par[i]!.1 ≤ i ∧ par[i]!.2 < A.size) :
    (mulRecArr A par).size = par.size + 1 ∧
      ∀ k < (mulRecArr A par).size, ∃ c ∈ H, Rep 820 (mulRecArr A par)[k]! c := by
  unfold mulRecArr
  refine Array.foldl_induction (motive := fun (i : ℕ) (a : Array Table) => a.size = i + 1 ∧
    ∀ k < a.size, ∃ c ∈ H, Rep 820 a[k]! c) ?_ ?_
  · refine ⟨rfl, fun k hk => ?_⟩
    have hk0 : k = 0 := by
      simp only [List.size_toArray, List.length_singleton] at hk
      omega
    subst hk0
    exact ⟨1, H.one_mem, by simpa using Rep.idT (by norm_num : 820 < 2 ^ 32)⟩
  · rintro ⟨i, hi⟩ b ⟨hsz, hb⟩
    change b.size = i + 1 at hsz
    have hp := hpar i hi
    rw [getElem!_pos par i hi] at hp
    obtain ⟨h1, h2⟩ := hp
    simp only [Fin.getElem_fin]
    refine ⟨by rw [Array.size_push, hsz], fun k hk => ?_⟩
    rw [Array.size_push] at hk
    by_cases hki : k < b.size
    · rw [getElem!_pos _ k (by rw [Array.size_push]; omega), Array.getElem_push_lt hki,
        ← getElem!_pos b k hki]
      exact hb k hki
    · have hk' : k = b.size := by omega
      subst hk'
      rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
      obtain ⟨c, hc, hrep⟩ := hb _ (by omega : par[i].1 < b.size)
      obtain ⟨hgl, hgH⟩ := hg _ h2
      exact ⟨c * tp 820 A[par[i].2]!, H.mul_mem hc hgH, Rep.compT hrep hgl⟩

theorem enumRecOK_spec {A : Array Table} {par : Array (ℕ × ℕ)} {size : ℕ}
    (h : enumRecOK A par size = true) :
    (∀ x ∈ A, permOK 820 x = true ∧
      CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x) = true) ∧
    size ≤ Nat.card ↥(closure (tp 820 '' {x | x ∈ A})) := by
  classical
  simp only [enumRecOK, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hperm, hpar⟩, hdist⟩, hle⟩ := h
  have hperm' : ∀ x ∈ A, permOK 820 x = true ∧
      CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x) = true := fun x hx => by
    simpa only [permInvOK, Bool.and_eq_true] using hperm x hx
  refine ⟨hperm', ?_⟩
  set K := closure (tp 820 '' {x | x ∈ A})
  have hga : ∀ l < A.size, Rep 820 A[l]! (tp 820 A[l]!) ∧ tp 820 A[l]! ∈ K := fun l hl =>
    ⟨rep_tp (hperm' _ (getElem!_mem_array hl)).1, subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  obtain ⟨hEsz, hE⟩ := mulRecArr_mem hga (par := par) fun i hi => by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hpar i hi
  set E := mulRecArr A par
  have hrep : ∀ k < E.size, Rep 820 E[k]! (tablePerm 820 E[k]!) := by
    intro k hk
    obtain ⟨c, -, hc⟩ := hE k hk
    rw [tablePerm_eq hc]
    exact hc
  have hnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hrep) hdist
  set L := E.toList.map (tablePerm 820) with hL
  have hsub : (L.toFinset : Set (Equiv.Perm (Fin 820))) ⊆ (K : Set (Equiv.Perm (Fin 820))) := by
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset, hL, List.mem_map] at hx
    obtain ⟨T, hT, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
    obtain ⟨c, hc, hcrep⟩ := hE k hk
    rw [← getElem!_pos E k hk, tablePerm_eq hcrep]
    exact hc
  calc size ≤ par.size + 1 := hle
    _ = (L.toFinset : Set (Equiv.Perm (Fin 820))).ncard := by
        rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, hL, List.length_map,
          Array.length_toList, hEsz]
    _ ≤ (K : Set (Equiv.Perm (Fin 820))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card ↥K := (Nat.card_coe_set_eq _).symm

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

theorem clsRecArr_conj {G : Subgroup (Equiv.Perm (Fin 820))} {gG gGinv : Array Table}
    (hg : ∀ l < gG.size, Rep 820 gG[l]! (tp 820 gG[l]!) ∧
      Rep 820 gGinv[l]! (tp 820 gG[l]!)⁻¹ ∧ tp 820 gG[l]! ∈ G)
    {x : Table} {xg : Equiv.Perm (Fin 820)} (hx : Rep 820 x xg) {par : Array (ℕ × ℕ)}
    (hpar : ∀ i < par.size, par[i]!.1 ≤ i ∧ par[i]!.2 < gG.size) :
    (clsRecArr gG gGinv x par).size = par.size + 1 ∧
      ∀ k < (clsRecArr gG gGinv x par).size, ∃ c ∈ G,
        Rep 820 (clsRecArr gG gGinv x par)[k]! (c * xg * c⁻¹) := by
  unfold clsRecArr
  refine Array.foldl_induction (motive := fun (i : ℕ) (a : Array Table) => a.size = i + 1 ∧
    ∀ k < a.size, ∃ c ∈ G, Rep 820 a[k]! (c * xg * c⁻¹)) ?_ ?_
  · refine ⟨rfl, fun k hk => ?_⟩
    have hk0 : k = 0 := by
      simp only [List.size_toArray, List.length_singleton] at hk
      omega
    subst hk0
    exact ⟨1, G.one_mem, by simpa using hx⟩
  · rintro ⟨i, hi⟩ b ⟨hsz, hb⟩
    change b.size = i + 1 at hsz
    have hp := hpar i hi
    rw [getElem!_pos par i hi] at hp
    obtain ⟨h1, h2⟩ := hp
    simp only [Fin.getElem_fin]
    refine ⟨by rw [Array.size_push, hsz], fun k hk => ?_⟩
    rw [Array.size_push] at hk
    by_cases hki : k < b.size
    · rw [getElem!_pos _ k (by rw [Array.size_push]; omega), Array.getElem_push_lt hki,
        ← getElem!_pos b k hki]
      exact hb k hki
    · have hk' : k = b.size := by omega
      subst hk'
      rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
      obtain ⟨c, hc, hrep⟩ := hb _ (by omega : par[i].1 < b.size)
      obtain ⟨hgl, hgil, hgH⟩ := hg _ h2
      refine ⟨tp 820 gG[par[i].2]! * c, G.mul_mem hgH hc, ?_⟩
      have := rep_conjT hgl hgil hrep
      simpa only [mul_inv_rev, mul_assoc] using this

theorem classRecOK_card_le {G : Subgroup (Equiv.Perm (Fin 820))} {sizeG csz : ℕ}
    (hG : Nat.card G = sizeG) {gG : Array Table} (hgG : ∀ x ∈ gG, tp 820 x ∈ G) {x : Table}
    {xg : Equiv.Perm (Fin 820)} (hx : Rep 820 x xg) {par : Array (ℕ × ℕ)}
    (h : classRecOK gG x par sizeG csz = true) :
    Nat.card ↥(G ⊓ centralizer ({xg} : Set (Equiv.Perm (Fin 820)))) ≤ csz := by
  simp only [classRecOK, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hgp, hpar⟩, hdist⟩, hle⟩ := h
  have hperm : ∀ x ∈ gG, permOK 820 x = true ∧
      CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x) = true := fun x hx => by
    simpa only [permInvOK, Bool.and_eq_true] using hgp x hx
  set gGinv := gG.map (invT 820) with hgGinv
  set o := clsRecArr gG gGinv x par with ho
  have hg : ∀ l < gG.size, Rep 820 gG[l]! (tp 820 gG[l]!) ∧
      Rep 820 gGinv[l]! (tp 820 gG[l]!)⁻¹ ∧ tp 820 gG[l]! ∈ G := by
    intro l hl
    have hmem := getElem!_mem_array hl
    have hr := rep_tp (hperm _ hmem).1
    refine ⟨hr, ?_, hgG _ hmem⟩
    rw [hgGinv, getElem!_pos (gG.map (invT 820)) l (by simpa using hl), Array.getElem_map,
      ← getElem!_pos gG l hl]
    exact rep_invT hr (hperm _ hmem).2
  obtain ⟨hosz, horb⟩ := clsRecArr_conj hg hx (par := par) fun i hi => by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hpar i hi
  have horep : ∀ k < o.size, Rep 820 o[k]! (tablePerm 820 o[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hdist
  have hclass : o.size ≤ (conjClass G xg).ncard := by
    have := length_le_ncard_of_nodup honodup (S := conjClass G xg) fun z hz => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hz
      obtain ⟨c, hc, hrep⟩ := horb k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩
    rwa [List.length_map, Array.length_toList] at this
  have hos := ncard_conjClass_mul_card G xg
  rw [hG] at hos
  have hnpos : 0 < (conjClass G xg).ncard := by
    have := hclass
    rw [hosz] at this
    omega
  refine Nat.le_of_mul_le_mul_left ?_ hnpos
  calc (conjClass G xg).ncard * Nat.card ↥(G ⊓ centralizer ({xg} : Set _)) = sizeG := hos
    _ ≤ csz * o.size := by rw [hosz]; exact hle
    _ ≤ csz * (conjClass G xg).ncard := Nat.mul_le_mul_left _ hclass
    _ = (conjClass G xg).ncard * csz := Nat.mul_comm _ _

theorem coverOK_spec{cg : Array Table} {y0 : Table} {cap size : ℕ}
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
