module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabGroup

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Blueprint CFSG.EvenSporadicStandard.M22Std.TabCheck
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def invs16 (k : Fin 2) : List (Carrier .M22) := (elemWords k).map (wordElt sylowGens)

theorem tab_invs16 (k : Fin 2) : (invs16 k).map tab = elemTabs k := by
  simp only [invs16, elemTabs, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  rw [Function.comp_apply, tab_wordElt, tab_sylowGens]

theorem elemAbOK_spec {L : List Tab} {As : List (List Tab)} (h : elemAbOK L As = true)
    {a b c d : Tab} (ha : a ∈ L) (hia : isInv a = true)
    (hb : b ∈ L) (hib : isInv b = true) (hab : comm a b = true) (hb1 : b ∉ span [a])
    (hc : c ∈ L) (hic : isInv c = true) (hac : comm a c = true) (hbc : comm b c = true)
    (hc2 : c ∉ span [b, a])
    (hd : d ∈ L) (hid : isInv d = true) (had : comm a d = true) (hbd : comm b d = true)
    (hcd : comm c d = true) (hd3 : d ∉ span [c, b, a]) :
    ∃ A ∈ As, ∀ y ∈ A, y ∈ span [d, c, b, a] := by
  unfold elemAbOK at h
  simp only [List.all_eq_true, List.mem_filter] at h
  have h1 := h a ⟨ha, hia⟩ b ⟨⟨hb, hib⟩, hab⟩
  have e1 : decide (b ∉ TabCheck.ext [idTab] a) = true := by simpa [span, TabCheck.ext] using hb1
  simp only [e1, ↓reduceIte] at h1
  simp only [List.all_eq_true, List.mem_filter] at h1
  have h2 := h1 c ⟨⟨⟨hc, hic⟩, hac⟩, hbc⟩
  have e2 : decide (c ∉ TabCheck.ext (TabCheck.ext [idTab] a) b) = true := by
    simpa [span, TabCheck.ext] using hc2
  simp only [e2, ↓reduceIte] at h2
  simp only [List.all_eq_true, List.mem_filter] at h2
  have h3 := h2 d ⟨⟨⟨⟨hd, hid⟩, had⟩, hbd⟩, hcd⟩
  have e3 : decide (d ∉ TabCheck.ext (TabCheck.ext (TabCheck.ext [idTab] a) b) c) = true := by
    simpa [span, TabCheck.ext] using hd3
  simp only [e3, ↓reduceIte] at h3
  simpa [List.any_eq_true, List.all_eq_true, span, TabCheck.ext] using h3

theorem exists_not_mem_of_length_lt {G : Type*} [Group G] (A : Subgroup G) (F : List G)
    (h : F.length < Nat.card A) : ∃ x ∈ A, x ∉ F := by
  classical
  by_contra hcon
  have hsub : (A : Set G) ⊆ ↑F.toFinset := fun x hx => by
    simpa using by_contra fun hxF => hcon ⟨x, hx, hxF⟩
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
  exact absurd (this.trans (List.toFinset_card_le F)) (not_le.2 h)

theorem mul_comm_of_sq {G : Type*} [Group G] {A : Subgroup G} (hsq : ∀ a ∈ A, a * a = 1)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq _ (A.mul_mem hx hy))).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by
      rw [inv_eq_of_mul_eq_one_right (hsq x hx), inv_eq_of_mul_eq_one_right (hsq y hy)]

theorem isInv_tab {x : Carrier .M22} (h1 : x ≠ 1) (h2 : x * x = 1) : isInv (tab x) = true := by
  simp only [isInv, decide_eq_true_eq]
  refine ⟨fun h => h1 (tab_injective (h.trans tab_one.symm)), ?_⟩
  rw [← tab_mul, h2, tab_one]

theorem comm_tab {x y : Carrier .M22} (h : x * y = y * x) : comm (tab x) (tab y) = true := by
  simp only [TabCheck.comm, decide_eq_true_eq, ← tab_mul, h]

theorem ne_one_of_not_mem_spanE {x : Carrier .M22} {gs : List (Carrier .M22)}
    (h : x ∉ spanE gs) : x ≠ 1 := fun hx => h (hx ▸ one_mem_spanE gs)

theorem invs16_spec : ∀ k, (invs16 k).length = 15 ∧ (invs16 k).Nodup ∧
    ∀ x ∈ invs16 k, x ≠ 1 ∧ x * x = 1 := by
  intro k
  obtain ⟨hlen, hnd, hall⟩ := of_decide_eq_true (invsOK_elemTabs k)
  refine ⟨?_, List.Nodup.of_map tab (by rwa [tab_invs16]), fun x hx => ?_⟩
  · rw [← List.length_map (f := tab), tab_invs16]
    exact hlen
  · obtain ⟨h1, h2⟩ := hall (tab x) (by rw [← tab_invs16]; exact List.mem_map_of_mem hx)
    refine ⟨fun h => h1 (by rw [h, tab_one]), tab_injective ?_⟩
    rw [tab_mul, h2, tab_one]

theorem exists_k_of_le (hS : sylowOK gensTab = true)
    (hE : elemAbOK (span gensTab) [elemTabs 0, elemTabs 1] = true)
    {A : Subgroup (Carrier .M22)} (hsq : ∀ a ∈ A, a * a = 1) (hcard : Nat.card A = 2 ^ 4)
    (hle : A ≤ sylowS) : ∃ k : Fin 2, ∀ x ∈ invs16 k, x ∈ A := by
  have hlt : ∀ n, n < 16 → n < Nat.card A := fun n hn => by rw [hcard]; omega
  obtain ⟨x1, hx1A, hx1⟩ := exists_not_mem_of_length_lt A (spanE ([] : List (Carrier .M22)))
    (by rw [length_spanE]; exact hlt _ (by norm_num))
  obtain ⟨x2, hx2A, hx2⟩ := exists_not_mem_of_length_lt A (spanE [x1])
    (by rw [length_spanE]; exact hlt _ (by norm_num))
  obtain ⟨x3, hx3A, hx3⟩ := exists_not_mem_of_length_lt A (spanE [x2, x1])
    (by rw [length_spanE]; exact hlt _ (by norm_num))
  obtain ⟨x4, hx4A, hx4⟩ := exists_not_mem_of_length_lt A (spanE [x3, x2, x1])
    (by rw [length_spanE]; exact hlt _ (by norm_num))
  have hmem : ∀ x ∈ A, tab x ∈ span gensTab := fun x hx =>
    tab_mem_span_of_mem_sylowS hS (hle hx)
  have hc : ∀ {x y}, x ∈ A → y ∈ A → comm (tab x) (tab y) = true := fun hx hy =>
    comm_tab (mul_comm_of_sq hsq hx hy)
  have hn : ∀ {x gs}, x ∉ spanE gs → tab x ∉ span (gs.map tab) := fun h h' =>
    h ((mem_spanE_iff _ _).1 h')
  obtain ⟨T, hT, hTy⟩ := elemAbOK_spec hE (hmem _ hx1A)
    (isInv_tab (ne_one_of_not_mem_spanE hx1) (hsq _ hx1A))
    (hmem _ hx2A) (isInv_tab (ne_one_of_not_mem_spanE hx2) (hsq _ hx2A)) (hc hx1A hx2A) (hn hx2)
    (hmem _ hx3A) (isInv_tab (ne_one_of_not_mem_spanE hx3) (hsq _ hx3A)) (hc hx1A hx3A)
    (hc hx2A hx3A) (hn hx3)
    (hmem _ hx4A) (isInv_tab (ne_one_of_not_mem_spanE hx4) (hsq _ hx4A)) (hc hx1A hx4A)
    (hc hx2A hx4A) (hc hx3A hx4A) (hn hx4)
  have hk : ∃ k : Fin 2, ∀ y ∈ elemTabs k, y ∈ span ([x4, x3, x2, x1].map tab) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact ⟨0, hTy⟩
    · exact ⟨1, hTy⟩
  obtain ⟨k, hk⟩ := hk
  refine ⟨k, fun x hx => ?_⟩
  have hx' : tab x ∈ elemTabs k := by rw [← tab_invs16]; exact List.mem_map_of_mem hx
  exact mem_of_mem_spanE A (by simp [hx1A, hx2A, hx3A, hx4A]) x
    ((mem_spanE_iff _ _).1 (hk _ hx'))

end CFSG.EvenSporadicStandard.M22Std
