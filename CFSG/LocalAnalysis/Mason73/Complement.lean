module

public import CFSG.LocalAnalysis.Mason73.Stab

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

theorem el_hv_eq_el_hv_iff' (hn : 2 ≤ n) {χ χ' : Fin 4 → ℕ} {π σ : Fin81.R0}
    (h : detSum (hv n χ) π) (h' : detSum (hv n χ') σ) :
    el (hv n χ) π h = el (hv n χ') σ h' ↔
      π = σ ∧ ∀ i j, (χ' i + χ j) % 2 = (χ' j + χ i) % 2 := by
  rw [el_eq_el_iff hn, hv_sub_hv_isConst_iff (by omega)]

theorem el_hv_mul (χ χ' : Fin 4 → ℕ) {π σ : Fin81.R0} (h : detSum (hv n χ) π)
    (h' : detSum (hv n χ') σ) :
    el (hv n χ) π h * el (hv n χ') σ h' =
      el (hv n (χ + fun i => χ' ((π : Perm (Fin 4))⁻¹ i))) (π * σ)
        (by rw [← hv_add, ← pv_hv]; exact detSum_mul h h') := by
  rw [el_mul]
  exact el_congr _ _ (by rw [pv_hv, hv_add]) rfl

theorem sgnH_even {π : Fin81.R0} (hπ : Perm.sign (π : Perm (Fin 4)) = 1) :
    sgnH (n := n) π = 0 := by
  rw [sgnH, hπ, map_one, toAdd_one]

theorem detSum_hv_even (hn : 1 ≤ n) {χ : Fin 4 → ℕ} {π : Fin81.R0}
    (hπ : Perm.sign (π : Perm (Fin 4)) = 1) (hχ : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 0) :
    detSum (hv n χ) π := by
  rw [detSum, sgnH_even hπ, add_zero]
  exact detSum_one_iff.1 (detSum_hv hn hχ)

theorem one_eq_el_hv (hn : 1 ≤ n) :
    (1 : L4Model n) = el (hv n ![0, 0, 0, 0]) 1 (detSum_hv hn (by decide)) := by
  rw [← el_zero_one]
  apply el_congr _ _ _ rfl
  funext i
  fin_cases i <;> simp [hv]

abbrev tP : Fin81.R0 := ⟨swap 0 2 * swap 1 3, by decide⟩
abbrev zP : Fin81.R0 := ⟨swap 0 1 * swap 2 3, by decide⟩

@[expose] def uT (hn : 1 ≤ n) : L4Model n :=
  el (hv n ![1, 0, 0, 0]) s23 (detSum_hv_odd hn (sgnH_s23 hn) (by decide))

@[expose] def vT (hn : 1 ≤ n) : L4Model n :=
  el (hv n ![0, 0, 1, 0]) s01 (detSum_hv_odd hn (sgnH_s01 hn) (by decide))

@[expose] def tT (hn : 1 ≤ n) : L4Model n :=
  el (hv n ![0, 0, 0, 0]) tP (detSum_hv_even hn (by decide) (by decide))

@[expose] def uvT (hn : 1 ≤ n) : L4Model n :=
  el (hv n ![1, 0, 0, 1]) zP (detSum_hv_even hn (by decide) (by decide))

theorem uT_mul_self (hn : 2 ≤ n) : uT (n := n) (by omega) * uT (by omega) = 1 := by
  rw [uT, el_hv_mul, one_eq_el_hv (by omega), el_hv_eq_el_hv_iff' hn]
  decide

theorem vT_mul_self (hn : 2 ≤ n) : vT (n := n) (by omega) * vT (by omega) = 1 := by
  rw [vT, el_hv_mul, one_eq_el_hv (by omega), el_hv_eq_el_hv_iff' hn]
  decide

theorem tT_mul_self (hn : 2 ≤ n) : tT (n := n) (by omega) * tT (by omega) = 1 := by
  rw [tT, el_hv_mul, one_eq_el_hv (by omega), el_hv_eq_el_hv_iff' hn]
  decide

theorem uvT_mul_self (hn : 2 ≤ n) : uvT (n := n) (by omega) * uvT (by omega) = 1 := by
  rw [uvT, el_hv_mul, one_eq_el_hv (by omega), el_hv_eq_el_hv_iff' hn]
  decide

theorem uT_mul_vT (hn : 2 ≤ n) : uT (n := n) (by omega) * vT (by omega) = uvT (by omega) := by
  rw [uT, vT, uvT, el_hv_mul, el_hv_eq_el_hv_iff' hn]
  decide

theorem vT_mul_uT (hn : 2 ≤ n) : vT (n := n) (by omega) * uT (by omega) = uvT (by omega) := by
  rw [uT, vT, uvT, el_hv_mul, el_hv_eq_el_hv_iff' hn]
  decide

theorem tT_mul_uT_mul_tT (hn : 2 ≤ n) :
    tT (n := n) (by omega) * uT (by omega) * tT (by omega) = vT (by omega) := by
  rw [tT, uT, vT, el_hv_mul, el_hv_mul, el_hv_eq_el_hv_iff' hn]
  decide

theorem x1T_eq (hn : 1 ≤ n) : x1T (n := n) hn = el (hv n χx1) 1 (detSum_hv hn (by decide)) := rfl
theorem y1T_eq (hn : 1 ≤ n) : y1T (n := n) hn = el (hv n χy1) 1 (detSum_hv hn (by decide)) := rfl
theorem zT_eq (hn : 1 ≤ n) : zT (n := n) hn = el (hv n χz) 1 (detSum_hv hn (by decide)) := rfl

theorem E1_gens_comm (hn : 2 ≤ n) :
    ∀ a ∈ ({x1T (by omega), y1T (by omega), uvT (by omega), tT (by omega)} : Set (L4Model n)),
      ∀ b ∈ ({x1T (by omega), y1T (by omega), uvT (by omega), tT (by omega)} :
        Set (L4Model n)), a * b = b * a := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro a (rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl) <;>
    simp only [x1T_eq, y1T_eq, uvT, tT, el_hv_mul, el_hv_eq_el_hv_iff' hn] <;> decide

abbrev E1 (hn : 2 ≤ n) : Subgroup (L4Model n) :=
  closure {x1T (by omega), y1T (by omega), uvT (by omega), tT (by omega)}

theorem closure_mul_self {G : Type*} [Group G] {S : Set G} (hS : ∀ a ∈ S, a * a = 1)
    (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : ∀ x ∈ closure S, x * x = 1 := by
  have hcc : closure S ≤ centralizer (closure S : Set G) :=
    closure_le_centralizer_closure fun a ha b hb => hc b hb a ha
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.1 (hcc hy) x hx).symm
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [hxy]; group
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem E1_mul_self (hn : 2 ≤ n) : ∀ x ∈ E1 (n := n) hn, x * x = 1 := by
  refine closure_mul_self ?_ (E1_gens_comm hn)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro a (rfl | rfl | rfl | rfl)
  · rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_x1T hn]
  · rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_y1T hn]
  · exact uvT_mul_self hn
  · exact tT_mul_self hn

theorem tT_mem_E1 (hn : 2 ≤ n) : tT (by omega) ∈ E1 (n := n) hn := subset_closure (by simp)

theorem E1_le_centralizer_tT (hn : 2 ≤ n) :
    E1 (n := n) hn ≤ centralizer {tT (by omega)} := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.2
    (mul_comm_of_mul_self (E1_mul_self hn) hx (tT_mem_E1 hn))

theorem four_le_ncard {G : Type*} {s : Set G} {a b c d : G} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hd : d ∈ s) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (hs : s.Finite) : 4 ≤ s.ncard := by
  have hsub : ({a, b, c, d} : Set G) ⊆ s := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  refine le_trans ?_ (Set.ncard_le_ncard hsub hs)
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
    Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
    Set.ncard_insert_of_notMem (by simp [hcd]), Set.ncard_singleton]

theorem card_E1 (hn : 3 ≤ n) : Nat.card (E1 (n := n) (by omega)) = 16 := by
  apply le_antisymm (card_le_sixteen_of_mul_self hn _ (E1_mul_self (by omega)))
  rw [card_eq_card_inf_A_mul]
  have hmem : ∀ x ∈ ({x1T (by omega), y1T (by omega), uvT (by omega), tT (by omega)} :
      Set (L4Model n)), x ∈ E1 (n := n) (by omega) := fun x hx => subset_closure hx
  have hx1 := hmem _ (by simp : x1T (by omega) ∈ ({x1T (by omega), y1T (by omega),
    uvT (by omega), tT (by omega)} : Set (L4Model n)))
  have hy1 := hmem _ (by simp : y1T (by omega) ∈ ({x1T (by omega), y1T (by omega),
    uvT (by omega), tT (by omega)} : Set (L4Model n)))
  have huv := hmem _ (by simp : uvT (by omega) ∈ ({x1T (by omega), y1T (by omega),
    uvT (by omega), tT (by omega)} : Set (L4Model n)))
  have ht := tT_mem_E1 (n := n) (by omega)
  have hz : zT (by omega) ∈ E1 (n := n) (by omega) := by
    rw [← x1T_mul_y1T (by omega)]
    exact mul_mem hx1 hy1
  have h1 : 4 ≤ Nat.card (E1 (n := n) (by omega) ⊓ A n : Subgroup (L4Model n)) := by
    refine le_trans ?_ (Nat.card_coe_set_eq
      ((E1 (n := n) (by omega) ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n))).ge
    refine four_le_ncard (a := 1) (b := zT (by omega)) (c := x1T (by omega))
      (d := y1T (by omega)) (one_mem _) (Subgroup.mem_inf.2 ⟨hz, zT_mem_A _⟩)
      (Subgroup.mem_inf.2 ⟨hx1, x1T_mem_A _⟩) (Subgroup.mem_inf.2 ⟨hy1, y1T_mem_A _⟩)
      ?_ ?_ ?_ ?_ ?_ ?_ (Set.toFinite _) <;>
    simp only [ne_eq, one_eq_el_hv (n := n) (by omega), zT_eq, x1T_eq, y1T_eq,
      el_hv_eq_el_hv_iff' (by omega : 2 ≤ n)] <;> decide
  have h2 : 4 ≤ Nat.card ((E1 (n := n) (by omega)).map piT) := by
    refine le_trans ?_ (Nat.card_coe_set_eq
      (((E1 (n := n) (by omega)).map piT : Subgroup Fin81.R0) : Set Fin81.R0)).ge
    refine four_le_ncard (a := 1) (b := zP) (c := tP) (d := zP * tP) (one_mem _)
      ⟨_, huv, rfl⟩ ⟨_, ht, rfl⟩ ⟨_, mul_mem huv ht, by rw [map_mul]; rfl⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Set.toFinite _)
  calc 16 = 4 * 4 := rfl
    _ ≤ _ := Nat.mul_le_mul h1 h2

theorem x1T_eq_omegaEl (hn : 3 ≤ n) : x1T (n := n) (by omega) = omegaEl hn (1, 0, 1) := by
  rw [omegaEl, dif_pos (by decide), x1T_eq, el_hv_eq_el_hv_iff' (by omega)]
  decide

theorem w1T_eq_omegaEl (hn : 3 ≤ n) : w1T (n := n) hn = omegaEl hn (1, 1, 1) := by
  rw [omegaEl, dif_neg (by decide), w1T, el_eq_el_iff (by omega)]
  refine ⟨rfl, ?_⟩
  have : wv n (pat (1, 1, 1)) - wv n ![1, 0, 0, 0] = hv n (pat (1, 1, 1)) - hv n ![1, 0, 0, 0] := by
    funext i
    simp only [Pi.sub_apply, wv]
    ring
  rw [this, hv_sub_hv_isConst_iff (by omega)]
  decide

abbrev V2 : Subgroup Fin81.R0 := stabP (1, 0, 1)

theorem card_V2 : Nat.card V2 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem centralizer_x1T (hn : 3 ≤ n) :
    centralizer {x1T (n := n) (by omega)} = V2.comap piT := by
  ext s
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap, x1T_eq_omegaEl hn,
    comm_omegaEl_iff hn]
  rfl

theorem card_centralizer_x1T (hn : 3 ≤ n) :
    Nat.card (centralizer {x1T (n := n) (by omega)}) = 2 ^ (3 * n) := by
  rw [centralizer_x1T hn, card_comap_of_surjective' piT_surjective, card_V2]
  change Nat.card (A n) * 4 = _
  rw [card_A (by omega), show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

abbrev V23 : Subgroup Fin81.R0 := stabP (1, 1, 1)

theorem card_V23 : Nat.card V23 = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem mem_V23_iff {π : Fin81.R0} : π ∈ V23 ↔ π = 1 ∨ π = s23 := by
  have key : ∀ π : Perm (Fin 4), π ∈ Fin81.R0 →
      (PatFix π (pat (1, 1, 1)) ↔ π = 1 ∨ π = swap 2 3) := by
    decide
  change PatFix (π : Perm (Fin 4)) (pat (1, 1, 1)) ↔ _
  rw [key _ π.2]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem centralizer_w1T (hn : 3 ≤ n) : centralizer {w1T (n := n) hn} = V23.comap piT := by
  ext s
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap, w1T_eq_omegaEl hn,
    comm_omegaEl_iff hn]
  rfl

theorem card_centralizer_w1T (hn : 3 ≤ n) :
    Nat.card (centralizer {w1T (n := n) hn}) = 2 ^ (3 * n - 1) := by
  rw [centralizer_w1T hn, card_comap_of_surjective' piT_surjective, card_V23]
  change Nat.card (A n) * 2 = _
  rw [card_A (by omega), ← pow_succ]
  congr 1
  omega

theorem card_le_eight_of_le_centralizer_w1T (hn : 3 ≤ n) (E : Subgroup (L4Model n))
    (hE : ∀ x ∈ E, x * x = 1) (hEw : E ≤ centralizer {w1T (n := n) hn}) : Nat.card E ≤ 8 := by
  refine card_le_eight_of_piT_mem hn E hE (τ := s23) fun x hx => ?_
  have := hEw hx
  rw [centralizer_w1T hn, Subgroup.mem_comap] at this
  exact mem_V23_iff.1 this

theorem omegaEl_zero (hn : 3 ≤ n) : omegaEl (n := n) hn (0, 0, 0) = 1 := by
  rw [omegaEl, dif_pos (by decide), one_eq_el_hv (by omega), el_hv_eq_el_hv_iff' (by omega)]
  decide

theorem zT_eq_omegaEl (hn : 3 ≤ n) : zT (n := n) (by omega) = omegaEl hn (0, 1, 1) := by
  rw [omegaEl, dif_pos (by decide), zT_eq, el_hv_eq_el_hv_iff' (by omega)]
  decide

theorem y1T_eq_omegaEl (hn : 3 ≤ n) : y1T (n := n) (by omega) = omegaEl hn (1, 1, 0) := by
  rw [omegaEl, dif_pos (by decide), y1T_eq, el_hv_eq_el_hv_iff' (by omega)]
  decide

theorem card_centralizer_le_of_not_mem_A (hn : 2 ≤ n) {g : L4Model n} (hg : g ∉ A n) :
    Nat.card (centralizer {g}) ≤ 2 ^ (2 * n + 1) := by
  rw [card_eq_card_inf_A_mul]
  have h1 : Nat.card (centralizer {g} ⊓ A n : Subgroup (L4Model n)) ≤ 2 ^ (2 * n - 2) := by
    rw [inf_comm]
    exact card_centA_le hn hg
  have h2 : Nat.card ((centralizer {g}).map piT) ≤ 8 := by
    rw [← Fin81.card_R0]
    exact Subgroup.card_le_card_group _
  calc _ ≤ 2 ^ (2 * n - 2) * 8 := Nat.mul_le_mul h1 h2
    _ = 2 ^ (2 * n + 1) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega

theorem card_centralizer_le (hn : 3 ≤ n) {g : L4Model n} (hg1 : g ≠ 1) (hg2 : g * g = 1)
    (hz : g ≠ zT (by omega)) (hx : g ≠ x1T (by omega)) (hy : g ≠ y1T (by omega)) :
    Nat.card (centralizer {g}) ≤ 2 ^ (3 * n - 1) := by
  by_cases hA : g ∈ A n
  · obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn hA hg2
    rw [card_centralizer_omegaEl hn]
    have key : ∀ p : Fin 2 × Fin 2 × Fin 2, (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 0 →
        p = (0, 0, 0) ∨ p = (0, 1, 1) ∨ p = (1, 0, 1) ∨ p = (1, 1, 0) := by
      decide
    have hodd : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1 := by
      by_contra hne
      rcases key p (by omega) with rfl | rfl | rfl | rfl
      · exact hg1 (omegaEl_zero hn)
      · exact hz (zT_eq_omegaEl hn).symm
      · exact hx (x1T_eq_omegaEl hn).symm
      · exact hy (y1T_eq_omegaEl hn).symm
    rw [card_stabP_of_odd p hodd, ← pow_succ]
    exact le_of_eq (by congr 1; omega)
  · exact (card_centralizer_le_of_not_mem_A (by omega) hA).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))

end CFSG.LocalAnalysis.Mason73
