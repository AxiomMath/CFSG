module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.KerTwoDict
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.InvolutionGraphBound
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.FixOrder13
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMGeom
public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Monster.Existence

section Data

structure ThirteenGraphData {G : Type} [Group G] {B : Type} [Group B] (P : B → Prop) (a : G)
    (c : Fin 9 → G) : Prop where
  trans : ∀ α β β' : G, IsConj a α → IsConj a β → IsConj a β' → IsConj (α * β) (α * β') →
    ∃ g ∈ cent α, g * β * g⁻¹ = β'
  ord : ∀ i, orderOf (c i) = suborbitClassOrder i
  cov : ∀ α β : G, IsConj a α → IsConj a β → ∃ i, IsConj (α * β) (c i)
  shape : ∀ (α β : G) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
    TwoPointShape (cent2 α β) i
  kerTwo : ∀ u : G, IsConj a u → ∃ π : ↥(cent u) →* B, KerTwo u π
  s19 : ∀ H : Subgroup G, TwoPointShape H 1 → 19 ∣ Nat.card H
  s13 : ∀ (H : Subgroup G) (i : Fin 9), (i = 2 ∨ i = 5 ∨ i = 7) → TwoPointShape H i →
    ¬ 13 ∣ Nat.card H
  fi : ∀ H : Subgroup G, TwoPointShape H 3 →
    13 * Nat.card {h : H // orderOf h = 13} ≤ Nat.card H
  th : ∀ H : Subgroup G, TwoPointShape H 4 →
    13 * Nat.card {h : H // orderOf h = 13} ≤ Nat.card H
  b13 : ∀ y : B, orderOf y = 13 →
    {s : B | P s ∧ s * y = y * s}.ncard ≤ 9 ∧ Nat.card (centralizer ({y} : Set B)) ≤ 468
  b19 : ∀ f : B, orderOf f = 2 → 19 ∣ Nat.card (centralizer ({f} : Set B)) → P f

end Data

section Aux

variable {G : Type} [Group G]

theorem orderOf_eq_of_isConj_thirteen {u v : G} (h : IsConj u v) : orderOf u = orderOf v := by
  obtain ⟨w, hw⟩ := isConj_iff.1 h
  rw [← hw, orderOf_conj_eq']

theorem card_centralizer_coe_eq_card_inf (Γ : Subgroup G) (s : Γ) :
    Nat.card (centralizer ({s} : Set Γ)) =
      Nat.card (Γ ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : G), g.1.2, ?_⟩
      invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩
      left_inv := fun g => Subtype.ext (Subtype.ext rfl)
      right_inv := fun g => Subtype.ext rfl }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (by simpa using congrArg Subtype.val h)
  · have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h

@[expose] def stabEquiv {K : Subgroup G} {D : Set G} [MulAction K D]
    (hsmul : ∀ (g : K) (s : D), ((g • s : D) : G) = g * s * g⁻¹) (ω : D) :
    MulAction.stabilizer K ω ≃* ↥(K ⊓ centralizer ({(ω : G)} : Set G)) :=
  { toFun := fun g => ⟨(g.1 : G), g.1.2, mem_centralizer_singleton_iff.2 (by
      have h1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 g.2)
      rw [hsmul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul] at h1
      exact h1)⟩
    invFun := fun h => ⟨⟨(h : G), (mem_inf.1 h.2).1⟩, MulAction.mem_stabilizer_iff.2
      (Subtype.ext (by
        rw [hsmul]
        show (h : G) * (ω : G) * (h : G)⁻¹ = (ω : G)
        rw [mul_inv_eq_iff_eq_mul]
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 h.2).2))⟩
    left_inv := fun g => rfl
    right_inv := fun h => rfl
    map_mul' := fun g h => rfl }

theorem stabilizer_thirteen_card {K : Subgroup G} {D : Set G} [MulAction K D]
    (hsmul : ∀ (g : K) (s : D), ((g • s : D) : G) = g * s * g⁻¹) (ω : D)
    (h : 13 * Nat.card {h : ↥(K ⊓ centralizer ({(ω : G)} : Set G)) // orderOf h = 13} ≤
      Nat.card ↥(K ⊓ centralizer ({(ω : G)} : Set G))) :
    13 * Nat.card {h : MulAction.stabilizer K ω // orderOf (h : K) = 13} ≤
      Nat.card (MulAction.stabilizer K ω) := by
  let e := stabEquiv hsmul ω
  have h1 : Nat.card {h : MulAction.stabilizer K ω // orderOf (h : K) = 13} =
      Nat.card {h : MulAction.stabilizer K ω // orderOf h = 13} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun h => by rw [Subgroup.orderOf_coe])
  rw [h1, card_orderOf_thirteen_congr e, Nat.card_congr e.toEquiv]
  exact h

end Aux

section Suborbit

variable {G : Type} [Group G] [Finite G]

theorem ncard_orbit_comm_le {u x : G} (hx : orderOf x = 13) (hux : u * x = x * u) {O : Set G}
    (hO : ∀ g ∈ cent u, ∀ s ∈ O, g * s * g⁻¹ ∈ O)
    (htrans : ∀ s ∈ O, ∀ s' ∈ O, ∃ g ∈ cent u, g * s * g⁻¹ = s')
    (hS : ∀ β ∈ O, β * x = x * β →
      13 * Nat.card {h : ↥(cent2 u β) // orderOf h = 13} ≤ Nat.card ↥(cent2 u β)) {c : ℕ}
    (hC : Nat.card ↥(cent u ⊓ cent x) ≤ c) :
    13 * {s : G | s ∈ O ∧ s * x = x * s}.ncard ≤ c := by
  by_cases hemp : {s : G | s ∈ O ∧ s * x = x * s} = ∅
  · rw [hemp, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨β₀, hβ₀O, hβ₀x⟩ := Set.nonempty_iff_ne_empty.2 hemp
  have hxC : x ∈ cent u := mem_centralizer_singleton_iff.2 hux.symm
  letI : MulAction (cent u) O := conjSMulOn (cent u) O hO
  have hsmul : ∀ (g : cent u) (s : O), ((g • s : O) : G) = g * s * g⁻¹ := fun g s => rfl
  haveI : MulAction.IsPretransitive (cent u) O := ⟨fun s s' => by
    obtain ⟨g, hg, hgs⟩ := htrans s s.2 s' s'.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgs⟩⟩
  let ω : O := ⟨β₀, hβ₀O⟩
  let t : cent u := ⟨x, hxC⟩
  have ht : orderOf t = 13 := by rw [Subgroup.orderOf_mk]; exact hx
  have htω : t • ω = ω := by
    apply Subtype.ext
    show x * β₀ * x⁻¹ = β₀
    rw [mul_inv_eq_iff_eq_mul]
    exact hβ₀x.symm
  have hS' := stabilizer_thirteen_card hsmul ω (hS β₀ hβ₀O hβ₀x)
  have hC' : Nat.card (centralizer ({t} : Set (cent u))) ≤ c := by
    rw [card_centralizer_coe_eq_card_inf]
    exact hC
  have hfix := thirteen_mul_card_fix_le ω ht htω hS' hC'
  have hcard : Nat.card {y : O // t • y = y} = {s : G | s ∈ O ∧ s * x = x * s}.ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun := fun y => ⟨(y.1 : G), y.1.2, ?_⟩
        invFun := fun s => ⟨⟨s.1, s.2.1⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun s => rfl }
    · have h1 := congrArg Subtype.val y.2
      rw [hsmul] at h1
      have h2 : x * (y.1 : G) * x⁻¹ = y.1 := h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · apply Subtype.ext
      rw [hsmul]
      show x * s.1 * x⁻¹ = s.1
      rw [mul_inv_eq_iff_eq_mul]
      exact s.2.2.symm
  rw [hcard] at hfix
  exact hfix

end Suborbit

section Main

variable {G : Type} [Group G] [Finite G] {B : Type} [Group B] [Finite B] {P : B → Prop} {a : G}
  {c : Fin 9 → G}

theorem class_cases (D : ThirteenGraphData P a c) {x u u' : G} (hx : orderOf x = 13)
    (hu : IsConj a u) (hu' : IsConj a u') (hux : u * x = x * u) (hu'x : u' * x = x * u') :
    ∃ i : Fin 9, IsConj (u * u') (c i) ∧ i ≠ 2 ∧ i ≠ 5 ∧ i ≠ 7 := by
  obtain ⟨i, hi⟩ := D.cov u u' hu hu'
  have hsh := D.shape u u' i hu hu' hi
  have hxmem : x ∈ cent2 u u' :=
    ⟨mem_centralizer_singleton_iff.2 hux.symm, mem_centralizer_singleton_iff.2 hu'x.symm⟩
  have h13 : 13 ∣ Nat.card (cent2 u u') := hx ▸ Subgroup.orderOf_dvd_natCard _ hxmem
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · intro h
    exact D.s13 _ i (Or.inl h) hsh h13
  · intro h
    exact D.s13 _ i (Or.inr (Or.inl h)) hsh h13
  · intro h
    exact D.s13 _ i (Or.inr (Or.inr h)) hsh h13

theorem orderOf_mul_cases (D : ThirteenGraphData P a c) {x u u' : G} (hx : orderOf x = 13)
    (hu : IsConj a u) (hu' : IsConj a u') (hux : u * x = x * u) (hu'x : u' * x = x * u') :
    orderOf (u * u') = 1 ∨ orderOf (u * u') = 2 ∨ orderOf (u * u') = 3 ∨ orderOf (u * u') = 4 ∨
      orderOf (u * u') = 6 := by
  obtain ⟨i, hi, h2, h5, h7⟩ := class_cases D hx hu hu' hux hu'x
  have hord : orderOf (u * u') = suborbitClassOrder i := by
    rw [orderOf_eq_of_isConj_thirteen hi, D.ord i]
  rw [hord]
  fin_cases i <;> simp_all [suborbitClassOrder]

theorem ncard_nbrs_le (D : ThirteenGraphData P a c) {x : G} (hx : orderOf x = 13)
    (hA1 : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u → IsConj a u) {u : G} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hux : u * x = x * u) :
    {u' : G | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ u' ≠ u ∧ u' * u = u * u'}.ncard ≤ 18 := by
  obtain ⟨π, hπ⟩ := D.kerTwo u (hA1 u hu2 hu1 hux)
  have hxC : x ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hux.symm
  have hyo : orderOf (π ⟨x, hxC⟩) = 13 :=
    hπ.orderOf_eq_prime hu2 hu1 (by norm_num) (by norm_num) hxC hx
  obtain ⟨hF9, -⟩ := D.b13 _ hyo
  have hmem : ∀ n ∈ {u' : G | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ u' ≠ u ∧ u' * u = u * u'},
      n ∈ centralizer ({u} : Set G) := fun n hn => mem_centralizer_singleton_iff.2 hn.2.2.2.2
  have hmap : ∀ n (hn : n ∈ {u' : G | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ u' ≠ u ∧
      u' * u = u * u'}), π ⟨n, hmem n hn⟩ ∈ {s : B | P s ∧ s * π ⟨x, hxC⟩ = π ⟨x, hxC⟩ * s} := by
    intro n hn
    obtain ⟨hn2, hn1, hnx, hnu, hnc⟩ := hn
    have hnconj : IsConj a n := hA1 n hn2 hn1 hnx
    have hun2 : orderOf (u * n) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · calc (u * n) ^ 2 = u * (n * u) * n := by simp only [pow_two, mul_assoc]
          _ = u * (u * n) * n := by rw [hnc]
          _ = (u * u) * (n * n) := by group
          _ = 1 := by rw [hu2, hn2, one_mul]
      · intro h
        apply hnu
        have h1 : n = u⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [h1, inv_eq_of_mul_eq_one_right hu2]
    obtain ⟨i, hi, h2, h5, h7⟩ := class_cases D hx (hA1 u hu2 hu1 hux) hnconj hux hnx
    have hord : orderOf (u * n) = suborbitClassOrder i := by
      rw [orderOf_eq_of_isConj_thirteen hi, D.ord i]
    have hi1 : i = 1 := by
      rw [hun2] at hord
      revert hord h2 h5 h7
      fin_cases i <;> simp [suborbitClassOrder]
    subst hi1
    have h19 : 19 ∣ Nat.card (cent2 u n) :=
      D.s19 _ (D.shape u n 1 (hA1 u hu2 hu1 hux) hnconj hi)
    have hw2 : orderOf (π ⟨n, hmem n ⟨hn2, hn1, hnx, hnu, hnc⟩⟩) = 2 :=
      hπ.orderOf_eq_two (hmem n ⟨hn2, hn1, hnx, hnu, hnc⟩) hn2 hn1 hnu
    have hKu : cent2 u n ≤ centralizer ({u} : Set G) := inf_le_left
    have h19w : 19 ∣ Nat.card (centralizer
        ({π ⟨n, hmem n ⟨hn2, hn1, hnx, hnu, hnc⟩⟩} : Set B)) := by
      refine hπ.dvd_of_dvd hu1 hKu ?_ (by norm_num) (by norm_num) h19
      intro k hk
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 hk).2)
    refine ⟨D.b19 _ hw2 h19w, ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hnx
  calc _ ≤ 2 * {s : B | P s ∧ s * π ⟨x, hxC⟩ = π ⟨x, hxC⟩ * s}.ncard :=
        hπ.ncard_le_two_mul hmem (Set.toFinite _) hmap
    _ ≤ 2 * 9 := Nat.mul_le_mul_left 2 hF9
    _ = 18 := by norm_num

theorem card_cent_inf_le (D : ThirteenGraphData P a c) {x : G} (hx : orderOf x = 13)
    (hA1 : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u → IsConj a u) {u : G} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hux : u * x = x * u) : Nat.card ↥(cent u ⊓ cent x) ≤ 936 := by
  obtain ⟨π, hπ⟩ := D.kerTwo u (hA1 u hu2 hu1 hux)
  have hxC : x ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hux.symm
  have hyo : orderOf (π ⟨x, hxC⟩) = 13 :=
    hπ.orderOf_eq_prime hu2 hu1 (by norm_num) (by norm_num) hxC hx
  obtain ⟨-, hC468⟩ := D.b13 _ hyo
  have hK : cent u ⊓ cent x ≤ centralizer ({u} : Set G) := inf_le_left
  have h := hπ.card_le hu1 hK (C := centralizer ({π ⟨x, hxC⟩} : Set B)) (by
    intro k hk
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 hk).2))
  omega

theorem ncard_suborbit_comm_le (D : ThirteenGraphData P a c) {x : G} (hx : orderOf x = 13)
    (hA1 : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u → IsConj a u) {u : G} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hux : u * x = x * u) (i : Fin 9)
    (hi : ∀ H : Subgroup G, TwoPointShape H i →
      13 * Nat.card {h : H // orderOf h = 13} ≤ Nat.card H) :
    {s : G | (IsConj a s ∧ IsConj (u * s) (c i)) ∧ s * x = x * s}.ncard ≤ 72 := by
  have hau : IsConj a u := hA1 u hu2 hu1 hux
  have hclosed : ∀ g ∈ cent u, ∀ s ∈ {s : G | IsConj a s ∧ IsConj (u * s) (c i)},
      g * s * g⁻¹ ∈ {s : G | IsConj a s ∧ IsConj (u * s) (c i)} := by
    intro g hg s hs
    have hgu : g * u = u * g := mem_centralizer_singleton_iff.1 hg
    refine ⟨hs.1.trans (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
    have : u * (g * s * g⁻¹) = g * (u * s) * g⁻¹ := by
      calc u * (g * s * g⁻¹) = (u * g) * s * g⁻¹ := by group
        _ = (g * u) * s * g⁻¹ := by rw [hgu]
        _ = g * (u * s) * g⁻¹ := by group
    rw [this]
    exact (isConj_iff.2 ⟨g, rfl⟩ : IsConj (u * s) (g * (u * s) * g⁻¹)).symm.trans hs.2
  have htrans : ∀ s ∈ {s : G | IsConj a s ∧ IsConj (u * s) (c i)},
      ∀ s' ∈ {s : G | IsConj a s ∧ IsConj (u * s) (c i)}, ∃ g ∈ cent u, g * s * g⁻¹ = s' :=
    fun s hs s' hs' => D.trans u s s' hau hs.1 hs'.1 (hs.2.trans hs'.2.symm)
  have hS : ∀ β ∈ {s : G | IsConj a s ∧ IsConj (u * s) (c i)}, β * x = x * β →
      13 * Nat.card {h : ↥(cent2 u β) // orderOf h = 13} ≤ Nat.card ↥(cent2 u β) :=
    fun β hβ _ => hi _ (D.shape u β i hau hβ.1 hβ.2)
  have h := ncard_orbit_comm_le hx hux hclosed htrans hS (card_cent_inf_le D hx hA1 hu2 hu1 hux)
  have h' : {s : G | (IsConj a s ∧ IsConj (u * s) (c i)) ∧ s * x = x * s}.ncard =
      {s : G | s ∈ {s : G | IsConj a s ∧ IsConj (u * s) (c i)} ∧ s * x = x * s}.ncard := rfl
  omega

theorem ncard_invComm_le (D : ThirteenGraphData P a c) {x : G} (hx : orderOf x = 13)
    (hA1 : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u → IsConj a u) :
    (invComm x).ncard ≤ 451 := by
  have h := ncard_involutions_le (x := x) (d := 18) (e := 144)
    (fun u u' hu2 hu1 hux hu'2 hu'1 hu'x => orderOf_mul_cases D hx (hA1 u hu2 hu1 hux)
      (hA1 u' hu'2 hu'1 hu'x) hux hu'x)
    (fun u hu2 hu1 hux => ncard_nbrs_le D hx hA1 hu2 hu1 hux)
    (fun u hu2 hu1 hux => by
      have h3 := ncard_suborbit_comm_le D hx hA1 hu2 hu1 hux 3 D.fi
      have h4 := ncard_suborbit_comm_le D hx hA1 hu2 hu1 hux 4 D.th
      have hsub : {u' : G | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ orderOf (u * u') = 3} ⊆
          {s : G | (IsConj a s ∧ IsConj (u * s) (c 3)) ∧ s * x = x * s} ∪
          {s : G | (IsConj a s ∧ IsConj (u * s) (c 4)) ∧ s * x = x * s} := by
        rintro u' ⟨hu'2, hu'1, hu'x, hord⟩
        have hconj : IsConj a u' := hA1 u' hu'2 hu'1 hu'x
        obtain ⟨i, hi⟩ := D.cov u u' (hA1 u hu2 hu1 hux) hconj
        have hio : orderOf (u * u') = suborbitClassOrder i := by
          rw [orderOf_eq_of_isConj_thirteen hi, D.ord i]
        rw [hord] at hio
        have hi34 : i = 3 ∨ i = 4 := by
          revert hio
          fin_cases i <;> simp [suborbitClassOrder]
        rcases hi34 with rfl | rfl
        · exact Or.inl ⟨⟨hconj, hi⟩, hu'x⟩
        · exact Or.inr ⟨⟨hconj, hi⟩, hu'x⟩
      calc _ ≤ ({s : G | (IsConj a s ∧ IsConj (u * s) (c 3)) ∧ s * x = x * s} ∪
            {s : G | (IsConj a s ∧ IsConj (u * s) (c 4)) ∧ s * x = x * s}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ _ + _ := Set.ncard_union_le _ _
        _ ≤ 72 + 72 := Nat.add_le_add h3 h4)
  have h2 : (invComm x).ncard ≤ 1 + 18 + 144 + 18 * (18 - 2) := h
  omega

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
