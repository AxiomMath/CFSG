module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Model

public noncomputable section

namespace CFSG.EvenSmallLie.FFourTwo.Cover

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open scoped commutatorElement

variable {K : Type} [Field K] {M : Type*} [Group M] (C : Cover K M) [Finite M]
  [Group.IsPerfect M]

theorem nf_mulU
    {a b : ℕ} (ha : a < 2 ^ 25) (hb : b < 2 ^ 25) :
    Pc.nf C.gU (mulU a b) = Pc.nf C.gU a * Pc.nf C.gU b ∧ mulU a b < 2 ^ 25 :=
  Pc.nf_mul C.pcData ha hb

theorem nf_invU
    {a : ℕ} (ha : a < 2 ^ 25) :
    Pc.nf C.gU (invU a) = (Pc.nf C.gU a)⁻¹ ∧ invU a < 2 ^ 25 :=
  ⟨(Pc.nf_inv C.pcData a ha).1, (Pc.nf_inv C.pcData a ha).2.1⟩

theorem nf_conjU
    {a x : ℕ} (ha : a < 25) (hx : x < 2 ^ 25) :
    Pc.nf C.gU (conjU a x) = C.gU a * Pc.nf C.gU x * (C.gU a)⁻¹ ∧ conjU a x < 2 ^ 25 := by
  have h2 : 2 ^ a < 2 ^ 25 := Nat.pow_lt_pow_right (by omega) ha
  obtain ⟨m1, m2⟩ := C.nf_mulU h2 hx
  obtain ⟨c1, c2⟩ := Pc.nf_mg C.pcData m2 ha
  refine ⟨?_, c2⟩
  rw [conjU, c1, m1, Pc.nf_two_pow, Pc.g_inv C.pcData ha]

omit [Finite M] [Group.IsPerfect M] in
theorem conj_list_prod (n : M) : ∀ l : List M, n * l.prod * n⁻¹ = (l.map fun x => n * x * n⁻¹).prod
  | [] => by simp
  | x :: l => by
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← conj_list_prod n l]; group

omit [Finite M] [Group.IsPerfect M] in
theorem nf_eq_bits
    {x : ℕ} (hx : x < 2 ^ 25) :
    Pc.nf C.gU x = ((bitsBelow 24 x).map C.gU).prod * ((zPart x).map C.gU).prod := by
  rw [Pc.nf_eq_prod C.gU 25 x hx, show (25 : ℕ) = 24 + 1 from rfl, List.range_succ,
    List.filter_append, List.map_append, List.prod_append, bitsBelow, zPart]
  congr 1
  by_cases h : x.testBit 24 <;> simp [h]

omit [Finite M] [Group.IsPerfect M] in
theorem prod_flatMap' (f : ℕ → List M) :
    ∀ l : List ℕ, (l.flatMap f).prod = (l.map fun a => (f a).prod).prod
  | [] => by simp
  | a :: l => by rw [List.flatMap_cons, List.prod_append, prod_flatMap' f l]; simp

omit [Finite M] [Group.IsPerfect M] in
theorem mem_bitsBelow {n x k : ℕ} (hk : k ∈ bitsBelow n x) : k < n ∧ x.testBit k = true := by
  rw [bitsBelow, List.mem_filter, List.mem_range] at hk
  exact ⟨hk.1, by simpa using hk.2⟩

omit [Finite M] [Group.IsPerfect M] in
theorem conj_zPart {n : M} (x : ℕ) :
    n * ((zPart x).map C.gU).prod * n⁻¹ = ((zPart x).map C.gU).prod := by
  rw [zPart]
  split_ifs
  · rw [List.map_singleton, List.prod_singleton, C.gU_24, mem_center_iff.1 C.z_mem_center n,
      mul_inv_cancel_right]
  · simp


omit [Finite M] [Group.IsPerfect M] in
theorem nf_mulList_zero
    {l : List ℕ} (hl : ∀ k ∈ l, k < 25) (hP : Pc.PcData C.gU cmF 25) :
    Pc.nf C.gU (Pc.mulList cmF 25 0 l) = (l.map C.gU).prod ∧ Pc.mulList cmF 25 0 l < 2 ^ 25 := by
  obtain ⟨h1, h2⟩ := Pc.nf_mulList hP l 0 hl (Nat.two_pow_pos 25)
  rw [Pc.nf_zero, one_mul] at h1
  exact ⟨h1, h2⟩

abbrev nU
    (a : ℕ) (ha : a < 4) : M := C.lift (nX (Cover.fi (3 - a) (by omega)))

theorem nf_weylU
    {a x : ℕ} (ha : a < 4) (hx : x < 2 ^ 25) (hb : x.testBit a = false) :
    Pc.nf C.gU (weylU a x) = C.nU a ha * Pc.nf C.gU x * (C.nU a ha)⁻¹ ∧ weylU a x < 2 ^ 25 := by
  have hl : ∀ k ∈ (bitsBelow 24 x).map (fun k => weylTab.getD (24 * a + k) 0) ++ zPart x,
      k < 25 := by
    intro k hk
    rw [List.mem_append, List.mem_map] at hk
    rcases hk with ⟨k', hk', rfl⟩ | hk
    · obtain ⟨h1, h2⟩ := mem_bitsBelow hk'
      have := (weylTab_spec a ha k' h1
        (by rintro rfl; rw [h2] at hb; exact absurd hb (by decide))).1
      omega
    · rw [zPart] at hk; split_ifs at hk <;> simp_all
  obtain ⟨w1, w2⟩ := C.nf_mulList_zero hl C.pcData
  refine ⟨?_, w2⟩
  have key : ∀ k ∈ bitsBelow 24 x, (C.gU ∘ fun k => weylTab.getD (24 * a + k) 0) k =
      ((fun y => C.nU a ha * y * (C.nU a ha)⁻¹) ∘ C.gU) k := by
    intro k hk
    obtain ⟨h1, h2⟩ := mem_bitsBelow hk
    have hka : k ≠ a := by rintro rfl; rw [h2] at hb; exact absurd hb (by decide)
    obtain ⟨t1, -, t3⟩ := weylTab_spec a ha k h1 hka
    simp only [Function.comp]
    rw [C.gU_lt h1, C.gU_lt t1, C.conj_yhat_nX _ (C.π_lift _) (isRoot_pr h1), eq_of_ofFn t3]
  rw [weylU, w1, C.nf_eq_bits hx, List.map_append, List.prod_append, List.map_map]
  rw [show C.nU a ha * (((bitsBelow 24 x).map C.gU).prod * ((zPart x).map C.gU).prod) *
      (C.nU a ha)⁻¹ = (C.nU a ha * ((bitsBelow 24 x).map C.gU).prod * (C.nU a ha)⁻¹) *
        (C.nU a ha * ((zPart x).map C.gU).prod * (C.nU a ha)⁻¹) by group,
    conj_list_prod, C.conj_zPart, List.map_map, List.map_congr_left key]


theorem conj_neg_gU
    {a k : ℕ} (ha : a < 4) (hk : k < 24) (hka : k ≠ a) :
    C.yhat (-pr a) * C.gU k * (C.yhat (-pr a))⁻¹ =
      ((negTab.getD (24 * a + k) []).map C.gU).prod := by
  have hr := isRoot_pr hk
  have hs : IsRoot .F4 (-pr a) := IsRoot.neg (isRoot_pr (by omega))
  have hne : pr k ≠ pr a := fun e => by
    rcases lt_or_gt_of_ne hka with h | h
    · exact pr_ne a (by omega) k h (congrArg List.ofFn e.symm)
    · exact pr_ne k hk a h (congrArg List.ofFn e)
  have hp : RootPair (pr k) (-pr a) := by
    refine ⟨hr, hs, fun e => ?_, fun e => hne (by rw [e, neg_neg])⟩
    have h1 := height_pr hk
    have h2 := height_pr (show a < 24 by omega)
    have : height (pr k) = -height (pr a) := by rw [e]; simp [height]
    omega
  have e0 : C.yhat (-pr a) * C.yhat (pr k) * (C.yhat (-pr a))⁻¹ =
      C.yhat (pr k) * ⁅C.yhat (pr k), C.yhat (-pr a)⁆ := by
    rw [commutatorElement_def, C.yhat_inv hr]
    simp only [← mul_assoc, C.yhat_mul_self hr, one_mul]
  rw [C.gU_lt hk, e0]
  rcases negOK_all a ha k hk hka with ⟨c1, hx, hw⟩ | ⟨c2, hx1, hx2, hw⟩ | ⟨c3, hx1, hx2, hw⟩ |
    ⟨n1, n2, n3, hw⟩
  · rw [hw, List.map_cons, List.map_singleton, List.prod_cons, List.prod_singleton, C.gU_lt hk,
      C.gU_lt hx.1, pr_of_isIdx hx, C.commutator_yhat_of_dec ⟨hr, hs, rfl, c1⟩]
  · rw [hw, (C.commutator_yhat_mixed_z ⟨hr, hs, c2⟩).1]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [C.gU_lt hk, C.gU_lt hx1.1, C.gU_lt hx2.1, C.gU_24, pr_of_isIdx hx1, pr_of_isIdx hx2]
    group
  · rw [hw, (C.commutator_yhat_mixed_z ⟨hs, hr, c3⟩).2]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [C.gU_lt hk, C.gU_lt hx1.1, C.gU_lt hx2.1, C.gU_24, pr_of_isIdx hx1, pr_of_isIdx hx2]
    group
  · rw [hw, commutatorElement_eq_one_iff_mul_comm.2 (C.commute_yhat hp n1 n2 n3)]
    simp [C.gU_lt hk]

theorem nf_negU
    {a x : ℕ} (ha : a < 4) (hx : x < 2 ^ 25) (hb : x.testBit a = false) :
    Pc.nf C.gU (negU a x) = C.yhat (-pr a) * Pc.nf C.gU x * (C.yhat (-pr a))⁻¹ ∧
      negU a x < 2 ^ 25 := by
  have hka : ∀ k ∈ bitsBelow 24 x, k < 24 ∧ k ≠ a := fun k hk => by
    obtain ⟨h1, h2⟩ := mem_bitsBelow hk
    exact ⟨h1, by rintro rfl; rw [h2] at hb; exact absurd hb (by decide)⟩
  have hl : ∀ k ∈ (bitsBelow 24 x).flatMap (fun k => negTab.getD (24 * a + k) []) ++ zPart x,
      k < 25 := by
    intro k hk
    rw [List.mem_append, List.mem_flatMap] at hk
    rcases hk with ⟨k', hk', hk⟩ | hk
    · obtain ⟨h1, h2⟩ := hka k' hk'
      rcases negOK_all a ha k' h1 h2 with ⟨-, hx', hw⟩ | ⟨-, hx1, hx2, hw⟩ | ⟨-, hx1, hx2, hw⟩ |
        ⟨-, -, -, hw⟩ <;> rw [hw] at hk <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      · rcases hk with rfl | rfl <;> [omega; exact lt_trans hx'.1 (by omega)]
      · rcases hk with rfl | rfl | rfl | rfl <;>
          [omega; exact lt_trans hx1.1 (by omega); exact lt_trans hx2.1 (by omega); omega]
      · rcases hk with rfl | rfl | rfl | rfl <;>
          [omega; exact lt_trans hx1.1 (by omega); exact lt_trans hx2.1 (by omega); omega]
      · rw [hk]; omega
    · rw [zPart] at hk; split_ifs at hk <;> simp_all
  obtain ⟨w1, w2⟩ := C.nf_mulList_zero hl C.pcData
  refine ⟨?_, w2⟩
  set y := C.yhat (-pr a)
  rw [negU, w1, C.nf_eq_bits hx, List.map_append, List.prod_append, List.map_flatMap,
    prod_flatMap']
  rw [show y * (((bitsBelow 24 x).map C.gU).prod * ((zPart x).map C.gU).prod) * y⁻¹ =
      (y * ((bitsBelow 24 x).map C.gU).prod * y⁻¹) * (y * ((zPart x).map C.gU).prod * y⁻¹) by
    group, conj_list_prod, C.conj_zPart, List.map_map]
  congr 1
  congr 1
  refine List.map_congr_left fun k hk => ?_
  obtain ⟨h1, h2⟩ := hka k hk
  exact (C.conj_neg_gU ha h1 h2).symm

abbrev hEl
    (a : ℕ) : M := C.gU a * C.yhat (-pr a) * (C.gU a * C.yhat (-pr a))

theorem nf_hU
    {a x : ℕ} (ha : a < 4) (hx : x < 2 ^ 25) (hok : hOK a x = true) :
    Pc.nf C.gU (hU a x) = C.hEl a * Pc.nf C.gU x * (C.hEl a)⁻¹ ∧ hU a x < 2 ^ 25 := by
  simp only [hOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨n1, n2⟩ := C.nf_negU ha hx hok.1
  obtain ⟨c1, c2⟩ := C.nf_conjU (by omega : a < 25) n2
  obtain ⟨n3, n4⟩ := C.nf_negU ha c2 hok.2
  obtain ⟨c3, c4⟩ := C.nf_conjU (by omega : a < 25) n4
  refine ⟨?_, c4⟩
  rw [hU, c3, n3, c1, n1]
  group

theorem nf_commHU
    {a x : ℕ} (ha : a < 4) (hx : x < 2 ^ 25) (hok : hOK a x = true) :
    Pc.nf C.gU (commHU a x) = ⁅Pc.nf C.gU x, C.hEl a⁆ ∧ commHU a x < 2 ^ 25 := by
  obtain ⟨h1, h2⟩ := C.nf_hU ha hx hok
  obtain ⟨i1, i2⟩ := C.nf_invU h2
  obtain ⟨m1, m2⟩ := C.nf_mulU hx i2
  refine ⟨?_, m2⟩
  rw [commHU, m1, i1, h1, commutatorElement_def]
  group

theorem reflect_single_self : ∀ i : Fin Tag.F4.rank,
    List.ofFn (reflect .F4 i (Pi.single i 1)) =
      List.ofFn (-Pi.single i 1 : Fin Tag.F4.rank → ℤ) := by
  decide +kernel

omit C [Finite M] [Group.IsPerfect M] in
theorem xr_mul_neg_pow_three
    (hK : Nat.card K = 2) (i : Fin Tag.F4.rank) :
    (xr (K := K) (Pi.single i 1) * xr (-Pi.single i 1)) ^ 3 = 1 := by
  have hα : IsRoot .F4 (Pi.single i 1 : Fin Tag.F4.rank → ℤ) := isRoot_single _ i
  have hc := nX_conj hK i hα
  rw [eq_of_ofFn (reflect_single_self i), nX_eq hK i] at hc
  have h1 := xr_mul_self hK hα
  have h2 := xr_mul_self hK (IsRoot.neg hα)
  set u := xr (K := K) (Pi.single i 1)
  set v := xr (K := K) (-Pi.single i 1)
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right h1
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right h2
  have hw : (u * v * u)⁻¹ = u * v * u := by rw [mul_inv_rev, mul_inv_rev, hu, hv, mul_assoc]
  rw [hw] at hc
  have e : u * v * u * v * u = v :=
    calc u * v * u * v * u = u * v * (u * u) * u * v * u := by rw [h1, mul_one]
      _ = u * v * u * u * (u * v * u) := by simp only [mul_assoc]
      _ = v := hc
  calc (u * v) ^ 3 = u * v * u * v * u * v := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = v * v := by rw [e]
    _ = 1 := h2

omit [Finite M] [Group.IsPerfect M] in
theorem hEl_pow_three
    {a : ℕ} (ha : a < 4) : C.hEl a ^ 3 = 1 := by
  set P := C.gU a * C.yhat (-pr a)
  have hα : pr a = Pi.single (Cover.fi (3 - a) (by omega)) 1 :=
    eq_of_ofFn (pr_simple ⟨a, ha⟩)
  have hP : C.π P = xr (Pi.single (Cover.fi (3 - a) (by omega)) 1) *
      xr (-Pi.single (Cover.fi (3 - a) (by omega)) 1) := by
    rw [map_mul, C.π_gU (by omega), C.π_yhat (IsRoot.neg (isRoot_pr (by omega))), hα]
  have h3 : C.π (P ^ 3) = 1 := by rw [map_pow, hP, xr_mul_neg_pow_three C.card]
  have h6 : P ^ 6 = 1 := by
    rcases (C.ker_iff _).1 h3 with h | h
    · rw [show 6 = 3 * 2 by rfl, pow_mul, h, one_pow]
    · rw [show 6 = 3 * 2 by rfl, pow_mul, h, sq, C.z_mul_z]
  calc C.hEl a ^ 3 = (C.gU a * C.yhat (-pr a)) ^ 6 := by
        rw [hEl]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h6
end CFSG.EvenSmallLie.FFourTwo.Cover
