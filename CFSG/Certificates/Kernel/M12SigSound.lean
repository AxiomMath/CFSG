module

public import Certificates.Data.Kernel.M12Sig
public import CFSG.Certificates.Kernel.M12Cent
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM12
public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.KC.M12Sig

open CFSG CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig CFSG.KC.M12Cent Subgroup
  CFSG.ComponentClassification.M12Cover CFSG.RankThree.Asc83Table
open scoped commutatorElement

theorem sig_tbl_pow_two_pow (g : G12) (n : ℕ) : tbl (g ^ 2 ^ n).1 = tsqIter n (tbl g.1) := by
  induction n generalizing g with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ n ih => rw [pow_succ', pow_mul, ih, tsqIter, tsq, ← tblG_mul, sq]

theorem sig_isTwo_of_pow {g : G12} (h : g ^ 2 ^ 7 = 1) : isTwo (tbl g.1) = true := by
  rw [isTwo, ← sig_tbl_pow_two_pow, h, tblG_one]
  exact beq_self_eq_true _

theorem sig_pow_two_pow_seven {Y : Subgroup G12} (hY : IsPGroup 2 Y)
    {y : G12} (hy : y ∈ Y) : y ^ 2 ^ 7 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hY.exists_card_eq
  have hdvd : 2 ^ n ∣ Nat.card G12 := hn ▸ Subgroup.card_subgroup_dvd_card Y
  rw [CFSG.Sporadic.Mathieu.card_M12] at hdvd
  have hn7 : n ≤ 7 := by
    by_contra hc
    have h8 : 2 ^ 8 ∣ 95040 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  have : (⟨y, hy⟩ : Y) ^ 2 ^ 7 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (_root_.orderOf_dvd_natCard _).trans (hn ▸ pow_dvd_pow 2 hn7)
  simpa using congrArg Subtype.val this

theorem sig_not_three_dvd {G : Type*} [Group G] [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  rw [hn]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem sig_length_le_card {H : Subgroup G12} {L : List (List ℕ)} (hL : L.Nodup)
    (hmem : ∀ t ∈ L, ∃ g ∈ H, tbl g.1 = t) : L.length ≤ Nat.card H := by
  classical
  choose f hfH hft using hmem
  let e : {t // t ∈ L} → H := fun t => ⟨f t.1 t.2, hfH t.1 t.2⟩
  have hinj : Function.Injective e := by
    intro s t hst
    have h := congrArg (fun g : H => tbl g.1.1) hst
    change tbl (f s.1 s.2).1 = tbl (f t.1 t.2).1 at h
    rw [hft, hft] at h
    exact Subtype.ext h
  rw [← card_mem_list L hL]
  exact Nat.card_le_card_of_injective e hinj

theorem sig_tbl_mem_of_card {H : Subgroup G12} {L : List (List ℕ)} (hL : L.Nodup)
    (hmem : ∀ t ∈ L, ∃ g ∈ H, tbl g.1 = t) (hcard : Nat.card H ≤ L.length) :
    ∀ g ∈ H, tbl g.1 ∈ L := by
  classical
  choose f hfH hft using hmem
  let e : {t // t ∈ L} → H := fun t => ⟨f t.1 t.2, hfH t.1 t.2⟩
  have hinj : Function.Injective e := by
    intro s t hst
    have h := congrArg (fun g : H => tbl g.1.1) hst
    change tbl (f s.1 s.2).1 = tbl (f t.1 t.2).1 at h
    rw [hft, hft] at h
    exact Subtype.ext h
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_mem_list L hL]; exact hcard)
  intro g hg
  obtain ⟨t, ht⟩ := hbij.2 ⟨g, hg⟩
  have h := congrArg (fun g : H => tbl g.1.1) ht
  change tbl (f t.1 t.2).1 = tbl g.1 at h
  rw [hft] at h
  exact h ▸ t.2

theorem sig_isElemAbelian (B : E9Basis G12) : CFSG.Assembly.IsElemAbelian 3 B.sub :=
  ⟨B.isElementaryAbelian.toIsMulCommutative, fun g hg => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      B.isElementaryAbelian.exponent_dvd_p ⟨g, hg⟩
    simpa using congrArg Subtype.val h⟩

theorem sig_comm (B : E9Basis G12) : ∀ a ∈ B.sub, ∀ b ∈ B.sub, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val ((sig_isElemAbelian B).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem invariant_eq_bot_of_cent (B : E9Basis G12)
    (hT : ∀ e ∈ B.sub, e ≠ 1 → Nat.card (centralizer ({e} : Set G12)) = 54)
    (hC : Nat.card (centralizer (B.sub : Set G12)) = 9) :
    invariantPiSubgroups ⊤ B.sub (piOf 2) = {⊥} := by
  ext X
  rw [Set.mem_singleton_iff]
  refine ⟨fun hX => ?_, ?_⟩
  · rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hX
    exact Sec4.Item434SporGen.eq_bot_of_le_normalizer_of_cent (sig_isElemAbelian B) B.card
      (sig_not_three_dvd hX.2.1) hX.2.2 hT
      (Sec4.Item434SporGen.mem_of_commute_of_card B.card hC (sig_comm B))
  · rintro rfl
    exact bot_mem_invariantPiSubgroups _ _ _

theorem sig_tbl_ai (i : ℕ) : tbl (⁅x, y⁆ ^ i * (x * y)).1 = aiT i := by
  rw [tblG_mul, tblG_pow, tbl_z, tbl_a]
  rfl

theorem sig_mem_cent_iff (i : ℕ) (g : G12) :
    g ∈ centralizer ({⁅x, y⁆ ^ i * (x * y)} : Set G12) ↔ predC [aiT i] (tbl g.1) = true := by
  rw [mem_centralizer_singleton_iff, predC, List.all_cons, List.all_nil, Bool.and_true,
    beq_iff_eq, ← sig_tbl_ai, ← tblG_mul, ← tblG_mul]
  exact eq_iff_tbl

theorem sig_ai_conj (hx : xconjB xT = true) {i : ℕ} (hi : i < 3) :
    x ^ i * (x * y) * (x ^ i)⁻¹ = ⁅x, y⁆ ^ i * (x * y) := by
  rw [eq_iff_tbl, tblG_conj, tblG_pow, tbl_x, tbl_a, sig_tbl_ai]
  have h := List.all_eq_true.mp hx i (List.mem_range.mpr hi)
  rw [beq_iff_eq] at h
  exact h

theorem sig_conj_a_of_comm {c : G12} (hc : c ∈ centralizer ({x * y} : Set G12)) :
    tconj (tbl c.1) aT = aT := by
  have h : c * (x * y) * c⁻¹ = x * y := by
    have h1 := mem_centralizer_singleton_iff.mp hc
    first
    | (rw [h1]; group)
    | (rw [← h1]; group)
  have h2 := congrArg (fun g : G12 => tbl g.1) h
  simp only [tblG_conj, tbl_a] at h2
  exact h2

theorem card_centralizer_a_le
    (hN : Nat.card (normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)) = 72)
    (hinv : invB invW = true) : Nat.card (centralizer ({x * y} : Set G12)) ≤ 36 := by
  set N := normalizer ((zpowers (x * y) : Subgroup G12) : Set G12) with hNdef
  set C := centralizer ({x * y} : Set G12) with hCdef
  have hCN : C ≤ N := by
    intro c hc
    rw [hNdef, mem_normalizer_zpowers_iff tbl_a a_cube a_ne_one, sig_conj_a_of_comm hc]
    simp
  have hw : tconj (tbl (wG invW).1) aT = tpow aT 2 := by
    have h := tbl_wG_conj invW (x * y)
    rw [tblG_conj, tbl_a] at h
    exact h.trans (beq_iff_eq.mp hinv)
  have hwN : wG invW ∈ N := by
    rw [hNdef, mem_normalizer_zpowers_iff tbl_a a_cube a_ne_one, hw]
    simp
  have hwC : wG invW ∉ C := by
    intro hc
    have h := sig_conj_a_of_comm hc
    rw [hw] at h
    exact absurd h (by decide +kernel)
  have hdvd : Nat.card C ∣ 72 := hN ▸ Subgroup.card_dvd_of_le hCN
  have hne : Nat.card C ≠ 72 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hCN (by rw [h, hN])
    exact hwC (this ▸ hwN)
  obtain ⟨m, hm⟩ := hdvd
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · omega
    · omega
    · omega
  have := Nat.mul_le_mul_left (Nat.card C) hm2
  omega

theorem sig_length_idxC {i : ℕ} (hi : i < 3) : (idxC i).length = 36 := by
  interval_cases i <;> rfl

theorem mem_C_of_facts
    (hN : Nat.card (normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)) = 72)
    (hinv : invB invW = true) (hx : xconjB xT = true) (hL : centL = true) :
    ∀ i < 3, ∀ g : G12, g * (⁅x, y⁆ ^ i * (x * y)) = ⁅x, y⁆ ^ i * (x * y) * g →
      ∃ k ∈ idxC i, tbl g.1 = prodT k := by
  intro i hi g hg
  have hLi := List.all_eq_true.mp hL i (List.mem_range.mpr hi)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hLi
  have hcard : Nat.card (centralizer ({⁅x, y⁆ ^ i * (x * y)} : Set G12)) ≤
      ((idxC i).map prodT).length := by
    rw [← sig_ai_conj hx hi, card_centralizer_conj, List.length_map, sig_length_idxC hi]
    exact card_centralizer_a_le hN hinv
  have hreal : ∀ t ∈ (idxC i).map prodT,
      ∃ g ∈ centralizer ({⁅x, y⁆ ^ i * (x * y)} : Set G12), tbl g.1 = t := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    refine ⟨⟨prodP k, prodP_mem k⟩, ?_, tbl_prodP k⟩
    rw [sig_mem_cent_iff]
    have h := List.all_eq_true.mp hLi.1 k hk
    rw [← tbl_prodP k] at h
    exact h
  have hgC : g ∈ centralizer ({⁅x, y⁆ ^ i * (x * y)} : Set G12) := by
    rw [mem_centralizer_singleton_iff]
    first
    | exact hg
    | exact hg.symm
  obtain ⟨k, hk, he⟩ := List.mem_map.mp (sig_tbl_mem_of_card hLi.2 hreal hcard g hgC)
  exact ⟨k, hk, he.symm⟩

theorem vstruct_of (hV : chkVStruct = true) (i : Fin 3) :
    tid ∈ VT i ∧ (∀ s ∈ VT i, ∀ t ∈ VT i, tmul s t ∈ VT i) ∧ (∀ s ∈ VT i, tinv s ∈ VT i) ∧
    (VT i).Nodup ∧ (VT i).length = 4 ∧ (∀ s ∈ VT i, commT (aiT i) s = true) ∧
    (∀ f ∈ AT, ∀ v ∈ VT i, tconj f v ∈ VT i) ∧
    (∀ u ∈ VT i, u ≠ tid → (∃ f ∈ AT, tconj f u = vg1 i) ∧ ∃ f ∈ AT, tconj f u = vg2 i) ∧
    (∀ j ∈ List.range 3, j ≠ i.val → vg1 i ∉ VT j) ∧
    (∀ s ∈ P0T, ∃ w ∈ List.range 3, ∀ v ∈ VT i, tconj (tinv s) v ∈ VT w) ∧
    (∀ w ∈ List.range 3, ∃ s ∈ P0T, ∀ v ∈ VT i, tconj (tinv s) v ∈ VT w) := by
  have h := List.all_eq_true.mp hV i.val (List.mem_range.mpr i.isLt)
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun u hu hne => (h8 u hu).resolve_left hne, ?_, h10, h11⟩
  intro j hj hji hmem
  rcases h9 j hj with h | h
  · exact hji h
  · rw [Bool.eq_false_iff] at h
    exact h (List.contains_iff_mem.mpr hmem)

@[expose] def VS (hV : chkVStruct = true) (i : Fin 3) : Subgroup G12 where
  carrier := {g | tbl g.1 ∈ VT i}
  mul_mem' {g h} hg hh := by
    change tbl (g * h).1 ∈ VT i
    rw [tblG_mul]
    exact (vstruct_of hV i).2.1 _ hg _ hh
  one_mem' := by
    change tbl (1 : G12).1 ∈ VT i
    rw [tblG_one]
    exact (vstruct_of hV i).1
  inv_mem' {g} hg := by
    change tbl g⁻¹.1 ∈ VT i
    rw [tblG_inv]
    exact (vstruct_of hV i).2.2.1 _ hg

theorem sig_centralizer_inv (a : G12) :
    centralizer ({a⁻¹} : Set G12) = centralizer ({a} : Set G12) := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem sig_inv_ai {i k : ℕ} (h : tinv (tmul (tpow zT i) (tpow aT 2)) = tmul (tpow zT k) aT) :
    (⁅x, y⁆ ^ i * (x * y) ^ 2)⁻¹ = ⁅x, y⁆ ^ k * (x * y) := by
  rw [eq_iff_tbl, tblG_inv, tblG_mul, tblG_pow, tblG_pow, tbl_z, tbl_a, h, tblG_mul, tblG_pow,
    tbl_z, tbl_a]

theorem sig_cent_A {b : G12} (hb : b ∈ basisA.sub) (hb1 : b ≠ 1) :
    centralizer ({b} : Set G12) = centralizer ({⁅x, y⁆} : Set G12) ∨
      ∃ k : Fin 3,
        centralizer ({b} : Set G12) = centralizer ({⁅x, y⁆ ^ k.val * (x * y)} : Set G12) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := basisA.exists_pow_mul_pow hb
  have hAa : basisA.a = ⁅x, y⁆ := rfl
  rw [hAa, basisA_b] at hb1 ⊢
  have hz2 : ⁅x, y⁆ ^ 2 = ⁅x, y⁆⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact basisA.ha
  interval_cases i <;> interval_cases j
  · simp at hb1
  · exact Or.inr ⟨⟨0, by norm_num⟩, by rw [show (x * y) ^ 1 = x * y from pow_one _]⟩
  · exact Or.inr ⟨⟨0, by norm_num⟩, by
      rw [← sig_centralizer_inv, sig_inv_ai (k := 0) (by decide +kernel)]⟩
  · exact Or.inl (by rw [pow_zero, mul_one, pow_one])
  · exact Or.inr ⟨⟨1, by norm_num⟩, by rw [show (x * y) ^ 1 = x * y from pow_one _]⟩
  · exact Or.inr ⟨⟨2, by norm_num⟩, by
      rw [← sig_centralizer_inv, sig_inv_ai (k := 2) (by decide +kernel)]⟩
  · exact Or.inl (by rw [pow_zero, mul_one, hz2, sig_centralizer_inv])
  · exact Or.inr ⟨⟨2, by norm_num⟩, by rw [show (x * y) ^ 1 = x * y from pow_one _]⟩
  · exact Or.inr ⟨⟨1, by norm_num⟩, by
      rw [← sig_centralizer_inv, sig_inv_ai (k := 1) (by decide +kernel)]⟩

theorem sig_inf_cent_eq_bot {Y B : Subgroup G12} (hY : IsPGroup 2 Y)
    (hBY : B ≤ normalizer (Y : Set G12)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    {v : G12} (hv : v ∈ B) (hcv : Nat.card (centralizer ({v} : Set G12)) = 54)
    (hCB : Nat.card (centralizer (B : Set G12)) = 9) :
    Y ⊓ centralizer ({v} : Set G12) = ⊥ := by
  set W := Y ⊓ centralizer ({v} : Set G12) with hWdef
  have hW54 : Nat.card W ∣ 54 := by
    rw [← hcv]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hW3 : ¬ 3 ∣ Nat.card W := fun h3 =>
    sig_not_three_dvd hY (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hc3 : Nat.Coprime (Nat.card W) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3).symm
  have hW2 : Nat.card W ∣ 2 :=
    (Nat.Coprime.pow_right 3 hc3).dvd_of_dvd_mul_right
      (by rw [show (2 : ℕ) * 3 ^ 3 = 54 by norm_num]; exact hW54)
  by_contra hne
  obtain ⟨t, htW, ht1⟩ : ∃ t ∈ W, t ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (eq_bot_iff.mpr fun s hs => (Subgroup.mem_bot).mpr (hall s hs))
  have hWc : Nat.card W = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hW2 with h1 | h2
    · exfalso
      have hW1 := Subgroup.card_eq_one.mp h1
      rw [hW1] at htW
      exact ht1 (Subgroup.mem_bot.mp htW)
    · exact h2
  have htB : ∀ c ∈ B, t * c = c * t := by
    intro c hc
    have hcv : c * v = v * c := hab c hc v hv
    have htv : t * v = v * t := Subgroup.mem_centralizer_singleton_iff.mp htW.2
    have hctc : c * t * c⁻¹ ∈ W := by
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hBY hc) t).mp htW.1,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hcv' : c⁻¹ * v = v * c⁻¹ := by
        calc c⁻¹ * v = c⁻¹ * (v * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * v) * c⁻¹ := by rw [hcv]
          _ = v * c⁻¹ := by group
      calc c * t * c⁻¹ * v = c * t * (v * c⁻¹) := by rw [mul_assoc (c * t), hcv']
        _ = c * (t * v) * c⁻¹ := by group
        _ = c * (v * t) * c⁻¹ := by rw [htv]
        _ = (c * v) * t * c⁻¹ := by group
        _ = (v * c) * t * c⁻¹ := by rw [hcv]
        _ = v * (c * t * c⁻¹) := by group
    have hne1 : c * t * c⁻¹ ≠ 1 := by
      intro h1
      apply ht1
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have heq := Sec4.Item434SporM11.eq_of_mem_of_card_eq_two hWc hctc htW hne1 ht1
    calc t * c = c * t * c⁻¹ * c := by rw [heq]
      _ = c * t := by group
  have htC : t ∈ centralizer (B : Set G12) :=
    Subgroup.mem_centralizer_iff.mpr fun c hc => (htB c hc).symm
  have ho : orderOf t = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (hWc ▸ Subgroup.orderOf_dvd_natCard W htW) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have h2 := Subgroup.orderOf_dvd_natCard (centralizer (B : Set G12)) htC
  rw [ho, hCB] at h2
  omega

theorem sig_vv (hvv : vvB VT = true) {i j : Fin 3} (hij : i.val < j.val) {v w : List ℕ}
    (hv : v ∈ VT i) (hw : w ∈ VT j) (hv1 : v ≠ tid) (hw1 : w ≠ tid) :
    isTwo (tmul v w) = false := by
  have key : ∀ p ∈ [((0 : ℕ), (1 : ℕ)), (0, 2), (1, 2)], ∀ v ∈ VT p.1, ∀ w ∈ VT p.2,
      (v == tid || w == tid || !isTwo (tmul v w)) = true := by
    intro p hp v hv w hw
    exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hvv p hp) v hv) w hw
  have hp : (i.val, j.val) ∈ [((0 : ℕ), (1 : ℕ)), (0, 2), (1, 2)] := by
    have hi := i.isLt
    have hj := j.isLt
    interval_cases hiv : i.val <;> interval_cases hjv : j.val <;> simp_all
  have h := key _ hp v hv w hw
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · exact absurd h hv1
  · exact absurd h hw1
  · exact h

theorem le_V_of_facts
    (hz : Nat.card (centralizer ({⁅x, y⁆} : Set G12)) = 54)
    (hA : Nat.card (centralizer (basisA.sub : Set G12)) = 9)
    (hC : ∀ i < 3, ∀ g : G12, g * (⁅x, y⁆ ^ i * (x * y)) = ⁅x, y⁆ ^ i * (x * y) * g →
      ∃ k ∈ idxC i, tbl g.1 = prodT k)
    (hV : chkVStruct = true) (hvv : vvB VT = true) (htwo : twoC VT = true) :
    ∀ Y : Subgroup G12, Y ∈ invariantPiSubgroups ⊤ basisA.sub (piOf 2) → Y ≠ ⊥ →
      ∃ i < 3, ∀ y ∈ Y, tbl y.1 ∈ VT i := by
  intro Y hY hne
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hY
  have hcop : Nat.Coprime 3 (Nat.card Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (sig_not_three_dvd hY.2.1)
  have hA9 : 3 ^ 2 ≤ Nat.card basisA.sub := by
    rw [basisA.card]
    norm_num
  have hpiece : ∀ k : Fin 3, ∀ g ∈ Y ⊓ centralizer ({⁅x, y⁆ ^ k.val * (x * y)} : Set G12),
      tbl g.1 ∈ VT k := by
    intro k g hg
    have hgc := mem_centralizer_singleton_iff.mp hg.2
    obtain ⟨m, hm, he⟩ := hC k.val k.isLt g (by first | exact hgc | exact hgc.symm)
    have h2 := sig_isTwo_of_pow (sig_pow_two_pow_seven hY.2.1 hg.1)
    have h := List.all_eq_true.mp (List.all_eq_true.mp htwo k.val (List.mem_range.mpr k.isLt)) m hm
    rw [← he, h2, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
    exact h
  have hzbot : Y ⊓ centralizer ({⁅x, y⁆} : Set G12) = ⊥ :=
    sig_inf_cent_eq_bot hY.2.1 hY.2.2 (sig_comm basisA) (subset_closure (Or.inl rfl)) hz hA
  by_cases hex : ∃ k : Fin 3, Y ⊓ centralizer ({⁅x, y⁆ ^ k.val * (x * y)} : Set G12) ≠ ⊥
  · obtain ⟨k0, hk0⟩ := hex
    have huniq : ∀ k : Fin 3,
        Y ⊓ centralizer ({⁅x, y⁆ ^ k.val * (x * y)} : Set G12) ≠ ⊥ → k = k0 := by
      intro k hk
      by_contra hkk
      obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hk0
      obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hk
      have hvT := hpiece k0 v.1 v.2
      have hwT := hpiece k w.1 w.2
      have hv1' : tbl v.1.1 ≠ tid := fun h =>
        hv1 (Subtype.ext (eq_iff_tbl.mpr (h.trans tblG_one.symm)))
      have hw1' : tbl w.1.1 ≠ tid := fun h =>
        hw1 (Subtype.ext (eq_iff_tbl.mpr (h.trans tblG_one.symm)))
      rcases Nat.lt_or_gt_of_ne (fun h => hkk (Fin.ext h).symm) with hlt | hlt
      · have h1 := sig_vv hvv hlt hvT hwT hv1' hw1'
        have h2 := sig_isTwo_of_pow (sig_pow_two_pow_seven hY.2.1 (Y.mul_mem v.2.1 w.2.1))
        rw [tblG_mul, h1] at h2
        exact Bool.noConfusion h2
      · have h1 := sig_vv hvv hlt hwT hvT hw1' hv1'
        have h2 := sig_isTwo_of_pow (sig_pow_two_pow_seven hY.2.1 (Y.mul_mem w.2.1 v.2.1))
        rw [tblG_mul, h1] at h2
        exact Bool.noConfusion h2
    refine ⟨k0.val, k0.isLt, fun g hg => ?_⟩
    have hle : Y ≤ VS hV k0 := by
      refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three (sig_isElemAbelian basisA) hA9
        hY.2.2 hcop fun b hb hb1 => ?_
      rcases sig_cent_A hb hb1 with h | ⟨k, h⟩
      · rw [h, hzbot]
        exact bot_le
      · rw [h]
        by_cases hk : Y ⊓ centralizer ({⁅x, y⁆ ^ k.val * (x * y)} : Set G12) = ⊥
        · rw [hk]
          exact bot_le
        · obtain rfl := huniq k hk
          exact fun g hg => hpiece k g hg
    exact hle hg
  · push Not at hex
    exfalso
    refine hne (eq_bot_iff.mpr ?_)
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three (sig_isElemAbelian basisA) hA9
      hY.2.2 hcop fun b hb hb1 => ?_
    rcases sig_cent_A hb hb1 with h | ⟨k, h⟩
    · rw [h, hzbot]
    · rw [h, hex k]

theorem cz_words {g : G12} {S W C R : List (List ℕ)}
    (h : centCheck (tbl g.1) S W C R = true) :
    ∀ c ∈ centralizer ({g} : Set G12), ∃ w ∈ C, tbl c.1 = wordN w := by
  have hcard := card_centralizer_self h
  unfold centCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hC⟩, -⟩, hCc⟩, hCk⟩, -⟩ := h
  have hnd : (C.map wordN).Nodup := by
    have hp := pairwise_of_incr hCk
    have : ((C.map wordN).map keyT).Nodup := by
      rw [List.map_map]
      exact hp.imp (fun h => Nat.ne_of_lt h)
    exact this.of_map _
  have hreal : ∀ t ∈ C.map wordN, ∃ c ∈ centralizer ({g} : Set G12), tbl c.1 = t := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    refine ⟨wG w, ?_, tbl_wG w⟩
    rw [mem_centralizer_singleton_iff, eq_iff_tbl, tblG_mul, tblG_mul, tbl_wG]
    have := List.all_eq_true.1 hCc _ hw
    rw [beq_iff_eq] at this
    first
    | exact this
    | exact this.symm
  intro c hc
  have hm := sig_tbl_mem_of_card hnd hreal (by rw [hcard, List.length_map, hC]) c hc
  obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
  exact ⟨w, hw, he.symm⟩

theorem sig_aux_comm {G : Type*} [Group G] {g h Z bZ : G} (h1 : h * bZ * h⁻¹ = Z)
    (h2 : g * bZ * g⁻¹ = Z) : g * h⁻¹ * Z = Z * (g * h⁻¹) := by
  have hb : bZ = h⁻¹ * Z * h := by
    rw [← h1]
    group
  rw [hb] at h2
  calc g * h⁻¹ * Z = g * (h⁻¹ * Z * h) * g⁻¹ * (g * h⁻¹) := by group
    _ = Z * (g * h⁻¹) := by rw [h2]

theorem sig_aux_conj {G : Type*} [Group G] {g w h A bA : G} (hg : g = w * h)
    (ha : g * bA * g⁻¹ = A) : w * (h * bA * h⁻¹) * w⁻¹ = A := by
  rw [← ha, hg]
  group

theorem sig_bz :Sec4.Item434SporGen.bzT = zbT := by decide +kernel

theorem sig_ba : tmul Sec4.Item434SporGen.bxT Sec4.Item434SporGen.byT = abT := by decide +kernel

theorem inner_of_outerB
    {C : List (List ℕ)} (h : outerB g1W zbT abT C = true)
    (hC : ∀ c ∈ centralizer ({⁅x, y⁆} : Set G12), ∃ w ∈ C, tbl c.1 = wordN w) :
    ∀ α : MulAut G12, (∀ f ∈ basisA.sub, α f = f) →
      α ∈ (MulAut.conj : G12 →* MulAut G12).range := by
  intro α hα
  obtain ⟨g, hg | hg⟩ := exists_conj_or_conj_mul_beta α
  · exact ⟨g, hg.symm⟩
  · exfalso
    unfold outerB at h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hzm : ⁅x, y⁆ ∈ basisA.sub := subset_closure (Or.inl rfl)
    have ham : x * y ∈ basisA.sub := subset_closure (Or.inr rfl)
    have hz : g * beta ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ := by
      have := hα _ hzm
      rwa [hg, MulAut.mul_apply, MulAut.conj_apply] at this
    have ha : g * beta (x * y) * g⁻¹ = x * y := by
      have := hα _ ham
      rwa [hg, MulAut.mul_apply, MulAut.conj_apply] at this
    have htz : tbl (beta ⁅x, y⁆).1 = zbT := Sec4.Item434SporGen.tbl_beta_z.trans sig_bz
    have hta : tbl (beta (x * y)).1 = abT := by
      rw [map_mul, tblG_mul, Sec4.Item434SporGen.tbl_beta_x, Sec4.Item434SporGen.tbl_beta_y, sig_ba]
    have hg1 : wG g1W * beta ⁅x, y⁆ * (wG g1W)⁻¹ = ⁅x, y⁆ := by
      rw [eq_iff_tbl, tbl_wG_conj, htz, h1, tbl_z]
    have hcomm := sig_aux_comm hg1 hz
    have hcz : g * (wG g1W)⁻¹ ∈ centralizer ({⁅x, y⁆} : Set G12) := by
      rw [mem_centralizer_singleton_iff]
      first
      | exact hcomm
      | exact hcomm.symm
    obtain ⟨w, hw, hcw⟩ := hC _ hcz
    have hcw' : g * (wG g1W)⁻¹ = wG w := eq_iff_tbl.mpr (hcw.trans (tbl_wG w).symm)
    have hg' : g = wG w * wG g1W := by
      rw [← hcw']
      group
    have hne := List.all_eq_true.mp h2 w hw
    rw [bne_iff_ne] at hne
    apply hne
    have e2 := sig_aux_conj hg' ha
    have e3 := congrArg (fun u : G12 => tbl u.1) e2
    simp only [tbl_wG_conj, hta, tbl_a] at e3
    exact e3

end CFSG.KC.M12Sig

end
