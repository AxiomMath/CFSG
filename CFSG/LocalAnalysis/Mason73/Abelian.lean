module

public import CFSG.LocalAnalysis.Mason73.Coord
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

theorem isConst_neg_iff {e : Fin 4 → ZMod (2 ^ n)} : IsConst (-e) ↔ IsConst e := by
  constructor
  · intro h i j
    have := h i j
    simpa using this
  · intro h i j
    simp [h i j]

theorem el_comm_diag_iff (hn : 2 ≤ n) {d e : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) (h' : detSum e 1) :
    el d π h * el e 1 h' = el e 1 h' * el d π h ↔ IsConst (pv (π : Perm (Fin 4)) e - e) := by
  rw [el_mul, el_mul, el_eq_el_iff hn]
  simp only [mul_one, one_mul, true_and]
  have : e + pv ((1 : Fin81.R0) : Perm (Fin 4)) d - (d + pv (π : Perm (Fin 4)) e) =
      -(pv (π : Perm (Fin 4)) e - e) := by
    rw [OneMemClass.coe_one, pv_one]
    abel
  rw [this, isConst_neg_iff]

@[expose] def B (n : ℕ) : Subgroup (Multiplicative (Fin 4 → ZMod (2 ^ n))) := (sumL4 n).ker

abbrev vec (e : B n) : Fin 4 → ZMod (2 ^ n) :=
  Multiplicative.toAdd (e : Multiplicative (Fin 4 → ZMod (2 ^ n)))

theorem mem_B {e : Multiplicative (Fin 4 → ZMod (2 ^ n))} :
    e ∈ B n ↔ ∑ i, Multiplicative.toAdd e i = 0 := by
  rw [B, MonoidHom.mem_ker, ← Multiplicative.toAdd.injective.eq_iff]
  rfl

theorem sumL4_surjective : Function.Surjective (sumL4 n) := by
  intro a
  refine ⟨Multiplicative.ofAdd (Pi.single 0 (Multiplicative.toAdd a)), ?_⟩
  apply Multiplicative.toAdd.injective
  change ∑ i, (Pi.single 0 (Multiplicative.toAdd a) : Fin 4 → ZMod (2 ^ n)) i = _
  simp

theorem card_vec : Nat.card (Multiplicative (Fin 4 → ZMod (2 ^ n))) = 2 ^ (4 * n) := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem card_B : Nat.card (B n) = 2 ^ (3 * n) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (sumL4_surjective (n := n))
  rw [card_vec, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
  have h2 : 2 ^ (4 * n) = 2 ^ (3 * n) * 2 ^ n := by rw [← pow_add]; ring_nf
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem detSum_of_mem_B {e : Multiplicative (Fin 4 → ZMod (2 ^ n))} (he : e ∈ B n) :
    detSum (Multiplicative.toAdd e) 1 :=
  detSum_one_iff.2 (mem_B.1 he)

@[expose] def beta : B n →* L4Model n where
  toFun e := el (vec e) 1
    (detSum_of_mem_B e.2)
  map_one' := rfl
  map_mul' e f := by
    rw [el_mul]
    rfl

theorem beta_apply (e : B n) :
    beta e = el (vec e) 1
      (detSum_of_mem_B e.2) := rfl

theorem beta_mem_A (e : B n) : beta e ∈ A n := by
  rw [beta_apply, el_mem_A]

@[expose] def betaA : B n →* A n := (beta (n := n)).codRestrict (A n) beta_mem_A

theorem betaA_surjective : Function.Surjective (betaA (n := n)) := by
  rintro ⟨g, hg⟩
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [el_mem_A] at hg
  subst hg
  have he : Multiplicative.ofAdd d ∈ B n := mem_B.2 (detSum_one_iff.1 h)
  exact ⟨⟨Multiplicative.ofAdd d, he⟩, rfl⟩

theorem card_ker_betaA (hn : 2 ≤ n) : Nat.card (betaA (n := n)).ker = 4 := by
  have h := Subgroup.card_ker_mul_card_of_surjective (betaA_surjective (n := n))
  rw [card_A hn, card_B] at h
  have h2 : 2 ^ (3 * n) = 4 * 2 ^ (3 * n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem card_comap_of_surjective' {G H : Type*} [Group G] [Group H] [Finite G] {f : G →* H}
    (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  have : Finite H := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index (K.comap f)
  have h2 := Subgroup.card_mul_index K
  have h3 := Subgroup.card_ker_mul_card_of_surjective hf
  rw [Subgroup.index_comap_of_surjective K hf] at h1
  have hpos : 0 < K.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  rw [← h3, ← h2] at h1
  rw [← mul_assoc] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem card_comap_beta (hn : 2 ≤ n) {S : Subgroup (L4Model n)} (hS : S ≤ A n) :
    Nat.card (S.comap beta) = 4 * Nat.card S := by
  have hc : S.comap beta = (S.subgroupOf (A n)).comap betaA := by
    ext e
    rfl
  rw [hc, card_comap_of_surjective' betaA_surjective, card_ker_betaA hn]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv

abbrev centA (g : L4Model n) : Subgroup (L4Model n) := A n ⊓ Subgroup.centralizer {g}

theorem isConst_of_mem_comap_centA (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) {e : B n} (he : e ∈ (centA (el d π h)).comap beta) :
    IsConst (pv (π : Perm (Fin 4))
        (vec e) -
      vec e) := by
  have he' : beta e ∈ Subgroup.centralizer {el d π h} :=
    (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 he)).2
  rw [Subgroup.mem_centralizer_singleton_iff, beta_apply] at he'
  exact (el_comm_diag_iff hn h _).1 he'.symm

@[expose] def coordDiff (p q : Fin 4) : B n →* Multiplicative (ZMod (2 ^ n)) where
  toFun e := Multiplicative.ofAdd (vec e p - vec e q)
  map_one' := by simp [vec]
  map_mul' e f := by
    apply Multiplicative.toAdd.injective
    simp only [vec, Subgroup.coe_mul, toAdd_mul, Pi.add_apply, toAdd_ofAdd]
    ring

theorem exists_ne_ne : ∀ p q : Fin 4, ∃ r, r ≠ p ∧ r ≠ q := by decide

theorem coordDiff_surjective {p q : Fin 4} (hpq : p ≠ q) :
    Function.Surjective (coordDiff (n := n) p q) := by
  intro a
  obtain ⟨r, hrp, hrq⟩ := exists_ne_ne p q
  set v : Fin 4 → ZMod (2 ^ n) := Pi.single p (Multiplicative.toAdd a) -
    Pi.single r (Multiplicative.toAdd a) with hv
  have hvB : Multiplicative.ofAdd v ∈ B n := by
    rw [mem_B, toAdd_ofAdd, hv]
    simp [Finset.sum_sub_distrib]
  refine ⟨⟨Multiplicative.ofAdd v, hvB⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change v p - v q = Multiplicative.toAdd a
  rw [hv]
  simp [Pi.single_apply, hrp.symm, hrq.symm, hpq, hpq.symm]

theorem card_ker_coordDiff {p q : Fin 4} (hpq : p ≠ q) :
    Nat.card (coordDiff (n := n) p q).ker = 2 ^ (2 * n) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (coordDiff_surjective (n := n) hpq)
  rw [card_B, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
  have h2 : 2 ^ (3 * n) = 2 ^ (2 * n) * 2 ^ n := by rw [← pow_add]; ring_nf
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem card_centA_le_of_fixed (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) {j : Fin 4} (hj : (π : Perm (Fin 4)) j = j) {q : Fin 4}
    (hq : (π : Perm (Fin 4))⁻¹ q ≠ q) : Nat.card (centA (el d π h)) ≤ 2 ^ (2 * n - 2) := by
  have hle : (centA (el d π h)).comap beta ≤
      (coordDiff (n := n) ((π : Perm (Fin 4))⁻¹ q) q).ker := by
    intro e he
    have hc := isConst_of_mem_comap_centA hn h he
    have hj' : ((π : Perm (Fin 4))⁻¹) j = j := by
      rw [Perm.inv_eq_iff_eq]
      exact hj.symm
    have h0 : (pv (π : Perm (Fin 4)) (vec e) -
        vec e) j = 0 := by
      simp [pv, hj']
    have hq0 := hc q j
    rw [h0] at hq0
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    change vec e ((π : Perm (Fin 4))⁻¹ q) -
      vec e q = 0
    simpa [pv] using hq0
  have h1 := Subgroup.card_le_of_le hle
  rw [card_comap_beta hn inf_le_left, card_ker_coordDiff hq] at h1
  have h2 : 2 ^ (2 * n) = 4 * 2 ^ (2 * n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h2] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

@[expose] def red (n : ℕ) : ZMod (2 ^ n) →+* ZMod (2 ^ (n - 1)) :=
  ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 1)) _

theorem red_eq_zero_of_two_mul (hn : 1 ≤ n) {x : ZMod (2 ^ n)} (hx : 2 * x = 0) : red n x = 0 := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  have hx' : ((2 * x.val : ℕ) : ZMod (2 ^ n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact_mod_cast hx
  rw [ZMod.natCast_eq_zero_iff] at hx'
  obtain ⟨k, hk⟩ := hx'
  have h2 : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hk2 : 2 * x.val = 2 * (2 ^ (n - 1) * k) := by
    rw [← mul_assoc, ← h2]
    exact hk
  have hk' : x.val = 2 ^ (n - 1) * k := Nat.eq_of_mul_eq_mul_left (by norm_num) hk2
  rw [red, ← ZMod.natCast_zmod_val x, map_natCast, hk', Nat.cast_mul, ZMod.natCast_self, zero_mul]

@[expose] def pairHom (a b c : Fin 4) :
    B n →* Multiplicative (ZMod (2 ^ (n - 1)) × ZMod (2 ^ (n - 1))) where
  toFun e := Multiplicative.ofAdd (red n (vec e a + vec e c), red n (vec e b - vec e a))
  map_one' := by simp [vec]
  map_mul' e f := by
    apply Multiplicative.toAdd.injective
    simp only [vec, Subgroup.coe_mul, toAdd_mul, Pi.add_apply, toAdd_ofAdd, Prod.mk_add_mk,
      ← map_add]
    congr 2 <;> ring

theorem red_surjective (hn : 1 ≤ n) : Function.Surjective (red n) := by
  intro y
  haveI : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  refine ⟨(y.val : ZMod (2 ^ n)), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem pairHom_surjective (hn : 1 ≤ n) {a b c d' : Fin 4} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hd'a : d' ≠ a) (hd'b : d' ≠ b) (hd'c : d' ≠ c)
    (hsum : ∀ v : Fin 4 → ZMod (2 ^ n), ∑ i, v i = v a + v b + v c + v d') :
    Function.Surjective (pairHom (n := n) a b c) := by
  rintro ⟨x, y⟩
  obtain ⟨x', rfl⟩ := red_surjective hn x
  obtain ⟨y', rfl⟩ := red_surjective hn y
  set v : Fin 4 → ZMod (2 ^ n) := Pi.single b y' + Pi.single c x' - Pi.single d' (x' + y') with hv
  have hvB : Multiplicative.ofAdd v ∈ B n := by
    rw [mem_B, toAdd_ofAdd, hsum, hv]
    simp [Pi.single_apply, hab, hab.symm, hac, hac.symm, hbc, hbc.symm, hd'a, hd'a.symm, hd'b,
      hd'b.symm, hd'c, hd'c.symm]
    ring
  refine ⟨⟨Multiplicative.ofAdd v, hvB⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change (red n (v a + v c), red n (v b - v a)) = (red n x', red n y')
  rw [hv]
  simp [Pi.single_apply, hab, hab.symm, hac, hac.symm, hbc, hbc.symm, hd'a, hd'a.symm, hd'b,
    hd'b.symm, hd'c, hd'c.symm]

theorem card_ker_pairHom (hn : 1 ≤ n) {a b c d' : Fin 4} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hd'a : d' ≠ a) (hd'b : d' ≠ b) (hd'c : d' ≠ c)
    (hsum : ∀ v : Fin 4 → ZMod (2 ^ n), ∑ i, v i = v a + v b + v c + v d') :
    Nat.card (pairHom (n := n) a b c).ker = 2 ^ (n + 2) := by
  have h := Subgroup.card_ker_mul_card_of_surjective
    (pairHom_surjective (n := n) hn hab hac hbc hd'a hd'b hd'c hsum)
  rw [card_B, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod] at h
  have h2 : 2 ^ (3 * n) = 2 ^ (n + 2) * (2 ^ (n - 1) * 2 ^ (n - 1)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem card_centA_le_of_fpfInv (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) {a b c d' : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hd'a : d' ≠ a) (hd'b : d' ≠ b) (hd'c : d' ≠ c)
    (hsum : ∀ v : Fin 4 → ZMod (2 ^ n), ∑ i, v i = v a + v b + v c + v d')
    (hπa : (π : Perm (Fin 4))⁻¹ a = b) (hπb : (π : Perm (Fin 4))⁻¹ b = a)
    (hπc : (π : Perm (Fin 4))⁻¹ c = d') :
    Nat.card (centA (el d π h)) ≤ 2 ^ n := by
  have hle : (centA (el d π h)).comap beta ≤ (pairHom (n := n) a b c).ker := by
    intro e he
    have hc := isConst_of_mem_comap_centA hn h he
    set f : Fin 4 → ZMod (2 ^ n) := vec e with hf
    have hca : pv (π : Perm (Fin 4)) f a - f a = f b - f a := by simp [pv, hπa]
    have hcb : pv (π : Perm (Fin 4)) f b - f b = f a - f b := by simp [pv, hπb]
    have hcc : pv (π : Perm (Fin 4)) f c - f c = f d' - f c := by simp [pv, hπc]
    have h1 := hc a b
    have h2 := hc a c
    simp only [Pi.sub_apply] at h1 h2
    rw [hca, hcb] at h1
    rw [hca, hcc] at h2
    have hsumf : f a + f b + f c + f d' = 0 := by
      rw [← hsum]
      exact mem_B.1 e.2
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    change (red n (f a + f c), red n (f b - f a)) = (0, 0)
    refine Prod.ext (red_eq_zero_of_two_mul (by omega) ?_) (red_eq_zero_of_two_mul (by omega) ?_)
    · linear_combination hsumf + h2 - h1
    · linear_combination h1
  have h1 := Subgroup.card_le_of_le hle
  rw [card_comap_beta hn inf_le_left,
    card_ker_pairHom (by omega) hab hac hbc hd'a hd'b hd'c hsum] at h1
  have h2 : 2 ^ (n + 2) = 4 * 2 ^ n := by ring
  rw [h2] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

theorem R0_cases : ∀ π : Perm (Fin 4), π ∈ Fin81.R0 → π = 1 ∨ π = swap 0 1 ∨ π = swap 2 3 ∨
    π = swap 0 1 * swap 2 3 ∨ π = swap 0 2 * swap 1 3 ∨ π = swap 0 3 * swap 1 2 ∨
    π * π = swap 0 1 * swap 2 3 := by
  decide

theorem card_centA_le_of_fpfInv' (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) (hπ : (π : Perm (Fin 4)) = swap 0 1 * swap 2 3 ∨
      (π : Perm (Fin 4)) = swap 0 2 * swap 1 3 ∨ (π : Perm (Fin 4)) = swap 0 3 * swap 1 2) :
    Nat.card (centA (el d π h)) ≤ 2 ^ n := by
  rcases hπ with hπ | hπ | hπ
  · exact card_centA_le_of_fpfInv hn h (a := 0) (b := 1) (c := 2) (d' := 3) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun v => by rw [Fin.sum_univ_four]) (by rw [hπ]; decide) (by rw [hπ]; decide)
      (by rw [hπ]; decide)
  · exact card_centA_le_of_fpfInv hn h (a := 0) (b := 2) (c := 1) (d' := 3) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun v => by rw [Fin.sum_univ_four]; ring) (by rw [hπ]; decide) (by rw [hπ]; decide)
      (by rw [hπ]; decide)
  · exact card_centA_le_of_fpfInv hn h (a := 0) (b := 3) (c := 1) (d' := 2) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun v => by rw [Fin.sum_univ_four]; ring) (by rw [hπ]; decide) (by rw [hπ]; decide)
      (by rw [hπ]; decide)

theorem centA_le_centA_sq (g : L4Model n) : centA g ≤ centA (g * g) := by
  intro x hx
  obtain ⟨hxA, hx⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hxA, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  rw [← mul_assoc, hx, mul_assoc, hx, ← mul_assoc]

theorem card_centA_le_of_fpf (hn : 2 ≤ n) {g : L4Model n}
    (hg : ∀ i, (piT g : Perm (Fin 4)) i ≠ i) : Nat.card (centA g) ≤ 2 ^ n := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [piT_el] at hg
  rcases R0_cases _ π.2 with hπ | hπ | hπ | hπ | hπ | hπ | hπ
  · exact absurd (by rw [hπ]; rfl) (hg 0)
  · exact absurd (by rw [hπ]; decide) (hg 2)
  · exact absurd (by rw [hπ]; decide) (hg 0)
  · exact card_centA_le_of_fpfInv' hn h (Or.inl hπ)
  · exact card_centA_le_of_fpfInv' hn h (Or.inr (Or.inl hπ))
  · exact card_centA_le_of_fpfInv' hn h (Or.inr (Or.inr hπ))
  · refine (Subgroup.card_le_of_le (centA_le_centA_sq _)).trans ?_
    rw [el_mul]
    exact card_centA_le_of_fpfInv' hn _ (Or.inl hπ)

theorem card_centA_le (hn : 2 ≤ n) {g : L4Model n} (hg : g ∉ A n) :
    Nat.card (centA g) ≤ 2 ^ (2 * n - 2) := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [el_mem_A] at hg
  have hle : 2 ^ n ≤ 2 ^ (2 * n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases R0_cases _ π.2 with hπ | hπ | hπ | hπ | hπ | hπ | hπ
  · exact absurd (Subtype.ext hπ) hg
  · exact card_centA_le_of_fixed hn h (j := 2) (q := 0) (by rw [hπ]; decide) (by rw [hπ]; decide)
  · exact card_centA_le_of_fixed hn h (j := 0) (q := 2) (by rw [hπ]; decide) (by rw [hπ]; decide)
  all_goals
    refine (card_centA_le_of_fpf hn ?_).trans hle
    rw [piT_el]
  · rw [hπ]; decide
  · rw [hπ]; decide
  · rw [hπ]; decide
  · intro i hi
    have hi2 : ((π : Perm (Fin 4)) * (π : Perm (Fin 4))) i = i := by
      rw [Perm.mul_apply, hi, hi]
    rw [hπ] at hi2
    exact (show ∀ j : Fin 4, (swap 0 1 * swap 2 3 : Perm (Fin 4)) j ≠ j by decide) i hi2

theorem ncard_le_three {α : Type*} (a b c : α) : ({a, b, c} : Set α).ncard ≤ 3 := by
  refine (Set.ncard_insert_le _ _).trans ?_
  refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
  rw [Set.ncard_singleton]

theorem eq_A_of_comm (hn : 3 ≤ n) {A' : Subgroup (L4Model n)}
    (hc : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a) (hcard : 2 ^ (3 * n - 2) ≤ Nat.card A') :
    A' = A n := by
  by_cases hA : A' ≤ A n
  · exact Subgroup.eq_of_le_of_card_ge hA (by rw [card_A (by omega)]; exact hcard)
  exfalso
  obtain ⟨g, hgA', hgA⟩ := Set.not_subset.mp hA
  set f : A' →* Fin81.R0 := piT.comp A'.subtype with hf
  have hsplit : Nat.card f.ker * Nat.card f.range = Nat.card A' := by
    have := Subgroup.card_ker_mul_card_of_surjective f.rangeRestrict_surjective
    rwa [MonoidHom.ker_rangeRestrict] at this
  have hker : ∀ g' ∈ A', Nat.card f.ker ≤ Nat.card (centA g') := by
    intro g' hg'
    have hinj : Function.Injective (fun x : f.ker => (⟨(x : A'), ⟨(MonoidHom.mem_ker.1 x.2),
        Subgroup.mem_centralizer_singleton_iff.2 (hc _ hg' _ (x : A').2).symm⟩⟩ : centA g')) := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Nat.card_le_card_of_injective _ hinj
  have hrange8 : Nat.card f.range ≤ 8 := by
    rw [← Fin81.card_R0]
    exact Subgroup.card_le_card_group _
  by_cases hfpf : ∃ g' ∈ A', ∀ i, (piT g' : Perm (Fin 4)) i ≠ i
  · obtain ⟨g', hg'A', hg'⟩ := hfpf
    have h1 := (hker g' hg'A').trans (card_centA_le_of_fpf (by omega) hg')
    have h2 : Nat.card A' ≤ 2 ^ n * 8 := hsplit ▸ Nat.mul_le_mul h1 hrange8
    have h3 : 2 ^ n * 8 < 2 ^ (3 * n - 2) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · push Not at hfpf
    have hsub : (f.range : Set Fin81.R0) ⊆
        ({1, ⟨swap 0 1, by decide⟩, ⟨swap 2 3, by decide⟩} : Set Fin81.R0) := by
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨i, hi⟩ := hfpf x hx
      have hx' := (piT x).2
      rcases R0_cases _ hx' with h | h | h | h | h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
      all_goals exfalso
      · rw [h] at hi
        exact (show ∀ j : Fin 4, (swap 0 1 * swap 2 3 : Perm (Fin 4)) j ≠ j by decide) i hi
      · rw [h] at hi
        exact (show ∀ j : Fin 4, (swap 0 2 * swap 1 3 : Perm (Fin 4)) j ≠ j by decide) i hi
      · rw [h] at hi
        exact (show ∀ j : Fin 4, (swap 0 3 * swap 1 2 : Perm (Fin 4)) j ≠ j by decide) i hi
      · have hi2 : ((piT x : Perm (Fin 4)) * (piT x : Perm (Fin 4))) i = i := by
          rw [Perm.mul_apply, hi, hi]
        rw [h] at hi2
        exact (show ∀ j : Fin 4, (swap 0 1 * swap 2 3 : Perm (Fin 4)) j ≠ j by decide) i hi2
    have hrange3 : Nat.card f.range ≤ 3 := by
      have h1 : Nat.card f.range = (f.range : Set Fin81.R0).ncard :=
        Nat.card_coe_set_eq (f.range : Set Fin81.R0)
      rw [h1]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_le_three _ _ _)
    have hrange2 : Nat.card f.range ≤ 2 := by
      have hdvd : Nat.card f.range ∣ 8 := by
        rw [← Fin81.card_R0]
        exact Subgroup.card_subgroup_dvd_card _
      have hpos : 0 < Nat.card f.range := Nat.card_pos
      interval_cases h : Nat.card f.range <;> omega
    have h1 := (hker g hgA').trans (card_centA_le (by omega) hgA)
    have h2 : Nat.card A' ≤ 2 ^ (2 * n - 2) * 2 := hsplit ▸ Nat.mul_le_mul h1 hrange2
    have h3 : 2 ^ (2 * n - 2) * 2 < 2 ^ (3 * n - 2) := by
      rw [← pow_succ]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end CFSG.LocalAnalysis.Mason73
