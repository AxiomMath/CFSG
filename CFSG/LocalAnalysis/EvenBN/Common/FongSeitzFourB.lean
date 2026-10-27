module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup Matrix
open scoped commutatorElement

theorem card_dvd_card_of_stabilizer_eq_bot {H S : Type*} [Group H] [MulAction H S] [Finite H]
    [Finite S] (h : ∀ s : S, MulAction.stabilizer H s = ⊥) : Nat.card H ∣ Nat.card S := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient H S) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer H S), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  rw [h]
  exact dvd_of_eq (Subgroup.index_bot (G := H)).symm

section OrderNine

variable {J V : Type*} [Group J] [Group V]

theorem six_le_of_pow_nine [Finite V] {d : ℕ} (ρ : J →* MulAut V) {h : J} (h9 : h ^ 9 = 1)
    (h3 : ρ (h ^ 3) ≠ 1) (hV : Nat.card V = 2 ^ d) : 6 ≤ d := by
  classical
  have hfo : IsOfFinOrder h := isOfFinOrder_iff_pow_eq_one.2 ⟨9, by norm_num, h9⟩
  have hord : orderOf h = 9 := by
    have hd : orderOf h ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one h9
    obtain ⟨j, hj, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    by_contra hne
    have hj1 : j ≤ 1 := by
      by_contra hj1
      exact hne (by rw [hoj, show j = 2 by omega]; norm_num)
    apply h3
    have : h ^ 3 = 1 := by
      rw [← pow_mod_orderOf, hoj]
      interval_cases j <;> norm_num
    rw [this, map_one]
  set K := zpowers h
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; norm_num)
  let : MulAction K V := MulAction.compHom V (ρ.comp K.subtype)
  have hcomm : ∀ (k : K) (v : V), ρ (h ^ 3) (ρ k v) = ρ k (ρ (h ^ 3) v) := by
    rintro ⟨k, hk⟩ v
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, ← zpow_natCast,
      ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
  let S : SubMulAction K V :=
    { carrier := {v | ρ (h ^ 3) v ≠ v}
      smul_mem' := fun k v hv hkv => hv ((ρ k).injective ((hcomm k v).symm.trans hkv)) }
  have hstab : ∀ s : S, MulAction.stabilizer K s = ⊥ := by
    intro s
    rw [eq_bot_iff]
    intro k hk
    rw [mem_bot]
    by_contra hk1
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hfo.mem_powers_iff_mem_zpowers.2 k.2)
    have hki : (k : J) = h ^ (n % 9) := by rw [← hn, ← pow_eq_pow_mod n h9]
    have hi0 : n % 9 ≠ 0 := by
      intro h0
      apply hk1
      apply Subtype.ext
      rw [hki, h0, pow_zero, OneMemClass.coe_one]
    have key : ∀ i < 9, i ≠ 0 → ∃ m < 9, i * m % 9 = 3 := by decide
    obtain ⟨m, -, hm⟩ := key (n % 9) (Nat.mod_lt _ (by norm_num)) hi0
    have hkm : k ^ m ∈ MulAction.stabilizer K s := pow_mem hk m
    have hkm' : ((k ^ m : K) : J) = h ^ 3 := by
      rw [SubgroupClass.coe_pow, hki, ← pow_mul, pow_eq_pow_mod _ h9, hm]
    rw [MulAction.mem_stabilizer_iff] at hkm
    have h5 : ρ ((k ^ m : K) : J) (s : V) = s := congrArg Subtype.val hkm
    rw [hkm'] at h5
    exact s.2 h5
  let W : Subgroup V :=
    { carrier := {v | ρ (h ^ 3) v = v}
      mul_mem' := fun {a b} (ha : ρ (h ^ 3) a = a) (hb : ρ (h ^ 3) b = b) =>
        show ρ (h ^ 3) (a * b) = a * b by rw [map_mul, ha, hb]
      one_mem' := map_one _
      inv_mem' := fun {a} (ha : ρ (h ^ 3) a = a) => show ρ (h ^ 3) a⁻¹ = a⁻¹ by
        rw [map_inv, ha] }
  have hsum : Nat.card V = Nat.card W + Nat.card S := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl fun v => ρ (h ^ 3) v = v).symm
  obtain ⟨e, he, hWe⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hV ▸ Subgroup.card_subgroup_dvd_card W)
  have hed : e < d := by
    refine lt_of_le_of_ne he fun hed => h3 ?_
    have htop : W = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hWe, hV, hed])
    ext v
    have hv : v ∈ W := htop ▸ mem_top v
    exact hv
  have h9S : 9 ∣ Nat.card S := by
    have := card_dvd_card_of_stabilizer_eq_bot hstab
    rwa [Nat.card_zpowers, hord] at this
  obtain ⟨c, hc⟩ := h9S
  rw [hV, hWe, hc] at hsum
  by_contra hd6
  interval_cases d <;> interval_cases e <;> omega

end OrderNine

section Eight

variable {k : Type*} [Field k] [CharP k 2]

theorem exists_cubic_root_of_card_eq_eight [Finite k] (hk : Nat.card k = 8) :
    ∃ t : k, t ^ 3 + t + 1 = 0 := by
  classical
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  let := Fintype.ofFinite k
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset k)) (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk]
      exact Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  obtain ⟨hs0, hs1⟩ := hs
  have hs8 : s ^ 8 = s := by
    have := FiniteField.pow_card s
    rwa [← Nat.card_eq_fintype_card, hk] at this
  have hs1' : s + 1 ≠ 0 := fun h => hs1 (by linear_combination h - h2)
  have hfac : s * (s + 1) * ((s ^ 3 + s + 1) * (s ^ 3 + s ^ 2 + 1)) = 0 := by
    linear_combination hs8 + (s ^ 7 + s ^ 6 + 2 * s ^ 5 + 2 * s ^ 4 + s ^ 3 + s ^ 2 + s) * h2
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd h (mul_ne_zero hs0 hs1')
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨s, h⟩
  · refine ⟨s⁻¹, ?_⟩
    field_simp
    linear_combination h

@[expose] def orderNineMat (t : k) : Matrix (Fin 2) (Fin 2) k :=
  !![0, 1; 1, t]

theorem orderNineMat_pow_three (t : k) (ht : t ^ 3 + t + 1 = 0) :
    orderNineMat t ^ 3 = !![t, 1 + t ^ 2; 1 + t ^ 2, 1 + t] := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [orderNineMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    grind

theorem orderNineMat_pow_nine (t : k) (ht : t ^ 3 + t + 1 = 0) : orderNineMat t ^ 9 = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [show 9 = 3 * 3 from rfl, pow_mul, orderNineMat_pow_three t ht, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

@[expose] def orderNineElt (t : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨orderNineMat t, by
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    rw [orderNineMat, det_fin_two_of]
    linear_combination -h2⟩

theorem coe_orderNineElt (t : k) :
    ((orderNineElt t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      orderNineMat t :=
  rfl

theorem orderNineElt_pow_nine (t : k) (ht : t ^ 3 + t + 1 = 0) : orderNineElt t ^ 9 = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    coe_orderNineElt]
  exact orderNineMat_pow_nine t ht

theorem orderNineElt_pow_three_ne_one (t : k) (ht : t ^ 3 + t + 1 = 0) :
    orderNineElt t ^ 3 ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) k =>
    (A : Matrix (Fin 2) (Fin 2) k) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    coe_orderNineElt, orderNineMat_pow_three t ht] at h1
  simp at h1
  exact one_ne_zero (by linear_combination ht - t * h1 : (1 : k) = 0)

end Eight

variable {k : Type*} [Field k] [Finite k]

theorem sl2_eq_one_of_card_lt [CharP k 2] {X V : Type*} [Group X] [Group V] [Finite X] [Finite V]
    {m d : ℕ} (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (ρ : X →* MulAut V) (hV : Nat.card V = 2 ^ d) (hd : d < 2 * m) : ρ = 1 := by
  rcases ne_or_eq m 3 with hm3 | rfl
  · exact eq_one_of_card_lt e hk hm hm3 ρ hV hd
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    norm_num
  have := sl2_isSimpleGroup_of_charTwo h4
  have hX : IsSimpleGroup X := e.isSimpleGroup
  rcases hX.eq_bot_or_eq_top_of_normal ρ.ker with hb | ht
  · exfalso
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hb
    obtain ⟨t, ht⟩ := exists_cubic_root_of_card_eq_eight (k := k) (by rw [hk]; norm_num)
    have h9 : e.symm (orderNineElt t) ^ 9 = 1 := by
      rw [← map_pow, orderNineElt_pow_nine t ht, map_one]
    have h3 : ρ (e.symm (orderNineElt t) ^ 3) ≠ 1 := by
      intro h1
      apply orderNineElt_pow_three_ne_one t ht
      have h2 : e.symm (orderNineElt t) ^ 3 = 1 := hinj (by rw [h1, map_one])
      rw [← map_pow] at h2
      exact e.symm.injective (h2.trans (map_one _).symm)
    have := six_le_of_pow_nine ρ h9 h3 hV
    omega
  · ext x v
    have hx : x ∈ ρ.ker := ht ▸ mem_top x
    rw [MonoidHom.mem_ker] at hx
    rw [hx, MonoidHom.one_apply]

theorem sl2_two_mul_le_of_ne_one [CharP k 2] {X V : Type*} [Group X] [Group V] [Finite X]
    [Finite V] {m d : ℕ} (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) (ρ : X →* MulAut V) (hV : Nat.card V = 2 ^ d) (hρ : ρ ≠ 1) : 2 * m ≤ d := by
  by_contra hd
  exact hρ (sl2_eq_one_of_card_lt e hk hm ρ hV (by omega))

theorem sl2_card_sq_le_of_ne_one [CharP k 2] {X V : Type*} [Group X] [Group V] [Finite X]
    [Finite V] {m : ℕ} (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) (ρ : X →* MulAut V) (hV : IsPGroup 2 V) (hρ : ρ ≠ 1) :
    Nat.card k ^ 2 ≤ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hV
  have := sl2_two_mul_le_of_ne_one e hk hm ρ hd hρ
  rw [hk, hd, ← pow_mul]
  exact Nat.pow_le_pow_right two_pos (by omega)

variable {G : Type*} [Group G]

theorem isPGroup_two_of_mul_self {V : Subgroup G} (hV : ∀ v ∈ V, v * v = 1) : IsPGroup 2 V :=
  fun v => ⟨1, Subtype.ext (by rw [pow_one, SubgroupClass.coe_pow, sq]; exact hV v v.2)⟩

theorem conjAction_eq_one_iff {X V : Subgroup G} (hXV : X ≤ normalizer (V : Set G)) :
    CFSG.SL2MinimalFaithful.conjAction hXV = 1 ↔ X ≤ centralizer (V : Set G) := by
  constructor
  · intro h1 x hx
    rw [mem_centralizer_iff]
    intro v hv
    have h2 := congrArg (fun φ : X →* MulAut V => ((φ ⟨x, hx⟩ ⟨v, hv⟩ : V) : G)) h1
    simp only [CFSG.SL2MinimalFaithful.conjAction_apply, MonoidHom.one_apply,
      MulAut.one_apply] at h2
    have h3 : x * v * x⁻¹ = v := h2
    calc v * x = x * v * x⁻¹ * x := by rw [h3]
      _ = x * v := by group
  · intro h
    ext x v
    rw [CFSG.SL2MinimalFaithful.conjAction_apply, MonoidHom.one_apply, MulAut.one_apply,
      ← mem_centralizer_iff.1 (h x.2) v v.2]
    simp

theorem mul_comm_of_mul_self {V : Subgroup G} (hV : ∀ v ∈ V, v * v = 1) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := by
  have hab := hV _ (mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV b hb)
  calc a * b = (b⁻¹ * a⁻¹) := (inv_eq_of_mul_eq_one_right hab).symm.trans (mul_inv_rev a b)
    _ = b * a := by rw [ha', hb']

theorem le_normalizer_of_mul_comm {V W : Subgroup G} (hWV : W ≤ V)
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) : V ≤ normalizer (W : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [hV x hx w (hWV hw), mul_inv_cancel_right]
    exact hw
  · intro hw
    have hw' : w ∈ V := by
      have := mul_mem (mul_mem (inv_mem hx) (hWV hw)) hx
      rwa [show x⁻¹ * (x * w * x⁻¹) * x = w by group] at this
    rw [hV x hx w hw', mul_inv_cancel_right] at hw
    exact hw

variable [Finite G]

theorem sl2_le_centralizer_of_card_lt [CharP k 2] {X V : Subgroup G} {m d : ℕ}
    (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hXV : X ≤ normalizer (V : Set G)) (hV : Nat.card V = 2 ^ d) (hd : d < 2 * m) :
    X ≤ centralizer (V : Set G) :=
  (conjAction_eq_one_iff hXV).1 (sl2_eq_one_of_card_lt e hk hm _ hV hd)

theorem sl2_card_sq_le_of_not_le_centralizer [CharP k 2] {X V : Subgroup G} {m : ℕ}
    (ψ : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hV : ∀ v ∈ V, v * v = 1) (hXV : X ≤ normalizer (V : Set G))
    (hnc : ¬ X ≤ centralizer (V : Set G)) : Nat.card k ^ 2 ≤ Nat.card V :=
  sl2_card_sq_le_of_ne_one ψ hk hm _ (isPGroup_two_of_mul_self hV)
    fun h1 => hnc ((conjAction_eq_one_iff hXV).1 h1)

theorem sl2_commutator_mem_of_card_lt [CharP k 2] {X Y Z : Subgroup G} {m d : ℕ}
    (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hZY : Z ≤ Y) (hYZ : Y ≤ normalizer (Z : Set G)) (hXY : X ≤ normalizer (Y : Set G))
    (hXZ : X ≤ normalizer (Z : Set G)) (hcard : Nat.card Y = 2 ^ d * Nat.card Z)
    (hd : d < 2 * m) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) : x * y * x⁻¹ * y⁻¹ ∈ Z := by
  set Z' : Subgroup Y := Z.subgroupOf Y with hZ'
  have hZ'n : Z'.Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hYZ g.2) n).mp (Subgroup.mem_subgroupOf.mp hn))⟩
  have hZ'card : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv
  set ρY := CFSG.SL2MinimalFaithful.conjAction hXY
  have hmap : ∀ j, Z'.map (ρY j : Y →* Y) = Z' := by
    intro j
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change (j : G) * z * (j : G)⁻¹ ∈ Z
      exact (Subgroup.mem_normalizer_iff.mp (hXZ j.2) z).mp hz
    · intro z hz
      refine ⟨ρY j⁻¹ z, ?_, ?_⟩
      · change ((j⁻¹ : X) : G) * z * ((j⁻¹ : X) : G)⁻¹ ∈ Z
        exact (Subgroup.mem_normalizer_iff.mp (hXZ (X.inv_mem j.2)) z).mp hz
      · change ρY j (ρY j⁻¹ z) = z
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  set ρ := CFSG.SL2MinimalFaithful.quotientAction ρY Z' hmap
  have hVcard : Nat.card (Y ⧸ Z') = 2 ^ d := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    rw [hZ'card, hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have h1 := sl2_eq_one_of_card_lt e hk hm ρ hVcard hd
  have h2 : ρ ⟨x, hx⟩ ((⟨y, hy⟩ : Y) : Y ⧸ Z') = ((⟨y, hy⟩ : Y) : Y ⧸ Z') := by
    rw [h1, MonoidHom.one_apply, MulAut.one_apply]
  rw [CFSG.SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    at h2
  change (ρY ⟨x, hx⟩ ⟨y, hy⟩ : G)⁻¹ * y ∈ Z at h2
  rw [CFSG.SL2MinimalFaithful.conjAction_apply] at h2
  exact (CFSG.SL2MinimalFaithful.inv_mul_mem_iff hYZ hy).1 h2

theorem sl2_card_sq_mul_le_of_not_mem [CharP k 2] {X V W : Subgroup G} {m : ℕ}
    (ψ : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hV : ∀ v ∈ V, v * v = 1) (hWV : W ≤ V) (hXV : X ≤ normalizer (V : Set G))
    (hXW : X ≤ normalizer (W : Set G)) {x v : G} (hx : x ∈ X) (hv : v ∈ V)
    (hxv : x * v * x⁻¹ * v⁻¹ ∉ W) : Nat.card k ^ 2 * Nat.card W ≤ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (isPGroup_two_of_mul_self hV)
  obtain ⟨b, hb, hWb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (ha ▸ Subgroup.card_dvd_of_le hWV)
  have hcard : Nat.card V = 2 ^ (a - b) * Nat.card W := by
    rw [ha, hWb, ← pow_add, Nat.sub_add_cancel hb]
  by_contra hlt
  push Not at hlt
  have hd : a - b < 2 * m := by
    rw [hcard, hk, ← pow_mul] at hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1
      (Nat.lt_of_mul_lt_mul_right hlt)
    omega
  exact hxv (sl2_commutator_mem_of_card_lt ψ hk hm hWV
    (le_normalizer_of_mul_comm hWV fun _ ha _ hb => mul_comm_of_mul_self hV ha hb) hXV hXW
    hcard hd hx hv)

theorem sl2_card_sq_le_relIndex_of_not_mem [CharP k 2] {X V W : Subgroup G} {m : ℕ}
    (ψ : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hV : ∀ v ∈ V, v * v = 1) (hWV : W ≤ V) (hXV : X ≤ normalizer (V : Set G))
    (hXW : X ≤ normalizer (W : Set G)) {x v : G} (hx : x ∈ X) (hv : v ∈ V)
    (hxv : x * v * x⁻¹ * v⁻¹ ∉ W) : Nat.card k ^ 2 ≤ W.relIndex V := by
  have h1 := sl2_card_sq_mul_le_of_not_mem ψ hk hm hV hWV hXV hXW hx hv hxv
  have h2 := Subgroup.relIndex_mul_card (H := W) (K := V)
  rw [inf_of_le_left hWV] at h2
  rw [← h2] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem sl2_eq_bot_or_eq_of_card_le [CharP k 2] {X A V₀ : Subgroup G} {m a : ℕ}
    (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAcard : Nat.card A = 2 ^ a) (ha : a ≤ 2 * m)
    (hXA : X ≤ normalizer (A : Set G)) (hXV : X ≤ normalizer (V₀ : Set G)) (hVA : V₀ ≤ A)
    (hnc : ¬ X ≤ centralizer (A : Set G)) : V₀ = ⊥ ∨ V₀ = A := by
  by_contra hne
  push Not at hne
  obtain ⟨hV1, hVA'⟩ := hne
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨b, hb, hVb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hAcard ▸ Subgroup.card_dvd_of_le hVA)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hV1 ((Subgroup.card_eq_one).1 (by rw [hVb, pow_zero]))
  have hba : b ≠ a := by
    rintro rfl
    exact hVA' (Subgroup.eq_of_le_of_card_ge hVA (by rw [hVb, hAcard]))
  have hba' : b < a := lt_of_le_of_ne hb hba
  have hXV₀ : X ≤ centralizer (V₀ : Set G) :=
    sl2_le_centralizer_of_card_lt e hk hm hXV hVb (by omega)
  have hcardA : Nat.card A = 2 ^ (a - b) * Nat.card V₀ := by
    rw [hAcard, hVb, ← pow_add, Nat.sub_add_cancel hb]
  have hXq : ∀ x ∈ X, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ V₀ := fun x hx y hy =>
    sl2_commutator_mem_of_card_lt e hk hm hVA (le_normalizer_of_mul_comm hVA hAc) hXA hXV
      hcardA (by omega) hx hy
  have hXA' : ⁅⁅A, X⁆, X⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro c hc x hx
    have hcV : c ∈ V₀ := by
      have : ⁅A, X⁆ ≤ V₀ := by
        rw [commutator_le]
        intro y hy x' hx'
        have := hXq x' hx' y⁻¹ (inv_mem hy)
        have e1 : ⁅y, x'⁆ = x' * y⁻¹ * x'⁻¹ * y⁻¹⁻¹ := by
          rw [commutatorElement_def]
          have := hAc y hy (x' * y⁻¹ * x'⁻¹)
            ((mem_normalizer_iff.1 (hXA hx') y⁻¹).1 (inv_mem hy))
          calc y * x' * y⁻¹ * x'⁻¹ = y * (x' * y⁻¹ * x'⁻¹) := by group
            _ = (x' * y⁻¹ * x'⁻¹) * y := this
            _ = x' * y⁻¹ * x'⁻¹ * y⁻¹⁻¹ := by rw [inv_inv]
        rw [e1]
        exact this
      exact this hc
    have := mem_centralizer_iff.1 (hXV₀ hx) c hcV
    rw [commutatorElement_def, this, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hXA'' : ⁅⁅X, A⁆, X⁆ = ⊥ := by
    rw [commutator_comm X A]
    exact hXA'
  have hcomm := commutator_commutator_eq_bot_of_rotate hXA'' hXA'
  have hperf : ⁅X, X⁆ = X := by
    have := LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h4)
    have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective
    exact Subgroup.isPerfect_iff.1 this
  rw [hperf] at hcomm
  exact hnc ((commutator_eq_bot_iff_le_centralizer).1 hcomm)

end CFSG.LocalAnalysis.EvenBN.Common
