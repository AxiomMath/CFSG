module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.PGroupFixedPointCongruence

public section

namespace CFSG.GroupTheory.PlaneAction

open Finset

section Additive

variable {V : Type*} [AddCommGroup V] {p : ℕ}

theorem sum_apply_end {ι : Type*} (s : Finset ι) (f : ι → AddMonoid.End V) (v : V) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  let ev : AddMonoid.End V →+ V :=
    { toFun := fun g => g v
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev f s

theorem odd_nsmul_eq_self (h2 : ∀ v : V, v + v = 0) {n : ℕ} (hn : Odd n) (v : V) :
    n • v = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [two_mul, add_nsmul, add_nsmul, h2, zero_add, one_nsmul]

theorem pow_apply_of_apply_eq {x : AddMonoid.End V} {v : V} (hv : x v = v) (n : ℕ) :
    (x ^ n) v = v := by
  rw [AddMonoid.End.coe_pow]
  exact Function.iterate_fixed hv n

theorem mul_geomSum_eq {x : AddMonoid.End V} (hx : x ^ p = 1) :
    x * ∑ i ∈ range p, x ^ i = ∑ i ∈ range p, x ^ i := by
  have h := mul_geom_sum x p
  rwa [hx, sub_self, sub_mul, one_mul, sub_eq_zero] at h

theorem apply_geomSum_apply {x : AddMonoid.End V} (hx : x ^ p = 1) (v : V) :
    x ((∑ i ∈ range p, x ^ i) v) = (∑ i ∈ range p, x ^ i) v :=
  DFunLike.congr_fun (mul_geomSum_eq hx) v

theorem geomSum_apply_eq_zero {x : AddMonoid.End V} (hx : x ^ p = 1)
    (hfix : ∀ v, x v = v → v = 0) (v : V) : (∑ i ∈ range p, x ^ i) v = 0 :=
  hfix _ (apply_geomSum_apply hx v)

theorem geomSum_apply_of_apply_eq (h2 : ∀ v : V, v + v = 0) (hp : Odd p) {x : AddMonoid.End V}
    {v : V} (hv : x v = v) : (∑ i ∈ range p, x ^ i) v = v := by
  rw [sum_apply_end]
  simp only [pow_apply_of_apply_eq hv, sum_const, card_range]
  exact odd_nsmul_eq_self h2 hp v

theorem geomSum_mul_apply_of_apply_eq {h y : AddMonoid.End V} (hc : Commute h y) {v : V}
    (hv : h v = v) : (∑ i ∈ range p, (h * y) ^ i) v = (∑ i ∈ range p, y ^ i) v := by
  rw [sum_apply_end, sum_apply_end]
  refine sum_congr rfl fun i _ => ?_
  rw [hc.mul_pow, (hc.pow_pow i i).eq]
  change (y ^ i) ((h ^ i) v) = (y ^ i) v
  rw [pow_apply_of_apply_eq hv]

theorem pow_fixed_eq_zero (hp : p.Prime) {ζ : AddMonoid.End V} (hζ : ζ ^ p = 1)
    (hfix : ∀ v, ζ v = v → v = 0) {j : ℕ} (hj0 : j ≠ 0) (hjp : j < p) (v : V)
    (hv : (ζ ^ j) v = v) : v = 0 := by
  obtain ⟨m, -, hm⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (Nat.coprime_of_lt_prime hj0 hjp hp).symm hp.one_lt
  apply hfix
  have h := pow_apply_of_apply_eq hv m
  rwa [← pow_mul, pow_eq_pow_mod _ hζ, hm, pow_one] at h

variable {β ζ : AddMonoid.End V}

theorem mul_pow_pow_eq_one (hc : Commute β ζ) (hβ : β ^ p = 1) (hζ : ζ ^ p = 1) (i : ℕ) :
    (β * ζ ^ i) ^ p = 1 := by
  rw [(hc.pow_right i).mul_pow, pow_right_comm, hβ, hζ, one_pow, one_mul]

theorem sum_geomSum_apply (h2 : ∀ v : V, v + v = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : Commute β ζ) (hζ : ζ ^ p = 1) (hfix : ∀ v, ζ v = v → v = 0) (v : V) :
    ∑ i ∈ range p, (∑ j ∈ range p, (β * ζ ^ i) ^ j) v = v := by
  have key : ∑ i ∈ range p, ∑ j ∈ range p, (β * ζ ^ i) ^ j =
      ∑ j ∈ range p, β ^ j * ∑ i ∈ range p, (ζ ^ j) ^ i := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [(hc.pow_right i).mul_pow, pow_right_comm]
  rw [← sum_apply_end, key, sum_apply_end, sum_eq_single 0]
  · rw [pow_zero, pow_zero, one_mul]
    exact geomSum_apply_of_apply_eq h2 (hp.odd_of_ne_two hp2) (AddMonoid.End.one_apply v)
  · intro j hj hj0
    change (β ^ j) ((∑ i ∈ range p, (ζ ^ j) ^ i) v) = 0
    rw [geomSum_apply_eq_zero (by rw [pow_right_comm, hζ, one_pow])
      (pow_fixed_eq_zero hp hζ hfix hj0 (mem_range.mp hj)) v, map_zero]
  · exact fun h => absurd (mem_range.mpr hp.pos) h

theorem geomSum_apply_eq_zero_of_ne (hp : p.Prime) (hc : Commute β ζ) (hζ : ζ ^ p = 1)
    (hfix : ∀ v, ζ v = v → v = 0) {i i' : ℕ} (hi : i < p) (hi' : i' < p) (hne : i ≠ i')
    {v : V} (hv : (β * ζ ^ i) v = v) : (∑ j ∈ range p, (β * ζ ^ i') ^ j) v = 0 := by
  obtain ⟨d, hd0, hdp, hd⟩ : ∃ d, d ≠ 0 ∧ d < p ∧ (i + d) % p = i' := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i' - i, by omega, by omega, by rw [Nat.add_sub_cancel' h.le, Nat.mod_eq_of_lt hi']⟩
    · refine ⟨p + i' - i, by omega, by omega, ?_⟩
      rw [show i + (p + i' - i) = i' + p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi']
  have h1 : β * ζ ^ i' = β * ζ ^ i * ζ ^ d := by
    rw [mul_assoc, ← pow_add, pow_eq_pow_mod (i + d) hζ, hd]
  rw [h1, geomSum_mul_apply_of_apply_eq ((hc.pow_right d).mul_left (Commute.pow_pow_self ζ i d))
    hv]
  exact geomSum_apply_eq_zero (by rw [pow_right_comm, hζ, one_pow])
    (pow_fixed_eq_zero hp hζ hfix hd0 hdp) v

variable (β ζ) in
def fixedDecompEquiv (h2 : ∀ v : V, v + v = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : Commute β ζ) (hβ : β ^ p = 1) (hζ : ζ ^ p = 1) (hfix : ∀ v, ζ v = v → v = 0) :
    V ≃ ((i : Fin p) → {v : V // (β * ζ ^ (i : ℕ)) v = v}) where
  toFun v i := ⟨(∑ j ∈ range p, (β * ζ ^ (i : ℕ)) ^ j) v,
    apply_geomSum_apply (mul_pow_pow_eq_one hc hβ hζ i) v⟩
  invFun f := ∑ i, (f i : V)
  left_inv v := by
    change ∑ i : Fin p, (∑ j ∈ range p, (β * ζ ^ (i : ℕ)) ^ j) v = v
    rw [Fin.sum_univ_eq_sum_range (fun i => (∑ j ∈ range p, (β * ζ ^ i) ^ j) v)]
    exact sum_geomSum_apply h2 hp hp2 hc hζ hfix v
  right_inv f := by
    funext i
    apply Subtype.ext
    change (∑ j ∈ range p, (β * ζ ^ (i : ℕ)) ^ j) (∑ k, (f k : V)) = f i
    rw [map_sum, sum_eq_single i]
    · exact geomSum_apply_of_apply_eq h2 (hp.odd_of_ne_two hp2) (f i).2
    · intro k _ hki
      exact geomSum_apply_eq_zero_of_ne hp hc hζ hfix k.2 i.2 (Fin.val_ne_of_ne hki) (f k).2
    · exact fun h => absurd (mem_univ i) h

theorem card_eq_prod_card_fixed (h2 : ∀ v : V, v + v = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : Commute β ζ) (hβ : β ^ p = 1) (hζ : ζ ^ p = 1) (hfix : ∀ v, ζ v = v → v = 0) :
    Nat.card V = ∏ i : Fin p, Nat.card {v : V // (β * ζ ^ (i : ℕ)) v = v} := by
  rw [Nat.card_congr (fixedDecompEquiv β ζ h2 hp hp2 hc hβ hζ hfix), Nat.card_pi]

end Additive

section Multiplicative

variable {M V : Type*} [Monoid M] [CommGroup V] [MulDistribMulAction M V] {p : ℕ}

theorem card_eq_prod_card_fixedBy (h2 : ∀ v : V, v ^ 2 = 1) (hp : p.Prime) (hp2 : p ≠ 2)
    {b z : M} (hbz : Commute b z) (hb : b ^ p = 1) (hz : z ^ p = 1)
    (hfix : ∀ v : V, z • v = v → v = 1) :
    Nat.card V = ∏ i : Fin p, Nat.card (MulAction.fixedBy V (b * z ^ (i : ℕ))) := by
  let ρ : M →* AddMonoid.End (Additive V) :=
    (MulEquiv.monoidEnd V : Monoid.End V →* AddMonoid.End (Additive V)).comp
      (MulDistribMulAction.toMonoidEnd M V)
  have hρ : ∀ (m : M) (v : Additive V), ρ m v = Additive.ofMul (m • v.toMul) := fun _ _ => rfl
  have h2' : ∀ v : Additive V, v + v = 0 := fun v => by
    change Additive.ofMul (v.toMul * v.toMul) = Additive.ofMul 1
    rw [← pow_two, h2]
  have hfix' : ∀ v : Additive V, ρ z v = v → v = 0 := fun v hv => by
    rw [hρ] at hv
    have h1 : v.toMul = 1 := hfix _ (congrArg Additive.toMul hv)
    exact congrArg Additive.ofMul h1
  have key := card_eq_prod_card_fixed h2' hp hp2 (hbz.map ρ)
    (by rw [← map_pow, hb, map_one]) (by rw [← map_pow, hz, map_one]) hfix'
  rw [← Nat.card_congr (Additive.toMul : Additive V ≃ V), key]
  refine prod_congr rfl fun i _ => Nat.card_congr ?_
  refine Equiv.subtypeEquiv Additive.toMul fun v => ?_
  rw [MulAction.mem_fixedBy, ← map_pow, ← map_mul, hρ]
  exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩

end Multiplicative

section Subgroup

open Subgroup CFSG.Open

variable {A : Type*} [Group A] {E : Subgroup A} {p : ℕ}

theorem conj_mem_centralizer_singleton_iff (c x g : A) :
    c * x * c⁻¹ ∈ centralizer {c * g * c⁻¹} ↔ x ∈ centralizer {g} := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    show c * x * c⁻¹ * (c * g * c⁻¹) = c * (x * g) * c⁻¹ by group,
    show c * g * c⁻¹ * (c * x * c⁻¹) = c * (g * x) * c⁻¹ by group, mul_left_inj, mul_right_inj]

theorem mem_fixedBy_normalizer_iff (g : normalizer (E : Set A)) (x : E) :
    x ∈ MulAction.fixedBy E g ↔ (x : A) ∈ centralizer {(g : A)} := by
  rw [MulAction.mem_fixedBy, mem_centralizer_singleton_iff, Subtype.ext_iff]
  change (g : A) * x * (g : A)⁻¹ = x ↔ _
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem card_fixedBy_normalizer (g : normalizer (E : Set A)) :
    Nat.card (MulAction.fixedBy E g) = Nat.card (E ⊓ centralizer {(g : A)} : Subgroup A) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, x.1.2, (mem_fixedBy_normalizer_iff g x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y, y.2.1⟩, (mem_fixedBy_normalizer_iff g _).mpr y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open scoped IsMulCommutative in
theorem card_eq_prod_card_inf_centralizer (hE : IsElemAbelian 2 E) (hp : p.Prime) (hp2 : p ≠ 2)
    {b z : A} (hb : b ∈ normalizer (E : Set A)) (hz : z ∈ normalizer (E : Set A))
    (hbz : Commute b z) (hbp : b ^ p = 1) (hzp : z ^ p = 1) (hfix : E ⊓ centralizer {z} = ⊥) :
    Nat.card E = ∏ i : Fin p, Nat.card (E ⊓ centralizer {b * z ^ (i : ℕ)} : Subgroup A) := by
  haveI : IsMulCommutative E := hE.1
  have h2 : ∀ v : E, v ^ 2 = 1 := fun v => Subtype.ext (hE.2 v v.2)
  have hfix' : ∀ v : E, (⟨z, hz⟩ : normalizer (E : Set A)) • v = v → v = 1 := fun v hv => by
    have hv' := (mem_fixedBy_normalizer_iff (E := E) ⟨z, hz⟩ v).mp hv
    have hmem : (v : A) ∈ E ⊓ centralizer {z} := ⟨v.2, hv'⟩
    rw [hfix, mem_bot] at hmem
    exact Subtype.ext hmem
  rw [card_eq_prod_card_fixedBy (M := normalizer (E : Set A)) h2 hp hp2
    (b := ⟨b, hb⟩) (z := ⟨z, hz⟩) (Subtype.ext hbz) (Subtype.ext hbp) (Subtype.ext hzp) hfix']
  refine prod_congr rfl fun i _ => ?_
  rw [card_fixedBy_normalizer]
  rfl

theorem pow_mul_mul_inv_pow {b z w : A} (hwb : w * b * w⁻¹ = b * z) (hwz : Commute w z)
    (i : ℕ) : w ^ i * b * (w ^ i)⁻¹ = b * z ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc w ^ (i + 1) * b * (w ^ (i + 1))⁻¹ = w * (w ^ i * b * (w ^ i)⁻¹) * w⁻¹ := by group
      _ = w * b * w⁻¹ * (w * z ^ i * w⁻¹) := by rw [ih]; group
      _ = b * z ^ (i + 1) := by
        rw [hwb, (hwz.pow_right i).eq, mul_inv_cancel_right, pow_succ', mul_assoc]

theorem card_eq_card_inf_centralizer_pow (hE : IsElemAbelian 2 E) (hp : p.Prime) (hp2 : p ≠ 2)
    {b z w : A} (hb : b ∈ normalizer (E : Set A)) (hz : z ∈ normalizer (E : Set A))
    (hw : w ∈ normalizer (E : Set A)) (hbz : Commute b z) (hbp : b ^ p = 1) (hzp : z ^ p = 1)
    (hwb : w * b * w⁻¹ = b * z) (hwz : Commute w z) (hfix : E ⊓ centralizer {z} = ⊥) :
    Nat.card E = Nat.card (E ⊓ centralizer {b} : Subgroup A) ^ p := by
  rw [card_eq_prod_card_inf_centralizer hE hp hp2 hb hz hbz hbp hzp hfix, ← Fin.prod_const]
  refine prod_congr rfl fun i _ => ?_
  have hwi : w ^ (i : ℕ) ∈ normalizer (E : Set A) := pow_mem hw _
  refine (Nat.card_congr ((MulAut.conj (w ^ (i : ℕ))).toEquiv.subtypeEquiv fun x => ?_)).symm
  change x ∈ E ⊓ centralizer {b} ↔
    w ^ (i : ℕ) * x * (w ^ (i : ℕ))⁻¹ ∈ E ⊓ centralizer {b * z ^ (i : ℕ)}
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← pow_mul_mul_inv_pow hwb hwz,
    conj_mem_centralizer_singleton_iff, ← mem_normalizer_iff.mp hwi x]

theorem card_inf_centralizer_modEq_one [Finite A] (hp : p.Prime) {b z : A}
    (hz : z ∈ normalizer (E : Set A)) (hbz : Commute b z) (hzp : z ^ p = 1)
    (hfix : E ⊓ centralizer {z} = ⊥) :
    Nat.card (E ⊓ centralizer {b} : Subgroup A) ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzb : z * b * z⁻¹ = b := by rw [← hbz.eq, mul_inv_cancel_right]
  refine card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot (X := zpowers z)
    (IsPGroup.of_card_dvd_pow (n := 1) ?_) ?_ ?_
  · rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hzp
  · rw [zpowers_le, mem_normalizer_iff]
    intro x
    have hC : z * x * z⁻¹ ∈ centralizer {b} ↔ x ∈ centralizer {b} := by
      simpa only [hzb] using conj_mem_centralizer_singleton_iff z x b
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← mem_normalizer_iff.mp hz x, hC]
  · rw [eq_bot_iff, ← hfix]
    exact fun x hx => ⟨hx.1.1, centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers z)) hx.2⟩

theorem two_pow_le_card_of_card_eq_pow [Finite A] (hE : IsElemAbelian 2 E) {C : Subgroup A}
    (hCE : C ≤ E) {n : ℕ} (hcard : Nat.card E = Nat.card C ^ p) (hmod : Nat.card C ≡ 1 [MOD n])
    (hne : E ≠ ⊥) : 2 ^ (p * orderOf (2 : ZMod n)) ≤ Nat.card E := by
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hE2.to_le hCE)
  have hdvd : orderOf (2 : ZMod n) ∣ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have h := (ZMod.natCast_eq_natCast_iff _ _ n).mpr (hk ▸ hmod)
    simpa using h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero, one_pow] at hcard
    exact hne (Subgroup.eq_bot_of_card_eq E hcard)
  calc 2 ^ (p * orderOf (2 : ZMod n)) ≤ 2 ^ (p * k) :=
        Nat.pow_le_pow_right two_pos
          (Nat.mul_le_mul_left p (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd))
    _ = Nat.card E := by rw [hcard, hk, ← pow_mul, mul_comm]

theorem two_pow_le_card_of_fpf [Finite A] (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian 2 E)
    {b z w : A} (hb : b ∈ normalizer (E : Set A)) (hz : z ∈ normalizer (E : Set A))
    (hw : w ∈ normalizer (E : Set A)) (hbz : Commute b z) (hbp : b ^ p = 1) (hzp : z ^ p = 1)
    (hwb : w * b * w⁻¹ = b * z) (hwz : Commute w z) (hfix : E ⊓ centralizer {z} = ⊥)
    (hne : E ≠ ⊥) : 2 ^ (p * orderOf (2 : ZMod p)) ≤ Nat.card E :=
  two_pow_le_card_of_card_eq_pow hE inf_le_left
    (card_eq_card_inf_centralizer_pow hE hp hp2 hb hz hw hbz hbp hzp hwb hwz hfix)
    (card_inf_centralizer_modEq_one hp hz hbz hzp hfix) hne

end Subgroup

theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 :=
  (orderOf_eq_iff two_pos).mpr ⟨by decide, by decide⟩

theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

end CFSG.GroupTheory.PlaneAction
