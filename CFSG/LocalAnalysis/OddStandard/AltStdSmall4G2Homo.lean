module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Mat

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open scoped Pointwise

section ZTwo

namespace Homo

variable {k : ℕ}

theorem exists_natCast (x : ZMod (2 ^ k)) : ∃ m : ℕ, m < 2 ^ k ∧ x = m :=
  ⟨x.val, ZMod.val_lt x, (ZMod.natCast_zmod_val x).symm⟩

theorem two_pow_eq_zero : (2 : ZMod (2 ^ k)) ^ k = 0 := by
  have h := ZMod.natCast_self (2 ^ k)
  push_cast at h
  exact h

theorem two_pow_pred_mul_two (hk : 1 ≤ k) : (2 : ZMod (2 ^ k)) ^ (k - 1) * 2 = 0 := by
  rw [← pow_succ, Nat.sub_add_cancel hk, two_pow_eq_zero]

theorem two_pow_mul_eq_zero_iff (hk : 1 ≤ k) (x : ZMod (2 ^ k)) :
    (2 : ZMod (2 ^ k)) ^ (k - 1) * x = 0 ↔ ∃ y, x = 2 * y := by
  constructor
  · obtain ⟨m, -, rfl⟩ := exists_natCast x
    intro h
    have h1 : ((2 ^ (k - 1) * m : ℕ) : ZMod (2 ^ k)) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : 2 ∣ m := by
      have e : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hk]
      rw [e] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    obtain ⟨q, rfl⟩ := h2
    exact ⟨q, by push_cast; ring⟩
  · rintro ⟨y, rfl⟩
    rw [← mul_assoc, two_pow_pred_mul_two hk, zero_mul]

theorem two_mul_eq_zero_iff (hk : 1 ≤ k) (x : ZMod (2 ^ k)) :
    2 * x = 0 ↔ ∃ b : ZMod 2, x = 2 ^ (k - 1) * (b.val : ZMod (2 ^ k)) := by
  constructor
  · obtain ⟨m, hm, rfl⟩ := exists_natCast x
    intro h
    have h1 : ((2 * m : ℕ) : ZMod (2 ^ k)) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have e : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
    rw [e] at h1 hm
    obtain ⟨q, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    have hq : q < 2 := by
      by_contra hq
      push Not at hq
      have : 2 * 2 ^ (k - 1) ≤ 2 ^ (k - 1) * q := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ hq
      omega
    refine ⟨(q : ZMod 2), ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq]
    push_cast
    ring
  · rintro ⟨b, rfl⟩
    rw [← mul_assoc, mul_comm (2 : ZMod (2 ^ k)), two_pow_pred_mul_two hk, zero_mul]

theorem two_pow_mul_val (hk : 1 ≤ k) (x : ZMod (2 ^ k)) :
    (2 : ZMod (2 ^ k)) ^ (k - 1) * x =
      2 ^ (k - 1) * ((((x.val : ℕ) : ZMod 2)).val : ZMod (2 ^ k)) := by
  obtain ⟨m, hm, rfl⟩ := exists_natCast x
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hm]
  have e : ((m : ℕ) : ZMod (2 ^ k)) =
      ((m % 2 : ℕ) : ZMod (2 ^ k)) + 2 * ((m / 2 : ℕ) : ZMod (2 ^ k)) := by
    have := congrArg (fun t : ℕ => (t : ZMod (2 ^ k))) (Nat.mod_add_div m 2)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
    exact this.symm
  rw [e, mul_add, ← mul_assoc (2 ^ (k - 1)) 2, two_pow_pred_mul_two hk, zero_mul, add_zero]

theorem val_cast_eq (hk : 1 ≤ k) (x : ZMod (2 ^ k)) :
    ((x.val : ℕ) : ZMod 2) = ZMod.castHom (dvd_pow_self 2 (by omega : k ≠ 0)) (ZMod 2) x := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem val_natCast_of_lt_two {m : ℕ} (hm : m < 2) (hk : 1 ≤ k) :
    ((m : ZMod (2 ^ k))).val = m := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  calc m < 2 := hm
    _ = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem natCast_val_val (hk : 1 ≤ k) (b : ZMod 2) :
    ((((b.val : ℕ) : ZMod (2 ^ k))).val : ZMod 2) = b := by
  rw [val_natCast_of_lt_two (ZMod.val_lt b) hk, ZMod.natCast_zmod_val]

theorem mulVec_liftE (hk : 1 ≤ k) (M : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k)))
    (v : Fin 3 → ZMod 2) :
    M *ᵥ liftE k v = liftE k (M.map (fun x => ((x.val : ℕ) : ZMod 2)) *ᵥ v) := by
  funext i
  simp only [liftE, mulVec, dotProduct, Matrix.map_apply]
  have e1 : ∑ j, M i j * (2 ^ (k - 1) * ((v j).val : ZMod (2 ^ k))) =
      2 ^ (k - 1) * ∑ j, M i j * ((v j).val : ZMod (2 ^ k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : (((∑ j, M i j * ((v j).val : ZMod (2 ^ k))).val : ℕ) : ZMod 2) =
      ∑ j, ((M i j).val : ZMod 2) * v j := by
    rw [val_cast_eq hk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← val_cast_eq hk, map_natCast, ZMod.natCast_zmod_val]
  rw [e1, two_pow_mul_val hk, e2]

end Homo

end ZTwo

section Mul3

variable {G : Type} [Group G]

theorem mul3_mul3 {a b c a' b' c' : G} (h1 : Commute c a') (h2 : Commute c b')
    (h3 : Commute b a') : a * b * c * (a' * b' * c') = a * a' * (b * b') * (c * c') := by
  simp only [mul_assoc]
  rw [h1.left_comm, h2.left_comm, h3.left_comm]

theorem mul3_pow {a b c : G} (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (m : ℕ) : (a * b * c) ^ m = a ^ m * b ^ m * c ^ m := by
  rw [(hac.mul_left hbc).mul_pow, hab.mul_pow]

end Mul3

section Eps

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n)

theorem epsV_mem_E (v : Fin 3 → ZMod 2) : epsV θ hn v ∈ E θ hn := N0.eps_mem_E θ hn _

theorem epsV_mem_L (v : Fin 3 → ZMod 2) : epsV θ hn v ∈ L := N0.eps_mem_L θ hn _

theorem epsV_add (v w : Fin 3 → ZMod 2) :
    epsV θ hn (v + w) = epsV θ hn v * epsV θ hn w := by
  rw [epsV, epsV, epsV, N0.eps_mul, ModIso.bits_symm_add, N0.xr_eq_xor]

theorem epsV_zero : epsV θ hn 0 = 1 := by
  rw [epsV, ModIso.bits_symm_zero, N0.eps_zero]

theorem epsV_injective : Function.Injective (epsV θ hn) := fun v w h =>
  ModIso.bits.symm.injective (N0.eps_injective θ hn h)

theorem epsV_eq_one_iff (v : Fin 3 → ZMod 2) : epsV θ hn v = 1 ↔ v = 0 := by
  rw [← epsV_zero θ hn]
  exact (epsV_injective θ hn).eq_iff

theorem epsV_mul_self (v : Fin 3 → ZMod 2) : epsV θ hn v * epsV θ hn v = 1 :=
  N0.eps_mul_self θ hn _

theorem epsV_sq (v : Fin 3 → ZMod 2) : epsV θ hn v ^ 2 = 1 := by
  rw [sq, epsV_mul_self]

theorem epsV_inv (v : Fin 3 → ZMod 2) : (epsV θ hn v)⁻¹ = epsV θ hn v :=
  N0.eps_inv θ hn _

theorem epsV_comm (v w : Fin 3 → ZMod 2) :
    epsV θ hn v * epsV θ hn w = epsV θ hn w * epsV θ hn v :=
  N0.eps_comm θ hn _ _

theorem mem_E_iff_epsV (x : G) : x ∈ E θ hn ↔ ∃ v, epsV θ hn v = x := by
  rw [N0.mem_E_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨ModIso.bits i, by rw [epsV, Equiv.symm_apply_apply]⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, rfl⟩

theorem E_comm {x y : G} (hx : x ∈ E θ hn) (hy : y ∈ E θ hn) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := (mem_E_iff_epsV θ hn x).1 hx
  obtain ⟨w, rfl⟩ := (mem_E_iff_epsV θ hn y).1 hy
  exact epsV_comm θ hn v w

theorem sq_eq_one_of_mem_E {x : G} (hx : x ∈ E θ hn) : x ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := (mem_E_iff_epsV θ hn x).1 hx
  exact epsV_sq θ hn v

@[expose] noncomputable def epsEquiv : Multiplicative (Fin 3 → ZMod 2) ≃* E θ hn :=
  MulEquiv.ofBijective
    ({ toFun := fun v => ⟨epsV θ hn (Multiplicative.toAdd v), epsV_mem_E θ hn _⟩
       map_one' := Subtype.ext (epsV_zero θ hn)
       map_mul' := fun v w => Subtype.ext (epsV_add θ hn _ _) } :
      Multiplicative (Fin 3 → ZMod 2) →* E θ hn)
    ⟨fun v w h => by
      have h1 : epsV θ hn (Multiplicative.toAdd v) = epsV θ hn (Multiplicative.toAdd w) :=
        congrArg (fun x : E θ hn => (x : G)) h
      exact epsV_injective θ hn h1, fun x => by
      obtain ⟨v, hv⟩ := (mem_E_iff_epsV θ hn x).1 x.2
      exact ⟨Multiplicative.ofAdd v, Subtype.ext hv⟩⟩

theorem coe_epsEquiv (v : Multiplicative (Fin 3 → ZMod 2)) :
    (epsEquiv θ hn v : G) = epsV θ hn (Multiplicative.toAdd v) := rfl

end Eps

section Coords

variable {G : Type} [Group G] {k : ℕ} {A : Subgroup G}
  (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)))
include ι

@[expose] def el (x : Fin 3 → ZMod (2 ^ k)) : G := ((ι.symm (Multiplicative.ofAdd x) : A) : G)

theorem el_mem (x : Fin 3 → ZMod (2 ^ k)) : el ι x ∈ A := (ι.symm _).2

theorem el_add (x y : Fin 3 → ZMod (2 ^ k)) : el ι (x + y) = el ι x * el ι y := by
  simp only [el, ofAdd_add, map_mul, Subgroup.coe_mul]

theorem el_zero : el ι 0 = 1 := by
  simp only [el, ofAdd_zero, map_one, OneMemClass.coe_one]

theorem el_neg (x : Fin 3 → ZMod (2 ^ k)) : el ι (-x) = (el ι x)⁻¹ := by
  simp only [el, ofAdd_neg, map_inv, Subgroup.coe_inv]

theorem el_nsmul (m : ℕ) (x : Fin 3 → ZMod (2 ^ k)) : el ι (m • x) = el ι x ^ m := by
  simp only [el, ofAdd_nsmul, map_pow, Subgroup.coe_pow]

theorem el_injective : Function.Injective (el ι) := by
  intro x y h
  have h1 := Subtype.ext h
  exact Multiplicative.ofAdd.injective (ι.symm.injective h1)

theorem el_eq_one_iff (x : Fin 3 → ZMod (2 ^ k)) : el ι x = 1 ↔ x = 0 := by
  rw [← el_zero ι]
  exact (el_injective ι).eq_iff

theorem el_toAdd (a : A) : el ι (Multiplicative.toAdd (ι a)) = a := by
  simp only [el, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem exists_el_eq {a : G} (ha : a ∈ A) : ∃ x, el ι x = a :=
  ⟨Multiplicative.toAdd (ι ⟨a, ha⟩), el_toAdd ι ⟨a, ha⟩⟩

theorem comm_of_coords {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := exists_el_eq ι ha
  obtain ⟨y, rfl⟩ := exists_el_eq ι hb
  rw [← el_add, ← el_add, add_comm]

theorem commute_of_coords {a b : G} (ha : a ∈ A) (hb : b ∈ A) : Commute a b :=
  comm_of_coords ι ha hb

theorem pow_two_pow_of_coords {a : G} (ha : a ∈ A) : a ^ 2 ^ k = 1 := by
  obtain ⟨x, rfl⟩ := exists_el_eq ι ha
  rw [← el_nsmul, el_eq_one_iff]
  funext i
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Homo.two_pow_eq_zero,
    zero_mul, Pi.zero_apply]

theorem card_of_coords : Nat.card A = 2 ^ (3 * k) := by
  rw [Nat.card_congr (ι.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]

theorem el_natCast (m : Fin 3 → ℕ) :
    el ι (fun i => (m i : ZMod (2 ^ k))) =
      el ι (Pi.single 0 1) ^ m 0 * el ι (Pi.single 1 1) ^ m 1 * el ι (Pi.single 2 1) ^ m 2 := by
  rw [← el_nsmul, ← el_nsmul, ← el_nsmul, ← el_add, ← el_add]
  congr 1
  funext i
  fin_cases i <;> simp

end Coords

structure ECoords {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
    (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (k : ℕ) (A : Subgroup G)
    (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))) : Prop where
  one_le : 1 ≤ k
  E_le : E θ hn ≤ A
  eps : ∀ v : Fin 3 → ZMod 2, el ι (liftE k v) = epsV θ hn v

@[expose] def ZAct {G : Type} [Group G] (z : G) (k : ℕ) (A : Subgroup G) : Prop :=
  (∀ a ∈ A, z * a * z⁻¹ = a⁻¹) ∨ (3 ≤ k ∧ ∀ a ∈ A, z * a * z⁻¹ = a⁻¹ * a ^ 2 ^ (k - 1))

namespace ECoords

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
  {hn : 8 ≤ n} {k : ℕ} {A : Subgroup G} {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))}
  (h : ECoords θ hn k A ι)
include h

theorem toAdd_eps (v : Fin 3 → ZMod 2) (hv : epsV θ hn v ∈ A) :
    Multiplicative.toAdd (ι ⟨epsV θ hn v, hv⟩) = liftE k v := by
  have h1 : (⟨epsV θ hn v, hv⟩ : A) = ι.symm (Multiplicative.ofAdd (liftE k v)) :=
    Subtype.ext (h.eps v).symm
  rw [h1, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem le_centralizer_E : A ≤ centralizer (E θ hn : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro e he
  exact comm_of_coords ι (h.E_le he) ha

theorem el_pow_two_pow_pred (x : Fin 3 → ZMod (2 ^ k)) :
    el ι x ^ 2 ^ (k - 1) = epsV θ hn (fun i => (((x i).val : ℕ) : ZMod 2)) := by
  rw [← el_nsmul, ← h.eps]
  congr 1
  funext i
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, liftE]
  exact Homo.two_pow_mul_val h.one_le (x i)

theorem pow_mem_E {a : G} (ha : a ∈ A) : a ^ 2 ^ (k - 1) ∈ E θ hn := by
  obtain ⟨x, rfl⟩ := exists_el_eq ι ha
  rw [h.el_pow_two_pow_pred]
  exact epsV_mem_E θ hn _

theorem el_lift_pow (v : Fin 3 → ZMod 2) :
    el ι (fun i => (((v i).val : ℕ) : ZMod (2 ^ k))) ^ 2 ^ (k - 1) = epsV θ hn v := by
  rw [h.el_pow_two_pow_pred]
  congr 1
  funext i
  exact Homo.natCast_val_val h.one_le (v i)

theorem exists_pow_eq_eps (v : Fin 3 → ZMod 2) : ∃ a ∈ A, a ^ 2 ^ (k - 1) = epsV θ hn v :=
  ⟨_, el_mem ι _, h.el_lift_pow v⟩

theorem mem_E_iff_sq_eq_one {a : G} (ha : a ∈ A) : a ∈ E θ hn ↔ a ^ 2 = 1 := by
  refine ⟨sq_eq_one_of_mem_E θ hn, fun h2 => ?_⟩
  obtain ⟨x, rfl⟩ := exists_el_eq ι ha
  rw [← el_nsmul, el_eq_one_iff] at h2
  have hx : ∀ i, ∃ b : ZMod 2, x i = 2 ^ (k - 1) * (b.val : ZMod (2 ^ k)) := by
    intro i
    have := congrFun h2 i
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.zero_apply] at this
    exact (Homo.two_mul_eq_zero_iff h.one_le (x i)).1 this
  choose b hb using hx
  have hxb : x = liftE k b := funext hb
  rw [hxb, h.eps]
  exact epsV_mem_E θ hn b

theorem pow_eq_one_iff_sq {a : G} (ha : a ∈ A) :
    a ^ 2 ^ (k - 1) = 1 ↔ ∃ b ∈ A, b ^ 2 = a := by
  constructor
  · intro h1
    obtain ⟨x, rfl⟩ := exists_el_eq ι ha
    rw [← el_nsmul, el_eq_one_iff] at h1
    have hx : ∀ i, ∃ y, x i = 2 * y := by
      intro i
      have := congrFun h1 i
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Pi.zero_apply] at this
      exact (Homo.two_pow_mul_eq_zero_iff h.one_le (x i)).1 this
    choose y hy using hx
    refine ⟨el ι y, el_mem ι y, ?_⟩
    rw [← el_nsmul]
    congr 1
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, hy i]
  · rintro ⟨b, hb, rfl⟩
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel h.one_le]
    exact pow_two_pow_of_coords ι hb

end ECoords

namespace ZAct

variable {G : Type} [Group G] {z : G} {k : ℕ} {A : Subgroup G}

theorem conj_mem (hz : ZAct z k A) {a : G} (ha : a ∈ A) : z * a * z⁻¹ ∈ A := by
  rcases hz with h | ⟨-, h⟩
  · rw [h a ha]
    exact inv_mem ha
  · rw [h a ha]
    exact mul_mem (inv_mem ha) (pow_mem ha _)

theorem mem_normalizer (hz : ZAct z k A) (hz2 : z * z = 1) : z ∈ normalizer (A : Set G) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rw [mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hz.conj_mem ha, fun ha => ?_⟩
  have := hz.conj_mem ha
  have e : z * (z * a * z⁻¹) * z⁻¹ = a := by
    rw [hzi]
    calc z * (z * a * z) * z = (z * z) * a * (z * z) := by group
      _ = a := by rw [hz2, one_mul, mul_one]
  rwa [e] at this

end ZAct

section Sup

variable {G : Type} [Group G] {z : G}

theorem zpow_eq_one_or_eq (hz2 : z * z = 1) (j : ℤ) : z ^ j = 1 ∨ z ^ j = z := by
  have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
  have hj : z ^ j = z ^ (j % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv j 2, _root_.zpow_add, _root_.zpow_mul, hz2',
      _root_.one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · left
    rw [hj, h, zpow_zero]
  · right
    rw [hj, h, zpow_one]

theorem mem_sup_zpowers_iff {A : Subgroup G} (hzN : z ∈ normalizer (A : Set G))
    (hz2 : z * z = 1) {x : G} : x ∈ A ⊔ zpowers z ↔ x ∈ A ∨ x * z ∈ A := by
  constructor
  · intro hx
    have hm := Subgroup.coe_mul_of_right_le_normalizer_left A (zpowers z) (zpowers_le.2 hzN)
    have hx' : x ∈ (A : Set G) * (zpowers z : Set G) := by
      rw [← hm]
      exact hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
    rcases zpow_eq_one_or_eq hz2 j with h | h
    · left
      rw [h, mul_one]
      exact ha
    · right
      rw [h, mul_assoc, hz2, mul_one]
      exact ha
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have : x = x * z * z⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left hx) (inv_mem (mem_sup_right (mem_zpowers z)))

theorem card_sup_of_inf_eq_bot {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G))
    (hAB : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  let f : A × B → (A ⊔ B : Subgroup G) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a ∈ A ⊓ B := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2, ?_⟩
        have : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
          calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
            _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
            _ = b' * (b : G)⁻¹ := by group
        rw [this]
        exact mul_mem b'.2 (inv_mem b.2)
      rw [hAB, mem_bot] at h2
      have ha : (a : G) = a' := by
        calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
          _ = a' := by rw [h2, mul_one]
      have hb : (b : G) = b' := by
        rw [ha] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by
        rw [← hm]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod]

variable {k : ℕ} {A : Subgroup G} (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)))
include ι

theorem pow_eq_one_of_not_mem (hk : 2 ≤ k) (hz : ZAct z k A) (hz2 : z * z = 1) {x : G}
    (hx : x ∈ A ⊔ zpowers z) (hxA : x ∉ A) : x ^ 2 ^ (k - 1) = 1 := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hxz : x * z ∈ A :=
    ((mem_sup_zpowers_iff (hz.mem_normalizer hz2) hz2).1 hx).resolve_left hxA
  set a := x * z with ha
  have hxa : x = a * z := by rw [ha, mul_assoc, hz2, mul_one]
  have hsq : x * x = a * (z * a * z⁻¹) := by
    rw [hxa, hzi]
    group
  rcases hz with h | ⟨hk3, h⟩
  · rw [h a hxz, mul_inv_cancel] at hsq
    obtain ⟨j, hj⟩ : ∃ j, k - 1 = j + 1 := ⟨k - 2, by omega⟩
    rw [hj, pow_succ', pow_mul, sq, hsq, one_pow]
  · rw [h a hxz, mul_inv_cancel_left] at hsq
    obtain ⟨j, hj⟩ : ∃ j, k - 1 = j + 2 := ⟨k - 3, by omega⟩
    have h4 : x ^ 4 = 1 := by
      have e : x ^ 4 = (x * x) ^ 2 := by
        rw [← sq]
        exact pow_mul x 2 2
      rw [e, hsq, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
      exact pow_two_pow_of_coords ι hxz
    rw [hj, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm, pow_mul, h4, one_pow]

theorem pow_two_pow_pred_ne_one (hk : 1 ≤ k) : el ι (Pi.single 0 1) ^ 2 ^ (k - 1) ≠ 1 := by
  rw [← el_nsmul, Ne, el_eq_one_iff]
  intro h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Pi.zero_apply] at h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd (by positivity) h0
  have h2 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem normalizer_sup_le (hk : 2 ≤ k) (hz : ZAct z k A) (hz2 : z * z = 1) :
    normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) ≤ normalizer (A : Set G) := by
  have key : ∀ g ∈ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G), ∀ b ∈ A,
      b ^ 2 ^ (k - 1) ≠ 1 → g * b * g⁻¹ ∈ A := by
    intro g hg b hb hb1
    by_contra hgb
    have h1 : g * b * g⁻¹ ∈ A ⊔ zpowers z := (mem_normalizer_iff.1 hg b).1 (mem_sup_left hb)
    have h2 := pow_eq_one_of_not_mem ι hk hz hz2 h1 hgb
    rw [conj_pow] at h2
    apply hb1
    have : b ^ 2 ^ (k - 1) = g⁻¹ * (g * b ^ 2 ^ (k - 1) * g⁻¹) * g := by group
    rw [this, h2]
    group
  have key' : ∀ g ∈ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G), ∀ a ∈ A,
      g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    set e := el ι (Pi.single 0 1) with he
    have heA : e ∈ A := el_mem ι _
    have he1 : e ^ 2 ^ (k - 1) ≠ 1 := pow_two_pow_pred_ne_one ι (by omega)
    by_cases ha1 : a ^ 2 ^ (k - 1) = 1
    · have hae : (a * e) ^ 2 ^ (k - 1) ≠ 1 := by
        rw [(commute_of_coords ι ha heA).mul_pow, ha1, one_mul]
        exact he1
      have h1 := key g hg _ (mul_mem ha heA) hae
      have h2 := key g hg e heA he1
      have : g * a * g⁻¹ = g * (a * e) * g⁻¹ * (g * e * g⁻¹)⁻¹ := by group
      rw [this]
      exact mul_mem h1 (inv_mem h2)
    · exact key g hg a ha ha1
  intro g hg
  rw [mem_normalizer_iff]
  intro a
  refine ⟨fun ha => key' g hg a ha, fun ha => ?_⟩
  have := key' g⁻¹ (inv_mem hg) _ ha
  rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this

end Sup

namespace ECoords

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
  {hn : 8 ≤ n} {k : ℕ} {A : Subgroup G} {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))}
  (h : ECoords θ hn k A ι) {z : G}
include h

theorem mem_E_of_conj_eq (hz : ZAct z k A) {a : G} (ha : a ∈ A) (hza : z * a * z⁻¹ = a) :
    a ∈ E θ hn := by
  rw [h.mem_E_iff_sq_eq_one ha]
  rcases hz with hz | ⟨hk3, hz⟩
  · rw [hz a ha] at hza
    rw [sq]
    calc a * a = a⁻¹ * a := by rw [hza]
      _ = 1 := inv_mul_cancel a
  · rw [hz a ha] at hza
    have e1 : a ^ 2 ^ (k - 1) = a ^ 2 := by
      calc a ^ 2 ^ (k - 1) = a * (a⁻¹ * a ^ 2 ^ (k - 1)) := by group
        _ = a ^ 2 := by rw [hza, sq]
    have e2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    have e3 : 2 ^ (k - 1) * 2 ^ (k - 2) = 2 ^ k * 2 ^ (k - 3) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    calc a ^ 2 = a ^ 2 ^ (k - 1) := e1.symm
      _ = (a ^ 2) ^ 2 ^ (k - 2) := by rw [← pow_mul, ← e2]
      _ = (a ^ 2 ^ (k - 1)) ^ 2 ^ (k - 2) := by rw [e1]
      _ = (a ^ 2 ^ k) ^ 2 ^ (k - 3) := by rw [← pow_mul, ← pow_mul, e3]
      _ = 1 := by rw [pow_two_pow_of_coords ι ha, one_pow]

theorem z_not_mem (hk : 2 ≤ k) (hz : ZAct z k A) : z ∉ A := by
  intro hzA
  have hle : A ≤ E θ hn := fun a ha =>
    h.mem_E_of_conj_eq hz ha (by rw [comm_of_coords ι hzA ha, mul_inv_cancel_right])
  have hfin : Finite (E θ hn) := Nat.finite_of_card_ne_zero (by rw [card_E]; norm_num)
  have h1 := Subgroup.card_le_of_le hle
  rw [card_E, card_of_coords ι] at h1
  have h2 : 2 ^ 6 ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem card_sup_zpowers (hk : 2 ≤ k) (hz : ZAct z k A) (hz2 : z * z = 1) :
    Nat.card (A ⊔ zpowers z : Subgroup G) = 2 * Nat.card A := by
  have hzA := h.z_not_mem hk hz
  have hz1 : z ≠ 1 := fun h1 => hzA (h1 ▸ one_mem A)
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hz2]) hz1
  have hinf : A ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA, hyz⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hyz
    rcases zpow_eq_one_or_eq hz2 j with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hyA
      exact absurd hyA hzA
  rw [card_sup_of_inf_eq_bot (zpowers_le.2 (hz.mem_normalizer hz2)) hinf, Nat.card_zpowers,
    hord, mul_comm]

end ECoords

section Mat

theorem matrix_ext_mulVec {R : Type*} [CommRing R] {M N : Matrix (Fin 3) (Fin 3) R}
    (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N := by
  have : Matrix.toLin' M = Matrix.toLin' N :=
    LinearMap.ext fun x => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]
  exact Matrix.toLin'.injective this

variable {G : Type} [Group G] {k : ℕ} {A : Subgroup G}
  (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)))

@[expose] def conjFun (g : normalizer (A : Set G)) (x : Fin 3 → ZMod (2 ^ k)) :
    Fin 3 → ZMod (2 ^ k) :=
  Multiplicative.toAdd
    (ι ⟨(g : G) * el ι x * (g : G)⁻¹, (mem_normalizer_iff.1 g.2 _).1 (el_mem ι x)⟩)

theorem el_conjFun (g : normalizer (A : Set G)) (x : Fin 3 → ZMod (2 ^ k)) :
    el ι (conjFun ι g x) = (g : G) * el ι x * (g : G)⁻¹ :=
  el_toAdd ι _

@[expose] def conjAdd (g : normalizer (A : Set G)) :
    (Fin 3 → ZMod (2 ^ k)) →+ (Fin 3 → ZMod (2 ^ k)) where
  toFun := conjFun ι g
  map_zero' := el_injective ι (by rw [el_conjFun, el_zero, mul_one, mul_inv_cancel])
  map_add' x y := el_injective ι (by
    rw [el_conjFun, el_add, el_add, el_conjFun, el_conjFun]
    group)

@[expose] noncomputable def matFun (g : normalizer (A : Set G)) :
    Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k)) :=
  LinearMap.toMatrix' ((conjAdd ι g).toZModLinearMap (2 ^ k))

theorem el_matFun_mulVec (g : normalizer (A : Set G)) (x : Fin 3 → ZMod (2 ^ k)) :
    el ι (matFun ι g *ᵥ x) = (g : G) * el ι x * (g : G)⁻¹ := by
  rw [matFun, LinearMap.toMatrix'_mulVec]
  exact el_conjFun ι g x

@[expose] noncomputable def mat :
    normalizer (A : Set G) →* Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k)) where
  toFun := matFun ι
  map_one' := matrix_ext_mulVec fun x => el_injective ι (by
    rw [el_matFun_mulVec, one_mulVec]
    simp)
  map_mul' g h := matrix_ext_mulVec fun x => el_injective ι (by
    rw [el_matFun_mulVec, ← mulVec_mulVec, el_matFun_mulVec, el_matFun_mulVec]
    simp only [Subgroup.coe_mul]
    group)

theorem mat_spec (g : normalizer (A : Set G)) (x : Fin 3 → ZMod (2 ^ k)) :
    (g : G) * el ι x * (g : G)⁻¹ = el ι (mat ι g *ᵥ x) :=
  (el_matFun_mulVec ι g x).symm

theorem mat_eq_one_iff (g : normalizer (A : Set G)) :
    mat ι g = 1 ↔ ∀ a ∈ A, (g : G) * a * (g : G)⁻¹ = a := by
  constructor
  · intro h1 a ha
    obtain ⟨x, rfl⟩ := exists_el_eq ι ha
    rw [mat_spec, h1, one_mulVec]
  · intro h1
    exact matrix_ext_mulVec fun x => el_injective ι (by
      rw [← mat_spec, one_mulVec, h1 _ (el_mem ι x)])

theorem red_mat {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {hn : 8 ≤ n}
    (h : ECoords θ hn k A ι) (g : normalizer (A : Set G)) (v : Fin 3 → ZMod 2) :
    (g : G) * epsV θ hn v * (g : G)⁻¹ = epsV θ hn (red k (mat ι g) *ᵥ v) := by
  have e : red k (mat ι g) = (mat ι g).map (fun x => ((x.val : ℕ) : ZMod 2)) := by
    ext i j
    rw [red_apply, Matrix.map_apply, ZMod.cast_eq_val]
  rw [← h.eps, ← h.eps, mat_spec, Homo.mulVec_liftE h.one_le, e]

theorem ZAct.el_conj {z : G} (hz : ZAct z k A) :
    ∃ u : ZMod (2 ^ k), (u = -1 ∨ (3 ≤ k ∧ u = -1 + 2 ^ (k - 1))) ∧
      ∀ x, z * el ι x * z⁻¹ = el ι (u • x) := by
  rcases hz with h1 | ⟨hk3, h1⟩
  · refine ⟨-1, Or.inl rfl, fun x => ?_⟩
    rw [h1 _ (el_mem ι x), neg_one_smul, el_neg]
  · refine ⟨-1 + 2 ^ (k - 1), Or.inr ⟨hk3, rfl⟩, fun x => ?_⟩
    rw [h1 _ (el_mem ι x), add_smul, neg_one_smul, el_add, el_neg, ← el_nsmul]
    congr 2
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem mat_z {z : G} (hz : ZAct z k A) (hz2 : z * z = 1) :
    ∃ u : ZMod (2 ^ k), (u = -1 ∨ (3 ≤ k ∧ u = -1 + 2 ^ (k - 1))) ∧
      mat ι ⟨z, hz.mem_normalizer hz2⟩ = u • 1 := by
  obtain ⟨u, hu, hux⟩ := ZAct.el_conj ι hz
  refine ⟨u, hu, matrix_ext_mulVec fun x => el_injective ι ?_⟩
  rw [← mat_spec, smul_mulVec, one_mulVec]
  exact hux x

end Mat

section Sq

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
  {hn : 8 ≤ n} {k : ℕ} {A : Subgroup G} {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))}

theorem coords_of_sq (h : ECoords θ hn k A ι) {A' : Subgroup G}
    (hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x) (hsq : ∀ a ∈ A, ∃ x ∈ A', x ^ 2 = a)
    (hcard : Nat.card A' = 8 * Nat.card A) :
    ∃ ι' : A' ≃* Multiplicative (Fin 3 → ZMod (2 ^ (k + 1))), ECoords θ hn (k + 1) A' ι' := by
  classical
  have hk := h.one_le
  have hAA' : A ≤ A' := fun a ha => by
    obtain ⟨x, hx, rfl⟩ := hsq a ha
    exact pow_mem hx 2
  choose t ht ht2 using fun i : Fin 3 => hsq _ (el_mem ι (Pi.single i 1))
  have htN : ∀ i, t i ^ 2 ^ (k + 1) = 1 := fun i => by
    rw [pow_succ', pow_mul, ht2 i]
    exact pow_two_pow_of_coords ι (el_mem ι _)
  have hc : ∀ i j, Commute (t i) (t j) := fun i j => hcomm _ (ht i) _ (ht j)
  set f : (Fin 3 → ZMod (2 ^ (k + 1))) → G := fun x =>
    t 0 ^ (x 0).val * t 1 ^ (x 1).val * t 2 ^ (x 2).val with hf
  have hfmem : ∀ x, f x ∈ A' := fun x =>
    mul_mem (mul_mem (pow_mem (ht 0) _) (pow_mem (ht 1) _)) (pow_mem (ht 2) _)
  have hpow_val : ∀ i (a b : ZMod (2 ^ (k + 1))),
      t i ^ (a + b).val = t i ^ a.val * t i ^ b.val := by
    intro i a b
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) (2 ^ (k + 1)), pow_add, pow_mul, htN i,
      one_pow, mul_one]
  have hfadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, Pi.add_apply, hpow_val]
    exact (mul3_mul3 ((hc 2 0).pow_pow _ _) ((hc 2 1).pow_pow _ _) ((hc 1 0).pow_pow _ _)).symm
  have hfq : ∀ q : Fin 3 → ℕ, t 0 ^ (2 ^ k * q 0) * t 1 ^ (2 ^ k * q 1) * t 2 ^ (2 ^ k * q 2) =
      el ι (fun i => ((2 ^ (k - 1) * q i : ℕ) : ZMod (2 ^ k))) := by
    intro q
    have e : ∀ i m, t i ^ (2 ^ k * m) = el ι (Pi.single i 1) ^ (2 ^ (k - 1) * m) := by
      intro i m
      rw [← ht2 i, ← pow_mul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]
    rw [e, e, e, el_natCast]
  have heps : ∀ b : Fin 3 → ZMod 2,
      el ι (fun i => ((2 ^ (k - 1) * (b i).val : ℕ) : ZMod (2 ^ k))) = epsV θ hn b := by
    intro b
    rw [← h.eps]
    congr 1
    funext i
    simp only [liftE]
    push_cast
    ring
  let F : Multiplicative (Fin 3 → ZMod (2 ^ (k + 1))) →* A' :=
    { toFun := fun x => ⟨f (Multiplicative.toAdd x), hfmem _⟩
      map_one' := Subtype.ext (by simp [hf])
      map_mul' := fun x y => Subtype.ext (hfadd _ _) }
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : f (Multiplicative.toAdd x) = 1 := congrArg Subtype.val hx
    set y := Multiplicative.toAdd x with hy
    have hsq1 : el ι (fun i => (((y i).val : ℕ) : ZMod (2 ^ k))) = 1 := by
      rw [el_natCast, ← ht2 0, ← ht2 1, ← ht2 2, ← pow_mul, ← pow_mul, ← pow_mul,
        mul_comm 2, mul_comm 2, mul_comm 2, pow_mul, pow_mul, pow_mul,
        ← mul3_pow ((hc 0 1).pow_pow _ _) ((hc 0 2).pow_pow _ _) ((hc 1 2).pow_pow _ _)]
      rw [show t 0 ^ (y 0).val * t 1 ^ (y 1).val * t 2 ^ (y 2).val = f y from rfl, hx1, one_pow]
    rw [el_eq_one_iff] at hsq1
    have hdvd : ∀ i, 2 ^ k ∣ (y i).val := fun i => by
      have := congrFun hsq1 i
      rwa [Pi.zero_apply, ZMod.natCast_eq_zero_iff] at this
    choose q hq using hdvd
    have hq2 : ∀ i, q i < 2 := by
      intro i
      have h1 := ZMod.val_lt (y i)
      rw [hq i, pow_succ] at h1
      exact Nat.lt_of_mul_lt_mul_left h1
    have hfy : f y = epsV θ hn (fun i => (q i : ZMod 2)) := by
      rw [← heps]
      have e : ∀ i, ((q i : ZMod 2)).val = q i := fun i => by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hq2 i)]
      simp only [e]
      rw [← hfq, hf]
      simp only [hq]
    rw [hx1, eq_comm, epsV_eq_one_iff] at hfy
    have hy0 : y = 0 := by
      funext i
      have h1 : (q i : ZMod 2) = 0 := congrFun hfy i
      have h2 : q i = 0 := by
        have := congrArg ZMod.val h1
        rwa [ZMod.val_natCast, Nat.mod_eq_of_lt (hq2 i), ZMod.val_zero] at this
      rw [Pi.zero_apply, ← ZMod.val_eq_zero, hq i, h2, mul_zero]
    rw [hy] at hy0
    exact Multiplicative.toAdd.injective (by rw [hy0, toAdd_one])
  have hfin : Finite A' := Nat.finite_of_card_ne_zero (by
    rw [hcard, card_of_coords ι]
    positivity)
  have hFbij : Function.Bijective F := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hFinj, ?_⟩
    rw [hcard, card_of_coords ι, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    ring
  set ι' := (MulEquiv.ofBijective F hFbij).symm with hι'
  have hel : ∀ x, el ι' x = f x := fun x => by
    simp only [el, hι', MulEquiv.symm_symm, MulEquiv.ofBijective_apply]
    rfl
  refine ⟨ι', ⟨by omega, h.E_le.trans hAA', fun v => ?_⟩⟩
  rw [hel, ← heps, ← hfq]
  have e : ∀ i, ((liftE (k + 1) v) i).val = 2 ^ k * (v i).val := by
    intro i
    simp only [liftE, Nat.add_sub_cancel]
    have hlt : 2 ^ k * (v i).val < 2 ^ (k + 1) := by
      have := ZMod.val_lt (v i)
      rw [pow_succ]
      exact Nat.mul_lt_mul_of_pos_left this (by positivity)
    rw [show (2 : ZMod (2 ^ (k + 1))) ^ k * ((v i).val : ZMod (2 ^ (k + 1))) =
      ((2 ^ k * (v i).val : ℕ) : ZMod (2 ^ (k + 1))) by push_cast; ring, ZMod.val_natCast,
      Nat.mod_eq_of_lt hlt]
  simp only [hf, e]

end Sq

section M1

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
  {hn : 8 ≤ n} {k : ℕ} {A : Subgroup G} {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))}

theorem zact_of_M1 (h : ECoords θ hn k A ι) {z : G} (hzA : ∀ a ∈ A, z * a * z⁻¹ ∈ A)
    (hΓ : ∀ a ∈ A, a * (z * a * z⁻¹) ∈ E θ hn) {x2 y2 : GL (Fin 3) (ZMod 2)}
    (hM1 : ∀ F : Matrix (Fin 3) (Fin 3) (ZMod 2),
      F * (x2 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (x2 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * F →
      F * (y2 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (y2 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * F →
        F = 0 ∨ F = 1)
    (hcov : ∀ M : GL (Fin 3) (ZMod 2), ∃ g ∈ normalizer (A : Set G) ⊓ centralizer ({z} : Set G),
      ∀ v, g * epsV θ hn v * g⁻¹ = epsV θ hn ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)) :
    (∀ a ∈ A, z * a * z⁻¹ = a⁻¹) ∨ (∀ a ∈ A, z * a * z⁻¹ = a⁻¹ * a ^ 2 ^ (k - 1)) := by
  classical
  have hΓmul : ∀ a ∈ A, ∀ b ∈ A, a * b * (z * (a * b) * z⁻¹) =
      a * (z * a * z⁻¹) * (b * (z * b * z⁻¹)) := by
    intro a ha b hb
    have hc : b * (z * a * z⁻¹) = (z * a * z⁻¹) * b := comm_of_coords ι hb (hzA a ha)
    calc a * b * (z * (a * b) * z⁻¹) = a * (b * (z * a * z⁻¹)) * (z * b * z⁻¹) := by group
      _ = a * ((z * a * z⁻¹) * b) * (z * b * z⁻¹) := by rw [hc]
      _ = a * (z * a * z⁻¹) * (b * (z * b * z⁻¹)) := by group
  have hΓsq : ∀ b ∈ A, b ^ 2 * (z * b ^ 2 * z⁻¹) = 1 := by
    intro b hb
    rw [sq, hΓmul b hb b hb, ← sq]
    exact sq_eq_one_of_mem_E θ hn (hΓ b hb)
  have hΓeq : ∀ a ∈ A, ∀ a' ∈ A, a ^ 2 ^ (k - 1) = a' ^ 2 ^ (k - 1) →
      a * (z * a * z⁻¹) = a' * (z * a' * z⁻¹) := by
    intro a ha a' ha' heq
    have haa : a * a'⁻¹ ∈ A := mul_mem ha (inv_mem ha')
    have h1 : (a * a'⁻¹) ^ 2 ^ (k - 1) = 1 := by
      rw [(commute_of_coords ι ha (inv_mem ha')).mul_pow, inv_pow, heq, mul_inv_cancel]
    obtain ⟨b, hb, hb2⟩ := (h.pow_eq_one_iff_sq haa).1 h1
    have h2 : a * a'⁻¹ * (z * (a * a'⁻¹) * z⁻¹) = 1 := by
      rw [← hb2]
      exact hΓsq b hb
    have h3 := hΓmul _ haa _ ha'
    rw [inv_mul_cancel_right, h2, one_mul] at h3
    exact h3
  have hlift_pow : ∀ v, el ι (fun i => (((v i).val : ℕ) : ZMod (2 ^ k))) ^ 2 ^ (k - 1) =
      epsV θ hn v := h.el_lift_pow
  choose γ hγ using fun v : Fin 3 → ZMod 2 => (mem_E_iff_epsV θ hn _).1
    (hΓ _ (el_mem ι (fun i => (((v i).val : ℕ) : ZMod (2 ^ k)))))
  have hγ' : ∀ a ∈ A, ∀ v, a ^ 2 ^ (k - 1) = epsV θ hn v →
      a * (z * a * z⁻¹) = epsV θ hn (γ v) := by
    intro a ha v hv
    rw [hγ v]
    exact hΓeq a ha _ (el_mem ι _) (by rw [hv, hlift_pow])
  have hγadd : ∀ v w, γ (v + w) = γ v + γ w := by
    intro v w
    apply epsV_injective θ hn
    have hm := mul_mem (el_mem ι (fun i => (((v i).val : ℕ) : ZMod (2 ^ k))))
      (el_mem ι (fun i => (((w i).val : ℕ) : ZMod (2 ^ k))))
    have hp : (el ι (fun i => (((v i).val : ℕ) : ZMod (2 ^ k))) *
        el ι (fun i => (((w i).val : ℕ) : ZMod (2 ^ k)))) ^ 2 ^ (k - 1) = epsV θ hn (v + w) := by
      rw [(commute_of_coords ι (el_mem ι _) (el_mem ι _)).mul_pow, hlift_pow, hlift_pow, epsV_add]
    rw [epsV_add, ← hγ' _ hm _ hp, hΓmul _ (el_mem ι _) _ (el_mem ι _), hγ, hγ]
  have hγeqv : ∀ M : GL (Fin 3) (ZMod 2), ∀ v,
      γ ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
        (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ γ v := by
    intro M v
    obtain ⟨g, ⟨hgN, hgz⟩, hgE⟩ := hcov M
    have hgz' : g * z = z * g := mem_centralizer_singleton_iff.1 hgz
    set a := el ι (fun i => (((v i).val : ℕ) : ZMod (2 ^ k))) with ha
    have haA : a ∈ A := el_mem ι _
    have hga : g * a * g⁻¹ ∈ A := (mem_normalizer_iff.1 hgN a).1 haA
    have hpow : (g * a * g⁻¹) ^ 2 ^ (k - 1) =
        epsV θ hn ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
      rw [conj_pow, ha, hlift_pow, hgE]
    have hzg : z * (g * a * g⁻¹) * z⁻¹ = g * (z * a * z⁻¹) * g⁻¹ := by
      calc z * (g * a * g⁻¹) * z⁻¹ = (z * g) * a * (z * g)⁻¹ := by group
        _ = (g * z) * a * (g * z)⁻¹ := by rw [hgz']
        _ = g * (z * a * z⁻¹) * g⁻¹ := by group
    have hΓg : g * a * g⁻¹ * (z * (g * a * g⁻¹) * z⁻¹) = g * (a * (z * a * z⁻¹)) * g⁻¹ := by
      rw [hzg]
      group
    apply epsV_injective θ hn
    rw [← hγ' _ hga _ hpow, hΓg, ← hgE, ← hγ v]
  have hγ0 : γ 0 = 0 := by
    have h0 := hγadd 0 0
    rw [add_zero] at h0
    exact left_eq_add.1 h0
  let γh : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := γ, map_zero' := hγ0, map_add' := hγadd }
  have hγsmul : ∀ (c : ZMod 2) v, γ (c • v) = c • γ v := by
    intro c v
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact map_nsmul γh c.val v
  let γl : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := γ, map_add' := hγadd, map_smul' := hγsmul }
  set F := LinearMap.toMatrix' γl with hF
  have hFv : ∀ v, F *ᵥ v = γ v := fun v => by
    rw [hF, LinearMap.toMatrix'_mulVec]
    rfl
  have hFM : ∀ M : GL (Fin 3) (ZMod 2), F * (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) * F := fun M =>
    matrix_ext_mulVec fun v => by
      rw [← mulVec_mulVec, ← mulVec_mulVec, hFv, hFv, hγeqv]
  rcases hM1 F (hFM x2) (hFM y2) with hF0 | hF1
  · left
    intro a ha
    obtain ⟨v, hv⟩ := (mem_E_iff_epsV θ hn _).1 (h.pow_mem_E ha)
    have h1 := hγ' a ha v hv.symm
    have h2 : γ v = 0 := by rw [← hFv, hF0, zero_mulVec]
    rw [h2, epsV_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  · right
    intro a ha
    obtain ⟨v, hv⟩ := (mem_E_iff_epsV θ hn _).1 (h.pow_mem_E ha)
    have h1 := hγ' a ha v hv.symm
    have h2 : γ v = v := by rw [← hFv, hF1, one_mulVec]
    rw [h2, hv] at h1
    rw [← h1]
    group

end M1

namespace LevelDatum

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
  {hn : 8 ≤ n} {z : G} {k : ℕ} {A : Subgroup G}

theorem exists_ecoords (h : LevelDatum θ hn z k A) :
    ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)), ECoords θ hn k A ι := by
  obtain ⟨ι, hι⟩ := h.coords
  refine ⟨ι, ⟨by have := h.two_le; omega, h.E_le, fun v => ?_⟩⟩
  have hv : epsV θ hn v ∈ A := h.E_le (epsV_mem_E θ hn v)
  rw [el, ← hι v hv, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem zAct (h : LevelDatum θ hn z k A) : ZAct z k A := h.zact

theorem comm (h : LevelDatum θ hn z k A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a := by
  obtain ⟨ι, -⟩ := h.exists_ecoords
  exact comm_of_coords ι ha hb

theorem pow_two_pow (h : LevelDatum θ hn z k A) {a : G} (ha : a ∈ A) : a ^ 2 ^ k = 1 := by
  obtain ⟨ι, -⟩ := h.exists_ecoords
  exact pow_two_pow_of_coords ι ha

theorem card (h : LevelDatum θ hn z k A) : Nat.card A = 2 ^ (3 * k) := by
  obtain ⟨ι, -⟩ := h.exists_ecoords
  exact card_of_coords ι

theorem le_centralizer_E (h : LevelDatum θ hn z k A) : A ≤ centralizer (E θ hn : Set G) := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.le_centralizer_E

theorem mem_E_iff_sq_eq_one (h : LevelDatum θ hn z k A) {a : G} (ha : a ∈ A) :
    a ∈ E θ hn ↔ a ^ 2 = 1 := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.mem_E_iff_sq_eq_one ha

theorem pow_mem_E (h : LevelDatum θ hn z k A) {a : G} (ha : a ∈ A) : a ^ 2 ^ (k - 1) ∈ E θ hn := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.pow_mem_E ha

theorem exists_pow_eq_eps (h : LevelDatum θ hn z k A) (v : Fin 3 → ZMod 2) :
    ∃ a ∈ A, a ^ 2 ^ (k - 1) = epsV θ hn v := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.exists_pow_eq_eps v

theorem pow_eq_one_iff_sq (h : LevelDatum θ hn z k A) {a : G} (ha : a ∈ A) :
    a ^ 2 ^ (k - 1) = 1 ↔ ∃ b ∈ A, b ^ 2 = a := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.pow_eq_one_iff_sq ha

theorem mem_E_of_conj_eq (h : LevelDatum θ hn z k A) {a : G} (ha : a ∈ A)
    (hza : z * a * z⁻¹ = a) : a ∈ E θ hn := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.mem_E_of_conj_eq h.zact ha hza

theorem z_not_mem (h : LevelDatum θ hn z k A) : z ∉ A := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.z_not_mem h.two_le h.zact

theorem conj_z_mem (h : LevelDatum θ hn z k A) {a : G} (ha : a ∈ A) : z * a * z⁻¹ ∈ A :=
  h.zAct.conj_mem ha

theorem z_mem_normalizer (h : LevelDatum θ hn z k A) (hz2 : z * z = 1) :
    z ∈ normalizer (A : Set G) :=
  h.zAct.mem_normalizer hz2

theorem card_sup (h : LevelDatum θ hn z k A) (hz2 : z * z = 1) :
    Nat.card (A ⊔ zpowers z : Subgroup G) = 2 * Nat.card A := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  exact hι.card_sup_zpowers h.two_le h.zact hz2

theorem normalizer_sup_le (h : LevelDatum θ hn z k A) (hz2 : z * z = 1) :
    normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) ≤ normalizer (A : Set G) := by
  obtain ⟨ι, -⟩ := h.exists_ecoords
  exact G2.normalizer_sup_le ι h.two_le h.zact hz2

theorem mem_sup_iff (h : LevelDatum θ hn z k A) (hz2 : z * z = 1) {x : G} :
    x ∈ A ⊔ zpowers z ↔ x ∈ A ∨ x * z ∈ A :=
  mem_sup_zpowers_iff (h.z_mem_normalizer hz2) hz2

end LevelDatum

end CFSG.OddStandard.AltStdSmall4.G2
