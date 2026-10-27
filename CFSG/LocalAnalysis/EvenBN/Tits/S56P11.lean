module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N7
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N4
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace S56

theorem sq_t_mul {G : Type*} [Group G] {t f a u : G} (ht : t * t = 1) (hft : f * t = t * f)
    (hat : a * t = t * a) (haf : a * f = f * a) (hff : f * f = 1) (huf : u * f = f * u)
    (hu : u * t = t * a * u) (huu : u * u = 1) : (t * f * u) * (t * f * u) = a := by
  have e1 : t * f * t = f := by
    calc t * f * t = f * t * t := by rw [← hft]
      _ = f := by rw [mul_assoc, ht, mul_one]
  calc (t * f * u) * (t * f * u) = t * f * (u * t) * f * u := by group
    _ = t * f * (t * a * u) * f * u := by rw [hu]
    _ = (t * f * t) * a * (u * f) * u := by group
    _ = f * a * (f * u) * u := by rw [e1, huf]
    _ = f * a * f * (u * u) := by group
    _ = a := by
      rw [huu, mul_one]
      calc f * a * f = a * f * f := by rw [← haf]
        _ = a := by rw [mul_assoc, hff, mul_one]

theorem isElemAbelian_closure {G : Type*} [Group G] (S : Set G)
    (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hs : ∀ a ∈ S, a * a = 1) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.closure S) := by
  have h1 : ∀ s ∈ S, ∀ y ∈ Subgroup.closure S, s * y = y * s := fun s hs y hy => by
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({s} : Set G) :=
      (Subgroup.closure_le _).2 fun b hb => by
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hc s hs b hb
    exact (Subgroup.mem_centralizer_iff.1 (hle hy) s (Set.mem_singleton s))
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x :=
      fun x hx y hy => by
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({y} : Set G) :=
      (Subgroup.closure_le _).2 fun b hb => by
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (h1 b hb y hy).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) y (Set.mem_singleton y)).symm
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => simp
  | mul x y hx hy hx' hy' =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx', hy', one_mul]
  | inv x hx hx' =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hx', inv_one]

end S56

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

@[expose] noncomputable def s56P11 (d : Data G) : Subgroup G where
  carrier := {g | g ∈ d.s56P ∧ g ∈ normalizer (d.s56U11 : Set G) ∧
    ∀ b ∈ d.B, g * b * g⁻¹ * b⁻¹ ∈ d.s56U11}
  mul_mem' := by
    rintro g h ⟨hgK, hgN, hg⟩ ⟨hhK, hhN, hh⟩
    refine ⟨mul_mem hgK hhK, mul_mem hgN hhN, fun y hy => ?_⟩
    have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
        g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 hgN _).1 (hh y hy)) (hg y hy)
  one_mem' := ⟨one_mem _, one_mem _, fun y _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgK, hgN, hg⟩
    refine ⟨inv_mem hgK, inv_mem hgN, fun y hy => ?_⟩
    have e : g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ = g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ * g := by group
    rw [e]
    exact (mem_normalizer_iff''.1 hgN _).1 (inv_mem (hg y hy))

@[expose] noncomputable def s56Pe11 (d : Data G) : Subgroup G := ⁅d.s56P11, d.N⁆

@[expose] noncomputable def s56R1 (d : Data G) (z₀ y : G) : Subgroup G :=
  d.F ⊔ Subgroup.closure ({z₀, y * z₀ * y⁻¹} : Set G)


theorem s56_P_le_N (d : Data G) : d.s56P ≤ d.N := (s56_P_le_P0 d).trans (s56_P0_le_N d)

theorem s56_mem_P_iff (d : Data G) {p : G} :
    p ∈ d.s56P ↔ p ∈ d.s56P0 ∧ ∀ f ∈ d.F, p * f = f * p := by
  rw [s56P_def, mem_inf, mem_centralizer_iff]
  exact and_congr_right fun _ => forall₂_congr fun f _ => ⟨fun h => h.symm, fun h => h.symm⟩

theorem s56_P_conj_F (d : Data G) {p f : G} (hp : p ∈ d.s56P) (hf : f ∈ d.F) :
    p * f * p⁻¹ = f := by
  rw [((s56_mem_P_iff d).1 hp).2 f hf]; group

theorem Hyp.s56_F_sq (hd : d.Hyp) {f : G} (hf : f ∈ d.F) : f * f = 1 := by
  have := hd.B_facts.2.2.1.2 f (s56_F_le_B d hf)
  rwa [pow_two] at this

theorem Hyp.s56_eps_mul_P (h49 : d.Thm49Statement) (hd : d.Hyp) {p q : G} (hp : p ∈ d.s56P)
    (hq : q ∈ d.s56P) : d.s56Eps (p * q) = d.s56Eps p * d.s56Eps q := by
  rw [hd.s56_eps_mul]
  congr 1
  exact s56_P_conj_F d hp (hd.s56_eps_mem_F_of_N h49 (s56_P_le_N d hq))

theorem Hyp.s56_eps_sq_P (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G} (hp : p ∈ d.s56P) :
    d.s56Eps p * d.s56Eps p = 1 :=
  hd.s56_F_sq (hd.s56_eps_mem_F_of_N h49 (s56_P_le_N d hp))

theorem Hyp.s56_eps_inv_P (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G} (hp : p ∈ d.s56P) :
    d.s56Eps p⁻¹ = d.s56Eps p := by
  have h1 := hd.s56_eps_mul_P h49 hp (inv_mem hp)
  rw [mul_inv_cancel, hd.s56_eps_one] at h1
  have h2 := hd.s56_eps_sq_P h49 hp
  have h3 : d.s56Eps p⁻¹ = (d.s56Eps p)⁻¹ := (inv_eq_of_mul_eq_one_right h1.symm).symm
  rw [h3]
  exact inv_eq_of_mul_eq_one_right h2

theorem Hyp.s56_eps_eq_one_of_mem_B (hd : d.Hyp) {b : G} (hb : b ∈ d.B) : d.s56Eps b = 1 := by
  have h := congrArg Subtype.val (hd.B_facts.2.2.1.1.is_comm.comm ⟨d.t, s56_t_mem_B d⟩ ⟨b, hb⟩)
  have h' : d.t * b = b * d.t := h
  rw [s56Eps, show b * d.t * b⁻¹ = d.t by rw [← h']; group, hd.t_mul_self]

theorem Hyp.s56_mem_B_of_eps_one (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G} (hp : p ∈ d.s56P)
    (h : d.s56Eps p = 1) : p ∈ d.B := by
  have hpt : p * d.t = d.t * p := by
    have h1 := hd.s56_conj_t p
    rw [h, mul_one] at h1
    calc p * d.t = p * d.t * p⁻¹ * p := by group
      _ = d.t * p := by rw [h1]
  rw [← hd.centralizer_B]
  refine mem_centralizer_iff.2 fun b hb => ?_
  have hpF := ((s56_mem_P_iff d).1 hp).2
  rcases (hd.s56_mem_B_iff).1 hb with hf | hf
  · exact (hpF b hf).symm
  · have hb' : b = d.t * (d.t * b) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
    rw [hb']
    calc d.t * (d.t * b) * p = d.t * ((d.t * b) * p) := by group
      _ = d.t * (p * (d.t * b)) := by rw [hpF _ hf]
      _ = (d.t * p) * (d.t * b) := by group
      _ = (p * d.t) * (d.t * b) := by rw [hpt]
      _ = p * (d.t * (d.t * b)) := by group

theorem Hyp.s56_N_conj_P (h49 : d.Thm49Statement) (hd : d.Hyp) {n p : G} (hn : n ∈ d.N)
    (hp : p ∈ d.s56P) : n * p * n⁻¹ ∈ d.s56P := by
  rw [s56_mem_P_iff]
  refine ⟨s56_N_conj_P0 d hn ((s56_mem_P_iff d).1 hp).1, fun f hf => ?_⟩
  have hf' : n⁻¹ * f * n⁻¹⁻¹ ∈ d.F := hd.s56_N_conj_F h49 (inv_mem hn) hf
  have h := ((s56_mem_P_iff d).1 hp).2 _ hf'
  calc n * p * n⁻¹ * f = n * (p * (n⁻¹ * f * n⁻¹⁻¹)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * f * n⁻¹⁻¹) * p) * n⁻¹ := by rw [h]
    _ = f * (n * p * n⁻¹) := by group

theorem Hyp.s56_eps_conj_N (h49 : d.Thm49Statement) (hd : d.Hyp) {n p : G} (hn : n ∈ d.N)
    (hp : p ∈ d.s56P) : d.s56Eps (n * p * n⁻¹) = n * d.s56Eps p * n⁻¹ := by
  have hnF := hd.s56_eps_mem_F_of_N h49 hn
  have hn'F := hd.s56_eps_mem_F_of_N h49 (inv_mem hn)
  have hpF := hd.s56_eps_mem_F_of_N h49 (s56_P_le_N d hp)
  have hcF : n * d.s56Eps p * n⁻¹ ∈ d.F := hd.s56_N_conj_F h49 hn hpF
  have h1 : d.s56Eps (n * (p * n⁻¹)) = d.s56Eps n * (n * d.s56Eps (p * n⁻¹) * n⁻¹) :=
    hd.s56_eps_mul n (p * n⁻¹)
  have h2 : d.s56Eps (p * n⁻¹) = d.s56Eps p * (p * d.s56Eps n⁻¹ * p⁻¹) :=
    hd.s56_eps_mul p n⁻¹
  have h3 : p * d.s56Eps n⁻¹ * p⁻¹ = d.s56Eps n⁻¹ := s56_P_conj_F d hp hn'F
  have h4 : d.s56Eps (n * n⁻¹) = d.s56Eps n * (n * d.s56Eps n⁻¹ * n⁻¹) := hd.s56_eps_mul n n⁻¹
  rw [mul_inv_cancel, hd.s56_eps_one] at h4
  have h5 : n * d.s56Eps n⁻¹ * n⁻¹ = d.s56Eps n := by
    have hsq := hd.s56_F_sq hnF
    have h6 : n * d.s56Eps n⁻¹ * n⁻¹ = (d.s56Eps n)⁻¹ := (inv_eq_of_mul_eq_one_right h4.symm).symm
    rw [h6]
    exact inv_eq_of_mul_eq_one_right hsq
  have hcomm : d.s56Eps n * (n * d.s56Eps p * n⁻¹) = (n * d.s56Eps p * n⁻¹) * d.s56Eps n :=
    hd.s56_F_comm hnF hcF
  have e : n * p * n⁻¹ = n * (p * n⁻¹) := by group
  rw [e, h1, h2, h3]
  calc d.s56Eps n * (n * (d.s56Eps p * d.s56Eps n⁻¹) * n⁻¹)
      = d.s56Eps n * ((n * d.s56Eps p * n⁻¹) * (n * d.s56Eps n⁻¹ * n⁻¹)) := by group
    _ = d.s56Eps n * ((n * d.s56Eps p * n⁻¹) * d.s56Eps n) := by rw [h5]
    _ = (d.s56Eps n * (n * d.s56Eps p * n⁻¹)) * d.s56Eps n := by group
    _ = ((n * d.s56Eps p * n⁻¹) * d.s56Eps n) * d.s56Eps n := by rw [hcomm]
    _ = (n * d.s56Eps p * n⁻¹) * (d.s56Eps n * d.s56Eps n) := by group
    _ = n * d.s56Eps p * n⁻¹ := by rw [hd.s56_F_sq hnF, mul_one]

theorem s56_pv11_ne_one (d : Data G) : d.pv 11 ≠ 1 := fun h =>
  Model.parrottV_ne.1 (d.lift_inj (s56_parrottV_mem_titsD (i := 11) (by omega)) (one_mem _)
    (by rw [d.lift_one]; exact h))

theorem s56_eq_one_of_mem_P0_pow_three (d : Data G) {x : G} (hx : x ∈ d.s56P0) (h3 : x ^ 3 = 1) :
    x = 1 := by
  obtain ⟨k, hk⟩ := s56_P0_isPGroup d ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h := pow_gcd_eq_one.2 ⟨hk', h3⟩
  have hc : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rwa [hc, pow_one] at h

theorem Hyp.s56_y_orbit (h49 : d.Thm49Statement) (hd : d.Hyp) {y : G} (hy : y ∈ d.N)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    y * d.z * y⁻¹ ∈ d.s56U11 ∧ y * d.z * y⁻¹ ≠ 1 ∧ y * d.z * y⁻¹ ≠ d.z ∧
      y * (y * d.z * y⁻¹) * y⁻¹ = d.z * (y * d.z * y⁻¹) ∧
      ∀ a ∈ d.s56U11, a = 1 ∨ a = d.z ∨ a = y * d.z * y⁻¹ ∨ a = d.z * (y * d.z * y⁻¹) := by
  have hz11 := s56_z_mem_U11 d
  have hv11 := s56_pv11_mem_U11 d
  have hzv : d.z * d.pv 11 = d.pv 11 * d.z := hd.s56_E_comm hd.s56_z_mem_E (s56_pv11_mem_E d)
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hvzz : d.pv 11 * d.z * d.z = d.pv 11 := by rw [mul_assoc, hzz, mul_one]
  have hy3'' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  have hyinv : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hy3'')
  have hcen : ∀ n ∈ d.N, (∀ u ∈ d.s56U11, n * u = u * n) → n ∈ d.s56P0 := fun n hn h => by
    rw [← hd.s56_CN_U11_eq h49]
    exact mem_inf.2 ⟨hn, mem_centralizer_iff.2 fun u hu => (h u hu).symm⟩
  have hyP : ¬ (y ∈ d.s56P0) := fun h => hy1 (s56_eq_one_of_mem_P0_pow_three d h hy3)
  have hU : ∀ u ∈ d.s56U11, y * u * y⁻¹ ∈ d.s56U11 := fun u hu => hd.s56_N_conj_U11 h49 hy hu
  have hcancel : ∀ a b : G, y * a * y⁻¹ = y * b * y⁻¹ → a = b := fun a b h =>
    mul_left_cancel (mul_right_cancel h)
  have hgen : ∀ n : G, n * d.pv 11 = d.pv 11 * n → n * d.z = d.z * n →
      ∀ u ∈ d.s56U11, n * u = u * n := fun n h1 h2 u hu => by
    rcases s56_mem_U11_iff.1 hu with rfl | rfl | rfl | rfl
    · simp
    · exact h1
    · exact h2
    · calc n * (d.pv 11 * d.z) = (n * d.pv 11) * d.z := by group
        _ = (d.pv 11 * n) * d.z := by rw [h1]
        _ = d.pv 11 * (n * d.z) := by group
        _ = d.pv 11 * (d.z * n) := by rw [h2]
        _ = (d.pv 11 * d.z) * n := by group
  generalize ha₁ : y * d.z * y⁻¹ = a₁
  have ha₁U : a₁ ∈ d.s56U11 := ha₁ ▸ hU _ hz11
  have hne_one : a₁ ≠ 1 := fun h => hd.s56_z_ne_one (hcancel _ _ (by rw [ha₁, h]; group))
  have hne_z : a₁ ≠ d.z := by
    intro hyz
    rw [← ha₁] at hyz
    have hb := hU _ hv11
    rcases s56_mem_U11_iff.1 hb with h | h | h | h
    · exact s56_pv11_ne_one d (hcancel _ _ (by rw [h]; group))
    · apply hyP
      refine hcen y hy (hgen y ?_ ?_)
      · calc y * d.pv 11 = (y * d.pv 11 * y⁻¹) * y := by group
          _ = d.pv 11 * y := by rw [h]
      · calc y * d.z = (y * d.z * y⁻¹) * y := by group
          _ = d.z * y := by rw [hyz]
    · exact s56_pv11_ne_z d (hcancel _ _ (by rw [h, hyz]))
    · apply hyP
      have hyyv : y * y * d.pv 11 = d.pv 11 * (y * y) :=
        calc y * y * d.pv 11 = (y * (y * d.pv 11 * y⁻¹) * y⁻¹) * (y * y) := by group
          _ = (y * (d.pv 11 * d.z) * y⁻¹) * (y * y) := by rw [h]
          _ = ((y * d.pv 11 * y⁻¹) * (y * d.z * y⁻¹)) * (y * y) := by group
          _ = ((d.pv 11 * d.z) * d.z) * (y * y) := by rw [h, hyz]
          _ = d.pv 11 * (y * y) := by rw [hvzz]
      have hyyz : y * y * d.z = d.z * (y * y) :=
        calc y * y * d.z = (y * (y * d.z * y⁻¹) * y⁻¹) * (y * y) := by group
          _ = d.z * (y * y) := by rw [hyz, hyz]
      have hyy : y * y ∈ d.s56P0 := hcen _ (mul_mem hy hy) (hgen _ hyyv hyyz)
      have hyy' : y = (y * y)⁻¹ := by rw [← hyinv, inv_inv]
      rw [hyy']
      exact inv_mem hyy
  have ha₂U : y * a₁ * y⁻¹ ∈ d.s56U11 := hU _ ha₁U
  have ha₂_ne_one : y * a₁ * y⁻¹ ≠ 1 := fun h => hne_one (hcancel _ _ (by rw [h]; group))
  have ha₂_ne_a₁ : y * a₁ * y⁻¹ ≠ a₁ := fun h => hne_z (by
    calc a₁ = y⁻¹ * (y * a₁ * y⁻¹) * y := by group
      _ = y⁻¹ * a₁ * y := by rw [h]
      _ = d.z := by rw [← ha₁]; group)
  have ha₂_ne_z : y * a₁ * y⁻¹ ≠ d.z := fun h => hne_z (by
    calc a₁ = y * d.z * y⁻¹ := ha₁.symm
      _ = y * (y * a₁ * y⁻¹) * y⁻¹ := by rw [h]
      _ = (y * y * y) * d.z * (y * y * y)⁻¹ := by rw [← ha₁]; group
      _ = d.z := by rw [hy3'']; group)
  have hb : (a₁ = d.pv 11 ∧ y * a₁ * y⁻¹ = d.pv 11 * d.z ∧ d.z * a₁ = d.pv 11 * d.z) ∨
      (a₁ = d.pv 11 * d.z ∧ y * a₁ * y⁻¹ = d.pv 11 ∧ d.z * a₁ = d.pv 11) := by
    rcases s56_mem_U11_iff.1 ha₁U with h1 | h1 | h1 | h1
    · exact absurd h1 hne_one
    · left
      refine ⟨h1, ?_, by rw [h1]; exact hzv⟩
      rcases s56_mem_U11_iff.1 ha₂U with h2 | h2 | h2 | h2
      · exact absurd h2 ha₂_ne_one
      · exact absurd (h2.trans h1.symm) ha₂_ne_a₁
      · exact absurd h2 ha₂_ne_z
      · exact h2
    · exact absurd h1 hne_z
    · right
      refine ⟨h1, ?_, ?_⟩
      · rcases s56_mem_U11_iff.1 ha₂U with h2 | h2 | h2 | h2
        · exact absurd h2 ha₂_ne_one
        · exact h2
        · exact absurd h2 ha₂_ne_z
        · exact absurd (h2.trans h1.symm) ha₂_ne_a₁
      · rw [h1]
        calc d.z * (d.pv 11 * d.z) = (d.z * d.pv 11) * d.z := by group
          _ = (d.pv 11 * d.z) * d.z := by rw [hzv]
          _ = d.pv 11 := hvzz
  have ha₂ : y * a₁ * y⁻¹ = d.z * a₁ := by
    rcases hb with ⟨_, h2, h3⟩ | ⟨_, h2, h3⟩
    · rw [h2, h3]
    · rw [h2, h3]
  refine ⟨ha₁U, hne_one, hne_z, ha₂, fun a ha => ?_⟩
  rcases s56_mem_U11_iff.1 ha with h | h | h | h
  · exact Or.inl h
  · rcases hb with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩
    · exact Or.inr (Or.inr (Or.inl (h.trans h1.symm)))
    · exact Or.inr (Or.inr (Or.inr (h.trans h3.symm)))
  · exact Or.inr (Or.inl h)
  · rcases hb with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩
    · exact Or.inr (Or.inr (Or.inr (h.trans h3.symm)))
    · exact Or.inr (Or.inr (Or.inl (h.trans h1.symm)))

theorem s56_P11_le_P (d : Data G) : d.s56P11 ≤ d.s56P := fun _ hg => hg.1

theorem Hyp.s56_P_normalizes_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G}
    (hp : p ∈ d.s56P) : p ∈ normalizer (d.s56U11 : Set G) :=
  Subgroup.centralizer_le_normalizer (d.s56U11 : Set G) (mem_centralizer_iff.2 fun u hu =>
    (hd.s56_P0_comm_U11 h49 ((s56_mem_P_iff d).1 hp).1 hu).symm)

theorem Hyp.s56_mem_P11_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {g : G} :
    g ∈ d.s56P11 ↔ g ∈ d.s56P ∧ d.s56Eps g ∈ d.s56U11 := by
  constructor
  · rintro ⟨hP, -, hc⟩
    refine ⟨hP, ?_⟩
    have h := hc d.t (s56_t_mem_B d)
    have hεF := hd.s56_eps_mem_F_of_N h49 (s56_P_le_N d hP)
    have hεt : d.s56Eps g * d.t = d.t * d.s56Eps g := hd.L_comm_t (s56_F_le_L d hεF)
    have e : g * d.t * g⁻¹ * d.t⁻¹ = d.s56Eps g := by
      rw [hd.s56_conj_t g]
      calc d.t * d.s56Eps g * d.t⁻¹ = (d.s56Eps g * d.t) * d.t⁻¹ := by rw [hεt]
        _ = d.s56Eps g := by group
    rwa [e] at h
  · rintro ⟨hP, hε⟩
    refine ⟨hP, hd.s56_P_normalizes_U11 h49 hP, fun b hb => ?_⟩
    have hεF := hd.s56_eps_mem_F_of_N h49 (s56_P_le_N d hP)
    have hεt : d.t * d.s56Eps g = d.s56Eps g * d.t := (hd.L_comm_t (s56_F_le_L d hεF)).symm
    rcases (hd.s56_mem_B_iff).1 hb with hf | hf
    · rw [s56_P_conj_F d hP hf]
      simpa using one_mem _
    · have hb' : b = d.t * (d.t * b) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
      have hgb : g * b * g⁻¹ = d.t * d.s56Eps g * (d.t * b) :=
        calc g * b * g⁻¹ = g * (d.t * (d.t * b)) * g⁻¹ := by rw [← hb']
          _ = (g * d.t * g⁻¹) * (g * (d.t * b) * g⁻¹) := by group
          _ = (d.t * d.s56Eps g) * (d.t * b) := by rw [hd.s56_conj_t g, s56_P_conj_F d hP hf]
      have e : g * b * g⁻¹ * b⁻¹ = d.s56Eps g :=
        calc g * b * g⁻¹ * b⁻¹ = (d.t * d.s56Eps g * (d.t * b)) * b⁻¹ := by rw [hgb]
          _ = d.t * d.s56Eps g * d.t := by group
          _ = d.s56Eps g * d.t * d.t := by rw [hεt]
          _ = d.s56Eps g := by rw [mul_assoc, hd.t_mul_self, mul_one]
      rw [e]
      exact hε

theorem Hyp.s56_B_le_P11 (h49 : d.Thm49Statement) (hd : d.Hyp) : d.B ≤ d.s56P11 := fun b hb =>
  (hd.s56_mem_P11_iff h49).2 ⟨hd.s56_B_le_P hb, by
    rw [hd.s56_eps_eq_one_of_mem_B hb]; exact one_mem _⟩

theorem Hyp.s56_P11_le_M (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56P11 ≤ d.M := fun g hg => by
  obtain ⟨hP, hε⟩ := (hd.s56_mem_P11_iff h49).1 hg
  have h := (hd.s56_P0_inf_M_iff h49 (p := g)).2
    ⟨((s56_mem_P_iff d).1 hP).1, d.s56Eps g, s56_U11_le_E d hd hε, hd.s56_conj_t g⟩
  exact (mem_inf.1 h).2

theorem Hyp.s56_N_conj_P11 (h49 : d.Thm49Statement) (hd : d.Hyp) {n g : G} (hn : n ∈ d.N)
    (hg : g ∈ d.s56P11) : n * g * n⁻¹ ∈ d.s56P11 := by
  rw [hd.s56_mem_P11_iff h49] at hg ⊢
  obtain ⟨hP, hε⟩ := hg
  refine ⟨hd.s56_N_conj_P h49 hn hP, ?_⟩
  rw [hd.s56_eps_conj_N h49 hn hP]
  exact hd.s56_N_conj_U11 h49 hn hε

theorem Hyp.s56_z0_mem_P (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    z₀ ∈ d.s56P := by
  have hQ0 : z₀ ∈ d.s56Q0 := hd.s56_Q2_le_Q0 h49 hz.mem_Q2
  have hzN : z₀ ∈ d.N :=
    (hd.s56_mem_N_iff_eps h49 hQ0).2 (by rw [hz.eps]; exact hd.s56_z_mem_F)
  have hP0 := hd.s56_Q2_inf_N_le_P0 h49 hz.mem_Q2 hzN
  rw [s56_mem_P_iff]
  exact ⟨hP0, fun f hf => (hz.comm_Q f (hd.s56_F_le_Q h49 hf)).symm⟩

theorem Hyp.s56_z0_mem_P11 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    z₀ ∈ d.s56P11 :=
  (hd.s56_mem_P11_iff h49).2 ⟨hd.s56_z0_mem_P h49 hz, by rw [hz.eps]; exact s56_z_mem_U11 d⟩

theorem Hyp.s56_M_comm_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {m : G} (hm : m ∈ d.M) : m * z₀ * m⁻¹ * z₀⁻¹ ∈ zpowers d.z := by
  have hZ := hd.s56_M_le_normalizer_Z h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.comm_v hz.dich
  have hmem : m * z₀ * m⁻¹ ∈ zpowers d.z ⊔ zpowers z₀ :=
    (mem_normalizer_iff.1 (hZ hm) z₀).1 (mem_sup_right (mem_zpowers z₀))
  have hcomm : ∀ a ∈ zpowers d.z, z₀ * a = a * z₀ := fun a ha =>
    hz.cen (hd.s56_zpowers_le_E ha)
  rcases s56y_mem_sup_zpowers (A := zpowers d.z) (y := z₀) hcomm hz.sq hmem with h | ⟨a, ha, h⟩
  · exfalso
    have h1 : z₀ = m * z₀ * m⁻¹ :=
      calc z₀ = m⁻¹ * (m * z₀ * m⁻¹) * m⁻¹⁻¹ := by group
        _ = m * z₀ * m⁻¹ := hd.s56_M_conj_zpowers (inv_mem hm) h
    have h2 : z₀ ∈ zpowers d.z := h1 ▸ h
    have h3 := hd.s56_eps_of_comm (m := z₀)
      (hd.L_comm_t (s56_E_le_L d (hd.s56_zpowers_le_E h2)))
    rw [hz.eps] at h3
    exact hd.s56_z_ne_one h3
  · rw [h]
    have e : z₀ * a * z₀⁻¹ = a := by rw [hcomm a ha]; group
    rw [e]
    exact ha

theorem Hyp.s56_inv_fiber (h49 : d.Thm49Statement) (hd : d.Hyp) {u u' a : G} (hu : u ∈ d.s56P)
    (hu' : u' ∈ d.s56P) (huu : u * u = 1) (hu'u' : u' * u' = 1) (hε : d.s56Eps u = a)
    (hε' : d.s56Eps u' = a) (ha : a ≠ 1) : u' * u⁻¹ ∈ d.F := by
  have haF : a ∈ d.F := hε ▸ hd.s56_eps_mem_F_of_N h49 (s56_P_le_N d hu)
  have hk : d.s56Eps (u' * u⁻¹) = 1 := by
    rw [hd.s56_eps_mul_P h49 hu' (inv_mem hu), hd.s56_eps_inv_P h49 hu, hε, hε']
    exact hd.s56_F_sq haF
  have hB := hd.s56_mem_B_of_eps_one h49 (mul_mem hu' (inv_mem hu)) hk
  rcases (hd.s56_mem_B_iff).1 hB with hF | hF
  · exact hF
  · exfalso
    apply ha
    have hf : d.t * (u' * u⁻¹) ∈ d.F := hF
    have hu'eq : u' = d.t * (d.t * (u' * u⁻¹)) * u := by
      rw [← mul_assoc, hd.t_mul_self, one_mul]; group
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have hfsq := hd.s56_F_sq hf
    have hut : u * d.t = d.t * a * u := by
      have h1 := hd.s56_conj_t u
      rw [hε] at h1
      calc u * d.t = (u * d.t * u⁻¹) * u := by group
        _ = d.t * a * u := by rw [h1]
    have key := S56.sq_t_mul (t := d.t) (f := d.t * (u' * u⁻¹)) (a := a) (u := u) hd.t_mul_self
      (hd.L_comm_t (s56_F_le_L d hf)) (hd.L_comm_t (s56_F_le_L d haF)) (hd.s56_F_comm haF hf) hfsq
      (((s56_mem_P_iff d).1 hu).2 _ hf) hut huu
    rw [← hu'eq] at key
    rw [← key]
    exact hu'u'

theorem Hyp.s56_z0_conj_t (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    z₀ * d.t * z₀⁻¹ = d.t * d.z := by
  rw [hd.s56_conj_t z₀, hz.eps]

theorem Hyp.s56_t_z0_sq (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) (hsq : z₀ * z₀ = 1) :
    (d.t * z₀) * (d.t * z₀) = d.z := by
  have h : z₀ * d.t = d.t * d.z * z₀ := by
    calc z₀ * d.t = (z₀ * d.t * z₀⁻¹) * z₀ := by group
      _ = d.t * d.z * z₀ := by rw [hd.s56_z0_conj_t hz]
  calc (d.t * z₀) * (d.t * z₀) = d.t * (z₀ * d.t) * z₀ := by group
    _ = d.t * (d.t * d.z * z₀) * z₀ := by rw [h]
    _ = (d.t * d.t) * d.z * (z₀ * z₀) := by group
    _ = d.z := by rw [hd.t_mul_self, hsq]; group

theorem Hyp.s56_z0_conj_comm (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {y : G} (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    z₀ * (y * z₀ * y⁻¹) = (y * z₀ * y⁻¹) * z₀ ∧
      (y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹) = (y * (y * z₀ * y⁻¹) * y⁻¹) * (y * z₀ * y⁻¹) ∧
      (y * (y * z₀ * y⁻¹) * y⁻¹) * z₀ = z₀ * (y * (y * z₀ * y⁻¹) * y⁻¹) := by
  obtain ⟨-, -, hne_z, -, -⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  have hy3'' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  have hc1M : y * z₀ * y⁻¹ ∈ d.M := hd.s56_P11_le_M h49
    (hd.s56_N_conj_P11 h49 hy (hd.s56_z0_mem_P11 h49 hz))
  have hc2M : y * (y * z₀ * y⁻¹) * y⁻¹ ∈ d.M := by
    have h := hd.s56_P11_le_M h49 (hd.s56_N_conj_P11 h49 (mul_mem hy hy)
      (hd.s56_z0_mem_P11 h49 hz))
    have e : y * y * z₀ * (y * y)⁻¹ = y * (y * z₀ * y⁻¹) * y⁻¹ := by group
    rwa [e] at h
  have hK1 := hd.s56_M_comm_z0 h49 hz hc1M
  have hK2 := hd.s56_M_comm_z0 h49 hz hc2M
  have hyc2 : y * (y * (y * z₀ * y⁻¹) * y⁻¹) * y⁻¹ = z₀ :=
    calc y * (y * (y * z₀ * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * z₀ * (y * y * y)⁻¹ := by group
      _ = z₀ := by rw [hy3'']; group
  have hw : z₀ * (y * z₀ * y⁻¹) * z₀⁻¹ * (y * z₀ * y⁻¹)⁻¹ =
      y * ((y * (y * z₀ * y⁻¹) * y⁻¹) * z₀ * (y * (y * z₀ * y⁻¹) * y⁻¹)⁻¹ * z₀⁻¹) * y⁻¹ := by
    calc z₀ * (y * z₀ * y⁻¹) * z₀⁻¹ * (y * z₀ * y⁻¹)⁻¹
        = (y * (y * (y * z₀ * y⁻¹) * y⁻¹) * y⁻¹) * (y * z₀ * y⁻¹) *
          (y * (y * (y * z₀ * y⁻¹) * y⁻¹) * y⁻¹)⁻¹ * (y * z₀ * y⁻¹)⁻¹ := by rw [hyc2]
      _ = _ := by group
  have hw1 : z₀ * (y * z₀ * y⁻¹) * z₀⁻¹ * (y * z₀ * y⁻¹)⁻¹ ∈ zpowers d.z := by
    have := inv_mem hK1
    have e : (y * z₀ * y⁻¹ * z₀ * (y * z₀ * y⁻¹)⁻¹ * z₀⁻¹)⁻¹ =
        z₀ * (y * z₀ * y⁻¹) * z₀⁻¹ * (y * z₀ * y⁻¹)⁻¹ := by group
    rwa [e] at this
  have hw2 : ∃ k ∈ zpowers d.z, z₀ * (y * z₀ * y⁻¹) * z₀⁻¹ * (y * z₀ * y⁻¹)⁻¹ = y * k * y⁻¹ :=
    ⟨_, hK2, hw⟩
  have hA : z₀ * (y * z₀ * y⁻¹) * z₀⁻¹ * (y * z₀ * y⁻¹)⁻¹ = 1 := by
    obtain ⟨k, hk, hwk⟩ := hw2
    rcases hd.s56_mem_zpowers_z hw1 with h1 | h1
    · exact h1
    · exfalso
      rcases hd.s56_mem_zpowers_z hk with h2 | h2
      · rw [h2] at hwk
        have : d.z = 1 := by rw [← h1, hwk]; group
        exact hd.s56_z_ne_one this
      · rw [h2] at hwk
        exact hne_z (by rw [← hwk, h1])
  have hAcomm : z₀ * (y * z₀ * y⁻¹) = (y * z₀ * y⁻¹) * z₀ :=
    calc z₀ * (y * z₀ * y⁻¹) = (z₀ * (y * z₀ * y⁻¹) * z₀⁻¹ * (y * z₀ * y⁻¹)⁻¹) *
        ((y * z₀ * y⁻¹) * z₀) := by group
      _ = (y * z₀ * y⁻¹) * z₀ := by rw [hA, one_mul]
  have hconj : ∀ a b : G, a * b = b * a → (y * a * y⁻¹) * (y * b * y⁻¹) = (y * b * y⁻¹) *
      (y * a * y⁻¹) := fun a b h =>
    calc (y * a * y⁻¹) * (y * b * y⁻¹) = y * (a * b) * y⁻¹ := by group
      _ = y * (b * a) * y⁻¹ := by rw [h]
      _ = (y * b * y⁻¹) * (y * a * y⁻¹) := by group
  have hB := hconj _ _ hAcomm
  have hC := hconj _ _ hB
  rw [hyc2] at hC
  exact ⟨hAcomm, hB, hC⟩

theorem Hyp.s56_z0_conj_facts (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    y * z₀ * y⁻¹ ∈ d.s56P11 ∧ y * (y * z₀ * y⁻¹) * y⁻¹ ∈ d.s56P11 ∧
      (y * z₀ * y⁻¹) * (y * z₀ * y⁻¹) = 1 ∧
      (y * (y * z₀ * y⁻¹) * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹) = 1 ∧
      d.s56Eps (y * z₀ * y⁻¹) = y * d.z * y⁻¹ ∧
      d.s56Eps (y * (y * z₀ * y⁻¹) * y⁻¹) = d.z * (y * d.z * y⁻¹) := by
  obtain ⟨-, -, -, hα, -⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  have hz0P := hd.s56_z0_mem_P h49 hz
  have hc1 : y * z₀ * y⁻¹ ∈ d.s56P11 := hd.s56_N_conj_P11 h49 hy (hd.s56_z0_mem_P11 h49 hz)
  have hc2 : y * (y * z₀ * y⁻¹) * y⁻¹ ∈ d.s56P11 := hd.s56_N_conj_P11 h49 hy hc1
  have hε1 : d.s56Eps (y * z₀ * y⁻¹) = y * d.z * y⁻¹ := by
    rw [hd.s56_eps_conj_N h49 hy hz0P, hz.eps]
  refine ⟨hc1, hc2, ?_, ?_, hε1, ?_⟩
  · calc y * z₀ * y⁻¹ * (y * z₀ * y⁻¹) = y * (z₀ * z₀) * y⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  · calc y * (y * z₀ * y⁻¹) * y⁻¹ * (y * (y * z₀ * y⁻¹) * y⁻¹)
        = y * (y * (z₀ * z₀) * y⁻¹) * y⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  · rw [hd.s56_eps_conj_N h49 hy (s56_P11_le_P d hc1), hε1]
    exact hα

theorem Hyp.s56_R1_le_P11 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hy : y ∈ d.N) : d.s56R1 z₀ y ≤ d.s56P11 :=
  sup_le (fun f hf => hd.s56_B_le_P11 h49 (s56_F_le_B d hf))
    ((Subgroup.closure_le _).2 (by
      intro x hx
      rcases hx with rfl | hx
      · exact hd.s56_z0_mem_P11 h49 hz
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hd.s56_N_conj_P11 h49 hy (hd.s56_z0_mem_P11 h49 hz)))

theorem Hyp.s56_R1_elemAb (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    CFSG.Open.IsElemAbelian 2 (d.s56R1 z₀ y) := by
  obtain ⟨hc1, -, hsq1, -, -, -⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  obtain ⟨hcomm01, -, -⟩ := hd.s56_z0_conj_comm h49 hz hy hy3 hy1
  have hz0P := hd.s56_z0_mem_P h49 hz
  have hc1P := s56_P11_le_P d hc1
  have e : d.s56R1 z₀ y = Subgroup.closure ((d.F : Set G) ∪ {z₀, y * z₀ * y⁻¹}) := by
    rw [s56R1, Subgroup.closure_union, Subgroup.closure_eq]
  rw [e]
  refine S56.isElemAbelian_closure _ ?_ ?_
  ·
    have hF : ∀ a ∈ d.F, ∀ g ∈ d.s56P, a * g = g * a := fun a ha g hg =>
      (((s56_mem_P_iff d).1 hg).2 a ha).symm
    rintro a (ha | rfl | rfl) b (hb | rfl | rfl)
    · exact hd.s56_F_comm ha hb
    · exact hF a ha _ hz0P
    · exact hF a ha _ hc1P
    · exact (hF b hb _ hz0P).symm
    · rfl
    · exact hcomm01
    · exact (hF b hb _ hc1P).symm
    · exact hcomm01.symm
    · rfl
  · rintro a (ha | rfl | rfl)
    · exact hd.s56_F_sq ha
    · exact hsq
    · exact hsq1

theorem s56_F_le_R1 (d : Data G) (z₀ y : G) : d.F ≤ d.s56R1 z₀ y := le_sup_left

theorem s56_z0_mem_R1 (d : Data G) {z₀ y : G} : z₀ ∈ d.s56R1 z₀ y :=
  mem_sup_right (Subgroup.subset_closure (Set.mem_insert _ _))

theorem s56_c1_mem_R1 (d : Data G) {z₀ y : G} : y * z₀ * y⁻¹ ∈ d.s56R1 z₀ y :=
  mem_sup_right (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem Hyp.s56_c12_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    (y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹) * z₀⁻¹ ∈ d.F := by
  obtain ⟨hc1, hc2, hsq1, hsq2, hε1, hε2⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  obtain ⟨-, hcomm12, -⟩ := hd.s56_z0_conj_comm h49 hz hy hy3 hy1
  obtain ⟨hα, hα1, hαz, hα2, -⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  have hz0P := hd.s56_z0_mem_P h49 hz
  have hc1P := s56_P11_le_P d hc1
  have hc2P := s56_P11_le_P d hc2
  have haF : y * d.z * y⁻¹ ∈ d.F := s56_U11_le_F d hα
  have hzF : d.z ∈ d.F := hd.s56_z_mem_F
  generalize y * z₀ * y⁻¹ = c₁ at *
  generalize y * c₁ * y⁻¹ = c₂ at *
  generalize y * d.z * y⁻¹ = a₁ at *
  have huu : (c₁ * c₂) * (c₁ * c₂) = 1 :=
    calc (c₁ * c₂) * (c₁ * c₂) = c₁ * (c₂ * c₁) * c₂ := by group
      _ = c₁ * (c₁ * c₂) * c₂ := by rw [← hcomm12]
      _ = (c₁ * c₁) * (c₂ * c₂) := by group
      _ = 1 := by rw [hsq1, hsq2, one_mul]
  have hε : d.s56Eps (c₁ * c₂) = d.z := by
    rw [hd.s56_eps_mul_P h49 hc1P hc2P, hε1, hε2]
    calc a₁ * (d.z * a₁) = (a₁ * d.z) * a₁ := by group
      _ = (d.z * a₁) * a₁ := by rw [hd.s56_F_comm haF hzF]
      _ = d.z * (a₁ * a₁) := by group
      _ = d.z := by rw [hd.s56_F_sq haF, mul_one]
  exact hd.s56_inv_fiber h49 hz0P (mul_mem hc1P hc2P) hsq huu hz.eps hε hd.s56_z_ne_one

theorem Hyp.s56_c2_mem_R1 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    y * (y * z₀ * y⁻¹) * y⁻¹ ∈ d.s56R1 z₀ y := by
  obtain ⟨-, -, hsq1, -, -, -⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  have hf := hd.s56_c12_z0 h49 hz hsq hy hy3 hy1
  have hc1R : y * z₀ * y⁻¹ ∈ d.s56R1 z₀ y := s56_c1_mem_R1 d
  have hz0R : z₀ ∈ d.s56R1 z₀ y := s56_z0_mem_R1 d
  have hFR : d.F ≤ d.s56R1 z₀ y := s56_F_le_R1 d z₀ y
  have e : y * (y * z₀ * y⁻¹) * y⁻¹ =
      (y * z₀ * y⁻¹) * ((y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹) * z₀⁻¹) * z₀ := by
    generalize y * z₀ * y⁻¹ = c₁ at *
    generalize y * c₁ * y⁻¹ = c₂ at *
    calc c₂ = (c₁ * c₁) * c₂ := by rw [hsq1, one_mul]
      _ = c₁ * (c₁ * c₂ * z₀⁻¹) * z₀ := by group
  rw [e]
  exact mul_mem (mul_mem hc1R (hFR hf)) hz0R

theorem Hyp.s56_t_not_mem_R1 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    d.t ∉ d.s56R1 z₀ y := fun ht => by
  have hel := hd.s56_R1_elemAb h49 hz hsq hy hy3 hy1
  have h1 := hel.2 (d.t * z₀) (mul_mem ht (s56_z0_mem_R1 d))
  rw [pow_two, hd.s56_t_z0_sq hz hsq] at h1
  exact hd.s56_z_ne_one h1

theorem Hyp.s56_R1_eps_surj (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∀ a ∈ d.s56U11, ∃ w ∈ d.s56R1 z₀ y, d.s56Eps w = a := by
  obtain ⟨-, -, -, -, hε1, hε2⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  obtain ⟨-, -, -, -, hall⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  intro a ha
  rcases hall a ha with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, hd.s56_eps_one⟩
  · exact ⟨z₀, s56_z0_mem_R1 d, hz.eps⟩
  · exact ⟨_, s56_c1_mem_R1 d, hε1⟩
  · exact ⟨_, hd.s56_c2_mem_R1 h49 hz hsq hy hy3 hy1, hε2⟩

theorem Hyp.s56_R1_conj_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) {n : G} (hn : n ∈ d.N) :
    n * z₀ * n⁻¹ ∈ d.s56R1 z₀ y := by
  have hz0P := hd.s56_z0_mem_P h49 hz
  have hvP := hd.s56_N_conj_P h49 hn hz0P
  have hvv : (n * z₀ * n⁻¹) * (n * z₀ * n⁻¹) = 1 :=
    calc (n * z₀ * n⁻¹) * (n * z₀ * n⁻¹) = n * (z₀ * z₀) * n⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  have hεv : d.s56Eps (n * z₀ * n⁻¹) = n * d.z * n⁻¹ := by
    rw [hd.s56_eps_conj_N h49 hn hz0P, hz.eps]
  have haU : n * d.z * n⁻¹ ∈ d.s56U11 := hd.s56_N_conj_U11 h49 hn (s56_z_mem_U11 d)
  have han : n * d.z * n⁻¹ ≠ 1 := fun h => hd.s56_z_ne_one
    (mul_left_cancel (mul_right_cancel (h.trans (by group : (1 : G) = n * 1 * n⁻¹))))
  obtain ⟨-, hα1, -, -, hall⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  obtain ⟨hc1, hc2, hsq1, hsq2, hε1, hε2⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
  have hc1P := s56_P11_le_P d hc1
  have hc2P := s56_P11_le_P d hc2
  have hFR := s56_F_le_R1 d z₀ y
  rcases hall _ haU with h | h | h | h
  · exact absurd h han
  · have hf := hd.s56_inv_fiber h49 hz0P hvP hsq hvv hz.eps (hεv.trans h) hd.s56_z_ne_one
    have e : n * z₀ * n⁻¹ = ((n * z₀ * n⁻¹) * z₀⁻¹) * z₀ := by group
    rw [e]
    exact mul_mem (hFR hf) (s56_z0_mem_R1 d)
  · have hf := hd.s56_inv_fiber h49 hc1P hvP hsq1 hvv hε1 (hεv.trans h) hα1
    have e : n * z₀ * n⁻¹ = ((n * z₀ * n⁻¹) * (y * z₀ * y⁻¹)⁻¹) * (y * z₀ * y⁻¹) := by group
    rw [e]
    exact mul_mem (hFR hf) (s56_c1_mem_R1 d)
  · have hne : d.z * (y * d.z * y⁻¹) ≠ 1 := h ▸ han
    have hf := hd.s56_inv_fiber h49 hc2P hvP hsq2 hvv hε2 (hεv.trans h) hne
    have e : n * z₀ * n⁻¹ = ((n * z₀ * n⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹)⁻¹) *
        (y * (y * z₀ * y⁻¹) * y⁻¹) := by group
    rw [e]
    exact mul_mem (hFR hf) (hd.s56_c2_mem_R1 h49 hz hsq hy hy3 hy1)

theorem Hyp.s56_R1_invariant (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) {n : G} (hn : n ∈ d.N)
    {r : G} (hr : r ∈ d.s56R1 z₀ y) : n * r * n⁻¹ ∈ d.s56R1 z₀ y := by
  have hle : d.s56R1 z₀ y ≤ (d.s56R1 z₀ y).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun f hf => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact mem_sup_left (hd.s56_N_conj_F h49 hn hf)
    · intro x hx
      rcases hx with rfl | hx
      · exact hd.s56_R1_conj_z0 h49 hz hsq hy hy3 hy1 hn
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        have h := hd.s56_R1_conj_z0 h49 hz hsq hy hy3 hy1 (mul_mem hn hy)
        have e : n * y * z₀ * (n * y)⁻¹ = n * (y * z₀ * y⁻¹) * n⁻¹ := by group
        rw [e] at h
        exact h
  exact hle hr

theorem Hyp.s56_P11_cases (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) {p : G}
    (hp : p ∈ d.s56P11) :
    p ∈ d.s56R1 z₀ y ∨ ∃ r ∈ d.s56R1 z₀ y, p = d.t * r := by
  obtain ⟨hpP, hpε⟩ := (hd.s56_mem_P11_iff h49).1 hp
  obtain ⟨w, hw, hwε⟩ := hd.s56_R1_eps_surj h49 hz hsq hy hy3 hy1 _ hpε
  have hwP := s56_P11_le_P d (hd.s56_R1_le_P11 h49 hz hy hw)
  have hq : d.s56Eps (p * w⁻¹) = 1 := by
    rw [hd.s56_eps_mul_P h49 hpP (inv_mem hwP), hd.s56_eps_inv_P h49 hwP, hwε]
    exact hd.s56_eps_sq_P h49 hpP
  have hB := hd.s56_mem_B_of_eps_one h49 (mul_mem hpP (inv_mem hwP)) hq
  rcases (hd.s56_mem_B_iff).1 hB with hF | hF
  · left
    have e : p = (p * w⁻¹) * w := by group
    rw [e]
    exact mul_mem (s56_F_le_R1 d z₀ y hF) hw
  · right
    refine ⟨(d.t * (p * w⁻¹)) * w, mul_mem (s56_F_le_R1 d z₀ y hF) hw, ?_⟩
    calc p = (d.t * d.t) * ((p * w⁻¹) * w) := by rw [hd.t_mul_self]; group
      _ = d.t * ((d.t * (p * w⁻¹)) * w) := by group

theorem Hyp.s56_Pe11_eq_R1 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    d.s56Pe11 = d.s56R1 z₀ y := by
  have hinv := fun {n : G} (hn : n ∈ d.N) {r : G} (hr : r ∈ d.s56R1 z₀ y) =>
    hd.s56_R1_invariant h49 hz hsq hy hy3 hy1 hn hr
  have htN : d.t ∈ d.N := s56_B_le_N d (s56_t_mem_B d)
  apply le_antisymm
  ·
    rw [s56Pe11]
    refine Subgroup.commutator_le.2 fun p hp n hn => ?_
    rw [commutatorElement_def]
    rcases hd.s56_P11_cases h49 hz hsq hy hy3 hy1 hp with hr | ⟨r, hr, rfl⟩
    · have e : p * n * p⁻¹ * n⁻¹ = p * (n * p⁻¹ * n⁻¹) := by group
      rw [e]
      exact mul_mem hr (hinv hn (inv_mem hr))
    · have h1 : n * d.t⁻¹ * n⁻¹ = (d.s56Eps n)⁻¹ * d.t⁻¹ := by
        rw [show n * d.t⁻¹ * n⁻¹ = (n * d.t * n⁻¹)⁻¹ by group, hd.s56_conj_t n]
        group
      have hεF := hd.s56_eps_mem_F_of_N h49 hn
      have e : d.t * r * n * (d.t * r)⁻¹ * n⁻¹ =
          d.t * (r * (n * r⁻¹ * n⁻¹) * (d.s56Eps n)⁻¹) * d.t⁻¹ :=
        calc d.t * r * n * (d.t * r)⁻¹ * n⁻¹
            = d.t * r * (n * r⁻¹ * n⁻¹) * (n * d.t⁻¹ * n⁻¹) := by group
          _ = _ := by rw [h1]; group
      rw [e]
      exact hinv htN (mul_mem (mul_mem hr (hinv hn (inv_mem hr)))
        (inv_mem (s56_F_le_R1 d z₀ y hεF)))
  ·
    have hP11t : d.t ∈ d.s56P11 := hd.s56_B_le_P11 h49 (s56_t_mem_B d)
    have hFP : d.F ≤ d.s56Pe11 := fun f hf => by
      obtain ⟨p, hp0, hpt⟩ := hd.s56_P0_transitive h49 hf
      have hft : f * d.t = d.t * f := hd.L_comm_t (s56_F_le_L d hf)
      have hft' : d.t * f⁻¹ = f⁻¹ * d.t :=
        calc d.t * f⁻¹ = f⁻¹ * (f * d.t) * f⁻¹ := by group
          _ = f⁻¹ * (d.t * f) * f⁻¹ := by rw [hft]
          _ = f⁻¹ * d.t := by group
      have h1 : p * d.t⁻¹ * p⁻¹ = f⁻¹ * d.t⁻¹ := by
        rw [show p * d.t⁻¹ * p⁻¹ = (p * d.t * p⁻¹)⁻¹ by group, hpt]
        group
      have e : d.t * p * d.t⁻¹ * p⁻¹ = f⁻¹ :=
        calc d.t * p * d.t⁻¹ * p⁻¹ = d.t * (p * d.t⁻¹ * p⁻¹) := by group
          _ = d.t * (f⁻¹ * d.t⁻¹) := by rw [h1]
          _ = (d.t * f⁻¹) * d.t⁻¹ := by group
          _ = (f⁻¹ * d.t) * d.t⁻¹ := by rw [hft']
          _ = f⁻¹ := by group
      have hmem : ⁅d.t, p⁆ ∈ d.s56Pe11 :=
        Subgroup.commutator_mem_commutator hP11t (s56_P0_le_N d hp0)
      rw [commutatorElement_def, e] at hmem
      simpa using inv_mem hmem
    have hf0 := hd.s56_c12_z0 h49 hz hsq hy hy3 hy1
    obtain ⟨hc1, hc2, hsq1, hsq2, -, -⟩ := hd.s56_z0_conj_facts h49 hz hsq hy hy3 hy1
    have hz0P11 := hd.s56_z0_mem_P11 h49 hz
    have h12 : (y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹) ∈ d.s56Pe11 := by
      have hmem : ⁅y * z₀ * y⁻¹, y⁆ ∈ d.s56Pe11 := Subgroup.commutator_mem_commutator hc1 hy
      have e : ⁅y * z₀ * y⁻¹, y⁆ = (y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹) := by
        rw [commutatorElement_def]
        have : (y * (y * z₀ * y⁻¹) * y⁻¹)⁻¹ = y * (y * z₀ * y⁻¹) * y⁻¹ :=
          inv_eq_of_mul_eq_one_right hsq2
        calc y * z₀ * y⁻¹ * y * (y * z₀ * y⁻¹)⁻¹ * y⁻¹
            = (y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹)⁻¹ := by group
          _ = _ := by rw [this]
      rwa [e] at hmem
    have hz0P : z₀ ∈ d.s56Pe11 := by
      have e : z₀ = ((y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹) * z₀⁻¹)⁻¹ *
          ((y * z₀ * y⁻¹) * (y * (y * z₀ * y⁻¹) * y⁻¹)) := by group
      rw [e]
      exact mul_mem (inv_mem (hFP hf0)) h12
    have hc1P : y * z₀ * y⁻¹ ∈ d.s56Pe11 := by
      have hmem : ⁅z₀, y⁆ ∈ d.s56Pe11 := Subgroup.commutator_mem_commutator hz0P11 hy
      have e : y * z₀ * y⁻¹ = (z₀⁻¹ * ⁅z₀, y⁆)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact inv_mem (mul_mem (inv_mem hz0P) hmem)
    refine sup_le hFP ((Subgroup.closure_le _).2 ?_)
    intro x hx
    rcases hx with rfl | hx
    · exact hz0P
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hc1P

theorem Hyp.s56_R1_card (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Nat.card (d.s56R1 z₀ y) = 2 ^ 7 := by
  have hRP11 := hd.s56_R1_le_P11 h49 hz hy
  have hRP : ∀ r : ↥(d.s56R1 z₀ y), r.1 ∈ d.s56P := fun r => s56_P11_le_P d (hRP11 r.2)
  have hεU : ∀ r : ↥(d.s56R1 z₀ y), d.s56Eps r.1 ∈ d.s56U11 := fun r =>
    ((hd.s56_mem_P11_iff h49).1 (hRP11 r.2)).2
  let φ : ↥(d.s56R1 z₀ y) →* ↥d.s56U11 :=
    MonoidHom.mk' (fun r => ⟨d.s56Eps r.1, hεU r⟩) fun r r' =>
      Subtype.ext (hd.s56_eps_mul_P h49 (hRP r) (hRP r'))
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨u, hu⟩ -
    obtain ⟨w, hw, hwε⟩ := hd.s56_R1_eps_surj h49 hz hsq hy hy3 hy1 u hu
    exact ⟨⟨w, hw⟩, Subtype.ext hwε⟩
  have hker : φ.ker = d.F.subgroupOf (d.s56R1 z₀ y) := by
    ext r
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : d.s56Eps r.1 = 1 := congrArg Subtype.val h
      have hB := hd.s56_mem_B_of_eps_one h49 (hRP r) h1
      rcases (hd.s56_mem_B_iff).1 hB with hF | hF
      · exact hF
      · exfalso
        apply hd.s56_t_not_mem_R1 h49 hz hsq hy hy3 hy1
        have e : d.t = (d.t * r.1) * r.1⁻¹ := by group
        rw [e]
        exact mul_mem (s56_F_le_R1 d z₀ y hF) (inv_mem r.2)
    · intro h
      apply Subtype.ext
      show d.s56Eps r.1 = 1
      exact hd.s56_eps_eq_one_of_mem_B (s56_F_le_B d h)
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, Subgroup.card_top, hker,
    Nat.card_congr (subgroupOfEquivOfLe (s56_F_le_R1 d z₀ y)).toEquiv, hd.B_facts.1,
    s56_card_U11] at h
  omega

theorem Hyp.s56_P11_structure (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G}
    (hz : d.S56Z0 z₀) (hsq : z₀ * z₀ = 1) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    d.B ≤ d.s56P11 ∧ d.F ≤ d.s56Pe11 ∧ d.s56P11 = d.s56Pe11 ⊔ zpowers d.t ∧
      d.s56Pe11 = d.F ⊔ Subgroup.closure ({z₀, y * z₀ * y⁻¹} : Set G) ∧
      CFSG.Open.IsElemAbelian 2 d.s56Pe11 ∧ Nat.card d.s56Pe11 = 2 ^ 7 ∧ d.t ∉ d.s56Pe11 := by
  have hE := hd.s56_Pe11_eq_R1 h49 hz hsq hy hy3 hy1
  refine ⟨hd.s56_B_le_P11 h49, ?_, ?_, hE, ?_, ?_, ?_⟩
  · rw [hE]; exact s56_F_le_R1 d z₀ y
  · apply le_antisymm
    · intro p hp
      rcases hd.s56_P11_cases h49 hz hsq hy hy3 hy1 hp with hr | ⟨r, hr, rfl⟩
      · exact mem_sup_left (hE ▸ hr)
      · exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (hE ▸ hr))
    · exact sup_le (hE ▸ hd.s56_R1_le_P11 h49 hz hy)
        (zpowers_le.2 (hd.s56_B_le_P11 h49 (s56_t_mem_B d)))
  · rw [hE]; exact hd.s56_R1_elemAb h49 hz hsq hy hy3 hy1
  · rw [hE]; exact hd.s56_R1_card h49 hz hsq hy hy3 hy1
  · rw [hE]; exact hd.s56_t_not_mem_R1 h49 hz hsq hy hy3 hy1

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
