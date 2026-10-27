module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnQ
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermCountBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermFacts3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup Equiv CFSG CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement
open CFSG.GorensteinWalter

section GenericC

variable {m : ℕ}

theorem commute_zpow2' {G : Type*} [Group G] {g p : G} (h : Commute g p) (a : ZMod 2) :
    Commute g (zpow2 p a) := by
  rcases zmod2_cases a with rfl | rfl
  · rw [zpow2_zero]; exact Commute.one_right g
  · rw [zpow2_one]; exact h

theorem commute_pairp {G : Type*} [Group G] {g p q : G} (hp : Commute g p) (hq : Commute g q) (c : F4c) :
    Commute g (pairp p q c) :=
  (commute_zpow2' hp c.a).mul_right (commute_zpow2' hq c.b)

theorem zpow2_mem' {G : Type*} [Group G] {S : Subgroup G} {g : G} (hg : g ∈ S) (a : ZMod 2) :
    zpow2 g a ∈ S := by
  rcases zmod2_cases a with rfl | rfl
  · rw [zpow2_zero]; exact S.one_mem
  · rw [zpow2_one]; exact hg

theorem Sfun_mem (S : Subgroup (Perm (Fin (m + 1)))) (h1 : ub m ∈ S) (h2 : vb m ∈ S) (h3 : xb1 m ∈ S)
    (h4 : xb2 m ∈ S) (h5 : tb m ∈ S) (y : UT3 F4c) : Sfun m y ∈ S :=
  S.mul_mem (S.mul_mem (S.mul_mem (zpow2_mem' h3 _) (zpow2_mem' h4 _))
    (S.mul_mem (zpow2_mem' h1 _) (zpow2_mem' h2 _))) (zpow2_mem' h5 _)

theorem sign_of_pow_three' {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} (h : σ ^ 3 = 1) :
    Perm.sign σ = 1 := by
  have h' : Perm.sign σ ^ 3 = 1 := by rw [← map_pow, h]; simp
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h'
    exact absurd h' (by decide)

theorem mem_zpowers_cube {G : Type*} [Group G] {o y : G} (h : o ^ 3 = 1) (hy : y ∈ zpowers o) :
    y = 1 ∨ y = o ∨ y = o * o := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_emod' k h]
  have : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases this with h0 | h1 | h2
  · left; rw [h0]; simp
  · right; left; rw [h1]; simp
  · right; right; rw [h2]; simp [pow_two]

theorem mem_zpowers_involution {G : Type*} [Group G] {v y : G} (h : v * v = 1) (hy : y ∈ zpowers v) :
    y = 1 ∨ y = v := by
  have h2 : v ^ 2 = 1 := by rw [pow_two]; exact h
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_emod' k h2]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

theorem mem_normalizer_of_invol {G : Type*} [Group G] {S : Subgroup G} {v : G} (hv2 : v * v = 1)
    (h : ∀ s ∈ S, v * s * v⁻¹ ∈ S) : v ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h g hg, fun hg => ?_⟩
  have := h _ hg
  have e : v * (v * g * v⁻¹) * v⁻¹ = g := by
    have hinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    rw [hinv]
    calc v * (v * g * v) * v = (v * v) * g * (v * v) := by simp only [mul_assoc]
      _ = g := by rw [hv2]; simp
  rwa [e] at this

end GenericC

section Cfg

variable {H : Type} [Group H] {K : Subgroup H} {m : ℕ}

structure Cfg (R : PermRep K (m + 1)) (z : H) where
  L : Lifts R
  hz : R.KerData z
  h7 : 7 ≤ m
  h10 : m ≤ 10

namespace Cfg

variable {R : PermRep K (m + 1)} {z : H} (Γ : Cfg R z)

include Γ

@[expose] def Q : Subgroup H := (Γ.L.psi Γ.hz Γ.h7 Γ.h10).range

@[expose] def X : Subgroup H := zpowers Γ.L.c

@[expose] def J : Subgroup H := Γ.Q ⊔ Γ.X

@[expose] def t : H := Γ.L.t

@[expose] def C : Subgroup H := K ⊓ centralizer ({Γ.t} : Set H)

theorem Q_card : Nat.card Γ.Q = 64 := Γ.L.card_psi_range Γ.hz Γ.h7 Γ.h10

theorem z_mem_Q : z ∈ Γ.Q := Γ.L.z_mem_range Γ.hz Γ.h7 Γ.h10

theorem mem_Q_of_rho {y : H} {x : UT3 F4c} (h : R.ρ y = Sfun m x) : y ∈ Γ.Q :=
  Γ.L.mem_range_of_rho Γ.hz Γ.h7 Γ.h10 y x h

theorem rho_of_mem_Q {y : H} (hy : y ∈ Γ.Q) : ∃ x : UT3 F4c, R.ρ y = Sfun m x := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, Γ.L.rho_psi Γ.hz Γ.h7 Γ.h10 x⟩

theorem Q_le_K : Γ.Q ≤ K := by
  rintro _ ⟨x, rfl⟩
  exact Γ.L.psi_mem_K Γ.hz Γ.h7 Γ.h10 x

theorem t_comm_Q {y : H} (hy : y ∈ Γ.Q) : Γ.t * y = y * Γ.t := by
  obtain ⟨x, rfl⟩ := hy
  rw [Γ.L.psi_apply]
  have hz := Γ.hz
  have h7 := Γ.h7
  have h10 := Γ.h10
  have ht : Commute Γ.t Γ.t := Commute.refl _
  have htz : Commute Γ.t z := hz.central Γ.t
  have c1 : Commute Γ.t (pairp Γ.L.x1 Γ.L.x2 x.b) :=
    commute_pairp (Γ.L.comm_tx1 hz h7 h10) (Γ.L.comm_tx2 hz h7 h10) x.b
  have c2 : Commute Γ.t (pairp Γ.L.u Γ.L.v x.a) :=
    commute_pairp (Γ.L.comm_tu hz h7 h10) (Γ.L.comm_tv hz h7 h10) x.a
  have c3 : Commute Γ.t (pairp Γ.L.t z x.c) := commute_pairp ht htz x.c
  exact ((c1.mul_right c2).mul_right c3).eq

theorem c_mem_K : Γ.L.c ∈ K :=
  R.mem_K_of_sign _ (by rw [Γ.L.hc]; exact sign_c3 m Γ.h7 Γ.h10)

theorem c_comm_t : Γ.L.c * Γ.t = Γ.t * Γ.L.c := by
  have h := commute_of_pow_three Γ.hz Γ.L.hc3
    (u := Γ.L.t) (by rw [Γ.L.hc, Γ.L.rho_t Γ.h7 Γ.h10]; exact (comm_c3_tb m Γ.h7 Γ.h10).symm)
  exact h.symm

theorem c_ne_one : Γ.L.c ≠ 1 := by
  intro h
  have := Γ.L.hc
  rw [h, map_one] at this
  exact c3_ne_one m Γ.h7 Γ.h10 this.symm

theorem X_card : Nat.card Γ.X = 3 := by
  rw [X, Nat.card_zpowers, orderOf_eq_prime Γ.L.hc3 Γ.c_ne_one]

theorem c_conj_Q {y : H} (hy : y ∈ Γ.Q) : Γ.L.c * y * Γ.L.c⁻¹ ∈ Γ.Q := by
  obtain ⟨x, hx⟩ := Γ.rho_of_mem_Q hy
  obtain ⟨x', hx'⟩ := Sfun_conj_c3 m Γ.h7 Γ.h10 x
  refine Γ.mem_Q_of_rho (x := x') ?_
  rw [map_mul, map_mul, map_inv, Γ.L.hc, hx, hx']

theorem cinv_conj_Q {y : H} (hy : y ∈ Γ.Q) : Γ.L.c⁻¹ * y * Γ.L.c ∈ Γ.Q := by
  have hc3 : Γ.L.c⁻¹ = Γ.L.c * Γ.L.c :=
    inv_eq_of_mul_eq_one_right ((pow_three Γ.L.c).symm.trans Γ.L.hc3)
  have h2 := Γ.c_conj_Q (Γ.c_conj_Q hy)
  have e : Γ.L.c⁻¹ * y * Γ.L.c = Γ.L.c * (Γ.L.c * y * Γ.L.c⁻¹) * Γ.L.c⁻¹ := by
    calc Γ.L.c⁻¹ * y * Γ.L.c = (Γ.L.c * Γ.L.c) * y * (Γ.L.c * Γ.L.c)⁻¹ := by
          rw [← hc3]; group
      _ = _ := by group
  rw [e]
  exact h2

theorem X_le_norm_Q : Γ.X ≤ normalizer (Γ.Q : Set H) := by
  rw [X, zpowers_le]
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact Γ.c_conj_Q hh
  · intro hh
    have := Γ.cinv_conj_Q hh
    have e : Γ.L.c⁻¹ * (Γ.L.c * h * Γ.L.c⁻¹) * Γ.L.c = h := by group
    rwa [e] at this

theorem Q_disj_X : Disjoint Γ.Q Γ.X := by
  apply disjoint_of_coprime_natCard
  rw [Γ.Q_card, Γ.X_card]
  decide

theorem J_card : Nat.card Γ.J = 192 := by
  rw [J, card_sup_eq_mul_of_disjoint_of_le_normalizer Γ.Q Γ.X Γ.X_le_norm_Q Γ.Q_disj_X, Γ.Q_card,
    Γ.X_card]

theorem Q_normal_in_J : (Γ.Q.subgroupOf Γ.J).Normal := by
  show (Γ.Q.subgroupOf (Γ.Q ⊔ Γ.X)).Normal
  rw [normal_subgroupOf_iff_le_normalizer (le_sup_left : Γ.Q ≤ Γ.Q ⊔ Γ.X)]
  exact sup_le (le_normalizer) Γ.X_le_norm_Q

theorem Q_le_C : Γ.Q ≤ Γ.C := by
  intro y hy
  exact mem_inf.mpr ⟨Γ.Q_le_K hy, mem_centralizer_singleton_iff.mpr (Γ.t_comm_Q hy).symm⟩

theorem X_le_C : Γ.X ≤ Γ.C := by
  rw [X, zpowers_le]
  exact mem_inf.mpr ⟨Γ.c_mem_K, mem_centralizer_singleton_iff.mpr Γ.c_comm_t⟩

theorem J_le_C : Γ.J ≤ Γ.C := sup_le Γ.Q_le_C Γ.X_le_C

theorem comm_QX_le : ⁅Γ.Q, Γ.X⁆ ≤ Γ.Q := by
  rw [commutator_le]
  intro q hq x hx
  have hn := Γ.X_le_norm_Q hx
  rw [mem_normalizer_iff] at hn
  have : x * q⁻¹ * x⁻¹ ∈ Γ.Q := (hn _).mp (Γ.Q.inv_mem hq)
  have e : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact Γ.Q.mul_mem hq this

theorem Q_le_comm_QX : Γ.Q ≤ ⁅Γ.Q, Γ.X⁆ := by
  have hz := Γ.hz
  have h7 := Γ.h7
  have h10 := Γ.h10
  set M := ⁅Γ.Q, Γ.X⁆ with hM
  have hX : Γ.L.c ∈ Γ.X := mem_zpowers _
  have hgen : ∀ x : UT3 F4c, ⁅Γ.L.psi hz h7 h10 x, Γ.L.c⁆ ∈ M := fun x =>
    Subgroup.commutator_mem_commutator ⟨x, rfl⟩ hX
  have hrho : ∀ x : UT3 F4c, R.ρ ⁅Γ.L.psi hz h7 h10 x, Γ.L.c⁆ = ⁅Sh m h7 h10 x, c3 m⁆ := by
    intro x
    simp only [commutatorElement_def, map_mul, map_inv, Γ.L.rho_psi hz h7 h10, Γ.L.hc]
    rfl
  have hle : Subgroup.closure (Set.range fun x : UT3 F4c => ⁅Sh m h7 h10 x, c3 m⁆) ≤ M.map R.ρ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hgen x, hrho x⟩
  obtain ⟨g1, g2, g3, g4, g5⟩ := Sh_comm_gen m h7 h10
  have hall : ∀ y : UT3 F4c, Sfun m y ∈ M.map R.ρ := fun y =>
    Sfun_mem (M.map R.ρ) (hle g1) (hle g2) (hle g3) (hle g4) (hle g5) y
  have hzM : z ∈ M := by
    obtain ⟨y0, hy0⟩ := ub_xb2_mem_range m h7 h10
    obtain ⟨w, hwM, hw⟩ := hall y0
    rw [hy0] at hw
    have hww : w * w = z := hz.sq_double (by omega) (by rw [hw]; exact ct_ub_xb2 m h7 h10)
    rw [← hww]
    exact M.mul_mem hwM hwM
  intro y hy
  obtain ⟨x, hx⟩ := Γ.rho_of_mem_Q hy
  obtain ⟨w, hwM, hw⟩ := hall x
  have hker : R.ρ (w⁻¹ * y) = 1 := by rw [map_mul, map_inv, hw, hx, inv_mul_cancel]
  rcases hz.ker _ hker with h1 | h1
  · have : y = w := by
      calc y = w * (w⁻¹ * y) := by group
        _ = w := by rw [h1, mul_one]
    rw [this]; exact hwM
  · have : y = w * z := by
      calc y = w * (w⁻¹ * y) := by group
        _ = w * z := by rw [h1]
    rw [this]; exact M.mul_mem hwM hzM

theorem comm_QX : ⁅Γ.Q, Γ.X⁆ = Γ.Q := le_antisymm Γ.comm_QX_le Γ.Q_le_comm_QX

theorem orderOf_z : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact Γ.hz.sq) Γ.hz.ne_one

theorem sg_not_in_range : ∀ y ∈ Γ.C, R.ρ y ≠ sg m := by
  intro y hy hρ
  have hz := Γ.hz
  have hker : R.ρ (Γ.L.g⁻¹ * y) = 1 := by rw [map_mul, map_inv, hρ, Γ.L.hg, inv_mul_cancel]
  have hyt : y * Γ.t = Γ.t * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
  have hgt := Γ.L.conj_g_t hz Γ.h7 Γ.h10
  have key : y * Γ.t * y⁻¹ = Γ.t * z := by
    rcases hz.ker _ hker with h1 | h1
    · have : y = Γ.L.g := by
        calc y = Γ.L.g * (Γ.L.g⁻¹ * y) := by group
          _ = Γ.L.g := by rw [h1, mul_one]
      rw [this]; exact hgt
    · have : y = Γ.L.g * z := by
        calc y = Γ.L.g * (Γ.L.g⁻¹ * y) := by group
          _ = Γ.L.g * z := by rw [h1]
      rw [this]
      calc Γ.L.g * z * Γ.t * (Γ.L.g * z)⁻¹ = Γ.L.g * (z * Γ.t) * z⁻¹ * Γ.L.g⁻¹ := by group
        _ = Γ.L.g * (Γ.t * z) * z⁻¹ * Γ.L.g⁻¹ := by rw [← hz.central Γ.t]
        _ = Γ.L.g * Γ.t * Γ.L.g⁻¹ := by group
        _ = Γ.t * z := hgt
  have h2 : y * Γ.t * y⁻¹ = Γ.t := by rw [hyt]; group
  rw [h2] at key
  have : z = 1 := by
    have := congrArg (fun w => Γ.t⁻¹ * w) key
    simpa using this.symm
  exact hz.ne_one this

theorem rho_t' : R.ρ Γ.t = tb m := Γ.L.rho_t Γ.h7 Γ.h10

theorem C_card_le [Finite H] : Nat.card Γ.C ≤ 192 * (m - 7).factorial := by
  have hz := Γ.hz
  have h7 := Γ.h7
  have h10 := Γ.h10
  let f : ↥Γ.C →* Perm (Fin (m + 1)) := R.ρ.comp Γ.C.subtype
  let Cn : Subgroup (Perm (Fin (m + 1))) :=
    centralizer ({tb m} : Set (Perm (Fin (m + 1)))) ⊓ alternatingGroup (Fin (m + 1))
  have hCn : Nat.card Cn = 192 * (m - 7).factorial := card_centralizer_tb_alt m h7 h10
  have hle : f.range ≤ Cn := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have hyK : y ∈ K := (mem_inf.mp hy).1
    have hyt : y * Γ.t = Γ.t * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    refine mem_inf.mpr ⟨?_, Perm.mem_alternatingGroup.mpr (R.sign_of_mem_K y hyK)⟩
    rw [mem_centralizer_singleton_iff]
    show R.ρ y * tb m = tb m * R.ρ y
    have := congrArg R.ρ hyt
    rw [map_mul, map_mul, Γ.rho_t'] at this
    exact this
  have hsgC : sg m ∈ Cn := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (comm_sg_tb m h7 h10),
    Perm.mem_alternatingGroup.mpr (PermRep.sign_eq_one_of_cycleType_two_two (ct_sg m h7 h10))⟩
  have hsg : sg m ∉ f.range := by
    rintro ⟨⟨y, hy⟩, hy'⟩
    exact Γ.sg_not_in_range y hy hy'
  have hlt : f.range < Cn := lt_of_le_of_ne hle (fun h => hsg (h ▸ hsgC))
  have hcard_lt : Nat.card f.range < Nat.card Cn := Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card Cn := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra h
    have h' : k ≤ 1 := by omega
    interval_cases k
    · rw [hk] at hpos; simp at hpos
    · rw [hk] at hcard_lt; omega
  have hker : Nat.card f.ker ≤ 2 := by
    have hle2 : f.ker.map Γ.C.subtype ≤ zpowers z := by
      rintro _ ⟨⟨y, hy⟩, hyk, rfl⟩
      have hρ : R.ρ y = 1 := hyk
      show y ∈ zpowers z
      rcases hz.ker y hρ with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers z
    have h1 := Subgroup.card_le_of_le hle2
    rw [Subgroup.card_map_of_injective Γ.C.subtype_injective, Nat.card_zpowers, Γ.orderOf_z] at h1
    exact h1
  have hmul := Subgroup.card_ker_mul_card_range f
  calc Nat.card Γ.C = Nat.card f.ker * Nat.card f.range := hmul.symm
    _ ≤ 2 * Nat.card f.range := Nat.mul_le_mul_right _ hker
    _ ≤ Nat.card Cn := by rw [hk]; nlinarith
    _ = 192 * (m - 7).factorial := hCn

theorem rho_J_mem : ∀ y ∈ Γ.J, R.ρ y ∈ Subgroup.closure
    ({ub m, vb m, xb1 m, xb2 m, tb m, c3 m} : Set (Perm (Fin (m + 1)))) := by
  have hQ : Γ.Q ≤ (Subgroup.closure
      ({ub m, vb m, xb1 m, xb2 m, tb m, c3 m} : Set (Perm (Fin (m + 1))))).comap R.ρ := by
    intro y hy
    obtain ⟨x, hx⟩ := Γ.rho_of_mem_Q hy
    refine Subgroup.mem_comap.mpr ?_
    rw [hx]
    exact Sfun_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) x
  have hX : Γ.X ≤ (Subgroup.closure
      ({ub m, vb m, xb1 m, xb2 m, tb m, c3 m} : Set (Perm (Fin (m + 1))))).comap R.ρ := by
    rw [X, zpowers_le]
    refine Subgroup.mem_comap.mpr ?_
    rw [Γ.L.hc]
    exact Subgroup.subset_closure (by simp)
  intro y hy
  exact (sup_le hQ hX : Γ.J ≤ _) hy

theorem rho_J_fix {y : H} (hy : y ∈ Γ.J) (i : Fin (m + 1)) (hi : 8 ≤ i.val) : R.ρ y i = i :=
  fix_of_mem_closure m Γ.h7 Γ.h10 i hi _ (Γ.rho_J_mem y hy)

theorem exists_vh (h9 : 9 ≤ m) : ∃ v : H, R.ρ v = vp m ∧ v * v = 1 := by
  obtain ⟨v, hv⟩ := R.lift_even
    (PermRep.sign_eq_one_of_cycleType_two_two_two_two (ct_vp m Γ.h7 Γ.h10 h9))
  exact ⟨v, hv, PermRep.sq_four (R := R) (by omega) (by rw [hv]; exact ct_vp m Γ.h7 Γ.h10 h9)⟩

theorem exists_oh (hm : m = 10) : ∃ o : H, R.ρ o = o3 m ∧ o ^ 3 = 1 :=
  exists_lift_pow_three Γ.hz (o3_cube m Γ.h7 Γ.h10 hm) (sign_of_pow_three' (o3_cube m Γ.h7 Γ.h10 hm))

section VFacts

variable {v : H} (hv : R.ρ v = vp m) (hv2 : v * v = 1) (h9 : 9 ≤ m)

include hv h9

theorem v_mem_K : v ∈ K :=
  R.mem_K_of_sign v (by
    rw [hv]; exact PermRep.sign_eq_one_of_cycleType_two_two_two_two (ct_vp m Γ.h7 Γ.h10 h9))

theorem v_ne_one : v ≠ 1 := by
  intro h
  rw [h, map_one] at hv
  have := vp_moves m Γ.h7 Γ.h10 h9
  rw [← hv] at this
  exact this rfl

theorem v_conj_Q {y : H} (hy : y ∈ Γ.Q) : v * y * v⁻¹ ∈ Γ.Q := by
  obtain ⟨x, hx⟩ := Γ.rho_of_mem_Q hy
  obtain ⟨x', hx'⟩ := Sfun_conj_vp m Γ.h7 Γ.h10 h9 x
  refine Γ.mem_Q_of_rho (x := x') ?_
  rw [map_mul, map_mul, map_inv, hv, hx, hx']

theorem v_conj_c : v * Γ.L.c * v⁻¹ ∈ Γ.J := by
  have h := conj_mem_ker Γ.hz (g := v) (u := Γ.L.c) (v := Γ.L.c⁻¹) (by
    rw [map_mul, map_mul, map_inv, map_inv, hv, Γ.L.hc]
    exact vp_c3 m Γ.h7 Γ.h10 h9)
  have hcX : Γ.L.c⁻¹ ∈ Γ.J := Subgroup.mem_sup_right (inv_mem (mem_zpowers Γ.L.c))
  rcases h with h | h
  · rw [h]; exact hcX
  · rw [h]; exact Γ.J.mul_mem hcX (Subgroup.mem_sup_left Γ.z_mem_Q)

theorem v_norm_J : ∀ j ∈ Γ.J, v * j * v⁻¹ ∈ Γ.J := by
  let φ : H →* H := (MulAut.conj v).toMonoidHom
  have hQ : Γ.Q.map φ ≤ Γ.J := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_sup_left (Γ.v_conj_Q hv h9 hy)
  have hX : Γ.X.map φ ≤ Γ.J := by
    rw [X, MonoidHom.map_zpowers, zpowers_le]
    exact Γ.v_conj_c hv h9
  have hJ : Γ.J.map φ ≤ Γ.J := by
    rw [J, Subgroup.map_sup]
    exact sup_le hQ hX
  intro j hj
  exact hJ ⟨j, hj, rfl⟩

theorem v_not_mem_J : v ∉ Γ.J := by
  intro hvJ
  have h1 := Γ.rho_J_fix hvJ (Fin.ofNat (m + 1) 8) (by
    have h10 := Γ.h10
    interval_cases m <;> first | omega | decide)
  rw [hv] at h1
  exact vp_moves m Γ.h7 Γ.h10 h9 h1

include hv2

theorem orderOf_v : orderOf v = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hv2) (Γ.v_ne_one hv h9)

theorem v_comm_t : v * Γ.t = Γ.t * v :=
  commute_of_squares_one Γ.hz (by rw [hv]; exact sq_vp m Γ.h7 Γ.h10 h9)
    (by rw [Γ.rho_t']; exact sq_tb m Γ.h7 Γ.h10)
    (by rw [hv, Γ.rho_t']; exact comm_vp_tb m Γ.h7 Γ.h10 h9) hv2 (Γ.L.sq_t Γ.h7 Γ.h10)
    (PermRep.sq_four (R := R) (by have := Γ.h7; omega)
      (by rw [map_mul, hv, Γ.rho_t']; exact ct_vp_tb m Γ.h7 Γ.h10 h9))

theorem v_le_C : v ∈ Γ.C :=
  mem_inf.mpr ⟨Γ.v_mem_K hv h9, mem_centralizer_singleton_iff.mpr (Γ.v_comm_t hv hv2 h9)⟩

end VFacts

section OFacts

variable {o : H}

theorem o_mem_K (ho : R.ρ o = o3 m) (hm : m = 10) : o ∈ K :=
  R.mem_K_of_sign o (by rw [ho]; exact sign_of_pow_three' (o3_cube m Γ.h7 Γ.h10 hm))

theorem o_ne_one (ho : R.ρ o = o3 m) (hm : m = 10) : o ≠ 1 := by
  intro h
  rw [h, map_one] at ho
  exact o3_ne_one m Γ.h7 Γ.h10 hm ho.symm

theorem orderOf_o (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) : orderOf o = 3 :=
  orderOf_eq_prime ho3 (Γ.o_ne_one ho hm)

theorem o_comm_of (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) {u : H} (h : R.ρ u * o3 m = o3 m * R.ρ u) :
    u * o = o * u :=
  commute_of_pow_three Γ.hz ho3 (by rw [ho]; exact h)

theorem o_comm_Q (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) {y : H} (hy : y ∈ Γ.Q) :
    y * o = o * y := by
  obtain ⟨x, rfl⟩ := hy
  rw [Γ.L.psi_apply]
  have hz := Γ.hz
  have h7 := Γ.h7
  have h10 := Γ.h10
  have cu : Commute o Γ.L.u :=
    (Γ.o_comm_of ho ho3 (by rw [Γ.L.hu]; exact (comm_o3_ub m h7 h10 hm).symm)).symm
  have cv : Commute o Γ.L.v :=
    (Γ.o_comm_of ho ho3 (by rw [Γ.L.hv]; exact (comm_o3_vb m h7 h10 hm).symm)).symm
  have c1 : Commute o Γ.L.x1 :=
    (Γ.o_comm_of ho ho3 (by rw [Γ.L.hx1]; exact (comm_o3_xb1 m h7 h10 hm).symm)).symm
  have c2 : Commute o Γ.L.x2 :=
    (Γ.o_comm_of ho ho3 (by rw [Γ.L.hx2]; exact (comm_o3_xb2 m h7 h10 hm).symm)).symm
  have ct : Commute o Γ.L.t :=
    (Γ.o_comm_of ho ho3 (by rw [Γ.L.rho_t h7 h10]; exact (comm_o3_tb m h7 h10 hm).symm)).symm
  have cz : Commute o z := hz.central o
  exact (((commute_pairp c1 c2 x.b).mul_right (commute_pairp cu cv x.a)).mul_right
    (commute_pairp ct cz x.c)).eq.symm

theorem o_comm_c (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) :
    Γ.L.c * o = o * Γ.L.c :=
  Γ.o_comm_of ho ho3 (by rw [Γ.L.hc]; exact (comm_o3_c3 m Γ.h7 Γ.h10 hm).symm)

theorem o_comm_J (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) :
    ∀ j ∈ Γ.J, j * o = o * j := by
  have hQ : Γ.Q ≤ centralizer ({o} : Set H) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (Γ.o_comm_Q ho ho3 hm hy)
  have hX : Γ.X ≤ centralizer ({o} : Set H) := by
    rw [X, zpowers_le]
    exact mem_centralizer_singleton_iff.mpr (Γ.o_comm_c ho ho3 hm)
  intro j hj
  exact mem_centralizer_singleton_iff.mp ((sup_le hQ hX : Γ.J ≤ _) hj)

theorem o_comm_t (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) : o * Γ.t = Γ.t * o :=
  (Γ.o_comm_of ho ho3 (by rw [Γ.rho_t']; exact (comm_o3_tb m Γ.h7 Γ.h10 hm).symm)).symm

theorem o_le_C (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) : o ∈ Γ.C :=
  mem_inf.mpr ⟨Γ.o_mem_K ho hm, mem_centralizer_singleton_iff.mpr (Γ.o_comm_t ho ho3 hm)⟩

theorem J_inf_zpowers_o (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) :
    Γ.J ⊓ zpowers o = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyJ, hyO⟩ := mem_inf.mp hy
  have hfix := fun w (hw : w ∈ Γ.J) => Γ.rho_J_fix hw (Fin.ofNat (m + 1) 8) (by
    subst hm; decide)
  have hmov1 : o3 m (Fin.ofNat (m + 1) 8) ≠ Fin.ofNat (m + 1) 8 := o3_moves m Γ.h7 Γ.h10 hm
  have hmov2 : (o3 m * o3 m) (Fin.ofNat (m + 1) 8) ≠ Fin.ofNat (m + 1) 8 := by
    subst hm; decide
  rcases mem_zpowers_cube ho3 hyO with h | h | h
  · rw [h]; exact one_mem _
  · exfalso
    have := hfix y hyJ
    rw [h, ho] at this
    exact hmov1 this
  · exfalso
    have := hfix y hyJ
    rw [h, map_mul, ho] at this
    exact hmov2 this

end OFacts

theorem v_conj_o {v o : H} (hv : R.ρ v = vp m) (ho : R.ρ o = o3 m) (ho3 : o ^ 3 = 1) (hm : m = 10) :
    v * o * v⁻¹ = o⁻¹ := by
  have h9 : 9 ≤ m := by omega
  have h := conj_mem_ker Γ.hz (g := v) (u := o) (v := o⁻¹) (by
    rw [map_mul, map_mul, map_inv, map_inv, hv, ho]
    exact vp_o3 m Γ.h7 Γ.h10 hm)
  rcases h with h | h
  · exact h
  · exfalso
    have h3 : (v * o * v⁻¹) ^ 3 = 1 := by
      calc (v * o * v⁻¹) ^ 3 = v * o ^ 3 * v⁻¹ := conj_pow
        _ = 1 := by rw [ho3]; group
    rw [h] at h3
    have hcomm : Commute o⁻¹ z := Γ.hz.central o⁻¹
    rw [hcomm.mul_pow, inv_pow, ho3, inv_one, one_mul] at h3
    have hz3 : z ^ 3 = z := by
      calc z ^ 3 = z * (z * z) := pow_three z
        _ = z := by rw [Γ.hz.sq, mul_one]
    rw [hz3] at h3
    exact Γ.hz.ne_one h3

structure Decomp where
  O : Subgroup H
  v : H
  O_card : Nat.card O = if m = 10 then 3 else 1
  O_comm : ∀ j ∈ Γ.J, ∀ o ∈ O, j * o = o * j
  O_disj : Γ.J ⊓ O = ⊥
  O_le_C : O ≤ Γ.C
  O_odd : ∀ o ∈ O, Odd (orderOf o)
  v_sq : v * v = 1
  v_le_C : v ∈ Γ.C
  v_norm_J : ∀ j ∈ Γ.J, v * j * v⁻¹ ∈ Γ.J
  v_norm_O : ∀ o ∈ O, v * o * v⁻¹ ∈ O
  C_eq : Γ.C = (Γ.J ⊔ O) ⊔ zpowers v
  v_not_mem : 9 ≤ m → v ∉ Γ.J ⊔ O
  v_rho : 9 ≤ m → R.ρ v = vp m

theorem decomp_small (hm : m ≤ 8) [Finite H] : Nonempty (Decomp Γ) := by
  have h1 : Γ.C = (Γ.J ⊔ ⊥) ⊔ zpowers (1 : H) := by
    have hle := Γ.J_le_C
    have hcard : Nat.card Γ.C ≤ Nat.card Γ.J := by
      rw [Γ.J_card]
      have hle2 := Γ.C_card_le
      have h7 := Γ.h7
      have hf : (m - 7).factorial = 1 := by interval_cases m <;> simp
      rw [hf] at hle2
      omega
    have := Subgroup.eq_of_le_of_card_ge hle hcard
    simp [this]
  refine ⟨⟨⊥, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h1, ?_, ?_⟩⟩
  · have : m ≠ 10 := by omega
    simp [this]
  · intro j _ o ho; rw [(mem_bot.mp ho)]; simp
  · simp
  · exact bot_le
  · intro o ho; rw [mem_bot.mp ho]; simp
  · simp
  · exact one_mem _
  · intro j hj; simpa using hj
  · intro o ho; rw [mem_bot.mp ho]; simp
  · intro h; omega
  · intro h; omega

theorem decomp_nine (hm : m = 9) [Finite H] : Nonempty (Decomp Γ) := by
  have h9 : 9 ≤ m := by omega
  obtain ⟨v, hv, hv2⟩ := Γ.exists_vh h9
  have hnorm : zpowers v ≤ normalizer (Γ.J : Set H) := by
    rw [zpowers_le]
    exact mem_normalizer_of_invol hv2 (Γ.v_norm_J hv h9)
  have hdisj : Disjoint Γ.J (zpowers v) := by
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    obtain ⟨hyJ, hyV⟩ := mem_inf.mp hy
    rcases mem_zpowers_involution hv2 hyV with h | h
    · rw [h]; exact one_mem _
    · exact absurd (h ▸ hyJ) (Γ.v_not_mem_J hv h9)
  have hcardD : Nat.card (Γ.J ⊔ zpowers v : Subgroup H) = 384 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer Γ.J (zpowers v) hnorm hdisj, Γ.J_card,
      Nat.card_zpowers, Γ.orderOf_v hv hv2 h9]
  have hle : (Γ.J ⊔ zpowers v : Subgroup H) ≤ Γ.C :=
    sup_le Γ.J_le_C (zpowers_le.mpr (Γ.v_le_C hv hv2 h9))
  have hcardC : Nat.card Γ.C ≤ Nat.card (Γ.J ⊔ zpowers v : Subgroup H) := by
    rw [hcardD]
    have := Γ.C_card_le
    subst hm
    simpa using this
  have hC : Γ.J ⊔ zpowers v = Γ.C := Subgroup.eq_of_le_of_card_ge hle hcardC
  refine ⟨⟨⊥, v, ?_, ?_, ?_, ?_, ?_, hv2, Γ.v_le_C hv hv2 h9, Γ.v_norm_J hv h9, ?_, ?_, ?_, fun _ => hv⟩⟩
  · have : m ≠ 10 := by omega
    simp [this]
  · intro j _ o ho; rw [mem_bot.mp ho]; simp
  · simp
  · exact bot_le
  · intro o ho; rw [mem_bot.mp ho]; simp
  · intro o ho; rw [mem_bot.mp ho]; simp
  · rw [← hC]; simp
  · intro _; simpa using Γ.v_not_mem_J hv h9

theorem decomp_ten (hm : m = 10) [Finite H] : Nonempty (Decomp Γ) := by
  have h9 : 9 ≤ m := by omega
  obtain ⟨v, hv, hv2⟩ := Γ.exists_vh h9
  obtain ⟨o, ho, ho3⟩ := Γ.exists_oh hm
  have hoo := Γ.orderOf_o ho ho3 hm
  have hOcard : Nat.card (zpowers o) = 3 := by rw [Nat.card_zpowers, hoo]
  have hJcomm : ∀ j ∈ Γ.J, ∀ x ∈ zpowers o, j * x = x * j := by
    intro j hj x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hc : Commute j o := Γ.o_comm_J ho ho3 hm j hj
    exact (hc.zpow_right k).eq
  have hvO : ∀ x ∈ zpowers o, v * x * v⁻¹ ∈ zpowers o := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow, Γ.v_conj_o hv ho ho3 hm]
    exact Subgroup.zpow_mem _ (inv_mem (mem_zpowers o)) k
  have hnormJO : zpowers v ≤ normalizer ((Γ.J ⊔ zpowers o : Subgroup H) : Set H) := by
    rw [zpowers_le]
    refine mem_normalizer_of_invol hv2 ?_
    let φ : H →* H := (MulAut.conj v).toMonoidHom
    have hJ : Γ.J.map φ ≤ Γ.J ⊔ zpowers o := by
      rintro _ ⟨j, hj, rfl⟩
      exact Subgroup.mem_sup_left (Γ.v_norm_J hv h9 j hj)
    have hO : (zpowers o).map φ ≤ Γ.J ⊔ zpowers o := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_right (hvO x hx)
    have hS : (Γ.J ⊔ zpowers o).map φ ≤ Γ.J ⊔ zpowers o := by
      rw [Subgroup.map_sup]; exact sup_le hJ hO
    intro s hs
    exact hS ⟨s, hs, rfl⟩
  have hcard1 : Nat.card (Γ.J ⊔ zpowers o : Subgroup H) = 576 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Γ.J (zpowers o) hJcomm).1
    rw [Γ.J_inf_zpowers_o ho ho3 hm, Subgroup.card_bot, Γ.J_card, hOcard] at h
    omega
  have hdisj : Disjoint (Γ.J ⊔ zpowers o) (zpowers v) := by
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    obtain ⟨hyS, hyV⟩ := mem_inf.mp hy
    rcases mem_zpowers_involution hv2 hyV with h | h
    · rw [h]; exact one_mem _
    · exfalso
      have hcent : Γ.J ⊔ zpowers o ≤ centralizer ({o} : Set H) := by
        refine sup_le (fun j hj => mem_centralizer_singleton_iff.mpr (Γ.o_comm_J ho ho3 hm j hj)) ?_
        rw [zpowers_le]
        exact mem_centralizer_singleton_iff.mpr rfl
      have hvo : v * o = o * v := by
        rw [h] at hyS
        exact mem_centralizer_singleton_iff.mp (hcent hyS)
      have h1 := Γ.v_conj_o hv ho ho3 hm
      have h2 : v * o * v⁻¹ = o := by rw [hvo]; group
      rw [h2] at h1
      have h3 : o * o = 1 := mul_eq_one_iff_eq_inv.mpr h1
      have h4 : o = 1 := by
        calc o = o * (o * o) := by rw [h3, mul_one]
          _ = o ^ 3 := (pow_three o).symm
          _ = 1 := ho3
      exact Γ.o_ne_one ho hm h4
  have hcard2 : Nat.card ((Γ.J ⊔ zpowers o) ⊔ zpowers v : Subgroup H) = 1152 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (Γ.J ⊔ zpowers o) (zpowers v) hnormJO hdisj,
      hcard1, Nat.card_zpowers, Γ.orderOf_v hv hv2 h9]
  have hle : ((Γ.J ⊔ zpowers o) ⊔ zpowers v : Subgroup H) ≤ Γ.C :=
    sup_le (sup_le Γ.J_le_C (zpowers_le.mpr (Γ.o_le_C ho ho3 hm)))
      (zpowers_le.mpr (Γ.v_le_C hv hv2 h9))
  have hcardC : Nat.card Γ.C ≤ Nat.card ((Γ.J ⊔ zpowers o) ⊔ zpowers v : Subgroup H) := by
    rw [hcard2]
    have hle2 := Γ.C_card_le
    subst hm
    have h6 : Nat.factorial 3 = 6 := by decide
    have : (10 - 7 : ℕ) = 3 := by norm_num
    rw [this, h6] at hle2
    omega
  have hC : (Γ.J ⊔ zpowers o) ⊔ zpowers v = Γ.C := Subgroup.eq_of_le_of_card_ge hle hcardC
  refine ⟨⟨zpowers o, v, ?_, hJcomm, Γ.J_inf_zpowers_o ho ho3 hm, zpowers_le.mpr (Γ.o_le_C ho ho3 hm),
    ?_, hv2, Γ.v_le_C hv hv2 h9, Γ.v_norm_J hv h9, hvO, hC.symm, ?_, fun _ => hv⟩⟩
  · rw [hOcard]; simp [hm]
  · intro x hx
    have hd : orderOf x ∣ 3 := by
      rw [← hOcard]
      exact Subgroup.orderOf_dvd_natCard _ hx
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h | h <;> rw [h] <;> decide
  · intro _ hvM
    have h1 : v ∈ (Γ.J ⊔ zpowers o) ⊓ zpowers v := ⟨hvM, mem_zpowers v⟩
    rw [disjoint_iff.mp hdisj] at h1
    exact Γ.v_ne_one hv h9 (mem_bot.mp h1)

theorem decomp [Finite H] : Nonempty (Decomp Γ) := by
  have h7 := Γ.h7
  have h10 := Γ.h10
  by_cases h8 : m ≤ 8
  · exact Γ.decomp_small h8
  · by_cases h9 : m = 9
    · exact Γ.decomp_nine h9
    · exact Γ.decomp_ten (by omega)

end Cfg

end Cfg

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
