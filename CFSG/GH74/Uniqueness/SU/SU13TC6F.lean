module

public import CFSG.GH74.Uniqueness.SU.SU13TC6E
public import CFSG.GH74.Uniqueness.SU.SU13TC6D
public import CFSG.GH74.Uniqueness.SU.SU13TC6GQuo

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_commutator₂ {A B A' B' : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A')
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B') {n : G} (hn : n ∈ ⁅A, B⁆) : g * n * g⁻¹ ∈ ⁅A', B'⁆ := by
  have h1 : A.map (MulAut.conj g).toMonoidHom ≤ A' := by
    rintro _ ⟨y, hy, rfl⟩
    exact hA y hy
  have h2 : B.map (MulAut.conj g).toMonoidHom ≤ B' := by
    rintro _ ⟨y, hy, rfl⟩
    exact hB y hy
  have h3 := Subgroup.commutator_mono h1 h2
  rw [← Subgroup.map_commutator] at h3
  exact h3 ⟨n, hn, by simp [MulAut.conj_apply]⟩

theorem inf_zpowers_eq_bot {s : G} (hs : orderOf s = 3) {K : Subgroup G} (hK : s ∉ K) :
    K ⊓ zpowers s = ⊥ := by
  have hord : Nat.card (zpowers s) = 3 := by rw [Nat.card_zpowers, hs]
  have hadvd : Nat.card (K ⊓ zpowers s : Subgroup G) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : (K ⊓ zpowers s : Subgroup G) ≤ zpowers s)
    rwa [hord] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hadvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    apply hK
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_right : (K ⊓ zpowers s : Subgroup G) ≤ zpowers s) (by rw [h, hord])
    have : s ∈ (K ⊓ zpowers s : Subgroup G) := by
      rw [heq]
      exact mem_zpowers _
    exact (mem_inf.mp this).1

end Generic

structure V1Data {G : Type} [Group G] [Finite G] {z : G} (X : Ctx9 G z) (V₁ : Subgroup G) : Prop where
  le_C : V₁ ≤ X.C
  Y_le : X.Y ≤ V₁
  norm : ∀ c ∈ X.C, ∀ v ∈ V₁, c * v * c⁻¹ ∈ V₁
  card : Nat.card V₁ = 3 ^ 7 * 4
  inv : ∀ x ∈ X.C, x * x = 1 → x ∈ V₁

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Ctx9

theorem zpowers_comm (X : Ctx9 G z) {p x : G} (hp : p ∈ zpowers X.L.e.s₂) (hx : x ∈ X.C) :
    p * x = x * p :=
  zpowers_comm_of_mem_centralizer hx hp

variable (X : Ctx9 G z) {V₁ : Subgroup G} (hV : V1Data X V₁)
include hV

theorem K_le_Y : ⁅X.Y, V₁⁆ ≤ X.Y := by
  rw [Subgroup.commutator_le]
  intro y hy v hv
  rw [commutatorElement_def]
  have hvC : v ∈ X.C := hV.le_C hv
  have : y * v * y⁻¹ * v⁻¹ = y * (v * y⁻¹ * v⁻¹) := by group
  rw [this]
  exact X.Y.mul_mem hy (X.conj_Y hvC (X.Y.inv_mem hy))

theorem K_conj {c n : G} (hc : c ∈ X.C) (hn : n ∈ ⁅X.Y, V₁⁆) : c * n * c⁻¹ ∈ ⁅X.Y, V₁⁆ :=
  conj_mem_commutator₂ (fun _ hy => X.conj_Y hc hy) (fun _ hv => hV.norm c hc _ hv) hn

theorem s₂_not_mem_K : X.L.e.s₂ ∉ ⁅X.Y, V₁⁆ := by
  intro hs
  have hform : ∀ v ∈ V₁, ∃ y ∈ X.Y, v = y ∨ v = y * X.L.e.t ∨ v = y * z ∨ v = y * (X.L.e.t * z) := by
    intro v hv
    obtain ⟨y, hy, r, hr, rfl⟩ := X.V1_form hV.Y_le hV.card (X.kfour_le_V1 hV.inv) v hv
    refine ⟨y, hy, ?_⟩
    rcases kfour_mem X.hz X.L.e hr with rfl | rfl | rfl | rfl
    · right; right; right; rfl
    · right; left; rfl
    · right; right; left; rfl
    · left; simp
  exact X.s₂_not_mem_Y' (mem_commutator_of_mem_commutator_centralizes (Y := X.Y) (V := V₁)
    (t := X.L.e.t) (z := z) (odd_card_oc _)
    (X.kfour_sq (t_mem_kfour X.hz X.L.e)) (X.kfour_sq (z_mem_kfour X.hz X.L.e)) X.L.e.t_comm
    (fun y hy => X.conj_Y X.t_mem_C hy) (fun y hy => X.conj_Y X.z_mem_C hy) hform X.s₂_mem_Y
    X.L.e.t_s₂.symm X.L.e.s₂_comm hs)

theorem Y_le_K_sup : X.Y ≤ ⁅X.Y, V₁⁆ ⊔ zpowers X.L.e.s₂ := by
  have : IsKleinFour (kfour X.hz X.L.e) := isKleinFour_kfour X.hz X.L.e
  have hR2 : IsPGroup 2 (kfour X.hz X.L.e) :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    2 Nat.prime_two (kfour X.hz X.L.e) X.Y hR2 (by rw [X.Y_card]; norm_num)
    (fun x hx => le_normalizer_oc X.C (X.kfour_le_C hx))
  intro y hy
  rw [hfac] at hy
  refine sup_le_sup (Subgroup.commutator_mono le_rfl (X.kfour_le_V1 hV.inv)) ?_ hy
  intro a ha
  obtain ⟨haY, haR⟩ := mem_inf.mp ha
  have hat : a * X.L.e.t = X.L.e.t * a :=
    (mem_centralizer_iff.mp haR X.L.e.t (t_mem_kfour X.hz X.L.e)).symm
  have haz : a * z = z * a := (mem_centralizer_iff.mp haR z (z_mem_kfour X.hz X.L.e)).symm
  have haE : a ∈ X.E := by
    have hmem : a ∈ oc X.C ⊓ centralizer ({z} : Set G) :=
      mem_inf.mpr ⟨haY, mem_centralizer_singleton_iff.mpr haz⟩
    rw [X.l3.Y_cent] at hmem
    exact hmem
  exact X.L.m.cent_t a haE hat.symm

theorem Y_eq_K_sup : ⁅X.Y, V₁⁆ ⊔ zpowers X.L.e.s₂ = X.Y :=
  le_antisymm (sup_le (X.K_le_Y hV) ((zpowers_le).mpr X.s₂_mem_Y)) (X.Y_le_K_sup hV)

theorem K_inf_s₂ : ⁅X.Y, V₁⁆ ⊓ zpowers X.L.e.s₂ = ⊥ :=
  inf_zpowers_eq_bot X.L.e.s₂_ord (X.s₂_not_mem_K hV)

theorem card_K : Nat.card (⁅X.Y, V₁⁆ : Subgroup G) = 3 ^ 6 := by
  have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (⁅X.Y, V₁⁆ : Subgroup G)
    (zpowers X.L.e.s₂) (fun k hk p hp => (X.zpowers_comm hp (X.Y_le_C (X.K_le_Y hV hk))).symm)).1
  rw [X.Y_eq_K_sup hV, X.K_inf_s₂ hV, Subgroup.card_bot, Nat.card_zpowers, X.L.e.s₂_ord, X.Y_card] at h
  omega

theorem mem_K_of_sq {y : G} (hy : y ∈ X.Y) (hyy : y * y ∈ ⁅X.Y, V₁⁆) : y ∈ ⁅X.Y, V₁⁆ := by
  have hy' : y ∈ ⁅X.Y, V₁⁆ ⊔ zpowers X.L.e.s₂ := by rw [X.Y_eq_K_sup hV]; exact hy
  obtain ⟨k, hk, p, hp, rfl⟩ := SU1.mem_sup_of_commute (A := ⁅X.Y, V₁⁆) (B := zpowers X.L.e.s₂)
    (fun k hk p hp => (X.zpowers_comm hp (X.Y_le_C (X.K_le_Y hV hk))).symm) hy'
  have hpc : p * k = k * p := X.zpowers_comm hp (X.Y_le_C (X.K_le_Y hV hk))
  have hsq : (k * p) * (k * p) = (k * k) * (p * p) := by
    calc (k * p) * (k * p) = k * (p * k) * p := by group
      _ = k * (k * p) * p := by rw [hpc]
      _ = (k * k) * (p * p) := by group
  have hpp : p * p ∈ ⁅X.Y, V₁⁆ := by
    have h1 : p * p = (k * k)⁻¹ * ((k * p) * (k * p)) := by rw [hsq]; group
    rw [h1]
    exact (⁅X.Y, V₁⁆ : Subgroup G).mul_mem ((⁅X.Y, V₁⁆ : Subgroup G).inv_mem
      ((⁅X.Y, V₁⁆ : Subgroup G).mul_mem hk hk)) hyy
  have hpb : p * p ∈ ⁅X.Y, V₁⁆ ⊓ zpowers X.L.e.s₂ :=
    mem_inf.mpr ⟨hpp, (zpowers X.L.e.s₂).mul_mem hp hp⟩
  rw [X.K_inf_s₂ hV, mem_bot] at hpb
  have hp3 : p ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := zpowers X.L.e.s₂) (x := ⟨p, hp⟩)
    rw [Nat.card_zpowers, X.L.e.s₂_ord] at h1
    exact congrArg Subtype.val h1
  have hp1 : p = 1 := by
    calc p = p ^ 3 * (p * p)⁻¹ := by group
      _ = 1 := by rw [hp3, hpb, inv_one, mul_one]
  rw [hp1, mul_one]
  exact hk

noncomputable abbrev Msub : Subgroup G :=
  TT (⁅X.Y, V₁⁆ : Subgroup G) (kfour X.hz X.L.e)
    (fun _ hd _ hw => X.K_conj hV (X.kfour_le_C hd) hw)

theorem M_le_C : Msub X hV ≤ X.C := by
  rintro _ ⟨k, hk, r, hr, rfl⟩
  exact X.C.mul_mem (X.Y_le_C (X.K_le_Y hV hk)) (X.kfour_le_C hr)

theorem K_inf_kfour : (⁅X.Y, V₁⁆ : Subgroup G) ⊓ kfour X.hz X.L.e = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxR⟩ := mem_inf.mp hx
  have := X.Y_inf_kfour
  have hxm : x ∈ X.Y ⊓ kfour X.hz X.L.e := mem_inf.mpr ⟨X.K_le_Y hV hxK, hxR⟩
  rw [this] at hxm
  exact hxm

theorem card_M : Nat.card (Msub X hV) = 3 ^ 6 * 4 := by
  have : IsKleinFour (kfour X.hz X.L.e) := isKleinFour_kfour X.hz X.L.e
  rw [card_TT_eq _ (X.K_inf_kfour hV), X.card_K hV, IsKleinFour.card_four]

theorem inv_mem_M {x : G} (hx : x ∈ X.C) (hxx : x * x = 1) : x ∈ Msub X hV := by
  obtain ⟨y, hy, r, hr, rfl⟩ := X.V1_form hV.Y_le hV.card (X.kfour_le_V1 hV.inv) x (hV.inv x hx hxx)
  have hrr : r * r = 1 := X.kfour_sq hr
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have hry : r * y * r = y⁻¹ := by
    calc r * y * r = y⁻¹ * (y * r * (y * r)) := by group
      _ = y⁻¹ := by rw [hxx, mul_one]
  have h1 : r * y⁻¹ * r = y := by
    calc r * y⁻¹ * r = r⁻¹ * y⁻¹ * r⁻¹ := by rw [hrinv]
      _ = (r * y * r)⁻¹ := by group
      _ = y := by rw [hry, inv_inv]
  have hc : y * r * y⁻¹ * r⁻¹ = y * y := by
    calc y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r) := by rw [hrinv]; group
      _ = y * y := by rw [h1]
  have hcK : y * r * y⁻¹ * r⁻¹ ∈ ⁅X.Y, V₁⁆ := by
    have := Subgroup.commutator_mem_commutator hy (X.kfour_le_V1 hV.inv hr)
    rwa [commutatorElement_def] at this
  rw [hc] at hcK
  exact ⟨y, X.mem_K_of_sq hV hy hcK, r, hr, rfl⟩

theorem M_conj {c m : G} (hc : c ∈ X.C) (hm : m ∈ Msub X hV) : c * m * c⁻¹ ∈ Msub X hV := by
  obtain ⟨k, hk, r, hr, rfl⟩ := hm
  have e : c * (k * r) * c⁻¹ = (c * k * c⁻¹) * (c * r * c⁻¹) := by group
  rw [e]
  refine (Msub X hV).mul_mem ⟨c * k * c⁻¹, X.K_conj hV hc hk, 1, (kfour X.hz X.L.e).one_mem, by simp⟩ ?_
  refine X.inv_mem_M hV (X.C.mul_mem (X.C.mul_mem hc (X.kfour_le_C hr)) (X.C.inv_mem hc)) ?_
  calc c * r * c⁻¹ * (c * r * c⁻¹) = c * (r * r) * c⁻¹ := by group
    _ = 1 := by rw [X.kfour_sq hr]; group

theorem comm_C_mem_M {a b : G} (ha : a ∈ X.C) (hb : b ∈ X.C) : a * b * a⁻¹ * b⁻¹ ∈ Msub X hV := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥X.C := (Msub X hV).subgroupOf X.C
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact X.M_conj hV g.2 hn
  have hNcard : Nat.card N = Nat.card (Msub X hV) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (X.M_le_C hV)).toEquiv
  have hq : Nat.card (↥X.C ⧸ N) = 3 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, X.card_M hV, X.card_C_twelve] at h1
    omega
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have h2 := hcomm.is_comm.comm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
  have h3 : (QuotientGroup.mk (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : ↥X.C) : ↥X.C ⧸ N) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (QuotientGroup.mk ⟨a, ha⟩ : ↥X.C ⧸ N) * QuotientGroup.mk ⟨b, hb⟩ *
          (QuotientGroup.mk ⟨a, ha⟩)⁻¹ * (QuotientGroup.mk ⟨b, hb⟩)⁻¹
        = (QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩) *
          (QuotientGroup.mk ⟨a, ha⟩)⁻¹ * (QuotientGroup.mk ⟨b, hb⟩)⁻¹ := by rw [h2]
      _ = 1 := by group
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h3)

theorem s₂_not_mem_M : X.L.e.s₂ ∉ Msub X hV := by
  rintro ⟨k, hk, r, hr, hkr⟩
  have hrY : r ∈ X.Y := by
    have : r = k⁻¹ * X.L.e.s₂ := by rw [hkr]; group
    rw [this]
    exact X.Y.mul_mem (X.Y.inv_mem (X.K_le_Y hV hk)) X.s₂_mem_Y
  have hr1 : r = 1 := X.kfour_odd_eq_one hr (X.odd_orderOf hrY (odd_card_oc _))
  rw [hr1, mul_one] at hkr
  exact X.s₂_not_mem_K hV (by rw [hkr]; exact hk)

end Ctx9

variable (X : Ctx9 G z)

theorem Ctx9.not_conj_s₂_mem (g : G) : g * X.L.e.s₂ * g⁻¹ ∉ ⁅X.Y, X.Y⁆ := by
  obtain ⟨V₁, hle, hY, hn, hc, hinv⟩ := X.exists_V1
  have hV : V1Data X V₁ := ⟨hle, hY, hn, hc, hinv⟩
  exact not_conj_mem_commutator (fun _ hn _ hy => X.Y'_comm hn hy)
    (fun _ ha _ hb => X.comm_C_mem_M hV ha hb) (X.s₂_not_mem_M hV) g

end CFSG.GH74.Uniqueness.SU.SU13
