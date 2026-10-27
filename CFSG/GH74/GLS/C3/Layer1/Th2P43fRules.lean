module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fTerm
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Sylow
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Th2P43fFrame

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

@[expose] def tt (a u w : G) : G := u * (a⁻¹ * w * a)

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem P_le_C : T ⊓ K ≤ centralizer ({x} : Set G) := fun _ hu => F.T_le_C hu.1

theorem conj_mem_T {w : G} (hw : w ∈ T ⊓ K) : a⁻¹ * w * a ∈ T := F.core.a_inv_norm hw.1

omit F in
theorem conj_mem_conj {w : G} (hw : w ∈ T ⊓ K) : a⁻¹ * w * a ∈ conjugate (T ⊓ K) a :=
  C3.Layer1.Bk.Sec4Core.mem_conj_of (T ⊓ K) hw

theorem tt_mem_T {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K) : tt a u w ∈ T :=
  T.mul_mem hu.1 (F.conj_mem_T hw)

theorem tt_mem_C {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K) :
    tt a u w ∈ centralizer ({x} : Set G) := F.T_le_C (F.tt_mem_T hu hw)

theorem comm_PP' [Finite G] {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K) :
    u * (a⁻¹ * w * a) = (a⁻¹ * w * a) * u :=
  F.core.comm_P_conj u hu _ (conj_mem_conj (K := K) (T := T) (a := a) hw)

theorem tt_sq [Finite G] {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K) (hu2 : u * u = 1) (hw2 : w * w = 1) :
    tt a u w * tt a u w = 1 := by
  unfold tt
  have hc := F.comm_PP' hu hw
  calc u * (a⁻¹ * w * a) * (u * (a⁻¹ * w * a)) = u * ((a⁻¹ * w * a) * u) * (a⁻¹ * w * a) := by
        group
    _ = u * (u * (a⁻¹ * w * a)) * (a⁻¹ * w * a) := by rw [← hc]
    _ = (u * u) * (a⁻¹ * (w * w) * a) := by group
    _ = 1 := by rw [hu2, hw2]; group

theorem a_z_a : a⁻¹ * z * a = x := by
  have := F.a_x
  calc a⁻¹ * z * a = a⁻¹ * (a * x * a⁻¹) * a := by rw [this]
    _ = x := by group

theorem psi_one : psi 1 = 1 := by
  have := F.psi_mul 1 (centralizer ({x} : Set G)).one_mem 1 (centralizer ({x} : Set G)).one_mem
  rw [mul_one] at this
  exact (mul_eq_left.1 this.symm)

omit F in
theorem x_mem_C : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem psi_x : psi x = 1 := (F.psi_ker x x_mem_C).2 F.x_mem_CxK

theorem psi_K_odd [Finite G] : ∀ k ∈ K, psi k = 1 → Odd (orderOf k) := by
  intro k hk h
  have hmem := (F.psi_K_ker k hk).1 h
  exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ hmem)

theorem psi_tt {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K) :
    psi (tt a u w) = psi u * psi (a⁻¹ * w * a) :=
  F.psi_mul u (F.P_le_C hu) _ (F.T_le_C (F.conj_mem_T hw))

theorem psi_P_sq {u : G} (hu : u ∈ T ⊓ K) (hu2 : u * u = 1) : psi u * psi u = 1 := by
  rw [← F.psi_mul u (F.P_le_C hu) u (F.P_le_C hu), hu2, F.psi_one]

theorem psi_P_ne_one [Finite G] {u : G} (hu : u ∈ T ⊓ K) (hu1 : u ≠ 1) : psi u ≠ 1 := by
  intro h
  have hQ : u ∈ T ⊓ CxK x K := ⟨hu.1, (F.psi_ker u (F.P_le_C hu)).1 h⟩
  have : u ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) := ⟨hu, hQ⟩
  rw [F.core.PQ_disj, Subgroup.mem_bot] at this
  exact hu1 this

theorem supp_psi_P [Finite G] {u : G} (hu : u ∈ T ⊓ K) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    (psi u).support.card = 4 := by
  obtain ⟨i, hi⟩ := F.psi_P u hu
  exact card_support_eq_four_of_even (F.psi_P_sq hu hu2) (F.psi_P_ne_one hu hu1)
    (by rw [hi]; exact sign_a7P i)

theorem swap_rule [Finite G] :
    ∃ g : G, ∀ u ∈ T ⊓ K, ∀ w ∈ T ⊓ K, g * tt a u w * g⁻¹ = tt a w u := by
  have ha2 : a * a ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ F.core.a_sq_mem
  obtain ⟨p₀, hp₀, q₀, hq₀, hpq⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ha2
  refine ⟨q₀⁻¹ * a, fun u hu w hw => ?_⟩
  have h1 : a * u * a⁻¹ ∈ conjugate (T ⊓ K) a := by
    rw [mem_conjugate_iff']
    have : a * (a * u * a⁻¹) * a⁻¹ = (a * a) * u * (a * a)⁻¹ := by group
    rw [this]
    exact F.core.P_norm _ F.core.a_sq_mem u hu
  have h2 : p₀ * (a * u * a⁻¹) = (a * u * a⁻¹) * p₀ := F.core.comm_P_conj p₀ hp₀ _ h1
  have h3 : a⁻¹ * u * a = q₀⁻¹ * (a * u * a⁻¹) * q₀ := by
    have e1 : a⁻¹ * u * a = (a * a)⁻¹ * (a * u * a⁻¹) * (a * a) := by group
    rw [e1, hpq]
    calc (p₀ * q₀)⁻¹ * (a * u * a⁻¹) * (p₀ * q₀)
        = q₀⁻¹ * (p₀⁻¹ * ((a * u * a⁻¹) * p₀)) * q₀ := by group
      _ = q₀⁻¹ * (p₀⁻¹ * (p₀ * (a * u * a⁻¹))) * q₀ := by rw [← h2]
      _ = q₀⁻¹ * (a * u * a⁻¹) * q₀ := by group
  have hqw : q₀⁻¹ * w * q₀ = w := by
    have := F.core.comm_P_conj w hw q₀ hq₀
    calc q₀⁻¹ * w * q₀ = q₀⁻¹ * (w * q₀) := by group
      _ = q₀⁻¹ * (q₀ * w) := by rw [this]
      _ = w := by group
  have hexp : (q₀⁻¹ * a) * tt a u w * (q₀⁻¹ * a)⁻¹ =
      (q₀⁻¹ * (a * u * a⁻¹) * q₀) * (q₀⁻¹ * w * q₀) := by
    unfold tt
    group
  rw [hexp, ← h3, hqw]
  unfold tt
  exact (F.comm_PP' hw hu).symm

theorem k_rule' [Finite G] {u u' w : G} (hu : u ∈ T ⊓ K) (hu' : u' ∈ T ⊓ K) (hw : w ∈ T ⊓ K)
    (hu2 : u * u = 1) (hu'2 : u' * u' = 1) (hw2 : w * w = 1)
    (hsupp : (psi u * psi (a⁻¹ * w * a)).support.card =
      (psi u' * psi (a⁻¹ * w * a)).support.card) :
    IsConj (tt a u w) (tt a u' w) := by
  obtain ⟨k, -, hk⟩ := k_rule F.K_le F.K_norm psi F.psi_mul F.psi_K_odd F.psi_surj
    (F.tt_mem_C hu hw) (F.tt_mem_C hu' hw) (F.tt_sq hu hw hu2 hw2) (F.tt_sq hu' hw hu'2 hw2)
    (by
      have e : tt a u' w * (tt a u w)⁻¹ = u' * u⁻¹ := by
        unfold tt
        group
      rw [e]
      exact K.mul_mem hu'.2 (K.inv_mem hu.2))
    (by rw [F.psi_tt hu hw, F.psi_tt hu' hw]; exact hsupp)
  exact isConj_iff.2 ⟨k, hk⟩

theorem isConj_P_z [Finite G] {u : G} (hu : u ∈ T ⊓ K) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    IsConj u z := by
  obtain ⟨k, -, hk⟩ := k_rule F.K_le F.K_norm psi F.psi_mul F.psi_K_odd F.psi_surj
    (F.P_le_C hu) (F.P_le_C F.z_mem) hu2 F.z_sq
    (K.mul_mem F.z_mem.2 (K.inv_mem hu.2))
    (by rw [F.supp_psi_P hu hu2 hu1, F.supp_psi_P F.z_mem F.z_sq F.z_ne])
  exact isConj_iff.2 ⟨k, hk⟩

theorem isConj_x_z : IsConj x z := isConj_iff.2 ⟨a, F.a_x⟩

theorem isConj_z_x : IsConj z x := F.isConj_x_z.symm

theorem isConj_P_x [Finite G] {u : G} (hu : u ∈ T ⊓ K) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    IsConj u x := (F.isConj_P_z hu hu2 hu1).trans F.isConj_z_x

theorem isConj_conj_x [Finite G] {w : G} (hw : w ∈ T ⊓ K) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    IsConj (a⁻¹ * w * a) x :=
  (isConj_iff.2 ⟨a, by group⟩ : IsConj (a⁻¹ * w * a) w).trans (F.isConj_P_x hw hw2 hw1)

theorem tt_zz : tt a z z = z * x := by
  unfold tt
  rw [F.a_z_a]

theorem isConj_tt_z_v [Finite G] {w : G} (hw : w ∈ T ⊓ K) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    IsConj (tt a z w) (z * x) := by
  obtain ⟨g, hg⟩ := F.swap_rule
  have h1 : IsConj (tt a z w) (tt a w z) := isConj_iff.2 ⟨g, hg z F.z_mem w hw⟩
  have h2 : IsConj (tt a w z) (tt a z z) := by
    refine F.k_rule' hw F.z_mem F.z_mem hw2 F.z_sq F.z_sq ?_
    rw [F.a_z_a, F.psi_x, mul_one, mul_one, F.supp_psi_P hw hw2 hw1,
      F.supp_psi_P F.z_mem F.z_sq F.z_ne]
  rw [F.tt_zz] at h2
  exact h1.trans h2

theorem isConj_tt_v_of_right [Finite G] {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K)
    (hu2 : u * u = 1) (hw2 : w * w = 1) (hu1 : u ≠ 1) (hw1 : w ≠ 1)
    (hθ : psi (a⁻¹ * w * a) = 1) : IsConj (tt a u w) (z * x) := by
  have h1 : IsConj (tt a u w) (tt a z w) := by
    refine F.k_rule' hu F.z_mem hw hu2 F.z_sq hw2 ?_
    rw [hθ, mul_one, mul_one, F.supp_psi_P hu hu2 hu1, F.supp_psi_P F.z_mem F.z_sq F.z_ne]
  exact h1.trans (F.isConj_tt_z_v hw hw2 hw1)

theorem isConj_tt_v_of_left [Finite G] {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K)
    (hu2 : u * u = 1) (hw2 : w * w = 1) (hu1 : u ≠ 1) (hw1 : w ≠ 1)
    (hθ : psi (a⁻¹ * u * a) = 1) : IsConj (tt a u w) (z * x) := by
  obtain ⟨g, hg⟩ := F.swap_rule
  have h1 : IsConj (tt a u w) (tt a w u) := isConj_iff.2 ⟨g, hg u hu w hw⟩
  exact h1.trans (F.isConj_tt_v_of_right hw hu hw2 hu2 hw1 hu1 hθ)

theorem card_T [Finite G] : Nat.card ↥T = 64 := by
  have := F.core.card_P_sup_conj
  rwa [← F.T_eq] at this

theorem card_S_ge [Finite G] : 128 ≤ Nat.card ↥S := by
  have hT64 := F.card_T
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le F.core.T_le_S
  rw [hT64] at hk
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply F.core.a_not_mem
    have : T = S := Subgroup.eq_of_le_of_card_ge F.core.T_le_S (by omega)
    rw [this]
    exact F.core.a_mem
  omega

theorem S_centralizes_v [Finite G] : ∀ s ∈ S, s * (z * x) * s⁻¹ = z * x := by
  have hzT : ∀ t ∈ T, t * z = z * t := by
    intro t ht
    have ht' : t ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ ht
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ht'
    have h1 : p * z = z * p := F.z_central p hp
    have h2 : q * z = z * q := (F.core.comm_P_conj z F.z_mem q hq).symm
    calc p * q * z = p * (q * z) := by group
      _ = p * (z * q) := by rw [h2]
      _ = (p * z) * q := by group
      _ = (z * p) * q := by rw [h1]
      _ = z * (p * q) := by group
  have hxT : ∀ t ∈ T, t * x = x * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.1 (F.T_le_C ht)
  have haz : a * z * a⁻¹ = x := by
    have h1 : a * z * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by
      calc a * z * a⁻¹ = a * (a * x * a⁻¹) * a⁻¹ := by rw [F.a_x]
        _ = (a * a) * x * (a * a)⁻¹ := by group
    rw [h1]
    have := hxT (a * a) F.core.a_sq_mem
    calc (a * a) * x * (a * a)⁻¹ = (x * (a * a)) * (a * a)⁻¹ := by rw [this]
      _ = x := by group
  have hTv : ∀ t ∈ T, t * (z * x) * t⁻¹ = z * x := by
    intro t ht
    calc t * (z * x) * t⁻¹ = (t * z) * x * t⁻¹ := by group
      _ = (z * t) * x * t⁻¹ := by rw [hzT t ht]
      _ = z * (t * x) * t⁻¹ := by group
      _ = z * (x * t) * t⁻¹ := by rw [hxT t ht]
      _ = z * x := by group
  intro s hs
  rcases F.S_cases s hs with hsT | hsT
  · exact hTv s hsT
  · have e : s = a * (a⁻¹ * s) := by group
    rw [e]
    have h1 := hTv _ hsT
    calc a * (a⁻¹ * s) * (z * x) * (a * (a⁻¹ * s))⁻¹
        = a * ((a⁻¹ * s) * (z * x) * (a⁻¹ * s)⁻¹) * a⁻¹ := by group
      _ = a * (z * x) * a⁻¹ := by rw [h1]
      _ = (a * z * a⁻¹) * (a * x * a⁻¹) := by group
      _ = x * z := by rw [haz, F.a_x]
      _ = z * x := by
        have := F.core.comm_P_conj z F.z_mem x F.x_mem
        exact this.symm

theorem not_isConj_v_of_Q [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {u : G} (hu : u ∈ T ⊓ CxK x K) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : ¬ IsConj u (z * x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hord : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
  set W : Subgroup G := conjugate S g with hW
  have hWp : IsPGroup 2 ↥W := F.core.S_pgroup.map (MulAut.conj g⁻¹).toMonoidHom
  have hWu : W ≤ centralizer ({u} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hs1 : g * w * g⁻¹ ∈ S := mem_conjugate_iff'.1 hw
    have h1 := F.S_centralizes_v _ hs1
    have hgu : g * u * g⁻¹ = z * x := hg
    have h2 : (g * w * g⁻¹) * (z * x) = (z * x) * (g * w * g⁻¹) := by
      calc (g * w * g⁻¹) * (z * x)
          = ((g * w * g⁻¹) * (z * x) * (g * w * g⁻¹)⁻¹) * (g * w * g⁻¹) := by group
        _ = (z * x) * (g * w * g⁻¹) := by rw [h1]
    rw [← hgu] at h2
    have h3 : g * (w * u) * g⁻¹ = g * (u * w) * g⁻¹ := by
      calc g * (w * u) * g⁻¹ = (g * w * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * u * g⁻¹) * (g * w * g⁻¹) := h2
        _ = g * (u * w) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)
  have hcard : Nat.card ↥W = Nat.card ↥S := card_conjugate' S g
  have hbd := card_le_of_le_centralizer_Q hG hs e7 hP2 hu hord
    (fun q hq => (forall_of_isElementaryAbelian F.Q_el).1 u hu q hq) hWp hWu
  have := F.card_S_ge
  omega

theorem psi_z [Finite G] : psi z = a7P 1 := by
  obtain ⟨j, hj⟩ := F.psi_P z F.z_mem
  have hcomm : ∀ i : Fin 8, a7P j * a7P i = a7P i * a7P j := by
    intro i
    obtain ⟨u', hu', hui⟩ := F.psi_P_surj i
    rw [← hj, ← hui, ← F.psi_mul z (F.P_le_C F.z_mem) u' (F.P_le_C hu'),
      ← F.psi_mul u' (F.P_le_C hu') z (F.P_le_C F.z_mem), F.z_central u' hu']
  rcases a7P_central_idx j hcomm with h0 | h1
  · exfalso
    apply F.psi_P_ne_one F.z_mem F.z_ne
    rw [hj, h0]
    rfl
  · rw [hj, h1]

theorem Q_le_conj [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) : T ⊓ CxK x K ≤ conjugate (T ⊓ K) a := by
  intro q hq
  by_contra hqP
  have hqT' : q ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ hq.1
  obtain ⟨u, hu, w, hw, hqe⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj hqT'
  have hwT : w ∈ T := F.core.conj_le F.core.P_le hw
  have hwC : w ∈ centralizer ({x} : Set G) := F.T_le_C hwT
  have hpq : psi u * psi w = 1 := by
    rw [← F.psi_mul u (F.P_le_C hu) w hwC, ← hqe]
    exact (F.psi_ker q (F.T_le_C hq.1)).2 hq.2
  have hwc : ∀ u' ∈ T ⊓ K, psi w * psi u' = psi u' * psi w := by
    intro u' hu'
    rw [← F.psi_mul w hwC u' (F.P_le_C hu'), ← F.psi_mul u' (F.P_le_C hu') w hwC]
    exact congrArg psi (F.core.comm_P_conj u' hu' w hw).symm
  have huc : ∀ u' ∈ T ⊓ K, psi u * psi u' = psi u' * psi u := by
    intro u' hu'
    have hui : psi u = (psi w)⁻¹ := eq_inv_of_mul_eq_one_left hpq
    rw [hui]
    exact ((Commute.inv_left (hwc u' hu')).eq)
  obtain ⟨i, hi⟩ := F.psi_P u hu
  have hcomm : ∀ j : Fin 8, a7P i * a7P j = a7P j * a7P i := by
    intro j
    obtain ⟨u', hu', hui⟩ := F.psi_P_surj j
    rw [← hi, ← hui]
    exact huc u' hu'
  have hQ2 : ∀ q' ∈ T ⊓ CxK x K, q' * q' = 1 := fun q' hq' =>
    (forall_of_isElementaryAbelian F.Q_el).2 q' hq'
  rcases a7P_central_idx i hcomm with h0 | h1
  ·
    have hu1 : u = 1 := by
      by_contra hne
      exact F.psi_P_ne_one hu hne (by rw [hi, h0]; rfl)
    apply hqP
    rw [hqe, hu1, one_mul]
    exact hw
  ·
    have huz1 : u * z = 1 := by
      by_contra hne
      refine F.psi_P_ne_one (Subgroup.mul_mem _ hu F.z_mem) hne ?_
      rw [F.psi_mul u (F.P_le_C hu) z (F.P_le_C F.z_mem), hi, h1, F.psi_z]
      decide
    have huz : u = z := by
      rw [eq_inv_of_mul_eq_one_left huz1]
      exact inv_eq_of_mul_eq_one_right F.z_sq
    have hzw : z * w = w * z := F.core.comm_P_conj z F.z_mem w hw
    have hq2 := hQ2 q hq
    have hw2 : w * w = 1 := by
      rw [hqe, huz] at hq2
      calc w * w = z * z * (w * w) := by rw [F.z_sq, one_mul]
        _ = (z * w) * (z * w) := by
          calc z * z * (w * w) = z * (z * w) * w := by group
            _ = z * (w * z) * w := by rw [hzw]
            _ = (z * w) * (z * w) := by group
        _ = 1 := hq2
    have hw1 : w ≠ 1 := by
      intro h1
      apply F.z_ne
      have hzQ : z ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) := by
        refine ⟨F.z_mem, ?_⟩
        have : q = z := by rw [hqe, huz, h1, mul_one]
        rw [← this]
        exact hq
      rw [F.core.PQ_disj, Subgroup.mem_bot] at hzQ
      exact hzQ
    have hw₀ : a * w * a⁻¹ ∈ T ⊓ K := mem_conjugate_iff'.1 hw
    have hw₀2 : (a * w * a⁻¹) * (a * w * a⁻¹) = 1 := by
      calc (a * w * a⁻¹) * (a * w * a⁻¹) = a * (w * w) * a⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    have hw₀1 : a * w * a⁻¹ ≠ 1 := by
      intro h1
      apply hw1
      calc w = a⁻¹ * (a * w * a⁻¹) * a := by group
        _ = 1 := by rw [h1]; group
    have hqt : q = tt a z (a * w * a⁻¹) := by
      unfold tt
      rw [hqe, huz]
      group
    have hq1 : q ≠ 1 := by
      intro h1
      exact hqP (by rw [h1]; exact one_mem _)
    exact F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 hq hq2 hq1 (hqt ▸ F.isConj_tt_z_v hw₀ hw₀2 hw₀1)

end Frame

end CFSG.GH74.GLS.Th2.P43f
