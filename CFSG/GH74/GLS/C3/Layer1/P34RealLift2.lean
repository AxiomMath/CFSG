module

public import CFSG.GH74.GLS.C3.Layer1.P34RealLift1

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
theorem inn_exists {g₀ : MulAut (kBar K)} (hg₀ : g₀ ∈ innAut (kBar K)) :
    ∃ k : ↥K, g₀ = MulAut.conj (QuotientGroup.mk k : kBar K) := by
  obtain ⟨b, rfl⟩ := hg₀
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨k, rfl⟩

namespace Real34

variable {x : G} {T : Subgroup G} {f : G} (H : Real34 x K T f)

include H in
theorem exists_conj_outer {u y w : G} (hu : u ∈ centralizer ({x} : Set G)) (huu : u * u = 1)
    (hout : act H.KN u ∉ innAut (kBar K)) (hy : y ∈ K ⊔ zpowers u) (hw : w ∈ K ⊔ zpowers u)
    (hy2 : orderOf y = 2) (hw2 : orderOf w = 2) {g₀ : MulAut (kBar K)}
    (hg₀ : g₀ ∈ innAut (kBar K)) (hconj : g₀ * act H.KN y * g₀⁻¹ = act H.KN w) :
    ∃ g ∈ K ⊔ zpowers u, g⁻¹ * y * g = w := by
  obtain ⟨k, rfl⟩ := inn_exists hg₀
  have hM : K ⊔ zpowers u ≤ centralizer ({x} : Set G) := sup_le H.KC ((zpowers_le).2 hu)
  have hyC := hM hy
  have hwC := hM hw
  have hkK : (k : G) ∈ K := k.2
  have hkM : (k : G) ∈ K ⊔ zpowers u := Subgroup.mem_sup_left hkK
  have hy'M : (k : G) * y * (k : G)⁻¹ ∈ K ⊔ zpowers u :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hkM hy) (Subgroup.inv_mem _ hkM)
  have hy'C : (k : G) * y * (k : G)⁻¹ ∈ centralizer ({x} : Set G) := hM hy'M
  have hy'2 : orderOf ((k : G) * y * (k : G)⁻¹) = 2 := by
    rw [← hy2]
    exact (MulAut.conj (k : G)).orderOf_eq y
  have hact : act H.KN ((k : G) * y * (k : G)⁻¹) = act H.KN w := by
    rw [act_conj H.KN (hM hkM) hyC, act_of_mem_K H.KN H.KC hkK]
    exact hconj
  obtain ⟨h, hh, hhv⟩ := conj_of_same_image H.KC H.KN H.cen hu huu
    (by rw [← act_of_mem H.KN hu]; exact hout) hy'M hw hy'2 hw2 hy'C hwC
    (by rw [← act_of_mem H.KN hy'C, ← act_of_mem H.KN hwC]; exact hact)
  refine ⟨(k : G)⁻¹ * h, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkM) hh, ?_⟩
  rw [← hhv]
  group

include H in
theorem exists_K_conj_P {p z : G} (hp : p ∈ T ⊓ K) (hz : z ∈ T ⊓ K) (hp2 : orderOf p = 2)
    (hz2 : orderOf z = 2) {g₀ : MulAut (kBar K)} (hg₀ : g₀ ∈ innAut (kBar K))
    (hconj : g₀ * act H.KN z * g₀⁻¹ = act H.KN p) :
    ∃ h ∈ K, (∀ q ∈ H.Q, h * q = q * h) ∧ h⁻¹ * p * h = z := by
  obtain ⟨k, rfl⟩ := inn_exists hg₀
  have hpK : p ∈ K := hp.2
  have hzK : z ∈ K := hz.2
  rw [act_of_mem_K H.KN H.KC hpK, act_of_mem_K H.KN H.KC hzK] at hconj
  have h1 : (QuotientGroup.mk k : kBar K) * QuotientGroup.mk (⟨z, hzK⟩ : ↥K) *
      (QuotientGroup.mk k : kBar K)⁻¹ = QuotientGroup.mk (⟨p, hpK⟩ : ↥K) := by
    apply H.cen
    rw [← hconj]
    simp only [map_mul, map_inv]
  have hbar : ∃ k' ∈ K, k'⁻¹ * p * k' * z⁻¹ ∈ pPrimeCoreOf 2 K := by
    refine ⟨(k : G), k.2, ?_⟩
    have h2 : QuotientGroup.mk ((k : ↥K)⁻¹ * ⟨p, hpK⟩ * k) = (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : kBar K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h1]
      group
    have h3 : (k : ↥K)⁻¹ * ⟨p, hpK⟩ * k * (⟨z, hzK⟩ : ↥K)⁻¹ ∈ pPrimeCore 2 ↥K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, h2, QuotientGroup.mk_inv]
      group
    exact Back.Setup91.mem_pPrimeCoreOf_iff.2
      ⟨K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem k.2) hpK) k.2) (K.inv_mem hzK), h3⟩
  have hbot : IsPGroup 2 ↥H.Q := H.sylowT.isPGroup.to_inf_left
  exact Back.exists_conj_centralizing hbot
    (fun q hq k' hk' => H.KN q (H.T_le_C (H.Q_le_T hq)) k' hk')
    (fun q hq k' hk' => (U1a.mem_CMK_iff.1 hq.2).2.2.2 k' hk') hpK hzK hp2 hz2
    (fun q hq => H.P_comm_Q hp hq) (fun q hq => H.P_comm_Q hz hq) hbar

section Fields

variable {zb : MulAut (kBar K)} (hA : AutP34 H.B (act H.KN f) zb) {z : G} (hz : z ∈ T ⊓ K)
  (hzb : act H.KN z = zb)

include H hA hz hzb in
theorem field_conj_P {p : G} (hp : p ∈ T ⊓ K) (hp2 : orderOf p = 2) :
    ∃ h ∈ K, (∀ q ∈ H.Q, h * q = q * h) ∧ h⁻¹ * p * h = z := by
  have hpC := H.P_le_C hp
  have hp' : act H.KN p ∈ H.B ⊓ innAut (kBar K) := (H.mem_B_inf_inn).2 ⟨p, hp, rfl⟩
  have hpo : orderOf (act H.KN p) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpp : p * p = 1 := by
      have := pow_orderOf_eq_one p
      rwa [hp2, sq] at this
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← act_mul H.KN hpC hpC, hpp, act_one]
    · intro h1
      have : act H.KN p = act H.KN 1 := by rw [h1, act_one]
      have := H.act_inj_P hp (Subgroup.one_mem _) this
      rw [this, orderOf_one] at hp2
      omega
  obtain ⟨g₀, hg₀, hg₀p⟩ := hA.conj_z (act H.KN p) hp' hpo
  exact H.exists_K_conj_P hp hz hp2 (z_order H hA hz hzb) hg₀ (by rw [hzb]; exact hg₀p)

include H hA hz hzb in
theorem field_C {y : G} (hyT : y ∈ T) (hy2 : y * y = 1)
    (hyR : y ∈ ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f) (hyP : y ∉ T ⊓ K) :
    ∃ g ∈ centralizer ({x} : Set G), g⁻¹ * y * g ∈ (H.Q ⊔ zpowers f) ⊔ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfC : f ∈ centralizer ({x} : Set G) := H.T_le_C H.f_mem
  have hzC : z ∈ centralizer ({x} : Set G) := H.P_le_C hz
  have hyC := H.T_le_C hyT
  have hαα : act H.KN f * act H.KN f = 1 := by
    rw [← act_mul H.KN hfC hfC, H.f_sq, act_one]
  have hz2 := z_order H hA hz hzb
  have hzz := z_sq H hA hz hzb
  have hact : act H.KN y ∈ (H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN f) :=
    (H.mem_PQf_iff hyT).1 hyR
  have hcomm : ∀ a ∈ H.B ⊓ innAut (kBar K), ∀ b ∈ zpowers (act H.KN f), a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a (act H.KN f) from (H.act_f_comm_Pbar ha).symm) j).eq
  obtain ⟨a, ha, b, hb, hab⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm hact
  obtain ⟨v, hv, rfl⟩ := (H.mem_B_inf_inn).1 ha
  have hvC := H.P_le_C hv
  have hv_inv_C : v⁻¹ ∈ centralizer ({x} : Set G) := Subgroup.inv_mem _ hvC
  set u : G := v⁻¹ * y with hu
  have huT : u ∈ T := T.mul_mem (T.inv_mem hv.1) hyT
  have huC := H.T_le_C huT
  have hyu : y = v * u := by rw [hu]; group
  have hactu : act H.KN u = b := by
    rw [hu, act_mul H.KN hv_inv_C hyC, act_inv H.KN hvC, hab]
    group
  rcases mem_zpowers_of_mul_self hαα hb with hb1 | hbα
  ·
    subst hb1
    have huQ : u ∈ H.Q := (H.mem_Q).2 ⟨huT, hactu⟩
    have hvu : v * u = u * v := H.P_comm_Q hv huQ
    have hv2' : v * v = 1 := by
      have h1 : y * y = v * v * (u * u) := by
        rw [hyu]
        calc v * u * (v * u) = v * (u * v) * u := by group
          _ = v * (v * u) * u := by rw [← hvu]
          _ = v * v * (u * u) := by group
      have huuQ : u * u ∈ H.Q := Subgroup.mul_mem _ huQ huQ
      have h2 : v * v = (u * u)⁻¹ := by
        rw [hy2] at h1
        exact eq_inv_of_mul_eq_one_left h1.symm
      have h3 : act H.KN (v * v) = act H.KN 1 := by
        rw [h2, act_inv H.KN (H.T_le_C (H.Q_le_T huuQ)), H.act_Q huuQ, act_one]
        group
      exact H.act_inj_P (Subgroup.mul_mem _ hv hv) (Subgroup.one_mem _) h3
    by_cases hv1 : v = 1
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      have : y = u := by rw [hyu, hv1, one_mul]
      rw [inv_one, one_mul, mul_one, this]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left huQ)
    · have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2') hv1
      obtain ⟨h, hhK, hhQ, hhv⟩ := field_conj_P H hA hz hzb hv hv2
      refine ⟨h, H.KC hhK, ?_⟩
      have hhu : h⁻¹ * u * h = u := by
        have := hhQ u huQ
        calc h⁻¹ * u * h = h⁻¹ * (u * h) := by group
          _ = h⁻¹ * (h * u) := by rw [this]
          _ = u := by group
      have heq : h⁻¹ * y * h = z * u := by
        calc h⁻¹ * y * h = (h⁻¹ * v * h) * (h⁻¹ * u * h) := by rw [hyu]; group
          _ = z * u := by rw [hhv, hhu]
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers z))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left huQ))
  ·
    subst hbα
    have hq : f⁻¹ * u ∈ H.Q := H.fiber_mem_Q huT H.f_mem hactu
    have hqT : f⁻¹ * u ∈ T := H.Q_le_T hq
    have hufq : u = f * (f⁻¹ * u) := by group
    have huQf : u ∈ (H.Q ⊔ zpowers f) ⊔ zpowers z :=
      Subgroup.mem_sup_left (by
        rw [hufq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers f)) (Subgroup.mem_sup_left hq))
    have hvu : v * u = u * v := by
      have h1 : f * v = v * f := H.f_cent v hv
      have h2 : v * (f⁻¹ * u) = (f⁻¹ * u) * v := H.P_comm_Q hv hq
      rw [hufq]
      calc v * (f * (f⁻¹ * u)) = (v * f) * (f⁻¹ * u) := by group
        _ = (f * v) * (f⁻¹ * u) := by rw [h1]
        _ = f * (v * (f⁻¹ * u)) := by group
        _ = f * ((f⁻¹ * u) * v) := by rw [h2]
        _ = (f * (f⁻¹ * u)) * v := by group
    have h1u : y * y = v * v * (u * u) := by
      rw [hyu]
      calc v * u * (v * u) = v * (u * v) * u := by group
        _ = v * (v * u) * u := by rw [← hvu]
        _ = v * v * (u * u) := by group
    have huu_act : act H.KN (u * u) = 1 := by
      rw [act_mul H.KN huC huC, hactu, hαα]
    have huuQ : u * u ∈ H.Q := (H.mem_Q).2 ⟨T.mul_mem huT huT, huu_act⟩
    have hv2' : v * v = 1 := by
      have h2 : v * v = (u * u)⁻¹ := by
        rw [hy2] at h1u
        exact eq_inv_of_mul_eq_one_left h1u.symm
      have h3 : act H.KN (v * v) = act H.KN 1 := by
        rw [h2, act_inv H.KN (H.T_le_C (T.mul_mem huT huT)), huu_act, act_one]
        group
      exact H.act_inj_P (Subgroup.mul_mem _ hv hv) (Subgroup.one_mem _) h3
    have huu : u * u = 1 := by
      rw [hv2', one_mul] at h1u
      rw [← h1u]
      exact hy2
    have hu1 : u ≠ 1 := by
      rintro h
      have : act H.KN u = 1 := by rw [h, act_one]
      exact H.act_f_ne_one (hactu ▸ this)
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hu1
    have hout : act H.KN u ∉ innAut (kBar K) := by rw [hactu]; exact H.act_f_not_inn
    by_cases hv1 : v = 1
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      have : y = u := by rw [hyu, hv1, one_mul]
      rw [inv_one, one_mul, mul_one, this]
      exact huQf
    · have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2') hv1
      have hy1 : y ≠ 1 := fun h => hyP (h ▸ Subgroup.one_mem _)
      have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
      have hvb : act H.KN v ∈ H.B ⊓ innAut (kBar K) := (H.mem_B_inf_inn).2 ⟨v, hv, rfl⟩
      have hvo : orderOf (act H.KN v) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [sq, ← act_mul H.KN hvC hvC, hv2', act_one]
        · intro h1
          have : act H.KN v = act H.KN 1 := by rw [h1, act_one]
          have := H.act_inj_P hv (Subgroup.one_mem _) this
          exact hv1 this
      obtain ⟨g₀, hg₀, hg₀y⟩ := hA.fus_alpha (act H.KN v) hvb hvo
      have hactY : act H.KN y = act H.KN f * act H.KN v := by
        rw [hyu, act_mul H.KN hvC huC, hactu]
        exact (H.act_f_comm_Pbar hvb).symm
      have hMy : y ∈ K ⊔ zpowers u := by
        rw [hyu]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv.2) (Subgroup.mem_sup_right (mem_zpowers u))
      have hMu : u ∈ K ⊔ zpowers u := Subgroup.mem_sup_right (mem_zpowers u)
      have hMC : K ⊔ zpowers u ≤ centralizer ({x} : Set G) := sup_le H.KC ((zpowers_le).2 huC)
      rcases hg₀y with hcase | hcase
      · obtain ⟨g, hg, hgy⟩ := H.exists_conj_outer huC huu hout hMy hMu hyo hu2 hg₀
          (by rw [hactY, hcase, hactu])
        refine ⟨g, hMC hg, ?_⟩
        rw [hgy]
        exact huQf
      · have hzC' := hzC
        have hz_u : z * u = u * z := by
          have h1 : f * z = z * f := H.f_cent z hz
          have h2 : z * (f⁻¹ * u) = (f⁻¹ * u) * z := H.P_comm_Q hz hq
          rw [hufq]
          calc z * (f * (f⁻¹ * u)) = (z * f) * (f⁻¹ * u) := by group
            _ = (f * z) * (f⁻¹ * u) := by rw [h1]
            _ = f * (z * (f⁻¹ * u)) := by group
            _ = f * ((f⁻¹ * u) * z) := by rw [h2]
            _ = (f * (f⁻¹ * u)) * z := by group
        have huz2 : (u * z) * (u * z) = 1 := by
          calc u * z * (u * z) = u * (z * u) * z := by group
            _ = u * (u * z) * z := by rw [hz_u]
            _ = (u * u) * (z * z) := by group
            _ = 1 := by rw [huu, hzz, one_mul]
        have huzT : u * z ∈ T := T.mul_mem huT hz.1
        have huz1 : u * z ≠ 1 := by
          intro h
          have h1 : u = z⁻¹ := eq_inv_of_mul_eq_one_left h
          apply hout
          rw [h1, act_inv H.KN hzC, hzb]
          exact (innAut (kBar K)).inv_mem (hzb ▸ (H.mem_B_inf_inn.2 ⟨z, hz, rfl⟩).2)
        have huzo : orderOf (u * z) = 2 := orderOf_eq_prime (by rw [sq]; exact huz2) huz1
        have hMuz : u * z ∈ K ⊔ zpowers u :=
          Subgroup.mul_mem _ hMu (Subgroup.mem_sup_left hz.2)
        obtain ⟨g, hg, hgy⟩ := H.exists_conj_outer huC huu hout hMy hMuz hyo huzo hg₀
          (by rw [hactY, hcase, act_mul H.KN huC hzC, hactu, hzb])
        refine ⟨g, hMC hg, ?_⟩
        rw [hgy]
        exact Subgroup.mul_mem _ huQf (Subgroup.mem_sup_right (mem_zpowers z))

include H hA hz hzb in
theorem field_shear {w : G} (hwT : w ∈ T) (hw2 : w * w = 1)
    (hwc : ∀ a ∈ T ⊓ K, w * a = a * w) (hwQz : w ∉ H.Q ⊔ zpowers z) :
    ∃ g : G, g⁻¹ * w * g ∈ zpowers w ⊔ (T ⊓ K) ∧ g⁻¹ * w * g ≠ w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwC := H.T_le_C hwT
  have hwB : act H.KN w ∈ H.B := (H.mem_B).2 ⟨w, hwT, rfl⟩
  have hout : act H.KN w ∉ innAut (kBar K) := by
    intro hin
    have hPQ := H.mem_PQ_of_act_mem hwT ⟨hwB, hin⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := (H.mem_PQ_iff).1 hPQ
    have hpa : ∀ a ∈ T ⊓ K, p * a = a * p := by
      intro a ha
      have h1 := hwc a ha
      rw [hpq] at h1
      have h2 : p * q * a = p * a * q := by
        calc p * q * a = p * (q * a) := by group
          _ = p * (a * q) := by rw [← H.P_comm_Q ha hq]
          _ = p * a * q := by group
      have h3 : a * (p * q) = a * p * q := by group
      rw [h2, h3] at h1
      exact mul_right_cancel h1
    rcases z_unique_aux H hA hz hzb hp hpa with hp1 | hpz
    · apply hwQz
      rw [hpq, hp1, one_mul]
      exact Subgroup.mem_sup_left hq
    · apply hwQz
      rw [hpq, hpz]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers z)) (Subgroup.mem_sup_left hq)
  have hw1 : act H.KN w ≠ 1 := fun h => hout (h ▸ (innAut (kBar K)).one_mem)
  have hwo : orderOf (act H.KN w) = 2 := by
    refine orderOf_eq_prime ?_ hw1
    rw [sq, ← act_mul H.KN hwC hwC, hw2, act_one]
  have hcomm : ∀ q ∈ H.B ⊓ innAut (kBar K), act H.KN w * q = q * act H.KN w := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := (H.mem_B_inf_inn).1 hq
    rw [← act_mul H.KN hwC (H.P_le_C ha), ← act_mul H.KN (H.P_le_C ha) hwC, hwc a ha]
  obtain ⟨pb, hpb, hpbo, g₀, hg₀, hg₀w⟩ := hA.shear (act H.KN w) hwB hwo hout hcomm
  obtain ⟨p, hp, rfl⟩ := (H.mem_B_inf_inn).1 hpb
  have hpC := H.P_le_C hp
  have hp2 : p * p = 1 := by
    have h1 : act H.KN (p * p) = act H.KN 1 := by
      rw [act_mul H.KN hpC hpC, act_one]
      have := pow_orderOf_eq_one (act H.KN p)
      rwa [hpbo, sq] at this
    exact H.act_inj_P (Subgroup.mul_mem _ hp hp) (Subgroup.one_mem _) h1
  have hp1 : p ≠ 1 := by
    rintro rfl
    rw [act_one, orderOf_one] at hpbo
    omega
  have hwp : w * p = p * w := hwc p hp
  have hwp2 : (w * p) * (w * p) = 1 := by
    calc w * p * (w * p) = w * (p * w) * p := by group
      _ = w * (w * p) * p := by rw [hwp]
      _ = (w * w) * (p * p) := by group
      _ = 1 := by rw [hw2, hp2, one_mul]
  have hwp1 : w * p ≠ 1 := by
    intro h
    have h1 : w = p⁻¹ := eq_inv_of_mul_eq_one_left h
    apply hout
    rw [h1, act_inv H.KN hpC]
    exact (innAut (kBar K)).inv_mem (H.mem_B_inf_inn.2 ⟨p, hp, rfl⟩).2
  have hwpo : orderOf (w * p) = 2 := orderOf_eq_prime (by rw [sq]; exact hwp2) hwp1
  have hw1' : w ≠ 1 := fun h => hw1 (by rw [h, act_one])
  have hwo' : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1'
  have hMw : w ∈ K ⊔ zpowers w := Subgroup.mem_sup_right (mem_zpowers w)
  have hMwp : w * p ∈ K ⊔ zpowers w := Subgroup.mul_mem _ hMw (Subgroup.mem_sup_left hp.2)
  obtain ⟨g, hg, hgw⟩ := H.exists_conj_outer hwC hw2 hout hMw hMwp hwo' hwpo hg₀
    (by rw [hg₀w, act_mul H.KN hwC hpC])
  refine ⟨g, ?_, ?_⟩
  · rw [hgw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers w)) (Subgroup.mem_sup_right hp)
  · rw [hgw]
    intro h
    exact hp1 (by simpa using h)

end Fields

end Real34

end CFSG.GH74.GLS.C3.Layer1.P34Real
