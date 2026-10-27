module

public import CFSG.CGT.T75H.SylowData
import CFSG.Adapters.Involutions
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.CGT.T75H.Split

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

section Generic

theorem exists_unique_involution_sq {C : Subgroup G} {e : ℕ} (ϕ : QuaternionGroup (2 ^ e) ≃* C) :
    ∃ z c : G, z ∈ C ∧ c ∈ C ∧ c * c = z ∧ z ≠ 1 ∧ z * z = 1 ∧
      ∀ x ∈ C, x * x = 1 → x = 1 ∨ x = z := by
  have : NeZero (2 ^ e) := ⟨pow_ne_zero e two_ne_zero⟩
  obtain ⟨q, hq⟩ : ∃ q : QuaternionGroup (2 ^ e), q = QuaternionGroup.xa 0 := ⟨_, rfl⟩
  have hq4 : orderOf q = 4 := by rw [hq]; exact QuaternionGroup.orderOf_xa 0
  have hq4' : q * q * (q * q) = 1 := by
    have := pow_orderOf_eq_one q
    rw [hq4] at this
    calc q * q * (q * q) = q ^ 2 * q ^ 2 := by rw [sq]
      _ = q ^ 4 := by rw [← pow_add]
      _ = 1 := this
  have hqq : q * q ≠ 1 := fun h => by
    have h2 : q ^ 2 = 1 := by rw [sq]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hq4] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
  refine ⟨((ϕ (q * q) : C) : G), ((ϕ q : C) : G), (ϕ (q * q)).2, (ϕ q).2, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul]
  · intro h
    exact hqq (ϕ.injective (by rw [map_one]; exact Subtype.ext h))
  · have h1 : (ϕ (q * q) : C) * ϕ (q * q) = 1 := by rw [← map_mul, hq4', map_one]
    simpa using congrArg Subtype.val h1
  · intro x hx hxx
    obtain ⟨p, hp⟩ := ϕ.surjective ⟨x, hx⟩
    have hpp : p * p = 1 := by
      apply ϕ.injective
      rw [map_mul, hp, map_one]
      exact Subtype.ext hxx
    by_cases hp1 : p = 1
    · left
      rw [hp1, map_one] at hp
      exact (congrArg Subtype.val hp).symm
    · right
      have hord : orderOf p = 2 := orderOf_eq_prime (by rw [sq]; exact hpp) hp1
      have hpa := CFSG.BrauerSuzuki.Helpers.quat_unique_order_two hord
      have hqa : q * q = QuaternionGroup.a ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e)) := by
        rw [hq, ← sq]; exact QuaternionGroup.xa_sq 0
      have hpq : p = q * q := by rw [hqa]; exact hpa
      rw [hpq] at hp
      exact (congrArg Subtype.val hp).symm

theorem false_of_weakClosed_involution [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {z : G} (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzC : z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (hwc : ∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z) : False := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G z hz1 hzz
    (fun g hcomm => CFSG.Adapters.isolated_of_weakClosure S hzC hzz hwc g hcomm)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hzcen : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hN g
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : g * z * g⁻¹ = z := by
        calc g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
          _ = z := by rw [h1, one_mul]
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [h2]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · rw [hc, Subgroup.mem_bot] at hzcen
      exact hz1 hzcen
    · obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  · rw [htop, Subgroup.card_top] at hNodd
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
    have h2 : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    obtain ⟨k, hk⟩ := hNodd
    omega

theorem conj_mem_centralizer {n c : G} (hn : n ∈ Subgroup.normalizer (T : Set G))
    (hc : c ∈ Subgroup.centralizer (T : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro t ht
  have ht' : n⁻¹ * t * n ∈ T := by
    have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hn) ht
    simpa using this
  have h1 := hc _ ht'
  calc t * (n * c * n⁻¹) = n * ((n⁻¹ * t * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * t * n)) * n⁻¹ := by rw [h1]
    _ = (n * c * n⁻¹) * t := by group

theorem isConj_mul_of_comm {x w z : G} (hxz : x * z = z * x) :
    IsConj (w * z) ((x * w * x⁻¹) * z) := by
  refine isConj_iff.2 ⟨x, ?_⟩
  calc x * (w * z) * x⁻¹ = x * w * x⁻¹ * (x * z * x⁻¹) := by group
    _ = x * w * x⁻¹ * z := by rw [hxz]; group

end Generic

namespace D8Data

variable {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)

include D

theorem hb1 : b ≠ 1 := fun h => D.hbL (by rw [h]; exact (normIn T T₁).one_mem)

theorem eq_of_mul_self_eq_one {d : G} (hd : d ∈ sStar T T₁) (hdd : d * d = 1) :
    d = 1 ∨ d = a ∨ d = b ∨ d = b * a ∨ d = ℓ ∨ d = ℓ * a := by
  by_cases hdT : d ∈ T
  · rcases D.hT d hdT with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases D.invol_class hd hdd hdT with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem mem_of_comm_b {d : G} (hd : d ∈ sStar T T₁) (hdb : d * b = b * d) : d ∈ T := by
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨u, hu, t, ht, hdu⟩ := exists_mul_of_mem_sup_normIn hL₁N hd
  rcases D.hL₁ u hu with hu1 | hu1
  · rw [hdu, hu1, one_mul]
    exact ht
  · exfalso
    rw [hdu, hu1] at hdb
    have hbt : t * b = b * t := elemAbelian_mul_comm D.sec3.cfg.wc.1 ht D.hb
    have h2 : ℓ * b * t = b * ℓ * t := by
      calc ℓ * b * t = ℓ * (b * t) := by group
        _ = ℓ * (t * b) := by rw [hbt]
        _ = ℓ * t * b := by group
        _ = b * (ℓ * t) := hdb
        _ = b * ℓ * t := by group
    have h3 : ℓ * b = b * ℓ := mul_right_cancel h2
    rcases D.cent_ℓ D.hb h3.symm with h4 | h4
    · exact D.hbL (by rw [h4]; exact (normIn T T₁).one_mem)
    · exact D.hbL (by rw [h4]; exact D.ha)

theorem mul_self_eq_one_of_comm_b {d : G} (hd : d ∈ sStar T T₁) (hdb : d * b = b * d) :
    d * d = 1 :=
  elemAbelian_mul_self D.sec3.cfg.wc.1 (D.mem_of_comm_b hd hdb)

theorem comm_a_sStar {d : G} (hd : d ∈ sStar T T₁) : d * a = a * d := by
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨u, hu, t, ht, rfl⟩ := exists_mul_of_mem_sup_normIn hL₁N hd
  have hta : t * a = a * t := elemAbelian_mul_comm D.sec3.cfg.wc.1 ht D.haT
  have hua : u * a = a * u := by
    rcases D.hL₁ u hu with h | h
    · rw [h]; simp
    · rw [h]; exact D.comm_aℓ.symm
  calc u * t * a = u * (t * a) := by group
    _ = u * (a * t) := by rw [hta]
    _ = (u * a) * t := by group
    _ = (a * u) * t := by rw [hua]
    _ = a * (u * t) := by group

theorem conj_y_a : y * a * y = ℓ * a := by
  have h1 := D.conj_a_y
  calc y * a * y = y * (a * y * a) * a := by
        calc y * a * y = y * a * y * (a * a) := by rw [D.aa, mul_one]
          _ = y * (a * y * a) * a := by group
    _ = y * (y * ℓ) * a := by rw [h1]
    _ = (y * y) * ℓ * a := by group
    _ = ℓ * a := by rw [D.yy, one_mul]

variable {S : Sylow 2 G}

theorem mul_self_mem_Cbar (hS : SylowData T T₁ S) {u : G} (hu : u ∈ (S : Subgroup G))
    (huT : ∀ t ∈ T, t * u = u * t) : u * u ∈ Cbar T T₁ S := by
  obtain ⟨d, hd, c, hc, rfl⟩ := D.exists_split hS.norm hS.le hS.sStar_norm u hu
  have hcb : b * c = c * b := (mem_Cbar_iff.1 hc).2.1 b D.hb
  have hdb : d * b = b * d := by
    have h1 := huT b D.hb
    have h2 : d * b * c = b * d * c := by
      calc d * b * c = d * (b * c) := by group
        _ = d * (c * b) := by rw [hcb]
        _ = (d * c) * b := by group
        _ = b * (d * c) := h1.symm
        _ = b * d * c := by group
    exact mul_right_cancel h2
  have hdd := D.mul_self_eq_one_of_comm_b hd hdb
  have hdc : d * c = c * d := comm_sStar_Cbar hd hc
  have h3 : (d * c) * (d * c) = c * c := by
    calc (d * c) * (d * c) = d * (c * d) * c := by group
      _ = d * (d * c) * c := by rw [hdc]
      _ = (d * d) * (c * c) := by group
      _ = c * c := by rw [hdd, one_mul]
  rw [h3]
  exact (Cbar T T₁ S).mul_mem hc hc

end D8Data

structure QuatPair (T T₁ : Subgroup G) (S : Sylow 2 G) (z c₀ : G) : Prop where
  z_mem : z ∈ Cbar T T₁ S
  c_mem : c₀ ∈ Cbar T T₁ S
  sq : c₀ * c₀ = z
  ne_one : z ≠ 1
  mul_self : z * z = 1
  uniq : ∀ x ∈ Cbar T T₁ S, x * x = 1 → x = 1 ∨ x = z

namespace QuatPair

variable {S : Sylow 2 G} {z c₀ : G} (Q : QuatPair T T₁ S z c₀)

include Q

theorem comm_cbar {c : G} (hc : c ∈ Cbar T T₁ S) : c * z = z * c := by
  have hw : c * z * c⁻¹ ∈ Cbar T T₁ S :=
    (Cbar T T₁ S).mul_mem ((Cbar T T₁ S).mul_mem hc Q.z_mem) ((Cbar T T₁ S).inv_mem hc)
  have hww : (c * z * c⁻¹) * (c * z * c⁻¹) = 1 := by
    calc (c * z * c⁻¹) * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [Q.mul_self]; group
  rcases Q.uniq _ hw hww with h | h
  · exfalso
    apply Q.ne_one
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · calc c * z = (c * z * c⁻¹) * c := by group
      _ = z * c := by rw [h]

theorem comm_S {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) (hS : SylowData T T₁ S) {s : G}
    (hs : s ∈ (S : Subgroup G)) : s * z = z * s := by
  obtain ⟨d, hd, c, hc, rfl⟩ := D.exists_split hS.norm hS.le hS.sStar_norm s hs
  calc d * c * z = d * (c * z) := by group
    _ = d * (z * c) := by rw [Q.comm_cbar hc]
    _ = (d * z) * c := by group
    _ = (z * d) * c := by rw [comm_sStar_Cbar hd Q.z_mem]
    _ = z * (d * c) := by group

theorem comm_S_az {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) (hS : SylowData T T₁ S) {s : G}
    (hs : s ∈ (S : Subgroup G)) : s * (a * z) = (a * z) * s := by
  obtain ⟨d, hd, c, hc, rfl⟩ := D.exists_split hS.norm hS.le hS.sStar_norm s hs
  have hca : a * c = c * a := (mem_Cbar_iff.1 hc).2.1 a D.haT
  have hdz := Q.comm_S D hS hs
  have hda : d * a = a * d := D.comm_a_sStar hd
  calc d * c * (a * z) = d * (c * a) * z := by group
    _ = d * (a * c) * z := by rw [hca]
    _ = (d * a) * c * z := by group
    _ = (a * d) * c * z := by rw [hda]
    _ = a * (d * c * z) := by group
    _ = a * (z * (d * c)) := by rw [hdz]
    _ = (a * z) * (d * c) := by group

end QuatPair

section Main

variable [Finite G] {ℓ a b y z c₀ : G} {S : Sylow 2 G}

omit [Finite G] in
theorem sStar_conj_invol (D : D8Data T T₁ ℓ a b y) (hconj : ∃ x : G, T₁ = conjSubgroup x T)
    (hS : SylowData T T₁ S) {n : G} (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    {x : G} (hx : x ∈ sStar T T₁) (hxx : x * x = 1) : n⁻¹ * x * n ∈ sStar T T₁ := by
  by_cases hx1 : x = 1
  · rw [hx1]
    simp
  · have hxD : x ∈ classD T := D.mem_classD_of_invol hx hxx hx1 hconj
    have hxS : x ∈ (S : Subgroup G) := hS.le hx
    have hnS : n⁻¹ * x * n ∈ (S : Subgroup G) := (Subgroup.mem_normalizer_iff''.1 hn x).1 hxS
    exact hS.dS _ hnS (classD_conj hxD n)

theorem not_isConj_z_az (D : D8Data T T₁ ℓ a b y) (hconj : ∃ x : G, T₁ = conjSubgroup x T)
    (hS : SylowData T T₁ S) (Q : QuatPair T T₁ S z c₀) : ¬ IsConj z (a * z) := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  have hzC : z ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun s hs => Q.comm_S D hS hs
  have haC : a * z ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun s hs => Q.comm_S_az D hS hs
  obtain ⟨n, hn, hnz⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer z g⁻¹ hzC
    (by rw [inv_inv, hg]; exact haC)
  have hnz' : n⁻¹ * z * n = a * z := by rw [← hnz, inv_inv, hg]
  have hnS : ∀ x ∈ (S : Subgroup G), n⁻¹ * x * n ∈ (S : Subgroup G) := fun x hx =>
    (Subgroup.mem_normalizer_iff''.1 hn x).1 hx
  have hc₀S : c₀ ∈ (S : Subgroup G) := (mem_Cbar_iff.1 Q.c_mem).1
  obtain ⟨w, hw⟩ : ∃ w : G, w = n⁻¹ * c₀ * n := ⟨_, rfl⟩
  have hwS : w ∈ (S : Subgroup G) := by rw [hw]; exact hnS c₀ hc₀S
  have hww : w * w = a * z := by
    calc w * w = n⁻¹ * (c₀ * c₀) * n := by rw [hw]; group
      _ = n⁻¹ * z * n := by rw [Q.sq]
      _ = a * z := hnz'
  have hb' : n * b * n⁻¹ ∈ sStar T T₁ := by
    have hn' : n⁻¹ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      (Subgroup.normalizer ((S : Subgroup G) : Set G)).inv_mem hn
    have := sStar_conj_invol D hconj hS hn' (le_sStar_left D.hb) D.bb
    simpa using this
  have hcb' : (n * b * n⁻¹) * c₀ = c₀ * (n * b * n⁻¹) := comm_sStar_Cbar hb' Q.c_mem
  have hwb : w * b = b * w := by
    calc w * b = n⁻¹ * (c₀ * (n * b * n⁻¹)) * n := by rw [hw]; group
      _ = n⁻¹ * ((n * b * n⁻¹) * c₀) * n := by rw [hcb']
      _ = b * w := by rw [hw]; group
  obtain ⟨d, hd, c', hc', hwdc⟩ := D.exists_split hS.norm hS.le hS.sStar_norm w hwS
  have hc'b : b * c' = c' * b := (mem_Cbar_iff.1 hc').2.1 b D.hb
  have hdb : d * b = b * d := by
    have h2 : d * b * c' = b * d * c' := by
      calc d * b * c' = d * (b * c') := by group
        _ = d * (c' * b) := by rw [hc'b]
        _ = (d * c') * b := by group
        _ = w * b := by rw [← hwdc]
        _ = b * w := hwb
        _ = b * (d * c') := by rw [hwdc]
        _ = b * d * c' := by group
    exact mul_right_cancel h2
  have hdd : d * d = 1 := D.mul_self_eq_one_of_comm_b hd hdb
  have hdc : d * c' = c' * d := comm_sStar_Cbar hd hc'
  have hw2 : w * w = c' * c' := by
    rw [hwdc]
    calc d * c' * (d * c') = d * (c' * d) * c' := by group
      _ = d * (d * c') * c' := by rw [hdc]
      _ = (d * d) * (c' * c') := by group
      _ = c' * c' := by rw [hdd, one_mul]
  have haC' : a ∈ Cbar T T₁ S := by
    have h1 : a * z = c' * c' := hww.symm.trans hw2
    have h2 : a = c' * c' * z⁻¹ := by rw [← h1]; group
    rw [h2]
    exact (Cbar T T₁ S).mul_mem ((Cbar T T₁ S).mul_mem hc' hc') ((Cbar T T₁ S).inv_mem Q.z_mem)
  have hmem : a ∈ sStar T T₁ ⊓ Cbar T T₁ S := ⟨le_sStar_left D.haT, haC'⟩
  rw [D.sStar_inf_Cbar, Subgroup.mem_bot] at hmem
  exact D.ha1 hmem

theorem exists_conj_fix_z (D : D8Data T T₁ ℓ a b y)
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    (hS : SylowData T T₁ S) (Q : QuatPair T T₁ S z c₀) :
    ∃ h₁ : G, h₁ * a * h₁⁻¹ = b ∧ h₁ * z * h₁⁻¹ = z := by
  obtain ⟨h, hhH, hh⟩ := h57 a D.haT D.ha1 b D.hb D.hb1
  have hhN : h ∈ Subgroup.normalizer (T : Set G) :=
    hSub_le_normalizer (fun w hw => (mem_normIn.1 hw).2) hhH
  have hSle : (S : Subgroup G) ≤ Subgroup.normalizer (T : Set G) := fun s hs => hS.norm s hs
  have hSN : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup G) (Subgroup.normalizer (T : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hSle, S.isPGroup', fun hd =>
      S.not_dvd_index (hd.trans (Subgroup.relIndex_dvd_index_of_le hSle))⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Sylow 2 G, S' = h • S := ⟨_, rfl⟩
  have hmem : ∀ x : G, x ∈ (S' : Subgroup G) ↔ h⁻¹ * x * h ∈ (S : Subgroup G) := by
    intro x
    rw [hS', Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  have hS'le : (S' : Subgroup G) ≤ Subgroup.normalizer (T : Set G) := by
    intro x hx
    have hx' := hSle ((hmem x).1 hx)
    have := (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hhN hx')
      ((Subgroup.normalizer (T : Set G)).inv_mem hhN)
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [e] at this
  have hS'N : CFSG.ABGLocalTools.IsSylowOf 2 (S' : Subgroup G) (Subgroup.normalizer (T : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hS'le, S'.isPGroup', fun hd =>
      S'.not_dvd_index (hd.trans (Subgroup.relIndex_dvd_index_of_le hS'le))⟩
  have hKN : Subgroup.centralizer (T : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer (T : Set G)
  have hNK : Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => conj_mem_centralizer hn hc, fun hc => ?_⟩
    have := conj_mem_centralizer ((Subgroup.normalizer (T : Set G)).inv_mem hn) hc
    have e : n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c := by group
    rwa [e] at this
  have hP₀ := hSN.inf_of_le_normalizer hKN hNK
  have hP₁ := hS'N.inf_of_le_normalizer hKN hNK
  obtain ⟨k, hkK, hk⟩ := hP₀.exists_mem_conj hP₁
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : G, h₁ = k⁻¹ * h := ⟨_, rfl⟩
  refine ⟨h₁, ?_, ?_⟩
  · have hbk : b * k = k * b := (Subgroup.mem_centralizer_iff.1 hkK) b D.hb
    calc h₁ * a * h₁⁻¹ = k⁻¹ * (h * a * h⁻¹) * k := by rw [hh₁]; group
      _ = k⁻¹ * (b * k) := by rw [hh]; group
      _ = k⁻¹ * (k * b) := by rw [hbk]
      _ = b := by group
  · have hnorm : ∀ u ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G),
        h₁ * u * h₁⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) := by
      intro u hu
      have hu' : h * u * h⁻¹ ∈ (S' : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) := by
        refine ⟨(hmem _).2 ?_, conj_mem_centralizer hhN hu.2⟩
        have e : h⁻¹ * (h * u * h⁻¹) * h = u := by group
        rw [e]
        exact hu.1
      have := (hk _).1 hu'
      have e : k⁻¹ * (h * u * h⁻¹) * k = h₁ * u * h₁⁻¹ := by rw [hh₁]; group
      rwa [e] at this
    have hc₀ : c₀ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) :=
      ⟨(mem_Cbar_iff.1 Q.c_mem).1,
        Subgroup.mem_centralizer_iff.2 fun t ht => (mem_Cbar_iff.1 Q.c_mem).2.1 t ht⟩
    have hu := hnorm c₀ hc₀
    have hsq := D.mul_self_mem_Cbar hS hu.1
      (fun t ht => (Subgroup.mem_centralizer_iff.1 hu.2) t ht)
    have hu2 : (h₁ * c₀ * h₁⁻¹) * (h₁ * c₀ * h₁⁻¹) = h₁ * z * h₁⁻¹ := by
      calc (h₁ * c₀ * h₁⁻¹) * (h₁ * c₀ * h₁⁻¹) = h₁ * (c₀ * c₀) * h₁⁻¹ := by group
        _ = h₁ * z * h₁⁻¹ := by rw [Q.sq]
    rw [hu2] at hsq
    have hzz' : (h₁ * z * h₁⁻¹) * (h₁ * z * h₁⁻¹) = 1 := by
      calc (h₁ * z * h₁⁻¹) * (h₁ * z * h₁⁻¹) = h₁ * (z * z) * h₁⁻¹ := by group
        _ = 1 := by rw [Q.mul_self]; group
    rcases Q.uniq _ hsq hzz' with h1 | h1
    · exfalso
      apply Q.ne_one
      calc z = h₁⁻¹ * (h₁ * z * h₁⁻¹) * h₁ := by group
        _ = 1 := by rw [h1]; group
    · exact h1

theorem isConj_az (D : D8Data T T₁ ℓ a b y)
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    (hS : SylowData T T₁ S) (Q : QuatPair T T₁ S z c₀) {d : G}
    (hd : d = a ∨ d = b ∨ d = b * a ∨ d = ℓ ∨ d = ℓ * a) : IsConj (a * z) (d * z) := by
  have hzy : y * z = z * y := (mem_Cbar_iff.1 Q.z_mem).2.2 y D.hy
  have hzb : b * z = z * b := (mem_Cbar_iff.1 Q.z_mem).2.1 b D.hb
  have hzℓ : ℓ * z = z * ℓ := comm_sStar_Cbar (normIn_le_sStar D.hℓ) Q.z_mem
  have h1 : IsConj (a * z) (ℓ * a * z) := by
    have := isConj_mul_of_comm (w := a) hzy
    rwa [D.inv_y, D.conj_y_a] at this
  have h2 : IsConj (ℓ * z) (ℓ * a * z) := by
    have := isConj_mul_of_comm (w := ℓ) hzb
    rwa [D.inv_b, D.conj_ℓ_b] at this
  have h3 : IsConj (b * z) (b * a * z) := by
    have := isConj_mul_of_comm (w := b) hzℓ
    rwa [D.inv_ℓ, D.conj_b_ℓ] at this
  have h4 : IsConj (a * z) (b * z) := by
    obtain ⟨h₁, hh₁a, hh₁z⟩ := exists_conj_fix_z D h57 hS Q
    refine isConj_iff.2 ⟨h₁, ?_⟩
    calc h₁ * (a * z) * h₁⁻¹ = (h₁ * a * h₁⁻¹) * (h₁ * z * h₁⁻¹) := by group
      _ = b * z := by rw [hh₁a, hh₁z]
  rcases hd with h | h | h | h | h
  · rw [h]
  · rw [h]
    exact h4
  · rw [h]
    exact h4.trans h3
  · rw [h]
    exact h1.trans h2.symm
  · rw [h]
    exact h1

theorem weakClosed (D : D8Data T T₁ ℓ a b y) (hconj : ∃ x : G, T₁ = conjSubgroup x T)
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    (hS : SylowData T T₁ S) (Q : QuatPair T T₁ S z c₀) {g : G}
    (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g⁻¹ * z * g = z := by
  obtain ⟨d, hd, c', hc', hdc⟩ := D.exists_split hS.norm hS.le hS.sStar_norm _ hg
  have hcomm : d * c' = c' * d := comm_sStar_Cbar hd hc'
  have hww : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [Q.mul_self]; group
  have hsq : (d * d) * (c' * c') = 1 := by
    calc (d * d) * (c' * c') = d * (d * c') * c' := by group
      _ = d * (c' * d) * c' := by rw [hcomm]
      _ = (d * c') * (d * c') := by group
      _ = 1 := by rw [← hdc]; exact hww
  have hdd : d * d = 1 := by
    have hmem : d * d ∈ sStar T T₁ ⊓ Cbar T T₁ S := by
      refine ⟨(sStar T T₁).mul_mem hd hd, ?_⟩
      have : d * d = (c' * c')⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact (Cbar T T₁ S).inv_mem ((Cbar T T₁ S).mul_mem hc' hc')
    rw [D.sStar_inf_Cbar, Subgroup.mem_bot] at hmem
    exact hmem
  have hcc : c' * c' = 1 := by
    rw [hdd, one_mul] at hsq
    exact hsq
  have hz1 := Q.ne_one
  have hzS : z ∈ (S : Subgroup G) := (mem_Cbar_iff.1 Q.z_mem).1
  rcases Q.uniq c' hc' hcc with h1 | h1
  · exfalso
    rw [h1, mul_one] at hdc
    have hd1 : d ≠ 1 := fun h => hz1 (by
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [hdc, h]; group)
    have hdD : d ∈ classD T := D.mem_classD_of_invol hd hdd hd1 hconj
    have hzD : z ∈ classD T := by
      have := classD_conj hdD g⁻¹
      rw [← hdc] at this
      have e : g⁻¹⁻¹ * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rwa [e] at this
    have hzs : z ∈ sStar T T₁ := hS.dS z hzS hzD
    have hmem : z ∈ sStar T T₁ ⊓ Cbar T T₁ S := ⟨hzs, Q.z_mem⟩
    rw [D.sStar_inf_Cbar, Subgroup.mem_bot] at hmem
    exact hz1 hmem
  · rw [h1] at hdc
    by_cases hd1 : d = 1
    · rw [hdc, hd1, one_mul]
    · exfalso
      have hdcases : d = a ∨ d = b ∨ d = b * a ∨ d = ℓ ∨ d = ℓ * a := by
        rcases D.eq_of_mul_self_eq_one hd hdd with h | h
        · exact absurd h hd1
        · exact h
      have hzd : IsConj z (d * z) := isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hdc⟩
      have haz : IsConj z (a * z) := hzd.trans (isConj_az D h57 hS Q hdcases).symm
      exact not_isConj_z_az D hconj hS Q haz

end Main

theorem false_of_quaternion_cbar [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    (hconj : ∃ x : G, T₁ = conjSubgroup x T) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    {S : Sylow 2 G} (hS : SylowData T T₁ S) {e : ℕ}
    (ϕ : QuaternionGroup (2 ^ e) ≃* ↥(Cbar T T₁ S)) : False := by
  obtain ⟨z, c₀, hz, hc, hsq, hz1, hzz, huniq⟩ := exists_unique_involution_sq ϕ
  have Q : QuatPair T T₁ S z c₀ := ⟨hz, hc, hsq, hz1, hzz, huniq⟩
  refine false_of_weakClosed_involution hna S hz1 hzz ?_
    fun g hg => weakClosed D hconj h57 hS Q hg
  rw [Subgroup.mem_centralizer_iff]
  exact fun s hs => Q.comm_S D hS hs

end CFSG.CGT.T75H
