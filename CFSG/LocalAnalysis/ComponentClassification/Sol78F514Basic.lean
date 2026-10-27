module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512A
public import CFSG.Goldschmidt75.Sig31Main

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_inv_mem_conjugate {K : Subgroup G} {g x : G} (hx : x ∈ K) :
    g⁻¹ * x * g ∈ conjugate K g :=
  mem_conjugate_iff.mpr (by rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group])

structure Hyp (L₀ L Q S T : Subgroup G) (z t s : G) {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
    (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) (Lin : Subgroup (MulAut 𝕊)) : Prop where
  sec5 : Sec5 G L₀ L Q S T z t
  autData : Foote5AutData 𝕊 Lin
  sT : s ∈ T
  sS : s ∉ S
  hz : z = s⁻¹ * t * s
  cardT : Nat.card T = 2 * Nat.card S
  centT : ∀ y ∈ T, y * t = t * y → y ∈ S
  nonab : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a
  QQs : Q ⊓ conjugate Q s = ⊥
  e8 : ∃ E : Subgroup G, E ≤ S ∧ T ≤ normalizer (E : Set G) ∧ (∀ e ∈ E, e * e = 1) ∧
    Nat.card E = 8 ∧ t ∈ E ∧ s⁻¹ * t * s ∈ E
  l511 : conjugate (S ⊓ L) s ≤ Q
  l512 : ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ S
  l513 : ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ S ⊓ L ∨ g⁻¹ * z * g ∈ conjugate (S ⊓ L) s ∨
    (actG L ε (g⁻¹ * z * g) ∈ Lin ∧ actG L ε (g⁻¹ * z * g) ∉ innAut5 𝕊)

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem s_mem_normalizer : s ∈ normalizer (S : Set G) :=
  mem_normalizer_of_card_eq_two_mul H.sec5.ST H.cardT H.sT

theorem mul_self_s_mem : s * s ∈ S :=
  mul_mem_of_card_eq_two_mul H.sec5.ST H.cardT H.sT H.sT H.sS H.sS

theorem z_mul_t : z * t = t * z := H.sec5.tZ z H.sec5.zS_mem

theorem mul_self_z : z * z = 1 := by rw [← sq, ← H.sec5.z2, pow_orderOf_eq_one]

theorem mul_self_t : t * t = 1 := by rw [← sq, ← H.sec5.t2, pow_orderOf_eq_one]

theorem conj_s_z : s * z * s⁻¹ = t := by rw [H.hz]; group

theorem conj_s_inv_z : s⁻¹ * z * s = t := by
  have h1 : (s * s) * t = t * (s * s) := H.sec5.tZ _ H.mul_self_s_mem
  rw [H.hz]
  calc s⁻¹ * (s⁻¹ * t * s) * s = (s * s)⁻¹ * (t * (s * s)) := by group
    _ = (s * s)⁻¹ * ((s * s) * t) := by rw [h1]
    _ = t := by group

theorem conj_s_t : s * t * s⁻¹ = z := by
  rw [← H.conj_s_inv_z]; group

theorem conj_s_inv_t : s⁻¹ * t * s = z := H.hz.symm

theorem z_ne_one : z ≠ 1 := fun h1 => by
  have h2 := H.sec5.z2
  rw [h1, orderOf_one] at h2
  omega

theorem t_ne_one : t ≠ 1 := fun h1 => by
  have h2 := H.sec5.t2
  rw [h1, orderOf_one] at h2
  omega

theorem d_mul_self : z * t * (z * t) = 1 := by
  calc z * t * (z * t) = z * (t * z) * t := by group
    _ = z * (z * t) * t := by rw [H.z_mul_t]
    _ = (z * z) * (t * t) := by group
    _ = 1 := by rw [H.mul_self_z, H.mul_self_t, one_mul]

theorem commute_d_of_mem_S {x : G} (hx : x ∈ S) : x * (z * t) = z * t * x := by
  have h1 := H.sec5.zS x hx
  have h2 := H.sec5.tZ x hx
  calc x * (z * t) = (x * z) * t := by group
    _ = z * (x * t) := by rw [h1]; group
    _ = z * t * x := by rw [h2]; group

theorem conj_s_inv_d : s⁻¹ * (z * t) * s = z * t := by
  calc s⁻¹ * (z * t) * s = (s⁻¹ * z * s) * (s⁻¹ * t * s) := by group
    _ = t * z := by rw [H.conj_s_inv_z, H.conj_s_inv_t]
    _ = z * t := H.z_mul_t.symm

theorem mul_s_mem_of_not_mem {x : G} (hxT : x ∈ T) (hxS : x ∉ S) : x * s ∈ S :=
  mul_mem_of_card_eq_two_mul H.sec5.ST H.cardT hxT H.sT hxS H.sS

theorem commute_d_of_mem_T {x : G} (hx : x ∈ T) : x * (z * t) = z * t * x :=
  H.sec5.zt_commute_T H.cardT H.sT H.sS H.hz hx

theorem T_le_centralizer_d : T ≤ centralizer ({z * t} : Set G) := fun _ hx =>
  mem_centralizer_singleton_iff.mpr (H.commute_d_of_mem_T hx)

theorem Rs_le_S : conjugate (S ⊓ L) s ≤ S :=
  conjugate_le_of_mem_normalizer H.s_mem_normalizer inf_le_left

theorem z_mem_Rs : z ∈ conjugate (S ⊓ L) s :=
  mem_conjugate_iff.mpr (by rw [H.conj_s_z]; exact H.sec5.tR)

theorem commute_R_Rs {a b : G} (ha : a ∈ S ⊓ L) (hb : b ∈ conjugate (S ⊓ L) s) :
    a * b = b * a :=
  (H.sec5.commute_Q_R (H.l511 hb) ha).symm

theorem R_inf_Rs : S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ Q ⊓ L := mem_inf.mpr ⟨H.l511 (mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).2⟩
  rwa [H.sec5.Q_inf_L] at h1

theorem R_le_centralizer_Rs : S ⊓ L ≤ centralizer ((conjugate (S ⊓ L) s : Subgroup G) : Set G) :=
  fun _ ha => mem_centralizer_iff.mpr fun _ hb => (H.commute_R_Rs ha hb).symm

theorem conj_s_mem_Rs {x : G} (hx : x ∈ S ⊓ L) : s * x * s⁻¹ ∈ conjugate (S ⊓ L) s := by
  rw [mem_conjugate_iff]
  have h1 := H.sec5.conj_mem_R H.mul_self_s_mem hx
  rwa [show s * s * x * (s * s)⁻¹ = s * (s * x * s⁻¹) * s⁻¹ by group] at h1

theorem R_le_conjugate_Q : S ⊓ L ≤ conjugate Q s := fun _ hx =>
  mem_conjugate_iff.mpr (H.l511 (H.conj_s_mem_Rs hx))

theorem S_le_normalizer_Rs : S ≤ normalizer ((conjugate (S ⊓ L) s : Subgroup G) : Set G) := by
  intro y hy
  have hy' : s * y * s⁻¹ ∈ S := by
    have := conj_mem_of_mem_normalizer (inv_mem H.s_mem_normalizer) hy
    rwa [inv_inv] at this
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [mem_conjugate_iff] at hx ⊢
    have h1 := H.sec5.conj_mem_R hy' hx
    rwa [show s * y * s⁻¹ * (s * x * s⁻¹) * (s * y * s⁻¹)⁻¹ = s * (y * x * y⁻¹) * s⁻¹ by
      group] at h1
  · rw [mem_conjugate_iff] at hx ⊢
    have h1 := H.sec5.conj_mem_R (inv_mem hy') hx
    rwa [show (s * y * s⁻¹)⁻¹ * (s * (y * x * y⁻¹) * s⁻¹) * (s * y * s⁻¹)⁻¹⁻¹ =
      s * x * s⁻¹ by group] at h1

theorem eq_of_mul_eq {a b a' b' : G} (ha : a ∈ S ⊓ L) (ha' : a' ∈ S ⊓ L)
    (hb : b ∈ conjugate (S ⊓ L) s) (hb' : b' ∈ conjugate (S ⊓ L) s) (he : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [he]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s :=
    mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [H.R_inf_Rs, mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at he
  exact mul_left_cancel he

theorem exists_mul_of_mem_sup {x : G} (hx : x ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s)
    (hx2 : x * x = 1) :
    ∃ a ∈ S ⊓ L, ∃ b ∈ conjugate (S ⊓ L) s, x = a * b ∧ a * a = 1 ∧ b * b = 1 :=
  CFSG.Goldschmidt75.exists_mul_of_mul_self H.R_le_centralizer_Rs H.R_inf_Rs hx hx2

theorem exists_conj_of_mem_Q {b : G} (hbQ : b ∈ Q) {r : G} (hr : r ∈ S ⊓ L)
    (hr2 : orderOf r = 2) (hrb : r * b = b * r) :
    ∃ k ∈ L, k * b = b * k ∧ k⁻¹ * r * k = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := H.sec5.quotient_simple.1
  have hW : IsPGroup 2 (zpowers b) := (H.sec5.isPGroup_Q.to_le (zpowers_le_of_mem hbQ))
  have hWC : zpowers b ≤ coreActionKernel L := (zpowers_le_of_mem hbQ).trans H.sec5.Q_le
  have hcen : ∀ {u : G}, u * b = b * u → u ∈ centralizer ((zpowers b : Subgroup G) : Set G) := by
    intro u hu
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (Commute.symm hu) k)).eq
  have htb : t * b = b * t := (H.sec5.commute_Q_R hbQ H.sec5.tR).symm
  obtain ⟨k, hkL, hkC, hk⟩ := exists_conj_of_involutions H.sec5.quotient_nonabelian
    H.sec5.hasDihedralSylowTwo_quotient hW hWC (mem_inf.mp hr).2 H.sec5.tL hr2 H.sec5.t2
    (hcen hrb) (hcen htb)
  refine ⟨k, hkL, ?_, hk⟩
  exact (mem_centralizer_iff.mp hkC b (mem_zpowers b)).symm

theorem exists_conj_diag {a b : G} (ha : a ∈ S ⊓ L) (hb : b ∈ conjugate (S ⊓ L) s)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : ∃ g : G, g⁻¹ * (a * b) * g = z * t := by
  obtain ⟨k, -, hkb, hk⟩ := H.exists_conj_of_mem_Q (H.l511 hb) ha ha2 (H.commute_R_Rs ha hb)
  have h1 : k⁻¹ * (a * b) * k = t * b := by
    calc k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
      _ = t * b := by rw [hk, show k⁻¹ * b * k = b by rw [mul_assoc, ← hkb]; group]
  set b' := s * b * s⁻¹ with hb'
  have hb'R : b' ∈ S ⊓ L := mem_conjugate_iff.mp hb
  have hb'2 : orderOf b' = 2 := by
    rw [hb', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hb2]
  have h2 : s * (t * b) * s⁻¹ = z * b' := by
    calc s * (t * b) * s⁻¹ = (s * t * s⁻¹) * (s * b * s⁻¹) := by group
      _ = z * b' := by rw [H.conj_s_t]
  have hzb' : b' * z = z * b' := (H.sec5.commute_Q_R H.sec5.zQ hb'R).symm
  obtain ⟨k', -, hk'z, hk'⟩ := H.exists_conj_of_mem_Q H.sec5.zQ hb'R hb'2 hzb'
  have h3 : k'⁻¹ * (z * b') * k' = z * t := by
    calc k'⁻¹ * (z * b') * k' = (k'⁻¹ * z * k') * (k'⁻¹ * b' * k') := by group
      _ = z * t := by rw [hk', show k'⁻¹ * z * k' = z by rw [mul_assoc, ← hk'z]; group]
  refine ⟨k * s⁻¹ * k', ?_⟩
  calc (k * s⁻¹ * k')⁻¹ * (a * b) * (k * s⁻¹ * k') =
      k'⁻¹ * (s * (k⁻¹ * (a * b) * k) * s⁻¹) * k' := by group
    _ = z * t := by rw [h1, h2, h3]

theorem isSylowOf_S_centralizer_z : IsSylowOf 2 S (centralizer ({z} : Set G)) :=
  H.sec5.sylS.of_le H.sec5.S_le_centralizer H.sec5.centralizer_le_normalizer

theorem conj_z_ne_d (g : G) : g⁻¹ * z * g ≠ z * t :=
  H.sec5.conj_z_ne_zt H.cardT H.sT H.sS H.hz g

theorem conj_z_mem_R_or_Rs {g : G} (hg : g⁻¹ * z * g ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s) :
    g⁻¹ * z * g ∈ S ⊓ L ∨ g⁻¹ * z * g ∈ conjugate (S ⊓ L) s :=
  H.sec5.mem_R_or_mem_Rs_of_conj H.nonab H.cardT H.sT H.sS H.hz H.l511 hg

theorem conj_z_eq_of_mem_sup {x : G} (hx : x ∈ centralizer ({z * t} : Set G))
    (hzx : x⁻¹ * z * x ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s) : x⁻¹ * z * x = z ∨ x⁻¹ * z * x = t := by
  have hxd : x⁻¹ * (z * t) * x = z * t := by
    have h1 := mem_centralizer_singleton_iff.mp hx
    calc x⁻¹ * (z * t) * x = x⁻¹ * (x * (z * t)) := by rw [h1]; group
      _ = z * t := by group
  have hdsup : z * t ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s := by
    rw [H.z_mul_t]
    exact mul_mem (mem_sup_left H.sec5.tR) (mem_sup_right H.z_mem_Rs)
  have htx : x⁻¹ * t * x = (x⁻¹ * z * x) * (z * t) := by
    calc x⁻¹ * t * x = (x⁻¹ * z * x) * (x⁻¹ * (z * t) * x) := by
          rw [show (x⁻¹ * z * x) * (x⁻¹ * (z * t) * x) = x⁻¹ * (z * z) * t * x by group,
            H.mul_self_z, mul_one]
      _ = (x⁻¹ * z * x) * (z * t) := by rw [hxd]
  have htsup : x⁻¹ * t * x ∈ S ⊓ L ⊔ conjugate (S ⊓ L) s := htx ▸ mul_mem hzx hdsup
  have htx' : x⁻¹ * t * x = (s * x)⁻¹ * z * (s * x) := by
    rw [show (s * x)⁻¹ * z * (s * x) = x⁻¹ * (s⁻¹ * z * s) * x by group, H.conj_s_inv_z]
  have htRR := H.conj_z_mem_R_or_Rs (g := s * x) (htx' ▸ htsup)
  rw [← htx'] at htRR
  have hzRR := H.conj_z_mem_R_or_Rs hzx
  have hd : z * t = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by
    rw [← hxd]; group
  rcases hzRR with hz1 | hz1 <;> rcases htRR with ht1 | ht1
  · exfalso
    have h1 : z ∈ S ⊓ L := by
      have h2 : z * t ∈ S ⊓ L := hd ▸ mul_mem hz1 ht1
      have h3 := mul_mem h2 H.sec5.tR
      rwa [mul_assoc, H.mul_self_t, mul_one] at h3
    have h4 : z ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr ⟨h1, H.z_mem_Rs⟩
    rw [H.R_inf_Rs, mem_bot] at h4
    exact H.z_ne_one h4
  · right
    have h1 : t * z = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by rw [← H.z_mul_t, hd]
    exact (H.eq_of_mul_eq H.sec5.tR hz1 H.z_mem_Rs ht1 h1).1.symm
  · left
    have h1 : t * z = (x⁻¹ * t * x) * (x⁻¹ * z * x) := by
      rw [← H.z_mul_t, hd, H.commute_R_Rs ht1 hz1]
    exact (H.eq_of_mul_eq H.sec5.tR ht1 H.z_mem_Rs hz1 h1).2.symm
  · exfalso
    have h1 : t ∈ conjugate (S ⊓ L) s := by
      have h2 : z * t ∈ conjugate (S ⊓ L) s := hd ▸ mul_mem hz1 ht1
      have h3 := mul_mem (H.z_mem_Rs) h2
      rwa [← mul_assoc, H.mul_self_z, one_mul] at h3
    have h4 : t ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr ⟨H.sec5.tR, h1⟩
    rw [H.R_inf_Rs, mem_bot] at h4
    exact H.t_ne_one h4

end Hyp

end CFSG.ComponentClassification.Sol78.F514
