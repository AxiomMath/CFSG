module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Rho
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step37
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3LinePrim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ABGLocalTools

structure Sec38Hyp (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G)
    (E F : Subgroup G) (x : G) (Zs P T Q B₀ : Subgroup G) (z y : G)
    (D J U V₀ V Q₀ : Subgroup G) : Prop where
  q0 : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀
  T_le : T ≤ centralizer (Q₀ : Set G)
  ext : IsExtraspecialPGroup 2 ↥(Q₀ ⊔ Q)
  card : Nat.card ↥(Q₀ ⊔ Q) = 2 ^ 9
  sylow : IsSylowOf 2 Q₀ (centralizer (Q : Set G))
  B₀_le : B₀ ≤ centralizer (Q₀ : Set G)
  x_not : x ∉ centralizer (Q₀ : Set G)
  B₀_perf : commutator ↥B₀ = ⊤
  B₀_simple : ∀ N : Subgroup G, N ≤ B₀ → B₀ ≤ normalizer (N : Set G) → ¬ N ≤ Q → N = B₀
  B₀_quot : Q ≤ B₀ ∧ B₀ ≤ normalizer (Q : Set G)
  B₀_card : Nat.card B₀ = 25920 * Nat.card Q

instance XSub.finite_linearEquiv {G : Type} [Group G] [Finite G] (D : XSub G) :
    Finite (D.Qt ≃ₗ[ZMod 2] D.Qt) :=
  Finite.of_injective (fun e : D.Qt ≃ₗ[ZMod 2] D.Qt => (e : D.Qt → D.Qt)) DFunLike.coe_injective

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem Q_le_centralizer : Q ≤ centralizer (Q₀ : Set G) :=
  H.q0.dData.suz.Q_le.trans H.T_le

theorem comm_Q₀_Q {a b : G} (ha : a ∈ Q₀) (hb : b ∈ Q) : a * b = b * a :=
  (mem_centralizer_iff.mp (H.Q_le_centralizer hb)) a ha

theorem z_mem_centerIn_Q : z ∈ centerIn Q := by
  rw [H.q0.dData.suz.Q_center]
  exact mem_zpowers _

theorem z_mem_centerIn_Q₀ : z ∈ centerIn Q₀ := by
  rw [H.q0.center_Q₀]
  exact H.z_mem_centerIn_Q

theorem z_mem_Q : z ∈ Q := H.z_mem_centerIn_Q.1

theorem z_mem_Q₀ : z ∈ Q₀ := H.z_mem_centerIn_Q₀.1

theorem z_ne_one : z ≠ 1 := by
  intro h
  have h1 := Sec3.card_centerIn_of_extraspecial H.q0.dData.suz.q8.1
  rw [H.q0.dData.suz.Q_center, h, zpowers_one_eq_bot, card_bot] at h1
  exact absurd h1 (by norm_num)

theorem center_sup : centerIn (Q₀ ⊔ Q) = zpowers z := by
  refine Sec3.centerIn_eq_zpowers H.ext ⟨mem_sup_right H.z_mem_Q, ?_⟩ H.z_ne_one
  have h : Q₀ ⊔ Q ≤ centralizer ({z} : Set G) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp H.z_mem_centerIn_Q₀.2) a ha))
    (fun a ha => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp H.z_mem_centerIn_Q.2) a ha))
  exact mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (h ha)

@[expose] def xsub : XSub G := ⟨Q₀ ⊔ Q, z, H.ext, H.center_sup⟩

@[simp] theorem xsub_Q₁ : H.xsub.Q₁ = Q₀ ⊔ Q := rfl

@[simp] theorem xsub_z : H.xsub.z = z := rfl

theorem Q₀_le : Q₀ ≤ H.xsub.Q₁ := le_sup_left

theorem Q_le : Q ≤ H.xsub.Q₁ := le_sup_right

theorem inf_le_zpowers : Q₀ ⊓ Q ≤ zpowers z := by
  rintro a ⟨ha₀, ha⟩
  rw [← H.q0.dData.suz.Q_center]
  exact ⟨ha, mem_centralizer_iff.mpr fun b hb => (H.comm_Q₀_Q ha₀ hb).symm⟩

theorem card_Q₀ : Nat.card Q₀ = 8 := by
  obtain ⟨e⟩ := H.q0.Q₀_iso
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem finrank_Qt : finrank (ZMod 2) H.xsub.Qt = 8 :=
  H.xsub.finrank_Qt (H.card.trans (by norm_num))

theorem finrank_W₀ : finrank (ZMod 2) (H.xsub.clSub Q₀) = 2 :=
  H.xsub.finrank_clSub H.Q₀_le H.z_mem_Q₀ (H.card_Q₀.trans (by norm_num))

theorem finrank_W' : finrank (ZMod 2) (H.xsub.clSub Q) = 6 :=
  H.xsub.finrank_clSub H.Q_le H.z_mem_Q (H.q0.dData.suz.q8.2.1.trans (by norm_num))

theorem W₀_sup_W' : H.xsub.clSub Q₀ ⊔ H.xsub.clSub Q = ⊤ := by
  rw [← H.xsub.clSub_sup H.Q₀_le H.Q_le]
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨a, ha, rfl⟩ := H.xsub.exists_cl v
  exact H.xsub.cl_mem_clSub ha ha

theorem W₀_inf_W' : H.xsub.clSub Q₀ ⊓ H.xsub.clSub Q = ⊥ :=
  H.xsub.clSub_inf_eq_bot H.Q_le H.z_mem_Q H.inf_le_zpowers

theorem polar_W₀_W' {v w : H.xsub.Qt} (hv : v ∈ H.xsub.clSub Q₀) (hw : w ∈ H.xsub.clSub Q) :
    polar H.xsub.q v w = 0 :=
  H.xsub.polar_clSub_eq_zero (fun _ ha _ hb => H.comm_Q₀_Q ha hb) hv hw

theorem W₀_aniso {v : H.xsub.Qt} (hv : v ∈ H.xsub.clSub Q₀) (hq : H.xsub.q v = 0) : v = 0 := by
  refine H.xsub.eq_zero_of_q_eq_zero (fun a ha _ ha2 => ?_) hv hq
  obtain ⟨e⟩ := H.q0.Q₀_iso
  obtain ⟨-, -, h3⟩ := Sec3.quaternion_facts
  have hz' : (⟨z, H.z_mem_Q₀⟩ : Q₀) * ⟨z, H.z_mem_Q₀⟩ = 1 := by
    have h := H.xsub.z_mul_z
    exact Subtype.ext h
  have ha' : (⟨a, ha⟩ : Q₀) * ⟨a, ha⟩ = 1 := Subtype.ext (by rw [← pow_two]; exact ha2)
  have hz1 : (⟨z, H.z_mem_Q₀⟩ : Q₀) ≠ 1 := fun h => H.z_ne_one (congrArg Subtype.val h)
  rcases h3 (e ⟨a, ha⟩) (e ⟨z, H.z_mem_Q₀⟩) (by rw [← map_mul, ha', map_one])
    (by rw [← map_mul, hz', map_one]) with h | h | h
  · rw [MulEquiv.map_eq_one_iff] at h
    have h1 : a = 1 := congrArg Subtype.val h
    rw [h1]
    exact one_mem _
  · exact absurd ((MulEquiv.map_eq_one_iff e).mp h) hz1
  · have h1 : a = z := congrArg Subtype.val (e.injective h)
    rw [h1]
    exact mem_zpowers _

theorem x_mem_centralizer_Q : x ∈ centralizer (Q : Set G) := by
  have hS := H.q0.dData.suz
  have hx : x ∈ centerIn (sec3B A₁ x) := by
    rw [hS.B_center]
    exact mem_zpowers _
  exact mem_centralizer_iff.mpr fun q hq =>
    (mem_centralizer_iff.mp hx.2) q (hS.T_le (hS.Q_le hq))

theorem mem_normalizer_sup {a : G} (h₀ : a ∈ normalizer (Q₀ : Set G))
    (h : a ∈ normalizer (Q : Set G)) : a ∈ H.xsub.N := by
  rw [mem_normalizer_iff_map_conj_eq] at h₀ h ⊢
  rw [xsub_Q₁, Subgroup.map_sup, h₀, h]

theorem x_mem_N : x ∈ H.xsub.N :=
  H.mem_normalizer_sup H.q0.x_Q₀ (centralizer_le_normalizer _ H.x_mem_centralizer_Q)

theorem B₀_le_N : B₀ ≤ H.xsub.N := fun _ hb =>
  H.mem_normalizer_sup (centralizer_le_normalizer _ (H.B₀_le hb)) (H.B₀_quot.2 hb)

noncomputable abbrev ρG : H.xsub.N →* (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) :=
  H.xsub.O.subtype.comp H.xsub.ρ

theorem ρG_cl (n : H.xsub.N) {a : G} (ha : a ∈ H.xsub.Q₁) :
    H.ρG n (H.xsub.cl a) = H.xsub.cl ((n : G) * a * (n : G)⁻¹) :=
  H.xsub.ρ_cl n ha

theorem ρx_W' {v : H.xsub.Qt} (hv : v ∈ H.xsub.clSub Q) : H.ρG ⟨x, H.x_mem_N⟩ v = v := by
  obtain ⟨a, haQ, ha, rfl⟩ := H.xsub.mem_clSub_iff.mp hv
  rw [H.ρG_cl _ ha]
  change H.xsub.cl (x * a * x⁻¹) = H.xsub.cl a
  rw [← mem_centralizer_iff.mp H.x_mem_centralizer_Q a haQ, mul_inv_cancel_right]

theorem ρB₀_W₀ {b : G} (hb : b ∈ B₀) {v : H.xsub.Qt} (hv : v ∈ H.xsub.clSub Q₀) :
    H.ρG ⟨b, H.B₀_le_N hb⟩ v = v := by
  obtain ⟨a, haQ, ha, rfl⟩ := H.xsub.mem_clSub_iff.mp hv
  rw [H.ρG_cl _ ha]
  change H.xsub.cl (b * a * b⁻¹) = H.xsub.cl a
  rw [← mem_centralizer_iff.mp (H.B₀_le hb) a haQ, mul_inv_cancel_right]

theorem centralizes_of_trivial {w : G} (hw3 : w ^ 3 = 1) (hwz : w * z = z * w)
    (h : ∀ a ∈ Q₀, (w * a * w⁻¹)⁻¹ * a ∈ zpowers z) : w ∈ centralizer (Q₀ : Set G) := by
  refine mem_centralizer_iff.mpr fun a ha => ?_
  obtain ⟨c, hcdef⟩ : ∃ c, c = (w * a * w⁻¹)⁻¹ * a := ⟨_, rfl⟩
  have hc : c ∈ zpowers z := hcdef ▸ h a ha
  have hca : w * a * w⁻¹ = a * c⁻¹ := by rw [hcdef]; group
  have hcz : c = 1 ∨ c = z := H.xsub.mem_zpowers_z_iff.mp hc
  have hcinv : c⁻¹ = c := by
    rcases hcz with h1 | h1
    · rw [h1, inv_one]
    · rw [h1]
      exact inv_eq_of_mul_eq_one_right H.xsub.z_mul_z
  rw [hcinv] at hca
  have hwc : w * c * w⁻¹ = c := by
    rcases hcz with h1 | h1
    · rw [h1]
      group
    · rw [h1, hwz, mul_inv_cancel_right]
  have hcc : c * c = 1 := by
    rcases hcz with h1 | h1
    · rw [h1, mul_one]
    · rw [h1]
      exact H.xsub.z_mul_z
  have e1 : w * (w * a * w⁻¹) * w⁻¹ = a := by
    have h3 : w * (a * c) * w⁻¹ = (w * a * w⁻¹) * (w * c * w⁻¹) := by group
    rw [hca, h3, hca, hwc, mul_assoc, hcc, mul_one]
  have e3 : (w * w * w) * a * (w * w * w)⁻¹ = a * c := by
    have h2 : (w * w * w) * a * (w * w * w)⁻¹ = w * (w * (w * a * w⁻¹) * w⁻¹) * w⁻¹ := by group
    rw [h2, e1, hca]
  have hw3' : w * w * w = 1 := by rw [← hw3, pow_three, mul_assoc]
  rw [hw3', one_mul, inv_one, mul_one] at e3
  have hc1 : c = 1 := by
    have h4 : a * c = a * 1 := by rw [← e3, mul_one]
    exact mul_left_cancel h4
  rw [hc1, mul_one] at hca
  calc a * w = w * a * w⁻¹ * w := by rw [hca]
    _ = w * a := by group

theorem x_pow_three : x ^ 3 = 1 := by
  rw [← H.q0.dData.suz.setting.order_x, pow_orderOf_eq_one]

theorem x_comm_z : x * z = z * x :=
  (mem_centralizer_iff.mp H.x_mem_centralizer_Q z H.z_mem_Q).symm

theorem ρx_W₀ : ∃ a ∈ Q₀, H.ρG ⟨x, H.x_mem_N⟩ (H.xsub.cl a) ≠ H.xsub.cl a := by
  by_contra! h
  apply H.x_not
  refine H.centralizes_of_trivial H.x_pow_three H.x_comm_z fun a ha => ?_
  have h1 := h a ha
  rw [H.ρG_cl _ (H.Q₀_le ha)] at h1
  have h2 := (H.xsub.cl_eq_cl_iff (H.xsub.conj_mem H.x_mem_N (H.Q₀_le ha)) (H.Q₀_le ha)).mp h1
  exact h2


theorem x'_pow_three : (⟨x, H.x_mem_N⟩ : H.xsub.N) ^ 3 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact H.x_pow_three)

theorem ρx_pow_three : H.ρG ⟨x, H.x_mem_N⟩ ^ 3 = 1 := by
  rw [← map_pow, H.x'_pow_three, map_one]

theorem ρx_sq_W₀ : ∃ a ∈ Q₀, (H.ρG ⟨x, H.x_mem_N⟩ ^ 2) (H.xsub.cl a) ≠ H.xsub.cl a := by
  by_contra! h
  obtain ⟨a, ha, hne⟩ := H.ρx_W₀
  apply hne
  have e : H.ρG ⟨x, H.x_mem_N⟩ = H.ρG ⟨x, H.x_mem_N⟩ ^ 2 * H.ρG ⟨x, H.x_mem_N⟩ ^ 2 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, H.ρx_pow_three, one_mul]
  rw [e, LinearEquiv.mul_apply, h a ha, h a ha]

theorem orderOf_ρx : orderOf (H.ρG ⟨x, H.x_mem_N⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime H.ρx_pow_three fun h => ?_
  obtain ⟨a, ha, hne⟩ := H.ρx_W₀
  rw [h] at hne
  exact hne rfl

omit H [Finite G] in
theorem _root_.CFSG.ComponentClassification.AS81.XSub.conj_eq_of_inner (D : XSub G) {g c : G}
    (hd : c⁻¹ * g ∈ centralizer (D.Q₁ : Set G)) {a : G} (ha : a ∈ D.Q₁) :
    g * a * g⁻¹ = c * a * c⁻¹ := by
  have h1 : a * (c⁻¹ * g) = (c⁻¹ * g) * a := mem_centralizer_iff.mp hd a ha
  calc g * a * g⁻¹ = c * ((c⁻¹ * g) * a) * (c⁻¹ * g)⁻¹ * c⁻¹ := by group
    _ = c * (a * (c⁻¹ * g)) * (c⁻¹ * g)⁻¹ * c⁻¹ := by rw [h1]
    _ = c * a * c⁻¹ := by group

omit H in
theorem _root_.CFSG.ComponentClassification.AS81.XSub.commutator_mem_centralizer (D : XSub G)
    {g₁ g₂ : D.N} (h₁ : D.ρ g₁ = 1) (h₂ : D.ρ g₂ = 1) :
    (g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹ ∈ centralizer (D.Q₁ : Set G) := by
  obtain ⟨c₁, hc₁, hd₁⟩ := (D.ρ_eq_one_iff g₁).mp h₁
  obtain ⟨c₂, hc₂, hd₂⟩ := (D.ρ_eq_one_iff g₂).mp h₂
  have flip : ∀ {g c : G}, c ∈ D.Q₁ → c⁻¹ * g ∈ centralizer (D.Q₁ : Set G) →
      c * g⁻¹ ∈ centralizer (D.Q₁ : Set G) := by
    intro g c hc hd
    have hcom : c * (c⁻¹ * g) = (c⁻¹ * g) * c := mem_centralizer_iff.mp hd c hc
    have e : c * g⁻¹ = (c⁻¹ * g)⁻¹ := by
      have h1 : g = c⁻¹ * g * c := by
        calc g = c * (c⁻¹ * g) := by group
          _ = (c⁻¹ * g) * c := hcom
          _ = c⁻¹ * g * c := by group
      have hcg : c * g = g * c := by
        calc c * g = c * (c⁻¹ * g * c) := by rw [← h1]
          _ = g * c := by group
      calc c * g⁻¹ = g⁻¹ * (g * c) * g⁻¹ := by group
        _ = g⁻¹ * (c * g) * g⁻¹ := by rw [hcg]
        _ = (c⁻¹ * g)⁻¹ := by group
    rw [e]
    exact inv_mem hd
  have hd₁' : c₁ * (g₁ : G)⁻¹ ∈ centralizer (D.Q₁ : Set G) := flip hc₁ hd₁
  have hd₂' : c₂ * (g₂ : G)⁻¹ ∈ centralizer (D.Q₁ : Set G) := flip hc₂ hd₂
  have hinv₁ : ∀ a ∈ D.Q₁, (g₁ : G)⁻¹ * a * (g₁ : G)⁻¹⁻¹ = c₁⁻¹ * a * c₁⁻¹⁻¹ := fun a ha =>
    D.conj_eq_of_inner (by rwa [inv_inv]) ha
  have hinv₂ : ∀ a ∈ D.Q₁, (g₂ : G)⁻¹ * a * (g₂ : G)⁻¹⁻¹ = c₂⁻¹ * a * c₂⁻¹⁻¹ := fun a ha =>
    D.conj_eq_of_inner (by rwa [inv_inv]) ha
  have hw : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ zpowers D.z := by
    have hm : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ D.Q₁ :=
      mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂)
    rw [← D.cl_eq_zero_iff hm, D.cl_mul (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂),
      D.cl_mul (mul_mem hc₁ hc₂) (inv_mem hc₁), D.cl_mul hc₁ hc₂, D.cl_inv hc₁, D.cl_inv hc₂]
    have e : D.cl c₁ + D.cl c₂ + D.cl c₁ + D.cl c₂ = (D.cl c₁ + D.cl c₁) + (D.cl c₂ + D.cl c₂) := by
      abel
    rw [e, ZModModule.add_self, ZModModule.add_self, add_zero]
  have hwc : ∀ a ∈ D.Q₁, a * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) = (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * a := by
    intro a ha
    rcases D.mem_zpowers_z_iff.mp hw with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact D.z_comm ha
  refine mem_centralizer_iff.mpr fun a ha => ?_
  have a1 : (g₂ : G)⁻¹ * a * (g₂ : G)⁻¹⁻¹ ∈ D.Q₁ := by
    rw [hinv₂ a ha]
    exact mul_mem (mul_mem (inv_mem hc₂) ha) (by rw [inv_inv]; exact hc₂)
  have a2 : (g₁ : G)⁻¹ * ((g₂ : G)⁻¹ * a * (g₂ : G)⁻¹⁻¹) * (g₁ : G)⁻¹⁻¹ ∈ D.Q₁ := by
    rw [hinv₁ _ a1]
    exact mul_mem (mul_mem (inv_mem hc₁) a1) (by rw [inv_inv]; exact hc₁)
  have a3 : (g₂ : G) * ((g₁ : G)⁻¹ * ((g₂ : G)⁻¹ * a * (g₂ : G)⁻¹⁻¹) * (g₁ : G)⁻¹⁻¹) *
      (g₂ : G)⁻¹ ∈ D.Q₁ := by
    rw [D.conj_eq_of_inner hd₂ a2]
    exact mul_mem (mul_mem hc₂ a2) (inv_mem hc₂)
  have key : ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹) * a *
      ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹)⁻¹ = a := by
    have e1 : ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹) * a *
        ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹)⁻¹ =
        (g₁ : G) * ((g₂ : G) * ((g₁ : G)⁻¹ * ((g₂ : G)⁻¹ * a * (g₂ : G)⁻¹⁻¹) *
          (g₁ : G)⁻¹⁻¹) * (g₂ : G)⁻¹) * (g₁ : G)⁻¹ := by group
    rw [e1, D.conj_eq_of_inner hd₁ a3, D.conj_eq_of_inner hd₂ a2, hinv₁ _ a1, hinv₂ a ha]
    have e2 : c₁ * (c₂ * (c₁⁻¹ * (c₂⁻¹ * a * c₂⁻¹⁻¹) * c₁⁻¹⁻¹) * c₂⁻¹) * c₁⁻¹ =
        (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * a * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹)⁻¹ := by group
    rw [e2, ← hwc a ha, mul_inv_cancel_right]
  calc a * ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹) =
      (((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹) * a *
        ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹)⁻¹) *
          ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹) := by rw [key]
    _ = ((g₁ : G) * g₂ * (g₁ : G)⁻¹ * (g₂ : G)⁻¹) * a := by group


theorem B₀_le_B : B₀ ≤ sec3B A₁ x := by
  rw [H.q0.dData.suz.B₀_eq]
  have h1 : ⁅sec3B A₁ x ⊓ centralizer ({z} : Set G), sec3B A₁ x ⊓ centralizer ({z} : Set G)⁆ ≤
      sec3B A₁ x ⊓ centralizer ({z} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  exact h1.trans inf_le_left

theorem B₀_comm_x {b : G} (hb : b ∈ B₀) : b * x = x * b := by
  have hx : x ∈ centerIn (sec3B A₁ x) := by
    rw [H.q0.dData.suz.B_center]
    exact mem_zpowers _
  exact mem_centralizer_iff.mp hx.2 b (H.B₀_le_B hb)

noncomputable abbrev ρB₀hom : ↥B₀ →* (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) :=
  H.ρG.comp (Subgroup.inclusion H.B₀_le_N)

noncomputable abbrev ρB₀ : Subgroup (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) := H.ρB₀hom.range

theorem ρG_eq_one_iff (n : H.xsub.N) : H.ρG n = 1 ↔ H.xsub.ρ n = 1 := by
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    change ((H.xsub.ρ n : H.xsub.O) : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) = 1
    rw [h]
    rfl

theorem mem_Q_of_ρ_eq_one {b : G} (hb : b ∈ B₀) (h : H.xsub.ρ ⟨b, H.B₀_le_N hb⟩ = 1) : b ∈ Q := by
  let K : Subgroup G :=
    { carrier := {b | ∃ hb : b ∈ B₀, H.xsub.ρ ⟨b, H.B₀_le_N hb⟩ = 1}
      mul_mem' := fun {a c} ha hc => ⟨mul_mem ha.1 hc.1, by
        rw [show (⟨a * c, H.B₀_le_N (mul_mem ha.1 hc.1)⟩ : H.xsub.N) =
          ⟨a, H.B₀_le_N ha.1⟩ * ⟨c, H.B₀_le_N hc.1⟩ from rfl, map_mul, ha.2, hc.2, one_mul]⟩
      one_mem' := ⟨one_mem _, by
        rw [show (⟨1, H.B₀_le_N (one_mem _)⟩ : H.xsub.N) = 1 from rfl, map_one]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [show (⟨a⁻¹, H.B₀_le_N (inv_mem ha.1)⟩ : H.xsub.N) = (⟨a, H.B₀_le_N ha.1⟩)⁻¹ from rfl,
          map_inv, ha.2, inv_one]⟩ }
  by_cases hKQ : K ≤ Q
  · exact hKQ ⟨hb, h⟩
  exfalso
  have hnorm : B₀ ≤ normalizer (K : Set G) := by
    intro c hc
    have key : ∀ {c : G} (hc : c ∈ B₀) {a : G}, a ∈ K → c * a * c⁻¹ ∈ K := by
      intro c hc a ha
      refine ⟨mul_mem (mul_mem hc ha.1) (inv_mem hc), ?_⟩
      rw [show (⟨c * a * c⁻¹, H.B₀_le_N (mul_mem (mul_mem hc ha.1) (inv_mem hc))⟩ : H.xsub.N) =
        ⟨c, H.B₀_le_N hc⟩ * ⟨a, H.B₀_le_N ha.1⟩ * (⟨c, H.B₀_le_N hc⟩)⁻¹ from rfl,
        map_mul, map_mul, ha.2, mul_one, map_inv, mul_inv_cancel]
    refine G2.mem_normalizer_of_conj (fun a ha => key hc ha) (fun a ha => ?_)
    have := key (inv_mem hc) ha
    rwa [inv_inv] at this
  have hKB : K = B₀ := H.B₀_simple K (fun a ha => ha.1) hnorm hKQ
  have hall : ∀ c (hc : c ∈ B₀), H.xsub.ρ ⟨c, H.B₀_le_N hc⟩ = 1 := by
    intro c hc
    have hcK : c ∈ K := hKB ▸ hc
    exact hcK.2
  have hB₀C : B₀ ≤ centralizer (H.xsub.Q₁ : Set G) := by
    have e : ⁅B₀, B₀⁆ = B₀ := by
      rw [← Subgroup.map_subtype_commutator, H.B₀_perf, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hc : ⁅B₀, B₀⁆ ≤ centralizer (H.xsub.Q₁ : Set G) := by
      rw [Subgroup.commutator_le]
      intro c₁ hc₁ c₂ hc₂
      rw [commutatorElement_def]
      exact H.xsub.commutator_mem_centralizer (g₁ := ⟨c₁, H.B₀_le_N hc₁⟩)
        (g₂ := ⟨c₂, H.B₀_le_N hc₂⟩) (hall c₁ hc₁) (hall c₂ hc₂)
    calc B₀ = ⁅B₀, B₀⁆ := e.symm
      _ ≤ centralizer (H.xsub.Q₁ : Set G) := hc
  have hab : commutator ↥Q = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (mem_centralizer_iff.mp (hB₀C (H.B₀_quot.1 b.2)) a (H.Q_le a.2))
  have h2 := H.q0.dData.suz.q8.1.2.2.2
  rw [← H.q0.dData.suz.q8.1.2.1, hab, card_bot] at h2
  exact absurd h2 (by norm_num)

theorem ker_ρB₀hom : H.ρB₀hom.ker = Q.subgroupOf B₀ := by
  ext b
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    exact H.mem_Q_of_ρ_eq_one b.2 ((H.ρG_eq_one_iff _).mp h)
  · intro hb
    exact (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem (H.Q_le hb))

theorem card_ρB₀ : Nat.card H.ρB₀ = 25920 := by
  have h := Subgroup.card_ker_mul_card_range H.ρB₀hom
  rw [H.ker_ρB₀hom, Nat.card_congr (subgroupOfEquivOfLe H.B₀_quot.1).toEquiv, H.B₀_card] at h
  have hQ : 0 < Nat.card Q := Nat.card_pos
  rw [mul_comm 25920] at h
  exact Nat.eq_of_mul_eq_mul_left hQ h

noncomputable abbrev ρX : Subgroup (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) :=
  zpowers (H.ρG ⟨x, H.x_mem_N⟩)

theorem card_ρX : Nat.card H.ρX = 3 := by
  rw [Nat.card_zpowers, H.orderOf_ρx]

theorem ρB₀_le_centralizer : H.ρB₀ ≤ centralizer (H.ρX : Set _) := by
  rintro _ ⟨b, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  have hc : Commute (H.ρG ⟨x, H.x_mem_N⟩) (H.ρB₀hom b) := by
    show H.ρG ⟨x, H.x_mem_N⟩ * H.ρG ⟨b, H.B₀_le_N b.2⟩ =
      H.ρG ⟨b, H.B₀_le_N b.2⟩ * H.ρG ⟨x, H.x_mem_N⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (H.B₀_comm_x b.2).symm
  exact (hc.zpow_left k).eq

theorem ρX_inf_ρB₀ : H.ρX ⊓ H.ρB₀ = ⊥ := by
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨hyX, hyB⟩ := mem_inf.mp hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hyX
  obtain ⟨b, hb⟩ := hyB
  have htriv : ∀ a ∈ Q₀, (H.ρG ⟨x, H.x_mem_N⟩ ^ k) (H.xsub.cl a) = H.xsub.cl a := by
    intro a ha
    rw [← hb]
    exact H.ρB₀_W₀ b.2 (H.xsub.cl_mem_clSub ha (H.Q₀_le ha))
  rw [← zpow_mod_orderOf, H.orderOf_ρx] at htriv ⊢
  have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h0 | h1 | h2
  · rw [h0, zpow_zero]
    exact one_mem _
  · rw [h1, zpow_one] at htriv
    obtain ⟨a, ha, hne⟩ := H.ρx_W₀
    exact absurd (htriv a ha) hne
  · rw [h2, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast] at htriv
    obtain ⟨a, ha, hne⟩ := H.ρx_sq_W₀
    exact absurd (htriv a ha) hne

noncomputable abbrev K₀ : Subgroup (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) := H.ρX ⊔ H.ρB₀

theorem card_K₀ : Nat.card H.K₀ = 77760 := by
  have h := card_sup_mul_card_inf (H := H.ρX) (R := H.ρB₀)
    (H.ρB₀_le_centralizer.trans (centralizer_le_normalizer _))
  rw [H.ρX_inf_ρB₀, card_bot, mul_one, H.card_ρX, H.card_ρB₀] at h
  rw [h]

theorem K₀_le_range : H.K₀ ≤ H.ρG.range := by
  refine sup_le ?_ ?_
  · rw [zpowers_le]
    exact ⟨_, rfl⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨_, rfl⟩

theorem K₀_le_O : H.K₀ ≤ H.xsub.O := by
  refine H.K₀_le_range.trans ?_
  rintro _ ⟨n, rfl⟩
  exact (H.xsub.ρ n).2

theorem isPlusType : CFSG.GroupTheory.WeirSylow.IsPlusType H.xsub.q := by
  by_contra hplus
  have : Module.Finite (ZMod 2) H.xsub.Qt := Module.Finite.of_finite
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
    H.xsub.q_nondegenerate (m := 3) (by rw [H.finrank_Qt]) (ε := -1) (Or.inr ⟨rfl, hplus⟩)
  have hprod : ∏ i ∈ Finset.Icc 1 3, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1) = 2835 := by
    rw [Nat.card_zmod]
    decide
  rw [hprod, Nat.card_zmod] at h
  have h1 : (Nat.card H.xsub.O : ℤ) = 394813440 := by rw [h]; norm_num
  have hdvd := Subgroup.card_dvd_of_le H.K₀_le_O
  rw [H.card_K₀] at hdvd
  have h' : Nat.card H.xsub.O = 394813440 := by exact_mod_cast h1
  rw [h'] at hdvd
  exact absurd hdvd (by norm_num)

omit H in
theorem dickson_trivial_of_pow_three {y : Multiplicative (ZMod 2)} (h : y ^ 3 = 1) : y = 1 := by
  have h2 : y ^ 2 = 1 := by
    induction y using Multiplicative.rec with
    | ofAdd a =>
      rw [← ofAdd_nsmul, two_nsmul, ZModModule.add_self, ofAdd_zero]
  calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
    _ = 1 := by rw [h, h2, inv_one, mul_one]

theorem ρX_le_omega : H.ρX ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  rw [zpowers_le]
  have h3 : dicksonHom H.xsub.q H.xsub.q_nondegenerate (H.xsub.ρ ⟨x, H.x_mem_N⟩) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, H.x'_pow_three, map_one, map_one]
  have h1 := dickson_trivial_of_pow_three h3
  have hk : H.xsub.ρ ⟨x, H.x_mem_N⟩ ∈ (dicksonHom H.xsub.q H.xsub.q_nondegenerate).ker := h1
  rw [dicksonHom_ker, mem_subgroupOf] at hk
  exact hk

theorem ρB₀_le_omega : H.ρB₀ ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  rintro _ ⟨b, rfl⟩
  let f : ↥B₀ →* Multiplicative (ZMod 2) :=
    (dicksonHom H.xsub.q H.xsub.q_nondegenerate).comp
      (H.xsub.ρ.comp (Subgroup.inclusion H.B₀_le_N))
  have hk : b ∈ f.ker := by
    have h1 := Abelianization.commutator_subset_ker f
    rw [H.B₀_perf] at h1
    exact h1 (mem_top b)
  have hk' : H.xsub.ρ (Subgroup.inclusion H.B₀_le_N b) ∈
      (dicksonHom H.xsub.q H.xsub.q_nondegenerate).ker := hk
  rw [dicksonHom_ker, mem_subgroupOf] at hk'
  exact hk'

theorem K₀_le_omega : H.K₀ ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate :=
  sup_le H.ρX_le_omega H.ρB₀_le_omega

@[expose] def glStab (W : Submodule (ZMod 2) H.xsub.Qt) :
    Subgroup (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) where
  carrier := {g | W.map (g : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = W}
  one_mem' := MinusLines.map_one_linearEquiv W
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [MinusLines.map_mul_linearEquiv, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← MinusLines.map_mul_linearEquiv, inv_mul_cancel, MinusLines.map_one_linearEquiv]

theorem mem_glStab {W : Submodule (ZMod 2) H.xsub.Qt} {g : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt} :
    g ∈ H.glStab W ↔ W.map (g : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = W := Iff.rfl

theorem ρG_mem_glStab {n : H.xsub.N} (hn : (n : G) ∈ normalizer (Q₀ : Set G)) :
    H.ρG n ∈ H.glStab (H.xsub.clSub Q₀) := by
  rw [mem_glStab]
  have h := H.xsub.map_ρ_clSub n Q₀
  have h2 : Q₀.map (MulAut.conj (n : G)).toMonoidHom = Q₀ := mem_normalizer_iff_map_conj_eq.mp hn
  rw [h2] at h
  exact h

theorem K₀_le_glStab : H.K₀ ≤ H.glStab (H.xsub.clSub Q₀) := by
  refine sup_le ?_ ?_
  · rw [zpowers_le]
    exact H.ρG_mem_glStab H.q0.x_Q₀
  · rintro _ ⟨b, rfl⟩
    exact H.ρG_mem_glStab (centralizer_le_normalizer _ (H.B₀_le b.2))

end Sec38Hyp

end CFSG.ComponentClassification.AS81
