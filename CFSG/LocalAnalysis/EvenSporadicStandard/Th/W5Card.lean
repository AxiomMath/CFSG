module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem natCard_sup_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    (hi : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hK : K ≤ centralizer (H : Set G) := fun k hk =>
    mem_centralizer_iff.2 fun h hh => hc h hh k hk
  let f : H × K → ↥(H ⊔ K) := fun p => ⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨h, hh⟩, ⟨k, hk⟩⟩ ⟨⟨h', hh'⟩, ⟨k', hk'⟩⟩ hEq
      simp only [f, Subtype.mk.injEq] at hEq
      have h1 : h'⁻¹ * h = k' * k⁻¹ := by
        calc h'⁻¹ * h = h'⁻¹ * (h * k) * k⁻¹ := by group
          _ = h'⁻¹ * (h' * k') * k⁻¹ := by rw [hEq]
          _ = k' * k⁻¹ := by group
      have hmem : h'⁻¹ * h ∈ H ⊓ K :=
        ⟨H.mul_mem (H.inv_mem hh') hh, by rw [h1]; exact K.mul_mem hk' (K.inv_mem hk)⟩
      rw [hi, mem_bot] at hmem
      have hh_eq : h = h' := (inv_mul_eq_one.1 hmem).symm
      subst hh_eq
      have : k = k' := mul_left_cancel hEq
      subst this
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := exists_mul_of_mem_sup hK hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

variable {L R : Subgroup G} {t : G} {S A B : Subgroup G} {z : G}

@[expose] def Bp (A : Subgroup G) (t : G) : Subgroup G :=
  centralizer (A : Set G) ⊓ normalizer ((W5 A t : Subgroup G) : Set G)

@[expose] def theta (t r : G) : G := r * t * r⁻¹ * t⁻¹

omit [Finite G] in
theorem centralizer_W5_le_Bp (A : Subgroup G) (t : G) :
    centralizer ((W5 A t : Subgroup G) : Set G) ≤ Bp A t := fun r hr => by
  refine ⟨mem_centralizer_iff.2 fun x hx => mem_centralizer_iff.1 hr x (mem_sup_left hx),
    mem_normalizer_iff.2 fun h => ?_⟩
  have hc := mem_centralizer_iff.1 hr
  constructor
  · intro hh
    have : r * h * r⁻¹ = h := by
      rw [← hc h hh]
      group
    rwa [this]
  · intro hh
    have h1 := hc (r * h * r⁻¹) hh
    have h2 : h = r * h * r⁻¹ := by
      apply mul_left_cancel (a := r)
      calc r * h = r * h * r⁻¹ * r := by group
        _ = r * (r * h * r⁻¹) := h1
    rwa [h2]

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.centralizer_W5_eq :
    centralizer ((W5 A t : Subgroup G) : Set G) = B ⊔ zpowers t := by
  ext y
  rw [H.mem_centralizer_W5_iff W]
  constructor
  · rintro ⟨b, hb, k, rfl⟩
    exact mul_mem (mem_sup_left hb) (mem_sup_right (zpow_mem (mem_zpowers t) k))
  · intro hy
    have hc : zpowers t ≤ centralizer (B : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun b hb => (H.comm_of_mem_L (W.B_le hb)).symm
    obtain ⟨b, hb, r, hr, rfl⟩ := exists_mul_of_mem_sup hc hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact ⟨b, hb, k, rfl⟩

theorem ThCyc.natCard_centralizer_W5 :
    Nat.card (centralizer ((W5 A t : Subgroup G) : Set G)) = 2 * Nat.card B := by
  have ht1 : t ≠ 1 := by
    intro h1
    have := H.order_two
    rw [h1, orderOf_one] at this
    omega
  rw [H.centralizer_W5_eq W, natCard_sup_of_commute, Nat.card_zpowers, H.order_two, mul_comm]
  · intro b hb k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((show Commute b t from (H.comm_of_mem_L (W.B_le hb)).symm).zpow_right j).eq
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxB, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
    rcases zpow_eq_one_or_self H.sq_t k with h | h
    · rw [h]
      exact one_mem _
    · exfalso
      rw [h] at hxB
      have : t ∈ L ⊓ R := ⟨W.B_le hxB, H.mem⟩
      rw [disjoint_iff.1 H.disjoint, mem_bot] at this
      exact ht1 this

theorem ThCyc.theta_mem_A {r : G} (hr : r ∈ Bp A t) : theta t r ∈ A := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  have hrt : r * t * r⁻¹ ∈ W5 A t :=
    (mem_normalizer_iff.1 hr.2 t).1 (mem_sup_right (mem_zpowers t))
  rcases (H.mem_W5_iff hA).1 hrt with h | ⟨a', ha', h⟩
  · exfalso
    apply H.not_conj_mem r⁻¹
    simpa using hA h
  · have : theta t r = a' := by
      rw [theta, h]
      group
    rw [this]
    exact ha'

theorem ThCyc.theta_mul {r r' : G} (hr : r ∈ Bp A t) (hr' : r' ∈ Bp A t) :
    theta t (r * r') = theta t r * theta t r' := by
  have h1 : r * theta t r' * r⁻¹ = theta t r' := by
    have hc := mem_centralizer_iff.1 hr.1 _ (H.theta_mem_A W hr')
    calc r * theta t r' * r⁻¹ = (r * theta t r' * r⁻¹) := rfl
      _ = theta t r' := by rw [← hc]; group
  have h2 : theta t r' * theta t r = theta t r * theta t r' := W.A_comm _ (H.theta_mem_A W hr')
    _ (H.theta_mem_A W hr)
  calc theta t (r * r') = r * (r' * t * r'⁻¹ * t⁻¹) * t * r⁻¹ * t⁻¹ := by
        simp only [theta]
        group
    _ = r * (theta t r' * t) * r⁻¹ * t⁻¹ := by
        simp only [theta]
        group
    _ = (r * theta t r' * r⁻¹) * (r * t * r⁻¹ * t⁻¹) := by group
    _ = theta t r' * theta t r := by rw [h1]; rfl
    _ = theta t r * theta t r' := h2

theorem ThCyc.theta_eq_one_iff {r : G} (hr : r ∈ Bp A t) :
    theta t r = 1 ↔ r ∈ centralizer ((W5 A t : Subgroup G) : Set G) := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  constructor
  · intro h1
    have hrt : r * t = t * r := by
      have : r * t * r⁻¹ * t⁻¹ = 1 := h1
      calc r * t = r * t * r⁻¹ * t⁻¹ * t * r := by group
        _ = t * r := by rw [this]; group
    refine mem_centralizer_iff.2 fun w hw => ?_
    have hrA := mem_centralizer_iff.1 hr.1
    rcases (H.mem_W5_iff hA).1 hw with h | ⟨a, ha, rfl⟩
    · exact hrA w h
    · calc a * t * r = a * (t * r) := by rw [mul_assoc]
        _ = a * (r * t) := by rw [hrt]
        _ = (a * r) * t := by rw [mul_assoc]
        _ = (r * a) * t := by rw [hrA a ha]
        _ = r * (a * t) := by rw [mul_assoc]
  · intro hr'
    have := mem_centralizer_iff.1 hr' t (mem_sup_right (mem_zpowers t))
    simp only [theta]
    calc r * t * r⁻¹ * t⁻¹ = (r * t) * r⁻¹ * t⁻¹ := rfl
      _ = (t * r) * r⁻¹ * t⁻¹ := by rw [← this]
      _ = 1 := by group

@[expose] noncomputable def thetaHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z) :
    ↥(Bp A t) →* ↥A :=
  MonoidHom.mk' (fun r => ⟨theta t r, H.theta_mem_A W r.2⟩)
    (fun r r' => Subtype.ext (H.theta_mul W r.2 r'.2))

theorem ThCyc.ker_thetaHom :
    (thetaHom H W).ker = (centralizer ((W5 A t : Subgroup G) : Set G)).subgroupOf (Bp A t) := by
  ext r
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  have := H.theta_eq_one_iff W r.2
  constructor
  · intro h
    exact this.1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (this.2 h)

theorem ThCyc.thetaHom_surjective : Function.Surjective (thetaHom H W) := by
  rintro ⟨a, ha⟩
  obtain ⟨P, g, -, -, hgn, -, hgt⟩ := H.exists_fusing_z W
  have hgS := H.normalizes_S W hgn hgt
  obtain ⟨r, hrN, hrt, hrA⟩ := H.exists_translation W hgt hgS ha
  have hrB : r ∈ Bp A t := by
    refine ⟨mem_centralizer_iff.2 fun x hx => ?_, hrN⟩
    have := hrA x hx
    calc x * r = (r * x * r⁻¹) * r := by rw [this]
      _ = r * x := by group
  refine ⟨⟨r, hrB⟩, Subtype.ext ?_⟩
  simp only [thetaHom, MonoidHom.mk'_apply, theta]
  rw [hrt]
  group

theorem ThCyc.natCard_Bp :
    Nat.card (Bp A t) = 2 * Nat.card B * Nat.card A := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (thetaHom H W).ker
  have h2 : Nat.card (↥(Bp A t) ⧸ (thetaHom H W).ker) = Nat.card A := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (thetaHom H W)).toEquiv]
    have : (thetaHom H W).range = ⊤ := MonoidHom.range_eq_top.2 (H.thetaHom_surjective W)
    rw [this]
    exact Nat.card_congr (Subgroup.topEquiv.toEquiv.trans (Equiv.refl _))
  have h3 : Nat.card (thetaHom H W).ker = 2 * Nat.card B := by
    rw [H.ker_thetaHom W, ← H.natCard_centralizer_W5 W]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centralizer_W5_le_Bp A t)).toEquiv
  rw [h1, h2, h3, mul_comm]

end

end CFSG.EvenSporadicStandard.ThStd
