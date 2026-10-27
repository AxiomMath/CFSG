module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutE1Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

namespace OutData

variable (D : OutData L z t T₁ F tb)

include D in
theorem zpowers_le_cent_lift : zpowers z ≤ centralizer (liftSub F : Set G) :=
  zpowers_le.2 (mem_centralizer_iff.2 fun _ ha => D.cfg.z_comm_of_mem_A (liftSub_le F ha))

include D in
theorem T_normalizes_E1 {y : centralizer ({z} : Set G)} (hy : y ∈ T₁) {e : G}
    (he : e ∈ (liftSub F ⊔ zpowers z : Subgroup G)) :
    (y : G) * e * (y : G)⁻¹ ∈ (liftSub F ⊔ zpowers z : Subgroup G) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer D.zpowers_le_cent_lift he
  have hyb : (y : G) * b = b * y := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_right (show Commute (y : G) z from
      mem_centralizer_singleton_iff.1 y.2) k)).eq
  have : (y : G) * (a * b) * (y : G)⁻¹ = ((y : G) * a * (y : G)⁻¹) * b := by
    calc (y : G) * (a * b) * (y : G)⁻¹ = (y : G) * a * ((y : G)⁻¹ * ((y : G) * b) * (y : G)⁻¹ *
        (y : G)) * (y : G)⁻¹ := by group
      _ = (y : G) * a * ((y : G)⁻¹ * (b * y) * (y : G)⁻¹ * (y : G)) * (y : G)⁻¹ := by rw [hyb]
      _ = ((y : G) * a * (y : G)⁻¹) * b := by group
  rw [this]
  exact Subgroup.mul_mem _ (mem_sup_left (D.T₁_normalizes_lift hy ha)) (mem_sup_right hb)


include D in
theorem E1_sq (hFsq : ∀ a ∈ F, a * a = 1) :
    ∀ a ∈ (liftSub F ⊔ zpowers z : Subgroup G), a * a = 1 := by
  intro a ha
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    D.zpowers_le_cent_lift ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha₂
  have hz1 : Commute z a₁ := (D.cfg.z_comm_of_mem_A (liftSub_le F ha₁)).symm
  have h2 : a₁ * a₁ = 1 := D.liftSub_sq hFsq a₁ ha₁
  have hzz : z ^ k * z ^ k = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact D.cfg.z_sq
    rw [this, one_zpow]
  have hc : Commute a₁ (z ^ k) := hz1.symm.zpow_right k
  have h3 := hc.mul_pow 2
  rw [pow_two, pow_two, pow_two] at h3
  rw [h3, h2, hzz, mul_one]

section Main

variable [Finite G]

include D in
theorem normalizes_E1 {x : G}
    (hx : x ∈ normalizer ((T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) : Set G))
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t)
    (hF : Nat.card F = 16) (hFsq : ∀ a ∈ F, a * a = 1) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) :
    (liftSub F ⊔ zpowers z : Subgroup G).map (MulAut.conj x).toMonoidHom =
      liftSub F ⊔ zpowers z := by
  classical
  set T : Subgroup G := T₁.map (centralizer ({z} : Set G)).subtype with hT
  set E1 : Subgroup G := liftSub F ⊔ zpowers z with hE1
  set E : Subgroup G := E1.map (MulAut.conj x).toMonoidHom with hE
  have hmemE : ∀ y, y ∈ E ↔ x⁻¹ * y * x ∈ E1 := fun y => by
    rw [hE, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hxT : ∀ y, y ∈ T ↔ x * y * x⁻¹ ∈ T := fun y => Subgroup.mem_normalizer_iff.1 hx y
  have hxT' : ∀ y, y ∈ T ↔ x⁻¹ * y * x ∈ T := fun y => by
    have := hxT (x⁻¹ * y * x)
    rw [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at this
    exact this.symm
  have hTmem : ∀ y : G, y ∈ T → ∃ h : y ∈ centralizer ({z} : Set G),
      (⟨y, h⟩ : centralizer ({z} : Set G)) ∈ T₁ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  have hzT : z ∈ T := D.cfg.z_mem
  have hE1T : E1 ≤ T := by
    refine sup_le (fun g hg => ?_) (zpowers_le.2 hzT)
    obtain ⟨h, hh⟩ := D.liftSub_le_T₁ g hg
    exact ⟨_, hh, rfl⟩
  have hET : E ≤ T := fun y hy => (hxT' y).2 (hE1T ((hmemE y).1 hy))
  have hEH : E ≤ centralizer ({z} : Set G) := fun y hy => D.cfg.T_le (hET hy)
  have htE1 : t ∈ E1 := by
    obtain ⟨t', ht', rfl⟩ := D.tlift
    exact mem_sup_left (mem_liftSub.2 ⟨t', rfl, ht' ▸ D.W.t_mem⟩)
  have hzE : z ∈ E := by
    rw [hmemE]
    have h2 : x * (z * t) * x⁻¹ = z := by
      calc x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
        _ = (z * t) * t := by rw [hxz, hxt]
        _ = z := by rw [mul_assoc, D.cfg.t_sq, mul_one]
    have h1 : x⁻¹ * z * x = z * t := by
      calc x⁻¹ * z * x = x⁻¹ * (x * (z * t) * x⁻¹) * x := by rw [h2]
        _ = z * t := by group
    rw [h1]
    exact Subgroup.mul_mem _ (mem_sup_right (mem_zpowers z)) htE1
  have hEnorm : ∀ y ∈ T, ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro y hy e he
    rw [hmemE] at he ⊢
    obtain ⟨h, hh⟩ := hTmem _ ((hxT' y).1 hy)
    have h1 := D.T_normalizes_E1 hh he
    have e1 : x⁻¹ * (y * e * y⁻¹) * x =
        (x⁻¹ * y * x) * (x⁻¹ * e * x) * (x⁻¹ * y * x)⁻¹ := by group
    rw [e1]
    exact h1
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    rw [hmemE] at ha hb
    have h1 := D.E1_comm hFc _ ha _ hb
    have e1 : x⁻¹ * a * x * (x⁻¹ * b * x) = x⁻¹ * (a * b) * x := by group
    have e2 : x⁻¹ * b * x * (x⁻¹ * a * x) = x⁻¹ * (b * a) * x := by group
    rw [e1, e2] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hEsq : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    rw [hmemE] at ha
    have h1 := D.E1_sq hFsq _ ha
    have e1 : x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
    rw [e1] at h1
    have := mul_left_cancel (mul_right_cancel (h1.trans (by group : (1 : G) = x⁻¹ * 1 * x)))
    exact this
  have hEcent : ∀ y ∈ T, (∀ e ∈ E, y * e = e * y) → y ∈ E := by
    intro y hy hc
    rw [hmemE]
    obtain ⟨h, hh⟩ := hTmem _ ((hxT' y).1 hy)
    refine D.cent_E1 (y := ⟨x⁻¹ * y * x, h⟩) (fun e he => ?_)
    have h1 := hc (x * e * x⁻¹) ((hmemE _).2 (by
      rw [show x⁻¹ * (x * e * x⁻¹) * x = e by group]
      exact he))
    calc x⁻¹ * y * x * e = x⁻¹ * (y * (x * e * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * e * x⁻¹) * y) * x := by rw [h1]
      _ = e * (x⁻¹ * y * x) := by group
  let θ := thetaH D.cfg.cent_le
  have hLH : L ≤ centralizer ({z} : Set G) := fun l hl => D.l_mem_H hl
  have hNn : (L.subgroupOf (centralizer ({z} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 D.cfg.cent_le
  have hker : ∀ g : centralizer ({z} : Set G), θ g = 1 ↔ g ∈ zpowers (zH z) := by
    intro g
    rw [D.ker g]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [zH] using hk)⟩
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa [zH] using congrArg Subtype.val hk⟩
  have I : ImageSetup θ (zH z) (L.subgroupOf (centralizer ({z} : Set G))) :=
    { z_sq := Subtype.ext D.cfg.z_sq
      z_central := fun g => Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
      ker := hker
      zN := fun h => D.cfg.z_not_mem_A (mem_subgroupOf.1 h)
      comm := fun a b => mem_subgroupOf.2 (D.cfg.commutator_mem a.2 b.2) }
  have NE : ImageSetup.NormalElemAb T₁ (E.subgroupOf (centralizer ({z} : Set G))) (zH z) :=
    { le := fun g hg => by
        obtain ⟨h, hh⟩ := hTmem g (hET (mem_subgroupOf.1 hg))
        exact hh
      normal := fun y hy e he => mem_subgroupOf.2
        (hEnorm (y : G) ⟨y, hy, rfl⟩ (e : G) (mem_subgroupOf.1 he))
      comm := fun a ha b hb => Subtype.ext
        (hEcomm (a : G) (mem_subgroupOf.1 ha) (b : G) (mem_subgroupOf.1 hb))
      sq := fun a ha => Subtype.ext (hEsq (a : G) (mem_subgroupOf.1 ha))
      z_mem := mem_subgroupOf.2 hzE
      cent := fun y hy hc => mem_subgroupOf.2 (hEcent (y : G) ⟨y, hy, rfl⟩ (fun e he =>
        congrArg Subtype.val (hc ⟨e, hEH he⟩ (mem_subgroupOf.2 he)))) }
  have hEcard : Nat.card E = 32 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact D.card_E1 hF
  have hEHcard : Nat.card (E.subgroupOf (centralizer ({z} : Set G))) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hEcard]
  have hcard16 : Nat.card ((E.subgroupOf (centralizer ({z} : Set G))).map θ) = 16 := by
    have := ImageSetup.card_image I (E := E.subgroupOf (centralizer ({z} : Set G)))
      (mem_subgroupOf.2 hzE)
    rw [hEHcard] at this
    omega
  obtain ⟨l, hlF, hl1, hl8⟩ := D.orbit8_lift
  set e0 : G := x * l * x⁻¹ with he0
  have hlE1 : (l : G) ∈ E1 := mem_sup_left (mem_liftSub.2 ⟨l, rfl, hlF⟩)
  have he0E : e0 ∈ E := (hmemE _).2 (by
    rw [he0, show x⁻¹ * (x * (l : G) * x⁻¹) * x = l by group]
    exact hlE1)
  have hO' : {g : G | ∃ y ∈ T₁, g = (y : G) * e0 * (y : G)⁻¹}.ncard = 8 := by
    have hset : {g : G | ∃ y ∈ T₁, g = (y : G) * e0 * (y : G)⁻¹} =
        (MulAut.conj x) '' {g : G | ∃ y ∈ T₁, g = (y : G) * l * (y : G)⁻¹} := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨h, hh⟩ := hTmem _ ((hxT' (y : G)).1 ⟨y, hy, rfl⟩)
        refine ⟨(x⁻¹ * (y : G) * x) * l * (x⁻¹ * (y : G) * x)⁻¹, ⟨⟨_, h⟩, hh, rfl⟩, ?_⟩
        simp only [MulAut.conj_apply, he0]
        group
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        obtain ⟨h, hh⟩ := hTmem _ ((hxT (y : G)).1 ⟨y, hy, rfl⟩)
        refine ⟨⟨_, h⟩, hh, ?_⟩
        simp only [MulAut.conj_apply, he0]
        group
    rw [hset, Set.ncard_image_of_injective _ (MulAut.conj x).injective]
    exact hl8
  let eH : centralizer ({z} : Set G) := ⟨e0, hEH he0E⟩
  have hOH : {g : centralizer ({z} : Set G) | ∃ y ∈ T₁, g = y * eH * y⁻¹}.ncard = 8 := by
    rw [← hO', ← Set.ncard_image_of_injective _ (centralizer ({z} : Set G)).subtype_injective]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hclass8 : {β : MulAut (L ⧸ center L) | ∃ α ∈ T₁.map θ, β = α * θ eH * α⁻¹}.ncard = 8 := by
    rw [ImageSetup.class_ncard I eH]
    exact hOH
  have hex : ∃ β ∈ (E.subgroupOf (centralizer ({z} : Set G))).map θ, β ≠ 1 ∧
      (autConjClass (T₁.map θ) β).ncard = 8 := by
    refine ⟨θ eH, ⟨eH, mem_subgroupOf.2 he0E, rfl⟩, ?_, hclass8⟩
    intro h1
    have : {β : MulAut (L ⧸ center L) | ∃ α ∈ T₁.map θ, β = α * θ eH * α⁻¹} = {1} := by
      ext β
      constructor
      · rintro ⟨α, -, rfl⟩
        rw [h1]
        simp
      · rintro rfl
        exact ⟨1, one_mem _, by rw [h1]; simp⟩
    rw [this, Set.ncard_singleton] at hclass8
    omega
  have hunique := D.W.e16.unique ((E.subgroupOf (centralizer ({z} : Set G))).map θ)
    (ImageSetup.image_le NE)
    (ImageSetup.image_normal NE) (ImageSetup.image_comm NE) (ImageSetup.image_sq NE) hcard16
    (ImageSetup.image_cent I NE) hex
  have hEle : E ≤ E1 := by
    intro e he
    have hmem : θ ⟨e, hEH he⟩ ∈ (E.subgroupOf (centralizer ({z} : Set G))).map θ :=
      ⟨⟨e, hEH he⟩, mem_subgroupOf.2 he, rfl⟩
    rw [hunique] at hmem
    obtain ⟨fb, hfb, hfbθ⟩ := hmem
    obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective fb
    have hl₀ : (l₀ : G) ∈ liftSub F := mem_liftSub.2 ⟨l₀, rfl, hfb⟩
    have h1 : θ ((⟨(l₀ : G), D.l_mem_H l₀.2⟩ : centralizer ({z} : Set G))⁻¹ * ⟨e, hEH he⟩) = 1 := by
      rw [map_mul, map_inv, D.theta_conj, hfbθ, inv_mul_cancel]
    have h2 : ((⟨(l₀ : G), D.l_mem_H l₀.2⟩ : centralizer ({z} : Set G))⁻¹ *
        ⟨e, hEH he⟩ : centralizer ({z} : Set G)) ∈ zpowers (zH z) :=
      (hker _).1 h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    have h3 : (l₀ : G)⁻¹ * e = z ^ k := by simpa [zH] using (congrArg Subtype.val hk).symm
    have h4 : e = (l₀ : G) * z ^ k := by rw [← h3]; group
    rw [h4]
    exact Subgroup.mul_mem _ (mem_sup_left hl₀) (mem_sup_right (Subgroup.zpow_mem _
      (mem_zpowers z) k))
  exact Subgroup.eq_of_le_of_card_ge hEle (by rw [hEcard, D.card_E1 hF])

end Main

end OutData

end CFSG.EvenSporadicStandard.M22Std
