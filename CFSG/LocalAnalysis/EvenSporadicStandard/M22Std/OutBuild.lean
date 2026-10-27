module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutE1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutNOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

theorem oneClass_of_isSporadic
    {G : Type} [Group G] {L : Subgroup G} (hL : IsSporadic L .M22) {t u : G} (ht : t ∈ L)
    (hu : u ∈ L) (ht2 : t * t = 1) (hu2 : u * u = 1) (ht1 : t ≠ 1) (hu1 : u ≠ 1) :
    ∃ c ∈ L, u = c * t * c⁻¹ := by
  obtain ⟨e⟩ := hL
  have hord : ∀ w : L, w * w = 1 → w ≠ 1 → orderOf (e w) = 2 := by
    intro w hw2 hw1
    rw [MulEquiv.orderOf_eq e]
    exact orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  let t' : L := ⟨t, ht⟩
  let u' : L := ⟨u, hu⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa using ht2)
  have ht'1 : t' ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  have hu'2 : u' * u' = 1 := Subtype.ext (by simpa using hu2)
  have hu'1 : u' ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
  obtain ⟨c₁, hc₁⟩ := m22_involution_conj (e u') (hord u' hu'2 hu'1)
  obtain ⟨c₂, hc₂⟩ := m22_involution_conj (e t') (hord t' ht'2 ht'1)
  refine ⟨((e.symm (c₁ * c₂⁻¹) : L) : G), (e.symm (c₁ * c₂⁻¹) : L).2, ?_⟩
  have hx : u' = e.symm (c₁ * c₂⁻¹) * t' * (e.symm (c₁ * c₂⁻¹))⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc₁, hc₂]
    group
  simpa using congrArg Subtype.val hx

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

namespace OutData

variable (D : OutData L z t T₁ F tb)

include D in
theorem nData : NData L (liftSub F) := by
  have hinj : Function.Injective (QuotientGroup.mk' (center L)) := fun a b h => D.mk_injective h
  let κe : L ≃* L ⧸ center L :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center L)) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  let ρ : (L ⧸ center L) →* G := L.subtype.comp κe.symm.toMonoidHom
  have hρ : Function.Injective ρ := L.subtype_injective.comp κe.symm.injective
  have h1 := NData.map hρ D.W.nd
  have hrange : ρ.range = L := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact (κe.symm y).2
    · intro hg
      exact ⟨κe ⟨g, hg⟩, by simp [ρ]⟩
  have hF : F.map ρ = liftSub F := by
    have h2 : F.comap (QuotientGroup.mk' (center L)) = F.map κe.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm κe F
    rw [liftSub, h2, Subgroup.map_map]
  rwa [hrange, hF] at h1


include D in
theorem t_mem_L : t ∈ L := by
  obtain ⟨t', -, rfl⟩ := D.tlift
  exact t'.2

include D in
theorem ker_zH (g : centralizer ({z} : Set G)) :
    thetaH D.cfg.cent_le g = 1 ↔ g ∈ zpowers (zH z) := by
  rw [D.ker g]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [zH] using hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa [zH] using congrArg Subtype.val hk⟩

section Finite

variable [Finite G]

include D in
theorem imageSetup : ImageSetup (thetaH D.cfg.cent_le) (zH z)
    (L.subgroupOf (centralizer ({z} : Set G))) :=
  { z_sq := Subtype.ext D.cfg.z_sq
    z_central := fun g => Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
    ker := D.ker_zH
    zN := fun h => D.cfg.z_not_mem_A (mem_subgroupOf.1 h)
    comm := fun a b => mem_subgroupOf.2 (D.cfg.commutator_mem a.2 b.2) }

include D in
theorem card_T₁ : Nat.card T₁ = 512 := by
  have h1 := ImageSetup.card_image D.imageSetup (E := T₁) D.zH_mem_T₁
  rw [D.W.card_S] at h1
  omega

include D in
theorem T_le_normalizer_E1 :
    (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) ≤
      normalizer ((liftSub F ⊔ zpowers z : Subgroup G) : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.mem_normalizer_iff.2 (forall_mem_iff_of_forall_mem fun e he =>
    D.T_normalizes_E1 hy he)

include D in
theorem outOne (hnonab : ∃ a b : G, a * b ≠ b * a) [IsSimpleGroup G]
    (hone : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∃ c ∈ L, u = c * t * c⁻¹) :
    OutOne L z (liftSub F) where
  z_mul_self := D.cfg.z_sq
  z_ne_one := D.cfg.z_ne
  z_comm := fun l hl => (D.cfg.z_comm_of_mem_A hl).symm
  z_not_mem := D.cfg.z_not_mem_A
  F_le := liftSub_le F
  F_comm := D.liftSub_comm D.W.e16.comm
  F_sq := D.liftSub_sq D.W.e16.sq
  F_card := D.card_liftSub D.W.e16.card
  not_conj := by
    intro u hu hu1 hconj
    obtain ⟨c, hc, hcu⟩ := hone u (liftSub_le F hu) (D.liftSub_sq D.W.e16.sq u hu) hu1
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    refine D.cfg.conj_z_ne_t (c⁻¹ * g) ?_
    have : t = c⁻¹ * u * c := by rw [hcu]; group
    rw [this, ← hg]
    group
  fused := by
    intro f hf
    by_cases hf1 : f = 1
    · rw [hf1, mul_one]
    · obtain ⟨c, hc, hcf⟩ := hone f (liftSub_le F hf) (D.liftSub_sq D.W.e16.sq f hf) hf1
      obtain ⟨g, hg⟩ := D.cfg.fused_eq hnonab
      have hz : IsConj z (z * t) := isConj_iff.2 ⟨g, hg⟩
      have hcz : c * z * c⁻¹ = z := by
        rw [D.cfg.z_comm_of_mem_A hc]
        group
      have h2 : IsConj (z * t) (z * f) := isConj_iff.2 ⟨c, by
        rw [hcf]
        calc c * (z * t) * c⁻¹ = (c * z * c⁻¹) * (c * t * c⁻¹) := by group
          _ = z * (c * t * c⁻¹) := by rw [hcz]⟩
      exact hz.trans h2
  cent_F := by
    intro k hk hc
    refine D.cent_E1 (y := ⟨k, mem_centralizer_singleton_iff.2 hk⟩) (fun e he => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      D.zpowers_le_cent_lift he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have h1 : k * a = a * k := (hc a ha).symm
    have h2 : Commute k z := hk
    have h3 : Commute k (z ^ j) := h2.zpow_right j
    exact (((show Commute k a from h1).mul_right h3)).eq
  trans := D.nData.trans
  NH_two := by
    have h1 : (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) ≤
        normalizer ((liftSub F ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) :=
      le_inf D.T_le_normalizer_E1 D.cfg.T_le
    have h2 := Subgroup.card_dvd_of_le h1
    rwa [Subgroup.card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
      D.card_T₁] at h2

include D in
theorem transitive_E1 [IsSimpleGroup G]
    (hone : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∃ c ∈ L, u = c * t * c⁻¹)
    {x : G}
    (hx : x ∈ normalizer ((T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) : Set G))
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t)
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∀ f ∈ liftSub F, ∃ c : G, (∀ y, y ∈ liftSub F ⊔ zpowers z ↔
      c * y * c⁻¹ ∈ liftSub F ⊔ zpowers z) ∧ c * z * c⁻¹ = z * f := by
  have hO := D.outOne hnonab hone
  have hxE := D.normalizes_E1 hx hxz hxt D.W.e16.card D.W.e16.sq D.W.e16.comm
  have hxN : ∀ y, y ∈ liftSub F ⊔ zpowers z ↔ x * y * x⁻¹ ∈ liftSub F ⊔ zpowers z := by
    apply forall_mem_iff_of_forall_mem
    intro y hy
    rw [← hxE]
    exact ⟨y, hy, rfl⟩
  have htF : t ∈ liftSub F := by
    obtain ⟨t', ht', rfl⟩ := D.tlift
    exact mem_liftSub.2 ⟨t', rfl, ht' ▸ D.W.t_mem⟩
  intro f hf
  by_cases hf1 : f = 1
  · exact ⟨1, fun y => by simp, by rw [hf1]; group⟩
  · obtain ⟨b, hbL, hbF, hb⟩ := hO.trans t htF D.cfg.t_ne f hf hf1
    have hbz : b * z * b⁻¹ = z := by
      rw [D.cfg.z_comm_of_mem_A hbL]
      group
    have hbE : ∀ y, y ∈ liftSub F ⊔ zpowers z ↔ b * y * b⁻¹ ∈ liftSub F ⊔ zpowers z :=
      hO.mem_normalizer_sup hbF (one_mem _) (by rw [hbz, mul_one])
    refine ⟨b * x * b⁻¹, fun y => ?_, ?_⟩
    · have e1 := hbE (b⁻¹ * y * b)
      have e2 := hxN (b⁻¹ * y * b)
      have e3 := hbE (x * (b⁻¹ * y * b) * x⁻¹)
      rw [show b * (b⁻¹ * y * b) * b⁻¹ = y by group] at e1
      rw [show b * (x * (b⁻¹ * y * b) * x⁻¹) * b⁻¹ = b * x * b⁻¹ * y * (b * x * b⁻¹)⁻¹ by group]
        at e3
      exact e1.symm.trans (e2.trans e3)
    · calc b * x * b⁻¹ * z * (b * x * b⁻¹)⁻¹ = b * (x * (b⁻¹ * z * b) * x⁻¹) * b⁻¹ := by group
        _ = b * (x * z * x⁻¹) * b⁻¹ := by
          have : b⁻¹ * z * b = z := by
            have := D.cfg.z_comm_of_mem_A (Subgroup.inv_mem _ hbL)
            rw [this]
            group
          rw [this]
        _ = b * (z * t) * b⁻¹ := by rw [hxz]
        _ = (b * z * b⁻¹) * (b * t * b⁻¹) := by group
        _ = z * f := by rw [hbz, hb]

include D in
theorem card_K [IsSimpleGroup G] (hone : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∃ c ∈ L, u = c * t * c⁻¹)
    {x : G}
    (hx : x ∈ normalizer ((T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) : Set G))
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t)
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Nat.card (Ksub z (liftSub F)) = 512 :=
  (D.outOne hnonab hone).card_Ksub (D.transitive_E1 hone hx hxz hxt hnonab)

include D in
theorem center_K [IsSimpleGroup G] (hone : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∃ c ∈ L, u = c * t * c⁻¹)
    {x : G}
    (hx : x ∈ normalizer ((T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) : Set G))
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {k : G} (hk : k ∈ Ksub z (liftSub F)) :
    (∀ k' ∈ Ksub z (liftSub F), k * k' = k' * k) ↔ k ∈ liftSub F :=
  (D.outOne hnonab hone).center_Ksub (D.transitive_E1 hone hx hxz hxt hnonab) hk

end Finite

end OutData

end CFSG.EvenSporadicStandard.M22Std
