module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4WF9Aff

public section

namespace CFSG.OddStandard.AltStdSmall4.WF9

open Subgroup

variable {G : Type} [Group G]

theorem mem_conjSub {z x : G} {X : Subgroup G} :
    x ∈ conjSub z X ↔ ∃ y ∈ X, z * y * z⁻¹ = x := by
  simp only [conjSub, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem conj_mem_conjSub {z y : G} {X : Subgroup G} (hy : y ∈ X) : z * y * z⁻¹ ∈ conjSub z X :=
  mem_conjSub.2 ⟨y, hy, rfl⟩

structure WrData (R : Subgroup G) (z : G) : Prop where
  sq : z * z = 1
  comm : ∀ a ∈ R, ∀ b ∈ conjSub z R, a * b = b * a
  inf : R ⊓ conjSub z R = ⊥
  not_mem : z ∉ R ⊔ conjSub z R

namespace WrData

variable {R : Subgroup G} {z : G} (hW : WrData R z)
include hW

theorem inv_z : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right hW.sq

theorem conj_conj (x : G) : z * (z * x * z⁻¹) * z⁻¹ = x :=
  calc z * (z * x * z⁻¹) * z⁻¹ = z * z * x * (z * z)⁻¹ := by group
    _ = x := by rw [hW.sq, one_mul, inv_one, mul_one]

theorem conj_mem_of_mem_conjSub {s : G} (hs : s ∈ conjSub z R) : z * s * z⁻¹ ∈ R := by
  obtain ⟨r, hr, rfl⟩ := mem_conjSub.1 hs
  rw [hW.conj_conj]
  exact hr

theorem conjSub_le_normalizer : conjSub z R ≤ normalizer (R : Set G) := fun b hb =>
  centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => hW.comm h hh b hb)

theorem mem_base_iff {x : G} :
    x ∈ R ⊔ conjSub z R ↔ ∃ r ∈ R, ∃ s ∈ conjSub z R, r * s = x :=
  mem_sup_iff_of_le_normalizer hW.conjSub_le_normalizer

theorem eq_of_mul_eq {r r' s s' : G} (hr : r ∈ R) (hr' : r' ∈ R) (hs : s ∈ conjSub z R)
    (hs' : s' ∈ conjSub z R) (heq : r * s = r' * s') : r = r' ∧ s = s' :=
  eq_of_mul_eq_of_inf_eq_bot hW.inf hr hr' hs hs' heq

theorem conj_mem_base {x : G} (hx : x ∈ R ⊔ conjSub z R) : z * x * z⁻¹ ∈ R ⊔ conjSub z R := by
  obtain ⟨r, hr, s, hs, rfl⟩ := hW.mem_base_iff.1 hx
  have h : z * (r * s) * z⁻¹ = (z * r * z⁻¹) * (z * s * z⁻¹) := by group
  rw [h]
  exact mul_mem (mem_sup_right (conj_mem_conjSub hr)) (mem_sup_left (hW.conj_mem_of_mem_conjSub hs))

theorem z_mem_normalizer : z ∈ normalizer ((R ⊔ conjSub z R : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hW.conj_mem_base, fun hx => ?_⟩
  have h := hW.conj_mem_base hx
  rwa [hW.conj_conj] at h

theorem mem_top_iff {x : G} :
    x ∈ R ⊔ conjSub z R ⊔ zpowers z ↔ x ∈ R ⊔ conjSub z R ∨ x * z ∈ R ⊔ conjSub z R := by
  rw [mem_sup_iff_of_le_normalizer (zpowers_le.2 hW.z_mem_normalizer)]
  constructor
  · rintro ⟨b, hb, w, hw, rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hW.sq hw with rfl | rfl
    · left
      rwa [mul_one]
    · right
      rwa [mul_assoc, hW.sq, mul_one]
  · rintro (hx | hx)
    · exact ⟨x, hx, 1, one_mem _, mul_one x⟩
    · exact ⟨x * z, hx, z, mem_zpowers z, by rw [mul_assoc, hW.sq, mul_one]⟩

theorem relIndex_base :
    (R ⊔ conjSub z R).relIndex (R ⊔ conjSub z R ⊔ zpowers z) = 2 := by
  have hzT : z ∈ R ⊔ conjSub z R ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  refine index_eq_two_iff.2 ⟨⟨z, hzT⟩, fun b => ?_⟩
  simp only [mem_subgroupOf, coe_mul]
  have key : ¬ ((b : G) ∈ R ⊔ conjSub z R ∧ (b : G) * z ∈ R ⊔ conjSub z R) := fun ⟨h1, h2⟩ =>
    hW.not_mem (by simpa only [inv_mul_cancel_left] using mul_mem (inv_mem h1) h2)
  rcases hW.mem_top_iff.1 b.2 with hb | hb
  · exact Or.inr ⟨hb, fun h => key ⟨hb, h⟩⟩
  · exact Or.inl ⟨hb, fun h => key ⟨h, hb⟩⟩

theorem isPGroup_top (hR : IsPGroup 2 R) :
    IsPGroup 2 (R ⊔ conjSub z R ⊔ zpowers z : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRz : IsPGroup 2 (conjSub z R) := hR.map (MulAut.conj z).toMonoidHom
  have hB := hR.to_sup_of_normal_left' hRz hW.conjSub_le_normalizer
  have hz : IsPGroup 2 (zpowers z) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hW.sq))
  exact hB.to_sup_of_normal_left' hz (zpowers_le.2 hW.z_mem_normalizer)

theorem card_cent_z [Finite G] :
    2 * Nat.card R ≤
      Nat.card ((R ⊔ conjSub z R ⊔ zpowers z) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  have hmem : ∀ r ∈ R,
      r * (z * r * z⁻¹) ∈ (R ⊔ conjSub z R) ⊓ centralizer ({z} : Set G) := by
    intro r hr
    refine mem_inf.2 ⟨mul_mem (mem_sup_left hr) (mem_sup_right (conj_mem_conjSub hr)),
      mem_centralizer_singleton_iff.2 ?_⟩
    have hc := hW.comm r hr _ (conj_mem_conjSub (z := z) hr)
    calc r * (z * r * z⁻¹) * z = z * r * z⁻¹ * r * z := by rw [hc]
      _ = z * r * (z⁻¹ * r * z) := by group
      _ = z * (r * (z * r * z⁻¹)) := by rw [hW.inv_z]; group
  let f : R → ((R ⊔ conjSub z R) ⊓ centralizer ({z} : Set G) : Subgroup G) := fun r =>
    ⟨r * (z * r * z⁻¹), hmem r r.2⟩
  have hf : Function.Injective f := fun r r' h =>
    Subtype.ext (hW.eq_of_mul_eq r.2 r'.2 (conj_mem_conjSub r.2) (conj_mem_conjSub r'.2)
      (congrArg Subtype.val h)).1
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := two_mul_card_le_of_mem
    (inf_le_inf_right _ le_sup_left : (R ⊔ conjSub z R) ⊓ centralizer ({z} : Set G) ≤
      (R ⊔ conjSub z R ⊔ zpowers z) ⊓ centralizer ({z} : Set G))
    (mem_inf.2 ⟨mem_sup_right (mem_zpowers z), mem_centralizer_singleton_iff.2 rfl⟩)
    (fun h => hW.not_mem (mem_inf.1 h).1)
  omega

theorem exists_conj_of_not_mem {x : G} (hx : x ∈ R ⊔ conjSub z R ⊔ zpowers z)
    (hxB : x ∉ R ⊔ conjSub z R) (hx2 : x * x = 1) : ∃ r ∈ R, r * z * r⁻¹ = x := by
  have hxz := (hW.mem_top_iff.1 hx).resolve_left hxB
  obtain ⟨r, hr, s, hs, hrs⟩ := hW.mem_base_iff.1 hxz
  have hx' : x = r * s * z := by rw [hrs, mul_assoc, hW.sq, mul_one]
  have hr' := hW.conj_mem_of_mem_conjSub hs
  have hs' : z * r * z⁻¹ ∈ conjSub z R := conj_mem_conjSub hr
  have hc1 := hW.comm _ hr' _ hs
  have hc2 := hW.comm r hr s hs
  have hsq : (r * (z * s * z⁻¹)) * (s * (z * r * z⁻¹)) = 1 * 1 := by
    rw [one_mul, ← hx2, hx']
    calc r * (z * s * z⁻¹) * (s * (z * r * z⁻¹))
        = r * (z * s * z⁻¹ * s) * (z * r * z⁻¹) := by group
      _ = r * (s * (z * s * z⁻¹)) * (z * r * z⁻¹) := by rw [hc1]
      _ = r * s * z * (s * r) * z⁻¹ := by group
      _ = r * s * z * (r * s) * z⁻¹ := by rw [hc2]
      _ = r * s * z * (r * s * z) := by rw [hW.inv_z]; group
  obtain ⟨h1, -⟩ :=
    hW.eq_of_mul_eq (mul_mem hr hr') (one_mem _) (mul_mem hs hs') (one_mem _) hsq
  have h2 : z * s * z⁻¹ = r⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hs_eq : s = z⁻¹ * r⁻¹ * z := by
    calc s = z⁻¹ * (z * s * z⁻¹) * z := by group
      _ = z⁻¹ * r⁻¹ * z := by rw [h2]
  refine ⟨r, hr, ?_⟩
  rw [hx', hs_eq]
  calc r * z * r⁻¹ = r * z * r⁻¹ * (z * z) := by rw [hW.sq, mul_one]
    _ = r * (z⁻¹ * r⁻¹ * z) * z := by rw [hW.inv_z]; group

theorem card_cent_ge [Finite G]
    (h16 : ∀ a ∈ R, a * a = 1 → 16 ≤ Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G))
    {x : G} (hx : x ∈ R ⊔ conjSub z R) (hx2 : x * x = 1) :
    256 ≤ Nat.card ((R ⊔ conjSub z R) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  obtain ⟨r, hr, s, hs, rfl⟩ := hW.mem_base_iff.1 hx
  have hrs : r * s = s * r := hW.comm r hr s hs
  have hsq : (r * r) * (s * s) = 1 * 1 := by
    rw [one_mul, ← hx2]
    calc r * r * (s * s) = r * (r * s) * s := by group
      _ = r * (s * r) * s := by rw [hrs]
      _ = r * s * (r * s) := by group
  obtain ⟨hr2, hs2⟩ :=
    hW.eq_of_mul_eq (mul_mem hr hr) (one_mem _) (mul_mem hs hs) (one_mem _) hsq
  obtain ⟨s₀, hs₀R, rfl⟩ := mem_conjSub.1 hs
  have hs₀2 : s₀ * s₀ = 1 := by
    have h : z * (s₀ * s₀) * z⁻¹ = 1 := by
      rw [← hs2]
      group
    calc s₀ * s₀ = z⁻¹ * (z * (s₀ * s₀) * z⁻¹) * z := by group
      _ = 1 := by rw [h]; group
  have hmem : ∀ a ∈ R ⊓ centralizer ({r} : Set G), ∀ a' ∈ R ⊓ centralizer ({s₀} : Set G),
      a * (z * a' * z⁻¹) ∈
        (R ⊔ conjSub z R) ⊓ centralizer ({r * (z * s₀ * z⁻¹)} : Set G) := by
    intro a ha a' ha'
    have hu : z * a' * z⁻¹ ∈ conjSub z R := conj_mem_conjSub (mem_inf.1 ha').1
    refine mem_inf.2 ⟨mul_mem (mem_sup_left (mem_inf.1 ha).1) (mem_sup_right hu),
      mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : Commute a r := mem_centralizer_singleton_iff.1 (mem_inf.1 ha).2
    have h2 : Commute a (z * s₀ * z⁻¹) := hW.comm a (mem_inf.1 ha).1 _ hs
    have h3 : Commute (z * a' * z⁻¹) r := (hW.comm r hr _ hu).symm
    have h4 : Commute (z * a' * z⁻¹) (z * s₀ * z⁻¹) := by
      have h := mem_centralizer_singleton_iff.1 (mem_inf.1 ha').2
      calc z * a' * z⁻¹ * (z * s₀ * z⁻¹) = z * (a' * s₀) * z⁻¹ := by group
        _ = z * (s₀ * a') * z⁻¹ := by rw [h]
        _ = z * s₀ * z⁻¹ * (z * a' * z⁻¹) := by group
    exact (h1.mul_right h2).mul_left (h3.mul_right h4)
  let f : (R ⊓ centralizer ({r} : Set G) : Subgroup G) ×
      (R ⊓ centralizer ({s₀} : Set G) : Subgroup G) →
      ((R ⊔ conjSub z R) ⊓ centralizer ({r * (z * s₀ * z⁻¹)} : Set G) : Subgroup G) :=
    fun p => ⟨(p.1 : G) * (z * p.2 * z⁻¹), hmem _ p.1.2 _ p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, a'⟩ ⟨b, b'⟩ h
    obtain ⟨h1, h2⟩ := hW.eq_of_mul_eq (mem_inf.1 a.2).1 (mem_inf.1 b.2).1
      (conj_mem_conjSub (mem_inf.1 a'.2).1) (conj_mem_conjSub (mem_inf.1 b'.2).1)
      (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext (mul_left_cancel (mul_right_cancel h2)))
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  have hA := h16 r hr hr2
  have hB := h16 s₀ hs₀R hs₀2
  calc 256 = 16 * 16 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hA hB
    _ ≤ _ := hcard

end WrData

end CFSG.OddStandard.AltStdSmall4.WF9
