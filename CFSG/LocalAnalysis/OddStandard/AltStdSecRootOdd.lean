module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecStd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHerCop

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Lift

variable {H : Type*} [Group H]

theorem exists_conj_of_involutions_of_mul_mem {P : Subgroup H} (hP : ∀ x ∈ P, Odd (orderOf x))
    {u v : H} (hu : u * u = 1) (hv : v * v = 1) (huv : v * u ∈ P) :
    ∃ r ∈ P, r * u * r⁻¹ = v := by
  have hv1 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvvu : v * (v * u) = u := by rw [← mul_assoc, hv, one_mul]
  have hinv : v * (v * u) * v⁻¹ = (v * u)⁻¹ := by
    rw [hvvu, mul_inv_rev, hu1, hv1]
  obtain ⟨r, hr, hrr, hvr⟩ := exists_sq_root_inverted (hP _ huv) hinv
  have hrP : r ∈ P := (zpowers_le.2 huv) hr
  have hvr' : v * r = r⁻¹ * v := mul_inv_eq_iff_eq_mul.1 hvr
  refine ⟨r, hrP, ?_⟩
  calc r * u * r⁻¹ = r * (v * (v * u)) * r⁻¹ := by rw [hvvu]
    _ = r * (v * (r * r)) * r⁻¹ := by rw [hrr]
    _ = r * ((v * r) * r) * r⁻¹ := by group
    _ = r * ((r⁻¹ * v) * r) * r⁻¹ := by rw [hvr']
    _ = v := by group

end Lift

section OddCore

variable {H : Type*} [Group H] [Finite H]

theorem mem_oddCore_iff {x : H} :
    x ∈ CFSG.oddCore H ↔ ∃ N : Subgroup H, N.Normal ∧ Odd (Nat.card N) ∧ x ∈ N := by
  constructor
  · intro hx
    exact ⟨CFSG.oddCore H, inferInstance,
      ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore H, hx⟩
  · rintro ⟨N, hN, hodd, hx⟩
    exact (le_sSup ⟨hN, hodd⟩ : N ≤ CFSG.oddCore H) hx

theorem map_mem_oddCore {K : Type*} [Group K] [Finite K] (φ : H ≃* K) {x : H}
    (hx : x ∈ CFSG.oddCore H) : φ x ∈ CFSG.oddCore K := by
  obtain ⟨N, hN, hodd, hxN⟩ := mem_oddCore_iff.1 hx
  refine mem_oddCore_iff.2 ⟨N.map φ.toMonoidHom, hN.map _ φ.surjective, ?_, ⟨x, hxN, rfl⟩⟩
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hodd

theorem mem_oddCore_map_iff {K : Type*} [Group K] [Finite K] (φ : H ≃* K) {x : H} :
    φ x ∈ CFSG.oddCore K ↔ x ∈ CFSG.oddCore H := by
  refine ⟨fun h => ?_, map_mem_oddCore φ⟩
  have := map_mem_oddCore φ.symm h
  simpa using this

end OddCore

section OddCoreOf

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_oddCoreOf_iff {H : Subgroup X} {x : X} :
    x ∈ oddCoreOf H ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : H) ∈ CFSG.oddCore ↥H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_oddCoreOf_conjSub_iff {H : Subgroup X} {g x : X} :
    x ∈ oddCoreOf (conjSub g H) ↔ g⁻¹ * x * g ∈ oddCoreOf H := by
  let φ : ↥H ≃* ↥(conjSub g H) :=
    H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hφ : ∀ y : ↥H, ((φ y : ↥(conjSub g H)) : X) = g * (y : X) * g⁻¹ := fun y => rfl
  rw [mem_oddCoreOf_iff, mem_oddCoreOf_iff]
  constructor
  · rintro ⟨hx, h⟩
    have hx' : g⁻¹ * x * g ∈ H := mem_conjSub_iff.1 hx
    refine ⟨hx', ?_⟩
    have hφx : φ ⟨g⁻¹ * x * g, hx'⟩ = ⟨x, hx⟩ := by
      apply Subtype.ext
      rw [hφ]
      group
    rw [← mem_oddCore_map_iff φ, hφx]
    exact h
  · rintro ⟨hx', h⟩
    have hx : x ∈ conjSub g H := mem_conjSub_iff.2 hx'
    refine ⟨hx, ?_⟩
    have hφx : φ ⟨g⁻¹ * x * g, hx'⟩ = ⟨x, hx⟩ := by
      apply Subtype.ext
      rw [hφ]
      group
    rw [← hφx, mem_oddCore_map_iff φ]
    exact h

end OddCoreOf


section ZStar

variable {G : Type} [Group G] [Finite G]

@[expose] def IsZStar (T : Subgroup G) (z : G) : Prop :=
  ∃ hz : z ∈ centralizer (T : Set G), ∀ c : centralizer (T : Set G),
    (⟨z, hz⟩ : centralizer (T : Set G)) * c * ⟨z, hz⟩⁻¹ * c⁻¹ ∈
      CFSG.oddCore (centralizer (T : Set G))

omit [Finite G] in
theorem isZStar_iff {T : Subgroup G} {z : G} :
    IsZStar T z ↔ z ∈ centralizer (T : Set G) ∧ ∀ c ∈ centralizer (T : Set G),
      z * c * z⁻¹ * c⁻¹ ∈ oddCoreOf (centralizer (T : Set G)) := by
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun c hc => mem_oddCoreOf_iff.2 ⟨?_, h ⟨c, hc⟩⟩⟩
    exact mul_mem (mul_mem (mul_mem hz hc) (inv_mem hz)) (inv_mem hc)
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun c => ?_⟩
    obtain ⟨hx, hmem⟩ := mem_oddCoreOf_iff.1 (h c c.2)
    exact hmem

omit [Finite G] in
theorem isZStar_iff_mem_center {T : Subgroup G} {z : G} :
    IsZStar T z ↔ ∃ hz : z ∈ centralizer (T : Set G),
      (QuotientGroup.mk (⟨z, hz⟩ : centralizer (T : Set G)) : Sec G T) ∈ center (Sec G T) := by
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, Subgroup.mem_center_iff.2 fun x => ?_⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := h c
    rw [← QuotientGroup.eq_one_iff] at h1
    have h2 : (QuotientGroup.mk (⟨z, hz⟩ : centralizer (T : Set G)) : Sec G T) *
        QuotientGroup.mk c * (QuotientGroup.mk (⟨z, hz⟩ : centralizer (T : Set G)) : Sec G T)⁻¹ *
        (QuotientGroup.mk c)⁻¹ = 1 := by
      simpa using h1
    calc (QuotientGroup.mk c : Sec G T) * QuotientGroup.mk ⟨z, hz⟩
        = ((QuotientGroup.mk ⟨z, hz⟩ : Sec G T) * QuotientGroup.mk c *
            (QuotientGroup.mk ⟨z, hz⟩ : Sec G T)⁻¹ * (QuotientGroup.mk c)⁻¹)⁻¹ *
          (QuotientGroup.mk ⟨z, hz⟩ * QuotientGroup.mk c) := by group
      _ = QuotientGroup.mk ⟨z, hz⟩ * QuotientGroup.mk c := by rw [h2]; group
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun c => ?_⟩
    have h1 := Subgroup.mem_center_iff.1 h (QuotientGroup.mk c)
    rw [← QuotientGroup.eq_one_iff]
    have : ((⟨z, hz⟩ * c * ⟨z, hz⟩⁻¹ * c⁻¹ : centralizer (T : Set G)) : Sec G T) =
        (QuotientGroup.mk ⟨z, hz⟩ : Sec G T) * QuotientGroup.mk c *
          (QuotientGroup.mk ⟨z, hz⟩ : Sec G T)⁻¹ * (QuotientGroup.mk c)⁻¹ := by simp
    rw [this, ← h1]
    group

omit [Finite G] in
theorem centralizer_conjSub (g : G) (T : Subgroup G) :
    centralizer ((conjSub g T : Subgroup G) : Set G) = conjSub g (centralizer (T : Set G)) := by
  ext x
  rw [mem_conjSub_iff]
  exact mem_centralizer_map_conj_iff

theorem IsZStar.conj {T : Subgroup G} {z : G} (h : IsZStar T z) (g : G) :
    IsZStar (conjSub g T) (g * z * g⁻¹) := by
  rw [isZStar_iff] at h ⊢
  obtain ⟨hz, h⟩ := h
  refine ⟨?_, ?_⟩
  · rw [centralizer_conjSub, mem_conjSub_iff]
    have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [this]
    exact hz
  · intro c' hc'
    rw [centralizer_conjSub, mem_conjSub_iff] at hc'
    rw [centralizer_conjSub, mem_oddCoreOf_conjSub_iff]
    have := h _ hc'
    have e : g⁻¹ * (g * z * g⁻¹ * c' * (g * z * g⁻¹)⁻¹ * c'⁻¹) * g =
        z * (g⁻¹ * c' * g) * z⁻¹ * (g⁻¹ * c' * g)⁻¹ := by group
    rw [e]
    exact this

end ZStar

end CFSG.OddStandard.AltStdSec
