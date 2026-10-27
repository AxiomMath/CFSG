module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DCtx

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem card_cls_mod3 [Finite G] : Nat.card (cls (Mm V H) x) % 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := d.hI.f3
  have h := card_fix_modEq (p := 3) (cls (Mm V H) x) f k hk (fun v hv => d.f_stable hv)
  have h1 : Nat.card {v : (cls (Mm V H) x) // f * (v : G) * f⁻¹ = v} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨x, x_mem_cls⟩, d.f_x⟩, ?_⟩
    intro w
    apply Subtype.ext; apply Subtype.ext
    exact d.fix_eq w.1.2 w.2
  rw [h1] at h
  unfold Nat.ModEq at h
  simpa using h

theorem card_cls_le [Finite G] : Nat.card (cls (Mm V H) x) ≤ Nat.card (Hzero H f) := by
  have hsub : cls (Mm V H) x ⊆ (fun q => q * x) '' (Hzero H f : Set G) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := d.cls_sub hy
    exact ⟨q, hq, rfl⟩
  calc Nat.card (cls (Mm V H) x) = (cls (Mm V H) x).ncard := Nat.card_coe_set_eq _
    _ ≤ ((fun q => q * x) '' (Hzero H f : Set G)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Hzero H f : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card (Hzero H f) := (Nat.card_coe_set_eq _).symm

end D13

namespace Out12

variable {x : G} {T V : Subgroup G} (h : Out12 G x T V)
include h

theorem centralizes_EV {t : G} (htV : t ∈ centralizer (V : Set G))
    (htx : t ∈ centralizer ({x} : Set G)) : t ∈ centralizer (EV x V : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  have hxt : x * t = t * x := mem_centralizer_iff.1 htx x rfl
  have hvt : ∀ v ∈ V, v * t = t * v := fun v hv => mem_centralizer_iff.1 htV v hv
  obtain ⟨v, hv, he' | he'⟩ := (h.mem_EV).1 he <;> rw [he']
  · exact hvt v hv
  · calc v * x * t = v * (x * t) := by group
      _ = v * (t * x) := by rw [hxt]
      _ = (v * t) * x := by group
      _ = (t * v) * x := by rw [hvt v hv]
      _ = t * (v * x) := by group

theorem EV_le_cent_M {H : Subgroup G} (hEH : EV x V ≤ H) :
    EV x V ≤ Mm V H ⊓ centralizer ({x} : Set G) := by
  intro e he
  refine ⟨⟨h.E_le_C he, le_normalizer (hEH he)⟩, ?_⟩
  show e ∈ centralizer ({x} : Set G)
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact h.EV_comm x_mem_EV he

theorem EV_sylow_cent_M [Finite G] {H : Subgroup G} (hEH : EV x V ≤ H) :
    SylowIn 2 (EV x V) (Mm V H ⊓ centralizer ({x} : Set G)) := by
  have hE := h.EV_le_cent_M hEH
  obtain ⟨P, hP, hEP⟩ := SylowIn.exists_ge (p := 2) hE h.EV_isPGroup
  have hPE : P ≤ EV x V := by
    apply h.cent_E_le hP.isPGroup
    intro g hg
    have hg' := hP.le hg
    exact h.centralizes_EV hg'.1.1 hg'.2
  have hP' : P = EV x V := le_antisymm hPE hEP
  rw [hP'] at hP
  exact hP

theorem card_cent_M [Finite G] {H : Subgroup G} (hEH : EV x V ≤ H) :
    ∃ o : ℕ, ¬ 2 ∣ o ∧ Nat.card ↥(Mm V H ⊓ centralizer ({x} : Set G)) = 8 * o := by
  have hS := h.EV_sylow_cent_M hEH
  have hE := h.EV_le_cent_M hEH
  have hrel := relIndex_mul_card (EV x V) (Mm V H ⊓ centralizer ({x} : Set G))
  rw [inf_of_le_left hE, h.card_EV] at hrel
  exact ⟨_, hS.2.2, by rw [← hrel]; ring⟩

end Out12

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
