module

public import CFSG.GH74.Uniqueness.SU.SU13TA9Trans
public import CFSG.GH74.Uniqueness.SU.SU13Data9

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] {z : G}

@[expose] noncomputable def Elts9.transfer {e : Elts (Hc z) (zH z)} (e9 : Elts9 (zH z) e) :
    Elts9 z e.transfer where
  s₄ := (e9.s₄ : G)
  x := (e9.x : G)
  s₄_comm := coe_mul_z e9.s₄
  s₄_ord := by rw [Subgroup.orderOf_coe]; exact e9.s₄_ord
  x_comm := coe_mul_z e9.x
  x_ord := by rw [Subgroup.orderOf_coe]; exact e9.x_ord
  t_s₄ := congrArg Subtype.val e9.t_s₄
  x_s₁ := congrArg Subtype.val e9.x_s₁
  x_s₂ := congrArg Subtype.val e9.x_s₂
  x_s₄ := congrArg Subtype.val e9.x_s₄
  s₄_class := by
    obtain ⟨h, -, hh⟩ := e9.s₄_class
    exact ⟨(h : G), coe_mul_z h, congrArg Subtype.val hh⟩

theorem Elts9.transfer_s₄ {e : Elts (Hc z) (zH z)} (e9 : Elts9 (zH z) e) :
    e9.transfer.s₄ = (e9.s₄ : G) := rfl

theorem Elts9.transfer_x {e : Elts (Hc z) (zH z)} (e9 : Elts9 (zH z) e) :
    e9.transfer.x = (e9.x : G) := rfl

variable [Finite G]

@[expose] noncomputable def FPart9.transfer {e : Elts (Hc z) (zH z)} (f : FPart9 (zH z) e) :
    FPart9 z e.transfer where
  toFPart := f.toFPart.transfer
  F_card := by
    show Nat.card ↥(f.F.map (incl z)) = 720
    rw [Subgroup.card_map_of_injective incl_injective]
    exact f.F_card

theorem MPart9.transfer {e : Elts (Hc z) (zH z)} {E : Subgroup (Hc z)} (p : MPart9 (zH z) e E) :
    MPart9 z e.transfer (E.map (incl z)) := by
  have hM : (centralizer ({e.s₂} : Set (Hc z)) ⊓ centralizer ({zH z} : Set (Hc z))).map (incl z) =
      centralizer ({e.transfer.s₂} : Set G) ⊓ centralizer ({z} : Set G) := by
    rw [centralizer_zH, inf_top_eq, map_centralizer_singleton]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hM, Subgroup.card_map_of_injective incl_injective]
    exact p.card
  · rw [← hM]
    exact Subgroup.map_mono p.E_le
  · rw [← hM, oc_map, p.oc_eq]
  · rw [← hM]
    obtain ⟨φ⟩ := p.kl
    exact ⟨(MbarEquiv _).symm.trans φ⟩
  · intro x hx htx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : e.t * y = y * e.t := incl_injective (by rw [map_mul, map_mul]; exact htx)
    have h2 := Subgroup.mem_map_of_mem (incl z) (p.cent_t y hy h1)
    rwa [MonoidHom.map_zpowers] at h2

end CFSG.GH74.Uniqueness.SU.SU13
