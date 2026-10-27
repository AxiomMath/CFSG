module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

structure Sec5CDAbs (L B : Subgroup G) (r : G) (i : Fin 6) (fr : NFrame Q (Fin 6) 1)
    (φc : ↥L →* omegaGroup hQ) : Prop where
  dim : Module.finrank (ZMod 3) V = 6
  sgn : quadSign Q = -1
  cover : OddCentralCover φc
  B_le : B ≤ L
  B_sq : ∀ b ∈ B, b * b = 1
  B_comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  B_map : ∀ b : ↥L, (b : G) ∈ B → (φc b : OGroup Q) ∈ ffB0 fr
  B_onto : ∀ g ∈ ffB0 fr, ∃ b : ↥L, (b : G) ∈ B ∧ (φc b : OGroup Q) = g
  r_sq : r * r = 1
  r_not_mem : r ∉ L
  r_comm : ∀ b ∈ B, r * b = b * r
  r_norm : r ∈ normalizer (L : Set G)
  r_act : ∀ l l' : ↥L, (l' : G) = r * l * r⁻¹ →
    (φc l' : OGroup Q) = fr.signChange {i} * (φc l : OGroup Q) * (fr.signChange {i})⁻¹

noncomputable def sec5c_liftL (L B : Subgroup G) (φc : ↥L →* omegaGroup hQ) (g : OGroup Q) : ↥L :=
  open scoped Classical in
  if hg : ∃ b : ↥L, (b : G) ∈ B ∧ (φc b : OGroup Q) = g then Classical.choose hg else 1

namespace Sec5CDAbs

variable {L B : Subgroup G} {r : G} {i : Fin 6} {fr : NFrame Q (Fin 6) 1}
  {φc : ↥L →* omegaGroup hQ} (h : Sec5CDAbs L B r i fr φc)

include h

theorem liftL_spec {g : OGroup Q} (hg : g ∈ ffB0 fr) :
    (sec5c_liftL L B φc g : G) ∈ B ∧ (φc (sec5c_liftL L B φc g) : OGroup Q) = g := by
  have hex : ∃ b : ↥L, (b : G) ∈ B ∧ (φc b : OGroup Q) = g := h.B_onto g hg
  unfold sec5c_liftL
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem liftL_mem {g : OGroup Q} (hg : g ∈ ffB0 fr) : (sec5c_liftL L B φc g : G) ∈ B :=
  (h.liftL_spec hg).1

theorem map_liftL {g : OGroup Q} (hg : g ∈ ffB0 fr) :
    (φc (sec5c_liftL L B φc g) : OGroup Q) = g :=
  (h.liftL_spec hg).2

theorem liftL_unique {b : ↥L} (hb : (b : G) ∈ B) :
    sec5c_liftL L B φc (φc b : OGroup Q) = b := by
  have hg : (φc b : OGroup Q) ∈ ffB0 fr := h.B_map b hb
  obtain ⟨h1, h2⟩ := h.liftL_spec hg
  refine h.cover.eq_of_mul_self_eq_one ?_ ?_ (Subtype.ext h2)
  · exact Subtype.ext (h.B_sq _ h1)
  · exact Subtype.ext (h.B_sq _ hb)

theorem liftL_sq {g : OGroup Q} (hg : g ∈ ffB0 fr) :
    sec5c_liftL L B φc g * sec5c_liftL L B φc g = 1 :=
  Subtype.ext (h.B_sq _ (h.liftL_mem hg))

theorem liftL_one : sec5c_liftL L B φc 1 = 1 := by
  have h1 : ((1 : ↥L) : G) ∈ B := B.one_mem
  have h2 := h.liftL_unique h1
  rwa [show ((φc 1 : omegaGroup hQ) : OGroup Q) = 1 by rw [map_one]; rfl] at h2

theorem liftL_mul {g g' : OGroup Q} (hg : g ∈ ffB0 fr) (hg' : g' ∈ ffB0 fr) :
    sec5c_liftL L B φc (g * g') = sec5c_liftL L B φc g * sec5c_liftL L B φc g' := by
  have hmem : ((sec5c_liftL L B φc g * sec5c_liftL L B φc g' : ↥L) : G) ∈ B :=
    B.mul_mem (h.liftL_mem hg) (h.liftL_mem hg')
  have h1 := h.liftL_unique hmem
  rw [map_mul, Subgroup.coe_mul, h.map_liftL hg, h.map_liftL hg'] at h1
  exact h1

theorem r_comm_liftL {g : OGroup Q} (hg : g ∈ ffB0 fr) :
    r * (sec5c_liftL L B φc g : G) = (sec5c_liftL L B φc g : G) * r :=
  h.r_comm _ (h.liftL_mem hg)

end Sec5CDAbs

end CFSG.OddStandard.SmallF3.Omega
