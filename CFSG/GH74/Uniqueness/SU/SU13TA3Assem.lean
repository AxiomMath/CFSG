module

public import CFSG.GH74.Uniqueness.SU.SU13TA3FT
public import CFSG.GH74.Uniqueness.SU.SU13TA3P3
public import CFSG.GH74.Uniqueness.SU.SU13TA3E

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13
  CFSG.GH74.Uniqueness.SU.SU4

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 10)}

theorem nonempty_fpart10 (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    Nonempty (FPart10 z (c.elts hπ hz hz1)) := by
  obtain ⟨T, hT, hzT, huniq, hquat⟩ := exists_T hπ c hz hz1
  obtain ⟨h5, h7⟩ := exists_orderOf_five_seven_Fh hπ
  have hcen : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcen g)
  refine ⟨⟨⟨Fh π, fun f _ => hcen f, ker_le_Fh hz, ?_, ?_, ?_, ?_, T, hT, hzT, huniq, hquat⟩, h5, h7⟩⟩
  · intro f hf
    exact (commute_s₁_of_mem_Fh hπ c hf).eq
  · show centralizer ({c.s₁} : Set H) ⊓ centralizer ({z} : Set H) = zpowers c.s₁ ⊔ Fh π
    rw [hzz, inf_top_eq]
    exact centralizer_s₁_eq hπ c
  · intro N hN hnorm hodd
    exact Fh_noOdd hπ hN hnorm hodd
  · intro N hN hnorm hne
    exact ker_le_of_normal_Fh hπ hN hnorm hne hz

theorem p3part (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    P3Part z (c.elts hπ hz hz1) :=
  ⟨isSylowIn_s₃ hπ c hz hz1⟩

theorem epart10 [Finite H] (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker)
    (hz1 : z ≠ 1) : EPart10 z (c.elts hπ hz hz1) := by
  obtain ⟨E, Es, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := exists_E hπ c hz hz1
  exact ⟨E, Es, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
