module

public import CFSG.GH74.Uniqueness.SU.SU13Data9
public import CFSG.GH74.Uniqueness.SU.SU13TA9Elts
public import CFSG.GH74.Uniqueness.SU.SU13TA9FT

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem isThreeCycle_pb_inv : (pb⁻¹).IsThreeCycle := isThreeCycle_pb.inv

theorem cycleType_ea_mul_eb_inv :
    ((ea * eb⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {3, 3} := by
  show (pa * pb⁻¹).cycleType = {3, 3}
  rw [disjoint_pa_pb.inv_right.cycleType_mul, isThreeCycle_pa.cycleType,
    isThreeCycle_pb_inv.cycleType]
  rfl

theorem x_ne_one (c : Cfg π) : c.x ≠ 1 := fun h => by
  have := c.π_x
  rw [h, map_one] at this
  exact ex_ne_one this.symm

@[expose] noncomputable def Cfg.elts9 (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker)
    (hz1 : z ≠ 1) : Elts9 z (c.elts hπ hz hz1) where
  s₄ := c.s₄
  x := c.x
  s₄_comm := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz) c.s₄
  s₄_ord := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₄_pow (fun h => by
    have := c.π_s₄
    rw [h, map_one] at this
    exact ea_mul_eb_inv_ne_one this.symm)
  x_comm := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz) c.x
  x_ord := orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) c.x_sq (x_ne_one c)
  t_s₄ := c.t_mul_s₄ hπ
  x_s₁ := c.x_mul_s₁ hπ
  x_s₂ := c.x_mul_s₂ hπ
  x_s₄ := mul_inv_eq_iff_eq_mul.mp (c.x_mul_s₄ hπ)
  s₄_class := by
    have hcen := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
    obtain ⟨g, hg⟩ := isConj_iff.mp (hπ.isConj_of_pow_three_of_isConj c.s₄_pow c.s₂_pow (by
      rw [c.π_s₄, c.π_s₂]
      exact isConj_alternatingGroup_of_cycleType_eq (by norm_num) (c := {3, 3})
        (Or.inr (Or.inl rfl)) cycleType_ea_mul_eb_inv cycleType_ea_mul_eb))
    exact ⟨g, hcen g, hg⟩

theorem exists_fpart9 (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    ∃ f : FPart9 z (c.elts hπ hz hz1), f.F = Fh π := by
  obtain ⟨T, hT, hzT, huniq, hquat⟩ := exists_T hπ c hz hz1
  have hcen : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcen g)
  refine ⟨⟨⟨Fh π, fun f _ => hcen f, ker_le_Fh hz, ?_, ?_, ?_, ?_, T, hT, hzT, huniq, hquat⟩,
    card_Fh hπ⟩, rfl⟩
  · intro f hf
    exact (commute_s₁_of_mem_Fh hπ c hf).eq
  · show centralizer ({c.s₁} : Set H) ⊓ centralizer ({z} : Set H) = zpowers c.s₁ ⊔ Fh π
    rw [hzz, inf_top_eq]
    exact centralizer_s₁_eq hπ c
  · intro N hN hnorm hodd
    exact Fh_noOdd hπ hN hnorm hodd
  · intro N hN hnorm hne
    exact ker_le_of_normal_Fh hπ hN hnorm hne hz

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
