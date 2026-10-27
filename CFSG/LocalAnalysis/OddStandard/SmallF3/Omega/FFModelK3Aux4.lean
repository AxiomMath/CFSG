module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem commSp_blockHom {t : OGroup Q} (htt : t * t = 1)
    {a : OGroup (Q.restrict (fixSp t))} (haa : a * a = 1)
    {b : OGroup (Q.restrict (commSp t))} (hbb : b * b = 1) :
    commSp (blockHom htt (a, b)) =
      (commSp a).map (fixSp t).subtype ⊔ (commSp b).map (commSp t).subtype := by
  have hsq : blockHom htt (a, b) * blockHom htt (a, b) = 1 := by
    rw [← map_mul]
    have hprod : (a, b) * (a, b) = (1, 1) := by
      rw [Prod.mk_mul_mk]
      exact Prod.ext haa hbb
    rw [hprod]
    exact map_one (blockHom htt)
  have hdisj : Disjoint (fixSp t) (commSp t) := (isCompl_fixSp_commSp htt).disjoint
  apply le_antisymm
  · intro v hv
    rw [mem_commSp_iff hsq] at hv
    obtain ⟨u, w, rfl⟩ := exists_fixSp_add_commSp htt v
    have happ := blockHom_apply htt (a, b) u w
    rw [happ, neg_add] at hv
    have hsum : ((((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u : fixSp t) : V) + (u : V)) +
        ((((b : commSp t ≃ₗ[ZMod 3] commSp t) w : commSp t) : V) + (w : V)) = 0 := by
      rw [show ((((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u : fixSp t) : V) + (u : V)) +
          ((((b : commSp t ≃ₗ[ZMod 3] commSp t) w : commSp t) : V) + (w : V)) =
          ((((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u : fixSp t) : V) +
            (((b : commSp t ≃ₗ[ZMod 3] commSp t) w : commSp t) : V)) +
          ((u : V) + (w : V)) from by abel, hv]
      abel
    have hleft_zero : (((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u : fixSp t) : V) + (u : V) = 0 := by
      have hmem : (((b : commSp t ≃ₗ[ZMod 3] commSp t) w : commSp t) : V) + (w : V) ∈
          commSp t :=
        (commSp t).add_mem (((b : commSp t ≃ₗ[ZMod 3] commSp t) w)).2 w.2
      refine Submodule.disjoint_def.mp hdisj _
        ((fixSp t).add_mem (((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u)).2 u.2) ?_
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact (commSp t).neg_mem hmem
    have hright_zero : (((b : commSp t ≃ₗ[ZMod 3] commSp t) w : commSp t) : V) + (w : V) = 0 := by
      have hmem : (((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u : fixSp t) : V) + (u : V) ∈
          fixSp t :=
        (fixSp t).add_mem (((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u)).2 u.2
      refine Submodule.disjoint_def.mp hdisj _ ?_
        ((commSp t).add_mem (((b : commSp t ≃ₗ[ZMod 3] commSp t) w)).2 w.2)
      rw [eq_neg_of_add_eq_zero_right hsum]
      exact (fixSp t).neg_mem hmem
    have hau : (a : fixSp t ≃ₗ[ZMod 3] fixSp t) u = -u := by
      apply Subtype.ext
      exact eq_neg_of_add_eq_zero_left hleft_zero
    have hbw : (b : commSp t ≃ₗ[ZMod 3] commSp t) w = -w := by
      apply Subtype.ext
      exact eq_neg_of_add_eq_zero_left hright_zero
    rw [Submodule.mem_sup]
    exact ⟨(u : V), ⟨u, (mem_commSp_iff haa).mpr hau, rfl⟩,
      (w : V), ⟨w, (mem_commSp_iff hbb).mpr hbw, rfl⟩, rfl⟩
  · intro v hv
    rw [Submodule.mem_sup] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := hv
    rw [mem_commSp_iff hsq]
    obtain ⟨xa, hxa, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨ya, hya, rfl⟩ := Submodule.mem_map.mp hy
    show ((blockHom htt (a, b) : OGroup Q) : V ≃ₗ[ZMod 3] V) ((xa : V) + (ya : V)) =
      -((xa : V) + (ya : V))
    rw [blockHom_apply htt (a, b) xa ya]
    have hxa' := (mem_commSp_iff haa).mp hxa
    have hya' := (mem_commSp_iff hbb).mp hya
    rw [hxa', hya']
    simp only [Submodule.coe_neg, neg_add]

end CFSG.OddStandard.SmallF3.Omega
