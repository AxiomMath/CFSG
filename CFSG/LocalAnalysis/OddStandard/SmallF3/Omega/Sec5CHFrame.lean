module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5c_twoRes_conj_mem {A : Type} [Group A] {H H' : Subgroup A} {g x : A}
    (hHH' : ∀ y ∈ H, g * y * g⁻¹ ∈ H') (hx : x ∈ twoRes H) : g * x * g⁻¹ ∈ twoRes H' := by
  have h1 : (twoRes H).map (MulAut.conj g).toMonoidHom ≤ twoRes H' := by
    unfold twoRes
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, ⟨hy, hodd⟩, rfl⟩
    have h2 : orderOf ((MulAut.conj g) y) = orderOf y := MulEquiv.orderOf_eq (MulAut.conj g) y
    rw [MulAut.conj_apply] at h2
    refine ⟨hHH' y hy, ?_⟩
    show Odd (orderOf (g * y * g⁻¹))
    rw [h2]
    exact hodd
  exact h1 ⟨x, hx, rfl⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private def sec5c_cyc : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 3 4

private theorem sec5c_cyc_cube : sec5c_cyc ^ 3 = 1 := by decide

private theorem sec5c_cyc_alt : sec5c_cyc ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, sec5c_cyc, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

theorem sec5c_frame_witness (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {ζ : OGroup Q} (hζ2 : ζ * ζ = 1) (hζ : invType ζ = (4, 1)) :
    ∃ w ∈ twoRes (omegaGroup hQ ⊓ Subgroup.centralizer ({ζ} : Set (OGroup Q))),
      w * w = 1 ∧ invType w = (2, -1) := by
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  have hc4 : ({2, 3, 4, 5} : Finset (Fin 6)).card = 4 := by decide
  have hc2 : ({2, 3} : Finset (Fin 6)).card = 2 := by decide
  have hs2 := fr.signChange_mul_self ({2, 3, 4, 5} : Finset (Fin 6))
  have he2 := fr.signChange_mul_self ({2, 3} : Finset (Fin 6))
  have hs : invType (fr.signChange ({2, 3, 4, 5} : Finset (Fin 6))) = invType ζ := by
    rw [fr.invType_signChange hQ _ (by rw [hc4]; decide), hc4, hζ]
    exact Prod.ext rfl (by decide)
  obtain ⟨c, hcΩ, hc⟩ := exists_mem_omegaGroup_conj hQ (by omega) hs2 hζ2 hs
  have hmem : fr.signChange ({2, 3} : Finset (Fin 6)) ∈ twoRes (omegaGroup hQ ⊓
      Subgroup.centralizer ({fr.signChange ({2, 3, 4, 5} : Finset (Fin 6))} : Set (OGroup Q))) := by
    refine fr.signChange_mem_twoRes (σ := sec5c_cyc) sec5c_cyc_cube ?_ ?_ (by decide)
    · refine Subgroup.mem_inf.mpr ⟨fr.permOrth_mem_omegaGroup hQ sec5c_cyc_alt, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (fr.permOrth_comm_signChange (σ := sec5c_cyc) (by decide)).symm
    · refine Subgroup.mem_inf.mpr
        ⟨fr.signChange_mem_omegaGroup hQ _ (by rw [hc2]; decide), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh, fr.signChange_mul, fr.signChange_mul, symmDiff_comm]
  refine ⟨c * fr.signChange ({2, 3} : Finset (Fin 6)) * c⁻¹, ?_, ?_, ?_⟩
  · refine sec5c_twoRes_conj_mem ?_ hmem
    intro y hy
    obtain ⟨hyΩ, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hcΩ hyΩ) (inv_mem hcΩ), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    have hcomm : fr.signChange ({2, 3, 4, 5} : Finset (Fin 6)) * y =
        y * fr.signChange ({2, 3, 4, 5} : Finset (Fin 6)) :=
      Subgroup.mem_centralizer_iff.mp hyC _ (Set.mem_singleton _)
    rw [hh, ← hc]
    calc c * fr.signChange ({2, 3, 4, 5} : Finset (Fin 6)) * c⁻¹ * (c * y * c⁻¹)
        = c * (fr.signChange ({2, 3, 4, 5} : Finset (Fin 6)) * y) * c⁻¹ := by group
      _ = c * (y * fr.signChange ({2, 3, 4, 5} : Finset (Fin 6))) * c⁻¹ := by rw [hcomm]
      _ = c * y * c⁻¹ * (c * fr.signChange ({2, 3, 4, 5} : Finset (Fin 6)) * c⁻¹) := by group
  · calc c * fr.signChange ({2, 3} : Finset (Fin 6)) * c⁻¹ *
          (c * fr.signChange ({2, 3} : Finset (Fin 6)) * c⁻¹)
        = c * (fr.signChange ({2, 3} : Finset (Fin 6)) *
            fr.signChange ({2, 3} : Finset (Fin 6))) * c⁻¹ := by group
      _ = 1 := by rw [he2]; group
  · rw [invType_conj hQ he2 c, fr.invType_signChange hQ _ (by rw [hc2]; decide), hc2]
    exact Prod.ext rfl (by decide)

end CFSG.OddStandard.SmallF3.Omega
