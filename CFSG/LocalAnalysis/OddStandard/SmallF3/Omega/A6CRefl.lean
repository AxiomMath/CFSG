module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ι : Type} [Fintype ι] [DecidableEq ι] {c : ZMod 3}

private theorem a6c_commSp_signChange (fr : NFrame Q ι c) (J : Finset ι) :
    commSp (fr.signChange J) = Submodule.span (ZMod 3) (fr.b '' (J : Set ι)) := by
  ext v
  rw [mem_commSp_iff (fr.signChange_mul_self J), Module.Basis.mem_span_image]
  constructor
  · intro hv i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hiJ
    have h1 : fr.b.repr (((fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) v) i =
        fr.b.repr (-v) i := by rw [hv]
    rw [fr.repr_signChange J v i, map_neg, Finsupp.neg_apply,
      if_neg (by simpa only [Finset.mem_coe] using hiJ)] at h1
    have h2 : (2 : ZMod 3) * fr.b.repr v i = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h1
    exact hi ((mul_eq_zero.mp h2).resolve_left (by decide))
  · intro hsupp
    apply fr.b.repr.injective
    ext i
    rw [fr.repr_signChange J v i, map_neg, Finsupp.neg_apply]
    by_cases hiJ : i ∈ J
    · simp [hiJ]
    · have h0 : fr.b.repr v i = 0 := by
        by_contra hne
        have hmem : i ∈ ↑(fr.b.repr v).support :=
          Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne)
        exact hiJ (by simpa only [Finset.mem_coe] using hsupp hmem)
      simp [hiJ, h0]

private theorem a6c_finrank_span_frame (fr : NFrame Q ι c) (J : Finset ι) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (fr.b '' (J : Set ι))) = J.card := by
  have hli : LinearIndependent (ZMod 3) (fun i : J => fr.b (i : ι)) :=
    fr.b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : J => fr.b (i : ι)) = fr.b '' (J : Set ι) := by
    rw [show Set.range (fun i : J => fr.b (i : ι)) = Set.range (fr.b ∘ Subtype.val) from rfl,
      Set.range_comp, Subtype.range_coe]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]

theorem a6c_invDim_signChange_single (fr : NFrame Q ι c) (i : ι) :
    invDim (fr.signChange {i}) = 1 := by
  simp only [invDim]
  rw [a6c_commSp_signChange fr {i}, a6c_finrank_span_frame fr {i}, Finset.card_singleton]

theorem a6c_signChange_KM2 (hdim : Module.finrank (ZMod 3) V = 6) (fr : NFrame Q ι c) (i : ι) :
    KM2 (QuotientGroup.mk (orthToSim Q (fr.signChange {i}))) := by
  have htt := fr.signChange_mul_self {i}
  have hd := a6c_invDim_signChange_single fr i
  refine ⟨invSign (fr.signChange {i}), toProj Q (fr.signChange {i}), rfl, ?_,
    fr.signChange {i}, htt, Prod.ext hd rfl, rfl⟩
  intro h
  rcases toProj_eq_or_eq_piOrth (h.trans (map_one (toProj Q)).symm) with h1 | h1
  · have h0 := (invDim_eq_zero_iff htt).mpr h1
    omega
  · have h6 := (invDim_eq_finrank_iff htt).mpr (by rwa [mul_one] at h1)
    omega

end CFSG.OddStandard.SmallF3.Omega
