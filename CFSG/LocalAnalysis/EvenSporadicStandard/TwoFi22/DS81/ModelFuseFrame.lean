module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelFuseSyl

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.Wong77.Module
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_conj_frame :
    ∃ g : CFSG.Sporadic.Fi22.J, ∀ y ∈ CFSG.Sporadic.Fi22.D, y ∈ CFSG.Sporadic.Fi22.slvl 0 →
      g⁻¹ * y * g ∈ fjProj.range := by
  have hE : IsPGroup 2 fjProj.range :=
    isPGroup_word.of_surjective fjProj.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  have hSi : ∀ i : Fin 23, piC (fjQ i) ∈ (S : Subgroup CFSG.Sporadic.Fi22.J) := fun i =>
    hES ⟨eVec i, fjProj_eVec i⟩
  obtain ⟨g, hg⟩ := exists_conj_into_slvl S
  have hD : ∀ i : {i : Fin 23 // i ≠ 0}, piC (fjQ i.1) ∈ CFSG.Sporadic.Fi22.D := fun i => by
    rw [fjQ_eq_ofStar i.2]
    exact piC_ofStar_mem_D _
  have hconj : ∀ x : CFSG.Sporadic.Fi22.J, x ∈ CFSG.Sporadic.Fi22.D →
      g * x * g⁻¹ ∈ CFSG.Sporadic.Fi22.D := fun x hx =>
    (show IsConj CFSG.Sporadic.Fi22.a x from hx).trans (isConj_iff.2 ⟨g, rfl⟩)
  let f : {i : Fin 23 // i ≠ 0} → {y : CFSG.Sporadic.Fi22.J //
      y ∈ CFSG.Sporadic.Fi22.D ∧ y ∈ CFSG.Sporadic.Fi22.slvl 0} :=
    fun i => ⟨g * piC (fjQ i.1) * g⁻¹, hconj _ (hD i), hg _ (hSi i.1)⟩
  have hinj : Function.Injective f := by
    intro i j h
    have h0 := congrArg Subtype.val h
    have h'' : piC (fjQ i.1) = piC (fjQ j.1) := by
      have h' : g * piC (fjQ i.1) * g⁻¹ = g * piC (fjQ j.1) * g⁻¹ := h0
      simpa using h'
    rw [fjQ_eq_ofStar i.2, fjQ_eq_ofStar j.2] at h''
    have hij : fjPt i.1 = fjPt j.1 := congrArg Subtype.val (ofStar_injective_of_piC h'')
    by_contra hne
    exact fjPt_ne (fun e => hne (Subtype.ext e)) hij
  have hcard : Nat.card {y : CFSG.Sporadic.Fi22.J //
      y ∈ CFSG.Sporadic.Fi22.D ∧ y ∈ CFSG.Sporadic.Fi22.slvl 0} ≤
      Nat.card {i : Fin 23 // i ≠ 0} := by
    refine card_D_slvl_le.trans ?_
    rw [Nat.card_eq_fintype_card]
    exact le_of_eq (by decide)
  refine ⟨g, fun y hyD hyS => ?_⟩
  obtain ⟨i, hi⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨y, hyD, hyS⟩
  have hy : y = g * piC (fjQ i.1) * g⁻¹ := (congrArg Subtype.val hi).symm
  rw [hy]
  have : g⁻¹ * (g * piC (fjQ i.1) * g⁻¹) * g = piC (fjQ i.1) := by group
  rw [this, ← fjProj_eVec i.1]
  exact ⟨eVec i.1, rfl⟩

theorem exists_conj_fuseEb0_le :
    ∃ g : CFSG.Sporadic.Fi22.J, ∀ z ∈ fuseEb0, g⁻¹ * z * g ∈ fjProj.range := by
  obtain ⟨g, hg⟩ := exists_conj_frame
  refine ⟨g, fun z hz => ?_⟩
  have hle : fuseEb0 ≤ fjProj.range.comap (MulAut.conj g⁻¹).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    simpa using hg y hy.1 hy.2
  have := hle hz
  rw [Subgroup.mem_comap] at this
  simpa using this

theorem exists_conj_mem_range
    {x : CFSG.Sporadic.Fi22.J} (hx : orderOf x = 2) :
    ∃ h : CFSG.Sporadic.Fi22.J, h * x * h⁻¹ ∈ fjProj.range := by
  obtain ⟨g, hg⟩ := exists_conj_fuseEb0_le
  obtain ⟨c, hc⟩ := exists_conj_mem_fuseEb0 hx
  refine ⟨g⁻¹ * c, ?_⟩
  have e : g⁻¹ * c * x * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * x * c⁻¹) * g := by group
  rw [e]
  exact hg _ hc

end CFSG.EvenSporadicStandard.TwoFi22.DS81
