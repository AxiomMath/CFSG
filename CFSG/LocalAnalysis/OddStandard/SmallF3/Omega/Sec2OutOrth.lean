module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions (mem_commSpace sub_mem_commSpace
  polar_sub_eq_polar_sub map_add_eq)

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem quadSign_restrict_congr' {A B : Submodule (ZMod 3) V} (h : A = B) :
    quadSign (Q.restrict A) = quadSign (Q.restrict B) := by
  rw [h]

theorem mem_fixSp_of_polar_eq_zero (hQ : Q.Nondegenerate) {g : OGroup Q} (hg : g * g = 1) {w : V}
    (hw : ∀ v ∈ commSp g, QuadraticMap.polar Q v w = 0) : w ∈ fixSp g := by
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hg' : (g : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) = 1 := by
    simpa using congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) hg
  rw [mem_fixSp_iff]
  have h0 : (g : V ≃ₗ[ZMod 3] V) w - w = 0 := hB.1 _ fun y => by
    rw [QuadraticMap.polarBilin_apply_apply, polar_sub_eq_polar_sub g.2 hg',
      QuadraticMap.polar_comm]
    exact hw _ (sub_mem_commSpace _ y)
  exact sub_eq_zero.mp h0

theorem commSp_le_fixSp_of_orth (hQ : Q.Nondegenerate) {g h : OGroup Q} (hg : g * g = 1)
    (horth : ∀ v ∈ commSp g, ∀ w ∈ commSp h, QuadraticMap.polar Q v w = 0) :
    commSp h ≤ fixSp g :=
  fun w hw => mem_fixSp_of_polar_eq_zero hQ hg fun v hv => horth v hv w hw

theorem mul_comm_of_orth (hQ : Q.Nondegenerate) {g h : OGroup Q} (hg : g * g = 1)
    (hh : h * h = 1)
    (horth : ∀ v ∈ commSp g, ∀ w ∈ commSp h, QuadraticMap.polar Q v w = 0) :
    g * h = h * g := by
  have h1 : commSp h ≤ fixSp g := commSp_le_fixSp_of_orth hQ hg horth
  have h2 : commSp g ≤ fixSp h := commSp_le_fixSp_of_orth hQ hh fun v hv w hw => by
    rw [QuadraticMap.polar_comm]
    exact horth w hw v hv
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  show (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) v) = (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v)
  have e1 : (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) v - v) =
      (h : V ≃ₗ[ZMod 3] V) v - v := mem_fixSp_iff.mp (h1 (sub_mem_commSpace _ v))
  have e2 : (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v - v) =
      (g : V ≃ₗ[ZMod 3] V) v - v := mem_fixSp_iff.mp (h2 (sub_mem_commSpace _ v))
  rw [map_sub] at e1 e2
  have e3 : (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) v) =
      (h : V ≃ₗ[ZMod 3] V) v - v + (g : V ≃ₗ[ZMod 3] V) v := by
    rw [← e1]; abel
  have e4 : (h : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) =
      (g : V ≃ₗ[ZMod 3] V) v - v + (h : V ≃ₗ[ZMod 3] V) v := by
    rw [← e2]; abel
  rw [e3, e4]
  abel

theorem mul_mul_self_of_orth (hQ : Q.Nondegenerate) {g h : OGroup Q} (hg : g * g = 1)
    (hh : h * h = 1)
    (horth : ∀ v ∈ commSp g, ∀ w ∈ commSp h, QuadraticMap.polar Q v w = 0) :
    (g * h) * (g * h) = 1 := by
  have hc := mul_comm_of_orth hQ hg hh horth
  calc (g * h) * (g * h) = g * (h * g) * h := by group
    _ = g * (g * h) * h := by rw [← hc]
    _ = (g * g) * (h * h) := by group
    _ = 1 := by rw [hg, hh, mul_one]

theorem commSp_mul_of_orth (hQ : Q.Nondegenerate) {g h : OGroup Q} (hg : g * g = 1)
    (hh : h * h = 1)
    (horth : ∀ v ∈ commSp g, ∀ w ∈ commSp h, QuadraticMap.polar Q v w = 0) :
    commSp (g * h) = commSp g ⊔ commSp h := by
  have h1 : commSp h ≤ fixSp g := commSp_le_fixSp_of_orth hQ hg horth
  have h2 : commSp g ≤ fixSp h := commSp_le_fixSp_of_orth hQ hh fun v hv w hw => by
    rw [QuadraticMap.polar_comm]
    exact horth w hw v hv
  have hgh := mul_mul_self_of_orth hQ hg hh horth
  apply le_antisymm
  · intro v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    have e1 : (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) w - w) =
        (h : V ≃ₗ[ZMod 3] V) w - w := mem_fixSp_iff.mp (h1 (sub_mem_commSpace _ w))
    rw [map_sub] at e1
    have e3 : ((g * h : OGroup Q) : V ≃ₗ[ZMod 3] V) w - w =
        ((g : V ≃ₗ[ZMod 3] V) w - w) + ((h : V ≃ₗ[ZMod 3] V) w - w) := by
      show (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) w) - w = _
      have : (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) w) =
          (h : V ≃ₗ[ZMod 3] V) w - w + (g : V ≃ₗ[ZMod 3] V) w := by
        rw [← e1]; abel
      rw [this]
      abel
    rw [e3]
    exact Submodule.add_mem_sup (sub_mem_commSpace _ w) (sub_mem_commSpace _ w)
  · refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · rw [mem_commSp_iff hgh]
      have hv1 : (h : V ≃ₗ[ZMod 3] V) v = v := mem_fixSp_iff.mp (h2 hv)
      have hv2 : (g : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff hg).mp hv
      show (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) v) = -v
      rw [hv1, hv2]
    · rw [mem_commSp_iff hgh]
      have hv1 : (g : V ≃ₗ[ZMod 3] V) v = v := mem_fixSp_iff.mp (h1 hv)
      have hv2 : (h : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff hh).mp hv
      show (g : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V) v) = -v
      rw [hv2, map_neg, hv1]

theorem invType_mul_of_orth (hQ : Q.Nondegenerate) {g h : OGroup Q} (hg : g * g = 1)
    (hh : h * h = 1)
    (horth : ∀ v ∈ commSp g, ∀ w ∈ commSp h, QuadraticMap.polar Q v w = 0) :
    invType (g * h) = (invDim g + invDim h,
      invSign g * invSign h * (-1) ^ (invDim g * invDim h)) := by
  have h1 : commSp h ≤ fixSp g := commSp_le_fixSp_of_orth hQ hg horth
  have hcomm := commSp_mul_of_orth hQ hg hh horth
  have hdisj : Disjoint (commSp g) (commSp h) :=
    ((isCompl_fixSp_commSp hg).disjoint.symm).mono_right h1
  have hinf : commSp g ⊓ commSp h = ⊥ := disjoint_iff.mp hdisj
  have hA := nondegenerate_restrict_commSp hQ hg
  have hB := nondegenerate_restrict_commSp hQ hh
  have hdim : Module.finrank (ZMod 3) ↥(commSp g ⊔ commSp h) =
      Module.finrank (ZMod 3) ↥(commSp g) + Module.finrank (ZMod 3) ↥(commSp h) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (commSp g) (commSp h)
    rw [hinf, finrank_bot] at this
    omega
  have hf : Function.Bijective
      ((Submodule.inclusion (le_sup_left : commSp g ≤ commSp g ⊔ commSp h)).coprod
        (Submodule.inclusion (le_sup_right : commSp h ≤ commSp g ⊔ commSp h))) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨a, b⟩ hab
      have hab' : (a : V) + (b : V) = 0 := congrArg Subtype.val hab
      have hamem : (a : V) ∈ commSp g ⊓ commSp h := by
        refine ⟨a.2, ?_⟩
        have : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left hab'
        rw [this]
        exact (commSp h).neg_mem b.2
      rw [hinf, Submodule.mem_bot] at hamem
      have hbz : (b : V) = 0 := by rw [hamem, zero_add] at hab'; exact hab'
      exact Prod.ext (Subtype.ext hamem) (Subtype.ext hbz)
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hequiv : ((Q.restrict (commSp g)).prod (Q.restrict (commSp h))).Equivalent
      (Q.restrict (commSp g ⊔ commSp h)) := by
    refine ⟨⟨LinearEquiv.ofBijective _ hf, fun p => ?_⟩⟩
    show Q ((p.1 : V) + (p.2 : V)) = Q (p.1 : V) + Q (p.2 : V)
    rw [map_add_eq Q, horth _ p.1.2 _ p.2.2, add_zero]
  have hsign : quadSign (Q.restrict (commSp (g * h))) = quadSign (Q.restrict (commSp g)) *
      quadSign (Q.restrict (commSp h)) *
        (-1) ^ (Module.finrank (ZMod 3) ↥(commSp g) * Module.finrank (ZMod 3) ↥(commSp h)) := by
    rw [quadSign_restrict_congr' hcomm, ← quadSign_congr (hA.prod hB) hequiv]
    exact quadSign_prod hA hB
  refine Prod.ext ?_ hsign
  show Module.finrank (ZMod 3) ↥(commSp (g * h)) = _
  rw [hcomm, hdim]
  rfl

end CFSG.OddStandard.SmallF3.Omega
