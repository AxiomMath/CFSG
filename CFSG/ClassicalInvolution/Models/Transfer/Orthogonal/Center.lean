module

public import CFSG.ClassicalInvolution.Models.Transfer.Basic
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Lemma610

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_one_or_eq_neg_of_mem_scalars [Nontrivial V] {z : V ≃ₗ[K] V} (hz : z ∈ scalars K V)
    (hz2 : z * z = 1) : z = 1 ∨ z = LinearEquiv.neg K := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hz
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hcc : c * c = 1 := by
    have h1 : (z * z) v = v := by rw [hz2]; rfl
    rw [LinearEquiv.mul_apply, hc v, map_smul, hc v, smul_smul] at h1
    have : (c * c - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  rcases mul_self_eq_one_iff.mp hcc with h | h
  · left
    ext x
    rw [hc x, h, one_smul]
    rfl
  · right
    ext x
    rw [hc x, h, neg_one_smul]
    rfl

variable (Q) in
@[expose] def CenterScalar : Prop :=
  Subgroup.center (elementaryGroup Q) ≤ (scalars K V).subgroupOf (elementaryGroup Q)

theorem center_elementaryGroup_eq [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T) (hTQ : ∀ x ∈ T, Q x = 0) :
    Subgroup.center (elementaryGroup Q) = (scalars K V).subgroupOf (elementaryGroup Q) := by
  have hsimple := isSimpleGroup_projElementary hQ hT hTQ
  have hS : (scalars K V).subgroupOf (elementaryGroup Q) ≤
      Subgroup.center (elementaryGroup Q) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (commute_of_mem_scalars hx y).symm
  have hnc : ∃ a b : ProjElementary Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : IsMulCommutative (ProjElementary Q) := ⟨⟨h⟩⟩
    have : Group.IsPerfect (ProjElementary Q) :=
      have : Group.IsPerfect (elementaryGroup Q) :=
        ⟨commutator_elementaryGroup_eq_top' hQ hT hTQ⟩
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.not_isMulCommutative _ ‹_›
  exact CFSG.LieType.CurtisTits.center_eq_of_isSimpleGroup_quotient _ hS hsimple hnc

theorem centerScalar_of_totallySingular [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) : CenterScalar Q :=
  (center_elementaryGroup_eq hQ hT hTQ).le

theorem two_mul_finrank_le [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hTQ : ∀ x ∈ T, Q x = 0) :
    2 * Module.finrank K T ≤ Module.finrank K V := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal hQ T
  have hle : T ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) T := by
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [polarBilin_apply_apply, QuadraticMap.polar, hTQ _ (T.add_mem hx hy), hTQ x hx, hTQ y hy]
    simp
  have h2 := Submodule.finrank_mono hle
  omega

theorem four_lt_finrank_of_totallySingular [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) : 4 < Module.finrank K V := by
  have := two_mul_finrank_le hQ hTQ
  omega

theorem eq_one_or_eq_neg_of_mem_center [Nontrivial V] (hZ : CenterScalar Q)
    {z : ↥(elementaryGroup Q)} (hz : z ∈ Subgroup.center (elementaryGroup Q)) (hz2 : z * z = 1) :
    z = 1 ∨ (z : V ≃ₗ[K] V) = LinearEquiv.neg K := by
  have hs : (z : V ≃ₗ[K] V) ∈ scalars K V := Subgroup.mem_subgroupOf.mp (hZ hz)
  rcases eq_one_or_eq_neg_of_mem_scalars hs (congrArg Subtype.val hz2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr h

theorem mem_elementaryGroup_of_isFundamental {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) : i ∈ elementaryGroup Q :=
  h.le_elementaryGroup h.mem

@[expose] def fundElt {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    ↥(elementaryGroup Q) :=
  ⟨i, mem_elementaryGroup_of_isFundamental h⟩

theorem coe_fundElt {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    (fundElt h : V ≃ₗ[K] V) = i :=
  rfl

theorem fundElt_mul_self {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    fundElt h * fundElt h = 1 :=
  Subtype.ext h.mul_self

theorem finrank_negSpace_of_isFundamental [Finite K] (hodd : Odd (Nat.card K))
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    Module.finrank K (negSpace i) = 4 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  rw [negSpace_La_neg_one h2, Frame.finrank_span]

theorem finrank_negSpace_add_finrank_posSpace [Finite K] [FiniteDimensional K V]
    (hodd : Odd (Nat.card K)) {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    Module.finrank K (negSpace i) + Module.finrank K (posSpace i) = Module.finrank K V := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  rw [negSpace_La_neg_one h2, posSpace_La_neg_one h2]
  exact Submodule.finrank_add_eq_of_isCompl (Frame.isCompl_span_perp F)

section Kernel

variable [Finite K] (hodd : Odd (Nat.card K))

include hodd

theorem not_mem_center_of_isFundamental (hZ : CenterScalar Q) (hdim : 4 < Module.finrank K V)
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    fundElt h ∉ Subgroup.center (elementaryGroup Q) := by
  intro hc
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  rcases eq_one_or_eq_neg_of_mem_center hZ hc (fundElt_mul_self h) with h1 | h1
  · exact h.ne_one hodd (congrArg Subtype.val h1)
  · have hneg : negSpace i = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [negSpace, Module.End.mem_eigenspace_iff, neg_one_smul]
      have : i = LinearEquiv.neg K := h1
      rw [this]
      rfl
    have h4 := finrank_negSpace_of_isFundamental hodd h
    rw [hneg, finrank_top] at h4
    omega

theorem map_fundElt_ne_one {X : Type*} [Group X] {θ : ↥(elementaryGroup Q) →* X}
    (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q)) (hZ : CenterScalar Q)
    (hdim : 4 < Module.finrank K V) {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) : θ (fundElt h) ≠ 1 :=
  fun h1 => not_mem_center_of_isFundamental hodd hZ hdim h (hker (MonoidHom.mem_ker.mpr h1))

theorem eq_one_of_mem_ker_of_isFundamental {X : Type*} [Group X] {θ : ↥(elementaryGroup Q) →* X}
    (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q)) (hZ : CenterScalar Q)
    (hdim : 4 < Module.finrank K V) {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) :
    ∀ z ∈ L.subgroupOf (elementaryGroup Q), z ∈ θ.ker → z = 1 := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact eq_one_of_mem_ker_of_equiv_sl2 θ hodd hker
    ((Subgroup.subgroupOfEquivOfLe h.le_elementaryGroup).trans e.symm)
    (Subgroup.mem_subgroupOf.mpr h.mem)
    (by rw [show fundElt h = ⟨i, _⟩ from rfl, Subgroup.orderOf_mk]; exact h.orderOf_eq_two hodd)
    (map_fundElt_ne_one hodd hker hZ hdim h)

theorem eq_of_map_eq_of_isFundamental [FiniteDimensional K V] {X : Type*} [Group X]
    {θ : ↥(elementaryGroup Q) →* X} (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q))
    (hZ : CenterScalar Q) (hdim : 4 < Module.finrank K V)
    (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ) {L L₀ : Subgroup (V ≃ₗ[K] V)}
    {i i₀ : V ≃ₗ[K] V} (h : IsFundamental Q L i) (h₀ : IsFundamental Q L₀ i₀)
    (hθ : θ (fundElt h₀) = θ (fundElt h)) : i₀ = i := by
  have hz : fundElt h₀ * (fundElt h)⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, mul_inv_cancel]
  have hzi : fundElt h₀ = (fundElt h₀ * (fundElt h)⁻¹) * fundElt h := by
    rw [inv_mul_cancel_right]
  have hzc := hker hz
  have hz2 : (fundElt h₀ * (fundElt h)⁻¹) * (fundElt h₀ * (fundElt h)⁻¹) = 1 :=
    sq_eq_one_of_mul_sq_eq_one (fundElt_mul_self h) hzc (by rw [← hzi]; exact fundElt_mul_self h₀)
  have hz1 : fundElt h₀ * (fundElt h)⁻¹ = 1 := by
    rcases hlift with h8 | hfree
    · have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
      rcases eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with h1 | h1
      · exact h1
      · exfalso
        apply h8
        have hi₀ : i₀ = LinearEquiv.neg K * i := by
          have := congrArg Subtype.val hzi
          rw [Subgroup.coe_mul, h1] at this
          exact this
        have hneg := finrank_negSpace_of_isFundamental hodd h₀
        rw [hi₀, negSpace_neg_mul] at hneg
        have := finrank_negSpace_add_finrank_posSpace hodd h
        rw [finrank_negSpace_of_isFundamental hodd h, hneg] at this
        omega
    · exact hfree _ hz hz2
  have : fundElt h₀ = fundElt h := mul_inv_eq_one.mp hz1
  exact congrArg Subtype.val this

theorem kerConjFree_of_isFundamental [FiniteDimensional K V] {X : Type*} [Group X]
    {θ : ↥(elementaryGroup Q) →* X} (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q))
    (hZ : CenterScalar Q) (hdim : 4 < Module.finrank K V)
    (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) : KerConjFree θ (fundElt h) := by
  intro g z hz hg
  have h₀ := h.conj (elementaryGroup_le_orthogonalGroup Q g.2)
  have hθ : θ (fundElt h₀) = θ (fundElt h) := by
    have : fundElt h₀ = g * fundElt h * g⁻¹ := Subtype.ext rfl
    rw [this, hg, map_mul, MonoidHom.mem_ker.mp hz, one_mul]
  have hgi : g * fundElt h * g⁻¹ = fundElt h :=
    Subtype.ext (eq_of_map_eq_of_isFundamental hodd hker hZ hdim hlift h h₀ hθ)
  rw [hg] at hgi
  exact mul_eq_right.mp hgi

end Kernel

end CFSG.ClassicalInvolution.Models.Transfer
