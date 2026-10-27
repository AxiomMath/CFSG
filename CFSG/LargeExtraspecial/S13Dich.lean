module

public import CFSG.LargeExtraspecial.S13No3
public import CFSG.LargeExtraspecial.S10EightJ
public import CFSG.LargeExtraspecial.S13Pts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem conj_mem_Lbar_of_commute' (haQ : g * S.z * g⁻¹ ∈ S.QG) (C : Cons311 S g) {l m : S.O}
    (hl : l ∈ S.Lbar g) (hm : m ∈ S.Mbar)
    (hc : ∀ x ∈ S.Lbar g, m * l * m⁻¹ * x = x * (m * l * m⁻¹)) :
    m * l * m⁻¹ ∈ S.Lbar g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : S.Lbar g ≤ S.Mbar := S.Lbar_le_Mbar g
  have hsc := lemma_3_12_isStronglyClosedIn (isPGroup_Lbar_subgroupOf haQ)
    (comm_Lbar_subgroupOf haQ) (isWeaklyClosed_Lbar_subgroupOf C)
  have hl' : (⟨l, hLM hl⟩ : S.Mbar) ∈ (S.Lbar g).subgroupOf S.Mbar := mem_subgroupOf.mpr hl
  have key := hsc.2 ⟨l, hLM hl⟩ hl' (⟨m, hm⟩ : S.Mbar)⁻¹ (by
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : ((x : S.Mbar) : S.O) ∈ S.Lbar g := mem_subgroupOf.mp hx
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact (hc _ hx').symm)
  have := mem_subgroupOf.mp key
  simpa using this

theorem span_pair_eq_of_finrank_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {F : Submodule (ZMod 2) V} (hF : finrank (ZMod 2) F = 2)
    {u v : V} (hu : u ∈ F) (hv : v ∈ F) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    Submodule.span (ZMod 2) {u, v} = F := by
  have hli := linearIndependent_pair_zmod2 hu0 hv0 huv
  have h2 := finrank_span_eq_card hli
  simp only [Fintype.card_fin] at h2
  have hle : Submodule.span (ZMod 2) (Set.range ![u, v]) ≤ F := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hv
  have hrange : Set.range ![u, v] = {u, v} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  rw [← hrange]
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hF, h2])

theorem pt_ne_zero (H : Hyp4 S g) (h : S.M) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ≠ 0 :=
  cl_conj_z_ne_zero S (H.mul h).conj_mem (H.mul h).conj_ne

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem eq_one_of_three {ρ : S.O} (hρ : ρ ∈ Ebar S g K) {h₁ h₂ h₃ : S.M}
    (hρ₁ : ρ ∈ S.Lbar ((h₁ : G) * g)) (hρ₂ : ρ ∈ S.Lbar ((h₂ : G) * g))
    (hρ₃ : ρ ∈ S.Lbar ((h₃ : G) * g))
    (hne : S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) ≠
      S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹))
    (h12 : S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₁ : G) * g)))
    (h13 : S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₁ : G) * g)))
    (h23 : S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₂ : G) * g)))
    (hns : S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) ∉ Submodule.span (ZMod 2)
      {S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹),
        S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹)}) : ρ = 1 := by
  by_contra hρ1
  rcases Y.one ρ hρ hρ1 with hD | X
  · have hF : ∀ {h : S.M}, ρ ∈ S.Lbar ((h : G) * g) →
        S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Fbar S g K := fun {h} hρh =>
      cl_mem_Fbar_of_le (Y.H.mul h) (hD _ ⟨h, rfl, hρh⟩)
    apply hns
    rw [span_pair_eq_of_finrank_two Y.finrank_Fbar (hF hρ₁) (hF hρ₂) (pt_ne_zero Y.H h₁)
      (pt_ne_zero Y.H h₂) hne]
    exact hF hρ₃
  · exact hns (Hyp10.mem_span_of_linked X hρ₁ hρ₂ hρ₃ hne h12 h13 h23)

theorem eq_one_of_three' {ρ : S.O} (hρ : ρ ∈ Ebar S g K) {g₁ g₂ g₃ : G}
    (hg₁ : ∃ h : S.M, g₁ = (h : G) * g) (hg₂ : ∃ h : S.M, g₂ = (h : G) * g)
    (hg₃ : ∃ h : S.M, g₃ = (h : G) * g)
    (hρ₁ : ρ ∈ S.Lbar g₁) (hρ₂ : ρ ∈ S.Lbar g₂) (hρ₃ : ρ ∈ S.Lbar g₃)
    (hne : S.cl (g₁ * S.z * g₁⁻¹) ≠ S.cl (g₂ * S.z * g₂⁻¹))
    (h12 : S.cl (g₂ * S.z * g₂⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g₁))
    (h13 : S.cl (g₃ * S.z * g₃⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g₁))
    (h23 : S.cl (g₃ * S.z * g₃⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g₂))
    (hns : S.cl (g₃ * S.z * g₃⁻¹) ∉
      Submodule.span (ZMod 2) {S.cl (g₁ * S.z * g₁⁻¹), S.cl (g₂ * S.z * g₂⁻¹)}) : ρ = 1 := by
  obtain ⟨h₁, rfl⟩ := hg₁
  obtain ⟨h₂, rfl⟩ := hg₂
  obtain ⟨h₃, rfl⟩ := hg₃
  exact Y.eq_one_of_three hρ hρ₁ hρ₂ hρ₃ hne h12 h13 h23 hns

end Hyp13

end CFSG.LargeExtraspecial.S13
