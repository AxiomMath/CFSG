module

public import CFSG.ClassicalInvolution.Asc77.AscCX9T

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25.U

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.CX

variable {G : Type} [Group G] [Finite G]

@[expose] def preimgOdd (X : Subgroup G) (T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) :
    Subgroup G :=
  (T.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))).map X.subtype

theorem mem_preimgOdd {X : Subgroup G} {T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)}
    {e : G} :
    e ∈ preimgOdd X T ↔
      ∃ he : e ∈ X, (QuotientGroup.mk ⟨e, he⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) ∈ T := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨he, h⟩
    exact ⟨⟨e, he⟩, h, rfl⟩

theorem preimgOdd_le (X : Subgroup G) (T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) :
    preimgOdd X T ≤ X :=
  Subgroup.map_subtype_le _

theorem conj_mem_preimgOdd {X' N' N : Subgroup G}
    {T' : Subgroup (↥X' ⧸ classicalInvolutionOddCore ↥X')} (hNX' : N' ≤ X')
    (hNT' : (N'.subgroupOf X').map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X')) = T')
    (hNN' : ∀ n ∈ N, ∀ h ∈ N', n * h * n⁻¹ ∈ N')
    (hOX' : ∀ n ∈ N, ∀ o ∈ oddCoreOf X', n * o * n⁻¹ ∈ oddCoreOf X') {n e : G} (hn : n ∈ N)
    (he : e ∈ preimgOdd X' T') : n * e * n⁻¹ ∈ preimgOdd X' T' := by
  obtain ⟨heX, heT⟩ := mem_preimgOdd.mp he
  rw [← hNT'] at heT
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp heT
  have hxN : (x : G) ∈ N' := Subgroup.mem_subgroupOf.mp hx
  have hxe' : (QuotientGroup.mk' (classicalInvolutionOddCore ↥X') x) =
      (QuotientGroup.mk ⟨e, heX⟩ : ↥X' ⧸ classicalInvolutionOddCore ↥X') := hxe
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hxe'
  have hoX : (x : G)⁻¹ * e ∈ oddCoreOf X' := by
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * ⟨e, heX⟩, hxe', ?_⟩
    simp
  have hc1 : n * (x : G) * n⁻¹ ∈ N' := hNN' n hn _ hxN
  have hc2 : n * ((x : G)⁻¹ * e) * n⁻¹ ∈ oddCoreOf X' := hOX' n hn _ hoX
  have hY : n * e * n⁻¹ = (n * (x : G) * n⁻¹) * (n * ((x : G)⁻¹ * e) * n⁻¹) := by group
  have hcX : n * e * n⁻¹ ∈ X' := by
    rw [hY]
    exact X'.mul_mem (hNX' hc1) (oddCoreOf_le_self X' hc2)
  refine mem_preimgOdd.mpr ⟨hcX, ?_⟩
  rw [← hNT']
  refine ⟨⟨n * (x : G) * n⁻¹, hNX' hc1⟩, Subgroup.mem_subgroupOf.mpr hc1, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
  obtain ⟨o, hoO, hoe⟩ := hc2
  have hxy : (⟨n * (x : G) * n⁻¹, hNX' hc1⟩ : ↥X')⁻¹ * ⟨n * e * n⁻¹, hcX⟩ = o := by
    apply Subtype.ext
    have hoe' : (o : G) = n * ((x : G)⁻¹ * e) * n⁻¹ := hoe
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hoe']
    group
  rw [hxy]
  exact hoO

theorem conj_mem_preimgOdd_self {X N : Subgroup G}
    {T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)} (hNX : N ≤ X)
    (hNT : (N.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) = T)
    {n e : G} (hn : n ∈ N) (he : e ∈ preimgOdd X T) : n * e * n⁻¹ ∈ preimgOdd X T := by
  obtain ⟨heX, heT⟩ := mem_preimgOdd.mp he
  have hnT : (QuotientGroup.mk ⟨n, hNX hn⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) ∈ T := by
    rw [← hNT]
    exact Subgroup.mem_map.mpr ⟨⟨n, hNX hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  have hcX : n * e * n⁻¹ ∈ X := X.mul_mem (X.mul_mem (hNX hn) heX) (X.inv_mem (hNX hn))
  refine mem_preimgOdd.mpr ⟨hcX, ?_⟩
  have h1 : (QuotientGroup.mk ⟨n * e * n⁻¹, hcX⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) =
      QuotientGroup.mk ⟨n, hNX hn⟩ * QuotientGroup.mk ⟨e, heX⟩ *
        (QuotientGroup.mk ⟨n, hNX hn⟩)⁻¹ := rfl
  rw [h1]
  exact T.mul_mem (T.mul_mem hnT heT) (T.inv_mem hnT)

@[expose] def rho (E X : Subgroup G) (T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X))
    (hEX : E ≤ X)
    (hET : ∀ e : ↥E,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX e) ∈ T) :
    ↥E →* ↥T :=
  ((QuotientGroup.mk' (classicalInvolutionOddCore ↥X)).comp (Subgroup.inclusion hEX)).codRestrict T
    hET

theorem coe_rho {E X : Subgroup G} {T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)}
    (hEX : E ≤ X)
    (hET : ∀ e : ↥E,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX e) ∈ T)
    (e : ↥E) :
    ((rho E X T hEX hET e : ↥T) : ↥X ⧸ classicalInvolutionOddCore ↥X) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX e) := rfl

theorem rho_surjective {E X N : Subgroup G} {T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)}
    (hEX : E ≤ X)
    (hET : ∀ e : ↥E,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX e) ∈ T)
    (hNT : (N.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) = T)
    (hconj : ∀ n ∈ N, ∀ e ∈ E, n * e * n⁻¹ ∈ E) (hTs : IsSimpleGroup ↥T) (z : ↥E)
    (hz1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX z) ≠ 1) :
    Function.Surjective (rho E X T hEX hET) := by
  have hnorm : (rho E X T hEX hET).range.Normal := by
    constructor
    rintro _ ⟨e, rfl⟩ g
    have hg : (g : ↥X ⧸ classicalInvolutionOddCore ↥X) ∈
        (N.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) := by
      rw [hNT]
      exact g.2
    obtain ⟨x₀, hx₀, hx₀g⟩ := Subgroup.mem_map.mp hg
    have hx₀N : (x₀ : G) ∈ N := Subgroup.mem_subgroupOf.mp hx₀
    have hmem : (x₀ : G) * (e : G) * (x₀ : G)⁻¹ ∈ E := hconj _ hx₀N _ e.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    rw [coe_rho]
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
        (Subgroup.inclusion hEX ⟨_, hmem⟩) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x₀ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX e) *
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x₀)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1, hx₀g]
    rfl
  have := hTs
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (rho E X T hEX hET).range with h | h
  · exfalso
    have h1 : rho E X T hEX hET z ∈ (rho E X T hEX hET).range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    apply hz1
    have h2 := congrArg (fun y : ↥T => (y : ↥X ⧸ classicalInvolutionOddCore ↥X)) h1
    exact h2
  · exact MonoidHom.range_eq_top.mp h

theorem ker_rho {E X : Subgroup G} {T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)}
    (hEX : E ≤ X)
    (hET : ∀ e : ↥E,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX e) ∈ T)
    (hsurj : Function.Surjective (rho E X T hEX hET)) (hTs : IsSimpleGroup ↥T) (z : ↥E)
    (hz2 : (z : G) * z = 1)
    (hz1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX z) ≠ 1) :
    (rho E X T hEX hET).ker = classicalInvolutionOddCore ↥E := by
  have hz1' : rho E X T hEX hET z ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzz : z * z = 1 := Subtype.ext hz2
  have := hTs
  have hO1 : classicalInvolutionOddCore ↥T = ⊥ :=
    oddCore_eq_bot_of_simple (t := rho E X T hEX hET z)
      (by rw [← map_mul, hzz, map_one]) hz1'
  refine ker_eq_oddCore_of_surjective _ hsurj hO1 ?_
  unfold rho
  rw [MonoidHom.ker_codRestrict]
  exact odd_natCard_ker_toLayer hEX

theorem exists_equiv_of_twin_layers {X X' N N' : Subgroup G}
    {T : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)}
    {T' : Subgroup (↥X' ⧸ classicalInvolutionOddCore ↥X')} (hNX : N ≤ X) (hNX' : N' ≤ X')
    (hNT : (N.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) = T)
    (hNT' : (N'.subgroupOf X').map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X')) = T')
    (hNN' : ∀ n ∈ N, ∀ h ∈ N', n * h * n⁻¹ ∈ N')
    (hN'N : ∀ n ∈ N', ∀ h ∈ N, n * h * n⁻¹ ∈ N)
    (hOX' : ∀ n ∈ N, ∀ o ∈ oddCoreOf X', n * o * n⁻¹ ∈ oddCoreOf X')
    (hOX : ∀ n ∈ N', ∀ o ∈ oddCoreOf X, n * o * n⁻¹ ∈ oddCoreOf X) (hTs : IsSimpleGroup ↥T)
    (hT's : IsSimpleGroup ↥T') {z : G} (hzX : z ∈ X) (hzX' : z ∈ X') (hz2 : z * z = 1)
    (hzT : z ∈ preimgOdd X T) (hzT' : z ∈ preimgOdd X' T')
    (hz1 : (QuotientGroup.mk ⟨z, hzX⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) ≠ 1)
    (hz1' : (QuotientGroup.mk ⟨z, hzX'⟩ : ↥X' ⧸ classicalInvolutionOddCore ↥X') ≠ 1) :
    ∃ φ : ↥T ≃* ↥T', ∀ (e : G) (hX : e ∈ X) (hX' : e ∈ X'), e ∈ preimgOdd X T →
      e ∈ preimgOdd X' T' → ∀ t : ↥T,
        (t : ↥X ⧸ classicalInvolutionOddCore ↥X) = QuotientGroup.mk ⟨e, hX⟩ →
          ((φ t : ↥T') : ↥X' ⧸ classicalInvolutionOddCore ↥X') = QuotientGroup.mk ⟨e, hX'⟩ := by
  set E : Subgroup G := preimgOdd X T ⊓ preimgOdd X' T' with hE
  have hEX : E ≤ X := inf_le_left.trans (preimgOdd_le X T)
  have hEX' : E ≤ X' := inf_le_right.trans (preimgOdd_le X' T')
  have hET : ∀ e : ↥E,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (Subgroup.inclusion hEX e) ∈ T := by
    intro e
    obtain ⟨he, h⟩ := mem_preimgOdd.mp (Subgroup.mem_inf.mp e.2).1
    exact h
  have hET' : ∀ e : ↥E,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X') (Subgroup.inclusion hEX' e) ∈ T' := by
    intro e
    obtain ⟨he, h⟩ := mem_preimgOdd.mp (Subgroup.mem_inf.mp e.2).2
    exact h
  have hzE : z ∈ E := Subgroup.mem_inf.mpr ⟨hzT, hzT'⟩
  have hconj : ∀ n ∈ N, ∀ e ∈ E, n * e * n⁻¹ ∈ E := fun n hn e he =>
    Subgroup.mem_inf.mpr ⟨conj_mem_preimgOdd_self hNX hNT hn (Subgroup.mem_inf.mp he).1,
      conj_mem_preimgOdd hNX' hNT' hNN' hOX' hn (Subgroup.mem_inf.mp he).2⟩
  have hconj' : ∀ n ∈ N', ∀ e ∈ E, n * e * n⁻¹ ∈ E := fun n hn e he =>
    Subgroup.mem_inf.mpr ⟨conj_mem_preimgOdd hNX hNT hN'N hOX hn (Subgroup.mem_inf.mp he).1,
      conj_mem_preimgOdd_self hNX' hNT' hn (Subgroup.mem_inf.mp he).2⟩
  have hsurj : Function.Surjective (rho E X T hEX hET) :=
    rho_surjective hEX hET hNT hconj hTs ⟨z, hzE⟩ hz1
  have hsurj' : Function.Surjective (rho E X' T' hEX' hET') :=
    rho_surjective hEX' hET' hNT' hconj' hT's ⟨z, hzE⟩ hz1'
  have hk := ker_rho hEX hET hsurj hTs ⟨z, hzE⟩ hz2 hz1
  have hk' := ker_rho hEX' hET' hsurj' hT's ⟨z, hzE⟩ hz2 hz1'
  obtain ⟨φ, hφ⟩ := exists_equiv_of_ker_eq _ _ hsurj hsurj' (hk.trans hk'.symm)
  refine ⟨φ, fun e hX hX' he he' t ht => ?_⟩
  have h1 : t = rho E X T hEX hET ⟨e, Subgroup.mem_inf.mpr ⟨he, he'⟩⟩ := Subtype.ext ht
  rw [h1, hφ]
  rfl

end CFSG.ClassicalInvolution.Q3.Q3T7P25.U
