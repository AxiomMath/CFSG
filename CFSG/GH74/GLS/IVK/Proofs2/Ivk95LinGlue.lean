module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinSL
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.GH74.Generic.S1.KL5Lift
public import CFSG.GH74.GLS.IVK.Statements.Sec4
public import CFSG.GH74.GLS.LU.Local.A3Rec

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open scoped MatrixGroups commutatorElement Matrix

section Glue

variable {k : Type} [Field k] {m : ℕ} {J : Type} [Group J]

structure IsCentralQuot (π : SL(m, k) →* J) : Prop where
  surj : Function.Surjective π
  ker_eq : ∀ x, π x = 1 ↔ x ∈ Subgroup.center SL(m, k)

variable {π : SL(m, k) →* J}

theorem IsCentralQuot.lift_involution (hπ : IsCentralQuot π) {z : J} (hz : orderOf z = 2) :
    ∃ g : SL(m, k), π g = z ∧ g ∉ Subgroup.center SL(m, k) ∧
      g ^ 2 ∈ Subgroup.center SL(m, k) := by
  obtain ⟨g, hg⟩ := hπ.surj z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  refine ⟨g, hg, fun hc => hz1 (hg ▸ (hπ.ker_eq g).2 hc), ?_⟩
  rw [← hπ.ker_eq, map_pow, hg, hz2]

theorem IsCentralQuot.conj_mem_centralizer (hπ : IsCentralQuot π) {g h : SL(m, k)}
    (hc : π h ∈ Subgroup.centralizer ({π g} : Set J)) {a : SL(m, k)}
    (ha : a ∈ Subgroup.centralizer ({g} : Set SL(m, k))) :
    h * a * h⁻¹ ∈ Subgroup.centralizer ({g} : Set SL(m, k)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ha ⊢
  have hs : h * g * h⁻¹ * g⁻¹ ∈ Subgroup.center SL(m, k) := by
    rw [← hπ.ker_eq]
    simp only [map_mul, map_inv]
    calc π h * π g * (π h)⁻¹ * (π g)⁻¹ = (π g * π h) * (π h)⁻¹ * (π g)⁻¹ := by rw [hc]
      _ = 1 := by group
  set s := h * g * h⁻¹ * g⁻¹ with hsdef
  have hsc : ∀ x : SL(m, k), x * s⁻¹ = s⁻¹ * x :=
    Subgroup.mem_center_iff.1 ((Subgroup.center SL(m, k)).inv_mem hs)
  have e1 : h * g * h⁻¹ = s * g := by rw [hsdef]; group
  have e2 : h⁻¹ * g * h = s⁻¹ * g := by
    have h0 : g = s⁻¹ * (h * g * h⁻¹) := by rw [e1]; group
    calc h⁻¹ * g * h = h⁻¹ * (s⁻¹ * (h * g * h⁻¹)) * h := by rw [← h0]
      _ = (h⁻¹ * s⁻¹) * (h * g * h⁻¹ * h) := by group
      _ = (s⁻¹ * h⁻¹) * (h * g * h⁻¹ * h) := by rw [hsc h⁻¹]
      _ = s⁻¹ * g := by group
  calc h * a * h⁻¹ * g = h * a * (h⁻¹ * g * h) * h⁻¹ := by group
    _ = h * a * (s⁻¹ * g) * h⁻¹ := by rw [e2]
    _ = s⁻¹ * (h * (a * g) * h⁻¹) := by
        calc h * a * (s⁻¹ * g) * h⁻¹ = h * (a * s⁻¹) * g * h⁻¹ := by group
          _ = h * (s⁻¹ * a) * g * h⁻¹ := by rw [hsc a]
          _ = (h * s⁻¹) * (a * g) * h⁻¹ := by group
          _ = (s⁻¹ * h) * (a * g) * h⁻¹ := by rw [hsc h]
          _ = s⁻¹ * (h * (a * g) * h⁻¹) := by group
    _ = s⁻¹ * (h * (g * a) * h⁻¹) := by rw [ha]
    _ = s⁻¹ * ((h * g * h⁻¹) * (h * a * h⁻¹)) := by group
    _ = s⁻¹ * ((s * g) * (h * a * h⁻¹)) := by rw [e1]
    _ = g * (h * a * h⁻¹) := by group

theorem IsCentralQuot.map_le_Ez (hπ : IsCentralQuot π) {g : SL(m, k)} {X : Subgroup SL(m, k)}
    (hXN : X ≤ Subgroup.centralizer ({g} : Set SL(m, k)))
    (hXnorm : ∀ n ∈ Subgroup.centralizer ({g} : Set SL(m, k)), ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hq : CFSG.IsQuasisimple ↥(X.map π)) : X.map π ≤ Ez (π g) := by
  set C := Subgroup.centralizer ({π g} : Set J) with hC
  set N := Subgroup.centralizer ({g} : Set SL(m, k)) with hN
  have hcomm : ∀ n ∈ N, π n ∈ C := by
    intro n hn
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg π (Subgroup.mem_centralizer_singleton_iff.1 hn)
  have hXC : X.map π ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcomm x (hXN hx)
  have hNC : N.map π ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcomm x hx
  have hXN' : X.map π ≤ N.map π := Subgroup.map_mono hXN
  have hn1 : ((X.map π).subgroupOf (N.map π)).Normal := by
    refine ⟨fun x hx n => ?_⟩
    obtain ⟨x0, hx0, hxe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨n0, hn0, hne⟩ := Subgroup.mem_map.1 n.2
    rw [Subgroup.mem_subgroupOf]
    show (n : J) * (x : J) * (n : J)⁻¹ ∈ X.map π
    rw [← hxe, ← hne]
    exact Subgroup.mem_map.2 ⟨n0 * x0 * n0⁻¹, hXnorm n0 hn0 x0 hx0, by simp⟩
  have hn2 : ((N.map π).subgroupOf C).Normal := by
    refine ⟨fun y hy c => ?_⟩
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    obtain ⟨h, hh⟩ := hπ.surj (c : J)
    rw [Subgroup.mem_subgroupOf]
    show (c : J) * (y : J) * (c : J)⁻¹ ∈ N.map π
    have hch : π h ∈ C := hh ▸ c.2
    rw [← hae, ← hh]
    exact Subgroup.mem_map.2 ⟨h * a * h⁻¹, hπ.conj_mem_centralizer hch ha, by simp⟩
  have hsub : ((X.map π).subgroupOf C).IsSubnormal := by
    refine CFSG.GroupTheory.isSubnormal_subgroupOf_trans hXN' hNC ?_ hn2.isSubnormal
    exact hn1.isSubnormal
  have hcomp : CFSG.IsComponent ((X.map π).subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXC).symm hq, hsub⟩
  intro x hx
  have hxC : x ∈ C := hXC hx
  have hlay : (⟨x, hxC⟩ : C) ∈ layer C :=
    CFSG.LocalCores.component_le_layer hcomp (Subgroup.mem_subgroupOf.2 hx)
  exact ⟨⟨x, hxC⟩, hlay, rfl⟩

theorem IsCentralQuot.range_le_Ez (hπ : IsCentralQuot π) {g : SL(m, k)} {Q : Type} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (ξ : Q →* SL(m, k)) (hcomm : ∀ x, ξ x * g = g * ξ x)
    (hnorm : ∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ x * n⁻¹ = ξ x')
    (hne : ∃ x, π (ξ x) ≠ 1) : ∀ x, π (ξ x) ∈ Ez (π g) := by
  have hq : CFSG.IsQuasisimple ↥(ξ.range.map π) := by
    have hrange : ξ.range.map π = (π.comp ξ).range := by
      rw [MonoidHom.range_comp]
    rw [hrange]
    exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hQ
      (φ := (π.comp ξ).rangeRestrict) (MonoidHom.rangeRestrict_surjective _)
      (by obtain ⟨x, hx⟩ := hne; exact ⟨x, fun h => hx (congrArg Subtype.val h)⟩)
  have hle := hπ.map_le_Ez (g := g) (X := ξ.range)
    (by rintro _ ⟨x, rfl⟩; exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm x))
    (by
      rintro n hn _ ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := hnorm n (Subgroup.mem_centralizer_singleton_iff.1 hn) x
      exact ⟨x', hx'.symm⟩) hq
  exact fun x => hle ⟨ξ x, ⟨x, rfl⟩, rfl⟩

theorem IsCentralQuot.perfect_lift_centralizer [Finite k] (hπ : IsCentralQuot π) {g : SL(m, k)}
    {K : Subgroup J} (hKC : K ≤ Subgroup.centralizer ({π g} : Set J)) (hK : ⁅K, K⁆ = K) :
    ∃ Kt : Subgroup SL(m, k), ⁅Kt, Kt⁆ = Kt ∧ Kt.map π = K ∧
      Kt ≤ Subgroup.centralizer ({g} : Set SL(m, k)) := by
  obtain ⟨Kt, hKt, hKtm⟩ := CFSG.GH74.Generic.S1.kl5_exists_perfect_lift π hπ.surj K hK
  refine ⟨Kt, hKt, hKtm, ?_⟩
  have hcen : ∀ x ∈ Kt, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.center SL(m, k) := by
    intro x hx
    rw [← hπ.ker_eq]
    have hxK : π x ∈ K := hKtm ▸ Subgroup.mem_map_of_mem π hx
    have hcomm : π x * π g = π g * π x :=
      Subgroup.mem_centralizer_singleton_iff.1 (hKC hxK)
    simp only [map_mul, map_inv]
    calc π x * π g * (π x)⁻¹ * (π g)⁻¹ = (π g * π x) * (π x)⁻¹ * (π g)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  let ψ : ↥Kt →* ↥(Subgroup.center SL(m, k)) :=
    { toFun := fun x => ⟨(x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹, hcen x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hty := Subgroup.mem_center_iff.1 (hcen y y.2)
        have htx := Subgroup.mem_center_iff.1 (hcen x x.2)
        change ((x : SL(m, k)) * y) * g * ((x : SL(m, k)) * y)⁻¹ * g⁻¹ =
          ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹) * ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹)
        have e1 : (y : SL(m, k)) * g * (y : SL(m, k))⁻¹ =
            ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) * g := by group
        calc ((x : SL(m, k)) * y) * g * ((x : SL(m, k)) * y)⁻¹ * g⁻¹
            = (x : SL(m, k)) * ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹) * (x : SL(m, k))⁻¹ * g⁻¹ := by
              group
          _ = (x : SL(m, k)) * (((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) * g) * (x : SL(m, k))⁻¹ *
                g⁻¹ := by rw [← e1]
          _ = ((x : SL(m, k)) * ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹)) *
                (g * (x : SL(m, k))⁻¹ * g⁻¹) := by group
          _ = (((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) * (x : SL(m, k))) *
                (g * (x : SL(m, k))⁻¹ * g⁻¹) := by rw [hty (x : SL(m, k))]
          _ = ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) *
                ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹) := by group
          _ = ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹) *
                ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) :=
              (hty ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹)).symm) }
  have hψ := ivk95l_hom_one_of_perfect (Subgroup.isPerfect_iff.2 hKt) ψ
  intro x hx
  have h1 := congrArg (fun f : ↥Kt →* ↥(Subgroup.center SL(m, k)) => ((f ⟨x, hx⟩ : ↥(Subgroup.center SL(m, k))) :
    SL(m, k))) hψ
  simp only [MonoidHom.one_apply, OneMemClass.coe_one] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : x * g * x⁻¹ * g⁻¹ = 1 := h1
  calc x * g = (x * g * x⁻¹ * g⁻¹) * (g * x) := by group
    _ = g * x := by rw [h2, one_mul]

theorem ivk95l_false_solvable [Finite k] (hπ : IsCentralQuot π) {g : SL(m, k)} {K : Subgroup J}
    (hKC : K ≤ Subgroup.centralizer ({π g} : Set J)) (hK : ⁅K, K⁆ = K) (hKne : K ≠ ⊥)
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set SL(m, k)))) : False := by
  obtain ⟨Kt, hKt, hKtm, hKtN⟩ := hπ.perfect_lift_centralizer hKC hK
  have hperf : Group.IsPerfect ↥Kt := Subgroup.isPerfect_iff.2 hKt
  have hsK : Group.IsSolvable ↥Kt :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKtN)
      (Subgroup.inclusion_injective hKtN)
  have hbot : Kt = ⊥ := by
    by_contra hne
    have : Nontrivial ↥Kt := (Subgroup.nontrivial_iff_ne_bot Kt).2 hne
    exact Group.IsPerfect.not_isSolvable ↥Kt hsK
  apply hKne
  rw [← hKtm, hbot, Subgroup.map_bot]

end Glue

end CFSG.GH74.GLS.IVK.Proofs2
