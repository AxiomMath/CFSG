module

public import CFSG.GH74.Generic.S45.PumpC1
public import CFSG.GH74.Generic.S45.GL42

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 Subgroup
open scoped commutatorElement

section Residual

variable {X : Type*} [Group X]

theorem oPrimeResidual_normal : (oPrimeResidual 2 X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨k, ?_⟩
    calc (g * x * g⁻¹) ^ (2 ^ k) = g * x ^ (2 ^ k) * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hk]; group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

theorem oPrimeResidual_eq_top_of_isPerfect [Finite X] [Group.IsPerfect X] :
    oPrimeResidual 2 X = ⊤ := by
  have : (oPrimeResidual 2 X).Normal := oPrimeResidual_normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hSN : (S : Subgroup X) ≤ oPrimeResidual 2 X := by
    intro s hs
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    exact Subgroup.subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hSodd : Odd (S : Subgroup X).index := by
    have := Sylow.not_dvd_index S
    exact Nat.odd_iff.2 (by omega)
  have hNodd : Odd (oPrimeResidual 2 X).index :=
    Odd.of_dvd_nat hSodd (Subgroup.index_dvd_of_le hSN)
  by_contra hne
  have hidx : (oPrimeResidual 2 X).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have hcard : Odd (Nat.card (X ⧸ oPrimeResidual 2 X)) := by
    rw [← Subgroup.index_eq_card]; exact hNodd
  have hnt : Nontrivial (X ⧸ oPrimeResidual 2 X) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hidx
    rw [Subgroup.index_eq_card]
    exact Nat.card_eq_one_iff_unique.2 ⟨h, ⟨1⟩⟩
  exact Group.IsPerfect.not_isSolvable (X ⧸ oPrimeResidual 2 X)
    (CFSG.Milestones.odd_order_solvable hcard)

end Residual

section QuasisimpleResidual

variable {G : Type} [Group G]

theorem le_oPrimeResidualOf_of_isQuasisimple [Finite G] {X Q : Subgroup G} (hQX : Q ≤ X)
    (hQ : IsQuasisimple ↥Q) : Q ≤ oPrimeResidualOf 2 X := by
  have : Group.IsPerfect ↥Q := hQ.1
  have htop : oPrimeResidual 2 ↥Q = ⊤ := oPrimeResidual_eq_top_of_isPerfect
  have hmap : (oPrimeResidual 2 ↥Q).map (Subgroup.inclusion hQX) ≤ oPrimeResidual 2 ↥X := by
    unfold oPrimeResidual
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  intro q hq
  have hq' : (⟨q, hq⟩ : ↥Q) ∈ oPrimeResidual 2 ↥Q := by rw [htop]; trivial
  exact ⟨Subgroup.inclusion hQX ⟨q, hq⟩, hmap ⟨_, hq', rfl⟩, rfl⟩

end QuasisimpleResidual


section Subnormal

theorem normal_subgroupOf_of_decomp' {H : Type*} [Group H] {P A' R : Subgroup H}
    (hdec : ∀ p ∈ P, ∃ a ∈ A', a⁻¹ * p ∈ R) (hcomm : ∀ a ∈ A', ∀ w ∈ R, a * w = w * a) :
    (A'.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : H) ∈ A' := hn
  obtain ⟨a₀, ha₀, hw⟩ := hdec (g : H) g.2
  have hcw := hcomm (n : H) hn' _ hw
  show (g : H) * (n : H) * (g : H)⁻¹ ∈ A'
  have h1 : (g : H) * (n : H) * (g : H)⁻¹ = a₀ * (n : H) * a₀⁻¹ := by
    set w : H := a₀⁻¹ * (g : H) with hwdef
    have hgw : (g : H) = a₀ * w := by rw [hwdef]; group
    rw [hgw]
    calc a₀ * w * (n : H) * (a₀ * w)⁻¹ = a₀ * (w * (n : H) * w⁻¹) * a₀⁻¹ := by group
      _ = a₀ * ((n : H) * w * w⁻¹) * a₀⁻¹ := by rw [← hcw]
      _ = a₀ * (n : H) * a₀⁻¹ := by group
  rw [h1]
  exact A'.mul_mem (A'.mul_mem ha₀ hn') (A'.inv_mem ha₀)

theorem isSubnormal_of_barSub_of_comm {G : Type} [Group G] [Finite G] {c : G} {L : Subgroup G}
    (hbar : (barSub c L).IsSubnormal)
    (hcomm : ∀ a ∈ L, ∀ w ∈ pPrimeCoreOf 2 (centralizer ({c} : Set G)), a * w = w * a) :
    (L.subgroupOf (centralizer ({c} : Set G))).IsSubnormal := by
  classical
  set C : Subgroup G := centralizer ({c} : Set G) with hC
  set A' : Subgroup ↥C := L.subgroupOf C with hA'
  set P : Subgroup ↥C := (barSub c L).comap (proj c) with hP
  have hPsub : P.IsSubnormal := hbar.comap (proj c)
  have hA'P : A' ≤ P := fun g hg => proj_mem_barSub g.2 hg
  have hnorm : (A'.subgroupOf P).Normal := by
    refine normal_subgroupOf_of_decomp' (R := pPrimeCore 2 ↥C) ?_ ?_
    · intro p hp
      obtain ⟨a₀, ha₀, hpa⟩ : ∃ a₀ ∈ A', proj c a₀ = proj c p := hp
      refine ⟨a₀, ha₀, (QuotientGroup.eq_one_iff _).1 ?_⟩
      show proj c (a₀⁻¹ * p) = 1
      rw [map_mul, map_inv, hpa, inv_mul_cancel]
    · intro a ha w hw
      exact Subtype.ext (hcomm (a : G) ha (w : G) ⟨w, hw, rfl⟩)
  exact Subgroup.IsSubnormal.trans hA'P hnorm.isSubnormal hPsub

end Subnormal

end CFSG.GH74.Generic.BProg
