module

public import CFSG.GH74.GLS.Stage2.Local.P34S5Bal
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Local.P34S5Jbar

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Frattini

variable {G : Type} [Group G]

theorem frattini_involution {N J : Subgroup G} (hJN : J ≤ N) (hnorm : ∀ n ∈ N, ∀ j ∈ J, n * j * n⁻¹ ∈ J)
    {u₀ : G} (hu₀ : u₀ ∈ J) (hu₀2 : orderOf u₀ = 2)
    (hone : ∀ u ∈ J, orderOf u = 2 → ∃ j ∈ J, j * u₀ * j⁻¹ = u) :
    ∀ n ∈ N, ∃ j ∈ J, ∃ c ∈ N ⊓ centralizer ({u₀} : Set G), n = j * c := by
  intro n hn
  have hu : n * u₀ * n⁻¹ ∈ J := hnorm n hn u₀ hu₀
  have hu2 : orderOf (n * u₀ * n⁻¹) = 2 := by
    rw [← hu₀2]
    exact (orderOf_eq_of_isConj' (isConj_iff.2 ⟨n, rfl⟩)).symm
  obtain ⟨j, hj, hjn⟩ := hone _ hu hu2
  refine ⟨j, hj, j⁻¹ * n, Subgroup.mem_inf.2 ⟨N.mul_mem (N.inv_mem (hJN hj)) hn, ?_⟩, by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc j⁻¹ * n * u₀ = j⁻¹ * (n * u₀ * n⁻¹) * n := by group
    _ = j⁻¹ * (j * u₀ * j⁻¹) * n := by rw [hjn]
    _ = u₀ * (j⁻¹ * n) := by group

end Frattini

section Jx

variable {G : Type} [Group G] [Finite G]

theorem Jx_normalized (x : G) : ∀ n ∈ centralizer ({x} : Set G), ∀ j ∈ Jx x, n * j * n⁻¹ ∈ Jx x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n hn j hj
  have hchar := CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
    (G := ↥(centralizer ({x} : Set G))) (p := 2)
  rw [Jx, pLayerOf_eq_map_P34] at hj ⊢
  obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.1 hj
  refine Subgroup.mem_map.2 ⟨(⟨n, hn⟩ : ↥(centralizer ({x} : Set G))) * j' * (⟨n, hn⟩ : ↥(centralizer ({x} : Set G)))⁻¹,
    ?_, rfl⟩
  have hnorm : (pLayer ↥(centralizer ({x} : Set G)) 2).Normal := inferInstance
  exact hnorm.conj_mem j' hj' _

theorem exists_conj_of_involutions {J : Subgroup G} (hD : DihJ (HBar J)) {u v : G} (hu : u ∈ J) (hv : v ∈ J)
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) : ∃ j ∈ J, j * u * j⁻¹ = v := by
  have hu' : orderOf (⟨u, hu⟩ : ↥J) = 2 := by
    rw [← hu2]
    exact (Subgroup.orderOf_coe (⟨u, hu⟩ : ↥J)).symm
  have hv' : orderOf (⟨v, hv⟩ : ↥J) = 2 := by
    rw [← hv2]
    exact (Subgroup.orderOf_coe (⟨v, hv⟩ : ↥J)).symm
  have hc : IsConj (mkH J ⟨u, hu⟩) (mkH J ⟨v, hv⟩) :=
    hD.involutions_conj (orderOf_mk_eq_two J hu') (orderOf_mk_eq_two J hv')
  obtain ⟨c, hc'⟩ := isConj_iff.1 (isConj_of_mk_isConj J hu' hv' hc)
  exact ⟨c, c.2, by simpa using congrArg Subtype.val hc'⟩

omit [Finite G] in
theorem exists_involution_of_not_solvable {X : Type} [Group X] [Finite X] (h : ¬ Group.IsSolvable X) :
    ∃ u : X, orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : Even (Nat.card X) := by
    by_contra hodd
    exact h (CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.1 hodd))
  exact exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 h2)

end Jx

section Kind

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem isCentralInvolution_of_isConj_P34 {z x : G} (hz : IsCentralInvolution z) (h : IsConj z x) :
    IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

omit [Finite G] in
theorem centralizer_ne_top_of_nonCentral {x : G} (hx : IsNonCentralInvolution x) :
    centralizer ({x} : Set G) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_orderOf_eq_two hx.1).exists_le_sylow
  refine hx.2 ⟨hx.1, Q, hQ (mem_zpowers x), fun s _ => ?_⟩
  have hs : s ∈ centralizer ({x} : Set G) := htop ▸ Subgroup.mem_top s
  exact Subgroup.mem_centralizer_singleton_iff.1 hs

theorem exists_two_involutions_not_conj {H : Subgroup G} (hFUS : FUS H) (h2 : HasTwoInvolutionClasses (HBar H)) :
    ∃ a b : G, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ IsConj a b := by
  obtain ⟨u, v, hu, hv, huv⟩ := h2
  obtain ⟨t, ht, rfl⟩ := exists_lift_involution H hu
  obtain ⟨t', ht', rfl⟩ := exists_lift_involution H hv
  refine ⟨(t : G), (t' : G), ?_, ?_, fun hc => huv (hFUS t t' ht ht' hc)⟩
  · rw [← ht]; exact Subgroup.orderOf_coe t
  · rw [← ht']; exact Subgroup.orderOf_coe t'

theorem kind_cases (hctx : Stage2Ctx G z k S) :
    (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∨
      ((IsClassicalKind k ∨ k = Kind.m12) ∧ ∃ x₀ : G, orderOf x₀ = 2 ∧ ¬ IsConj z x₀ ∧
        ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x₀ u) := by
  have hcen := hctx.central
  cases hctx.data with
  | g2 h => exact Or.inl h.one_class
  | m12 h => exact Or.inr ⟨Or.inr rfl, h.two_classes⟩
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    obtain ⟨x, hx⟩ := h.two
    exact Or.inr ⟨Or.inl (Or.inl rfl), x, hx.x_inv,
      fun hc => hx.x_nonCentral (isCentralInvolution_of_isConj_P34 hcen hc), hx.classes⟩
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    rcases h.fusion with ⟨-, hone⟩ | ⟨-, x, hx, -⟩
    · exact Or.inl hone
    · exact Or.inr ⟨Or.inl (Or.inr ⟨ε, rfl⟩), x, hx.x_inv,
        fun hc => hx.x_nonCentral (isCentralInvolution_of_isConj_P34 hcen hc), hx.classes⟩
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact Or.inl h.one_class
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact Or.inl h.one_class

end Kind

end CFSG.GH74.GLS.Stage2.Local.P34
