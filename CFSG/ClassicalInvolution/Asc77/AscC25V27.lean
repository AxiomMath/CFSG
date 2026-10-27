module

public import CFSG.ClassicalInvolution.Asc77.AscC25V25
public import CFSG.ClassicalInvolution.Asc77.AscC25V6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Parity

variable {G : Type} [Group G] [Finite G]

abbrev czIn (a z : G) : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
  (Subgroup.centralizer ({z} : Set G)).subgroupOf (Subgroup.centralizer ({a} : Set G))

omit [Finite G] in
theorem mem_czIn {a z : G} {y : ↥(Subgroup.centralizer ({a} : Set G))} :
    y ∈ czIn a z ↔ (y : G) * z = z * (y : G) := by
  rw [czIn, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]

theorem odd_index_czIn {a z y₀ : G}
    (hy₀a : y₀ ∈ Subgroup.centralizer ({a} : Set G)) (hy₀4 : orderOf y₀ = 4)
    (hy₀z : y₀ * z = z * y₀)
    (hnc : ∀ g : G, (g * z * g⁻¹) * y₀ = y₀ * (g * z * g⁻¹) → g * z * g⁻¹ = z) :
    Odd (czIn a z).index := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := Subgroup.centralizer ({a} : Set G) with hY
  set y₀' : ↥Y := ⟨y₀, hy₀a⟩ with hy₀'
  have hy₀'4 : orderOf y₀' = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact hy₀4
  set A : Subgroup ↥Y := Subgroup.zpowers y₀' with hA
  have hAp : IsPGroup 2 ↥A := by
    rw [IsPGroup.iff_card]
    exact ⟨2, by rw [hA, Nat.card_zpowers, hy₀'4]; norm_num⟩
  have hy₀H : y₀' ∈ czIn a z := mem_czIn.mpr hy₀z
  have hAH : A ≤ czIn a z := by
    rw [hA, Subgroup.zpowers_le]
    exact hy₀H
  have hone : ((1 : ↥Y) : ↥Y ⧸ czIn a z) ∈ MulAction.fixedPoints ↥A (↥Y ⧸ czIn a z) := by
    intro m
    show (QuotientGroup.mk ((m : ↥Y) * (1 : ↥Y)) : ↥Y ⧸ czIn a z) = QuotientGroup.mk (1 : ↥Y)
    rw [mul_one, QuotientGroup.eq, mul_one]
    exact (czIn a z).inv_mem (hAH m.2)
  by_contra hodd
  have hdvd : 2 ∣ Nat.card (↥Y ⧸ czIn a z) := by
    have : Even (czIn a z).index := Nat.not_odd_iff_even.mp hodd
    exact even_iff_two_dvd.mp this
  obtain ⟨x, hx, hne⟩ := hAp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (↥Y ⧸ czIn a z) hdvd hone
  induction x using QuotientGroup.induction_on with | _ y => ?_
  apply hne
  have hmem := (MulAction.mem_fixedPoints).mp hx ⟨y₀', Subgroup.mem_zpowers y₀'⟩
  have h1 : (((y₀' : ↥Y) * y : ↥Y) : ↥Y ⧸ czIn a z) = (y : ↥Y ⧸ czIn a z) := hmem
  rw [QuotientGroup.eq] at h1
  have h3 := mem_czIn.mp h1
  have h3' : (y : G)⁻¹ * y₀⁻¹ * y * z = z * ((y : G)⁻¹ * y₀⁻¹ * y) := by
    simpa [mul_assoc] using h3
  have hcomm : ((y : G) * z * (y : G)⁻¹) * y₀ = y₀ * ((y : G) * z * (y : G)⁻¹) := by
    calc ((y : G) * z * (y : G)⁻¹) * y₀
        = y₀ * (y₀⁻¹ * ((y : G) * z * (y : G)⁻¹)) * y₀ := by group
      _ = y₀ * (((y : G) * ((y : G)⁻¹ * y₀⁻¹ * y * z) * (y : G)⁻¹)) * y₀ := by group
      _ = y₀ * (((y : G) * (z * ((y : G)⁻¹ * y₀⁻¹ * y)) * (y : G)⁻¹)) * y₀ := by rw [h3']
      _ = y₀ * (((y : G) * z * (y : G)⁻¹) * y₀⁻¹) * y₀ := by group
      _ = y₀ * ((y : G) * z * (y : G)⁻¹) := by group
  have hzy := hnc (y : G) hcomm
  have hyz : (y : G) * z = z * (y : G) := by
    calc (y : G) * z = ((y : G) * z * (y : G)⁻¹) * y := by group
      _ = z * y := by rw [hzy]
  rw [QuotientGroup.eq]
  exact mem_czIn.mpr (by simpa using hyz)

theorem exists_conj_comm_of_odd {a z b : G}
    (hb2 : b * b = 1) (hbY : b ∈ Subgroup.centralizer ({a} : Set G))
    (hodd : Odd (czIn a z).index) :
    ∃ d ∈ Subgroup.centralizer ({a} : Set G), (d⁻¹ * b * d) * z = z * (d⁻¹ * b * d) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := Subgroup.centralizer ({a} : Set G) with hY
  set b' : ↥Y := ⟨b, hbY⟩ with hb'
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  have hBp : IsPGroup 2 ↥(Subgroup.zpowers b') := isPGroup_two_zpowers_of_sq hb'2
  have hndvd : ¬ 2 ∣ Nat.card (↥Y ⧸ czIn a z) := hodd.not_two_dvd_nat
  obtain ⟨x, hx⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (↥Y ⧸ czIn a z) hndvd
  induction x using QuotientGroup.induction_on with | _ y => ?_
  have hmem := (MulAction.mem_fixedPoints).mp hx ⟨b', Subgroup.mem_zpowers b'⟩
  have h1 : (QuotientGroup.mk ((b' : ↥Y) * y) : ↥Y ⧸ czIn a z) = QuotientGroup.mk y := hmem
  rw [QuotientGroup.eq] at h1
  have h3 := mem_czIn.mp h1
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  refine ⟨(y : G), y.2, ?_⟩
  have h3' : (y : G)⁻¹ * b⁻¹ * y * z = z * ((y : G)⁻¹ * b⁻¹ * y) := by
    simpa [mul_assoc] using h3
  rw [hbi] at h3'
  exact h3'

end Parity

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


omit [IsSimpleGroup G] in
theorem exists_order_four_of_isFAut {R' : Subgroup G} {a : G} (hF : IsFAut R' a) :
    ∃ y₀ ∈ R', orderOf y₀ = 4 ∧ y₀ * a = a * y₀ := by
  obtain ⟨-, -, Q, -, hQ, hQuat, -, -⟩ := hF
  obtain ⟨k, hk, ⟨eQ⟩⟩ := hQuat
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  refine ⟨((eQ.symm (QuaternionGroup.xa 0) : Q) : G), (hQ.1 (eQ.symm _).2).1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hQ.1 (eQ.symm _).2).2

theorem odd_index_of_isFAut (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hF : IsFAut R' a) : Odd (czIn a z).index := by
  obtain ⟨y₀, hy₀R', hy₀4, hy₀a⟩ := exists_order_four_of_isFAut hF
  have hy₀K' : y₀ ∈ K' := h.hyp.hR'.2.1 hy₀R'
  refine odd_index_czIn (a := a) (z := z) (y₀ := y₀)
    (Subgroup.mem_centralizer_singleton_iff.mpr hy₀a) hy₀4 (comm_z_of_mem h.hzR' hy₀R') ?_
  intro g hg
  have := eq_conj_z_of_commute_order_four h (c := 1) (g := g) (y₀ := y₀)
    (by rwa [conjSub_one]) hy₀4 hg
  simpa using this

theorem zG_cases (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a)
    {b g : G} (hbg : b = g * z * g⁻¹) (hba : b * a = a * b) :
    ∃ d : G, d * a = a * d ∧
      (d⁻¹ * b * d = z ∨
        ((d⁻¹ * b * d) * z = z * (d⁻¹ * b * d) ∧ (d⁻¹ * b * d) * a = a * (d⁻¹ * b * d) ∧
          conjSub (d⁻¹ * b * d) K' = K)) := by
  have hb2 : b * b = 1 := by
    rw [hbg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.hz'.sq]; group
  have hbY : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hba
  obtain ⟨d, hdY, hd⟩ := exists_conj_comm_of_odd hb2 hbY (odd_index_of_isFAut h hF)
  have hda : d * a = a * d := Subgroup.mem_centralizer_singleton_iff.mp hdY
  have hda' : d⁻¹ * a = a * d⁻¹ := by
    calc d⁻¹ * a = d⁻¹ * (a * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * a) * d⁻¹ := by rw [← hda]
      _ = a * d⁻¹ := by group
  have hb1a : (d⁻¹ * b * d) * a = a * (d⁻¹ * b * d) := by
    calc (d⁻¹ * b * d) * a = d⁻¹ * (b * (d * a)) := by group
      _ = d⁻¹ * (b * (a * d)) := by rw [hda]
      _ = d⁻¹ * ((b * a) * d) := by group
      _ = d⁻¹ * ((a * b) * d) := by rw [hba]
      _ = (d⁻¹ * a) * b * d := by group
      _ = a * (d⁻¹ * b * d) := by rw [hda']; group
  refine ⟨d, hda, ?_⟩
  have d' := twinCtx'_of_hyp25 h
  rcases d'.conj_K hd with h1 | h1
  · left
    by_contra hne
    have hbN : d⁻¹ * b * d ∈ Subgroup.normalizer (K' : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr h1
    exact false_of_conj_normalizer' h haS ha2 hF (b := d⁻¹ * b * d) (g := d⁻¹ * g)
      (by rw [hbg]; group) hne hb1a hbN
  · exact Or.inr ⟨hd, hb1a, h1⟩

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
