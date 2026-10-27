module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwDefs
public import CFSG.Quasithin.H13.GoldschmidtU43ModOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Quasithin.H13.U43

theorem sw_x0_closure_odd : Subgroup.closure {x : X₀ | Odd (orderOf x)} = ⊤ := by
  classical
  haveI := isSimpleGroup_X₀
  set S : Set X₀ := {x : X₀ | Odd (orderOf x)} with hS
  have hconj : ∀ g : X₀, (MulAut.conj g) '' S = S := by
    intro g
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hS] at hy ⊢
      simp only [Set.mem_setOf_eq] at hy ⊢
      rw [(MulAut.conj g).orderOf_eq y]
      exact hy
    · intro hx
      refine ⟨(MulAut.conj g).symm x, ?_, (MulAut.conj g).apply_symm_apply x⟩
      rw [hS] at hx ⊢
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [((MulAut.conj g).symm).orderOf_eq x]
      exact hx
  have hnormal : (Subgroup.closure S).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    rw [MonoidHom.map_closure]
    change Subgroup.closure ((MulAut.conj g) '' S) = Subgroup.closure S
    rw [hconj g]
  obtain ⟨x, hx⟩ : ∃ x : X₀, orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
    have hdvd : 3 ∣ Nat.card X₀ := by rw [card_X₀]; norm_num
    exact exists_prime_orderOf_dvd_card' 3 hdvd
  have hxS : x ∈ S := by
    rw [hS]; show Odd (orderOf x); rw [hx]; norm_num
  have hxH : x ∈ Subgroup.closure S := Subgroup.subset_closure hxS
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    norm_num at hx
  rcases hnormal.eq_bot_or_eq_top with h | h
  · rw [h] at hxH
    simp only [Subgroup.mem_bot] at hxH
    exact absurd hxH hxne
  · exact h

theorem sw_x0_comm_sup_top {N₁ N₂ : Subgroup X₀} (hc : ∀ u ∈ N₁, ∀ v ∈ N₂, u * v = v * u)
    (h : N₁ ⊔ N₂ = ⊤) : N₁ = ⊥ ∨ N₂ = ⊥ := by
  haveI := isSimpleGroup_X₀
  have hN2 : N₂ ≤ Subgroup.normalizer (N₁ : Set X₀) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv u hu
    have huv := hc u hu v hv
    rw [← huv, mul_assoc, mul_inv_cancel, mul_one]
    exact hu
  have hnorm : Subgroup.normalizer (N₁ : Set X₀) = ⊤ := by
    rw [← top_le_iff, ← h]
    exact sup_le Subgroup.le_normalizer hN2
  have hN1normal : N₁.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  rcases hN1normal.eq_bot_or_eq_top with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    have hN2center : N₂ ≤ Subgroup.center X₀ := by
      intro v hv
      rw [Subgroup.mem_center_iff]
      intro u
      exact hc u (by rw [h1]; exact Subgroup.mem_top u) v hv
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X₀) with hc2 | hc2
    · exact le_bot_iff.mp (hc2 ▸ hN2center)
    · exfalso
      haveI : IsMulCommutative X₀ := Subgroup.center_eq_top_iff.mp hc2
      have hprime := (Group.is_simple_iff_prime_card (α := X₀)).mp inferInstance
      rw [card_X₀] at hprime
      norm_num at hprime

theorem sw_exists_central_invol {P : Type} [Group P] [Finite P] {Q : Subgroup P}
    (hQ : IsPGroup 2 Q) (hne : 1 < Nat.card Q) :
    ∃ u ∈ Q, orderOf u = 2 ∧ ∀ q ∈ Q, q * u = u * q := by
  have hnt : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp hne
  let Z : Subgroup Q := Subgroup.center Q
  have hZnt : Nontrivial Z := hQ.center_nontrivial
  have hZ : IsPGroup 2 Z := hQ.to_subgroup Z
  have hdiv : 2 ∣ Nat.card Z := by
    rcases hZ.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne'
    · exact h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  refine ⟨((c : Q) : P), (c : Q).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  · intro q hq
    have hqc : (⟨q, hq⟩ : Q) * c = c * ⟨q, hq⟩ := Subgroup.mem_center_iff.mp c.2 ⟨q, hq⟩
    simpa using congrArg Subtype.val hqc

theorem sw_no_big_two_group (hone : X0OneClass) (hx : orderOf xElt = 2) (hO : SwOddCent)
    {P : Subgroup X₀} (hP : IsPGroup 2 P) (hbig : 16 ≤ Nat.card P) {y : X₀}
    (hy : Odd (orderOf y)) (hy1 : y ≠ 1) (hc : ∀ p ∈ P, p * y = y * p) : False := by
  classical
  haveI : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  have hPnt : 1 < Nat.card P := by omega
  obtain ⟨u, hu, hu2, huc⟩ := sw_exists_central_invol (P := X₀) (Q := P) hP hPnt
  obtain ⟨g, hg⟩ := isConj_iff.mp (hone u xElt hu2 hx)
  let φ : X₀ →* X₀ := (MulAut.conj g).toMonoidHom
  let P' : Subgroup X₀ := P.map φ
  have hP' : IsPGroup 2 P' := hP.map φ
  have hcard' : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (K := P) (f := φ) (MulAut.conj g).injective
  have hP'C : P' ≤ SwC := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    rw [SwC, Subgroup.mem_centralizer_singleton_iff]
    show g * p * g⁻¹ * xElt = xElt * (g * p * g⁻¹)
    rw [← hg]
    have hpu : p * u = u * p := huc p hp
    calc g * p * g⁻¹ * (g * u * g⁻¹)
        = g * (p * u) * g⁻¹ := by group
      _ = g * (u * p) * g⁻¹ := by rw [hpu]
      _ = g * u * g⁻¹ * (g * p * g⁻¹) := by group
  let y' : X₀ := g * y * g⁻¹
  have hy'C : y' ∈ SwC := by
    rw [SwC, Subgroup.mem_centralizer_singleton_iff]
    show y' * xElt = xElt * y'
    rw [← hg]
    have huy : u * y = y * u := hc u hu
    calc g * y * g⁻¹ * (g * u * g⁻¹)
        = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [huy]
      _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  have hy'odd : Odd (orderOf y') := by
    have h : orderOf y' = orderOf y := by
      rw [show y' = g * y * g⁻¹ from rfl, ← MulAut.conj_apply]
      exact (MulAut.conj g).orderOf_eq y
    rw [h]; exact hy
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hy1
    have h1 : (MulAut.conj g) y = 1 := by
      rw [MulAut.conj_apply]
      exact h
    have h2 : (MulAut.conj g) y = (MulAut.conj g) 1 := by rw [h1, map_one]
    simpa using (MulAut.conj g).injective h2
  have hcomm' : ∀ p ∈ P', p * y' = y' * p := by
    intro p hp
    rw [Subgroup.mem_map] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    have hp₀y : p₀ * y = y * p₀ := hc p₀ hp₀
    calc g * p₀ * g⁻¹ * y'
        = g * (p₀ * y) * g⁻¹ := by rw [show y' = g * y * g⁻¹ from rfl]; group
      _ = g * (y * p₀) * g⁻¹ := by rw [hp₀y]
      _ = y' * (g * p₀ * g⁻¹) := by rw [show y' = g * y * g⁻¹ from rfl]; group
  have hlt : Nat.card P' < 16 := hO y' hy'C hy'odd hy'1 P' hP' hP'C hcomm'
  rw [hcard'] at hlt
  omega

end CFSG.OddStandard.SmallF3.Omega
