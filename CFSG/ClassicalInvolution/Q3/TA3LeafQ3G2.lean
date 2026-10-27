module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Good
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (mem_zpowers_of_sq)


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.inter_eq_or_inter_eq (hD : TightDatum R S t) {C : Subgroup Y} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] {h3 : (3 : F₂) = 0} (P : CentShape Y C t F₁ F₂ h3)
    (h4A : ∀ m ∈ R, m ∈ P.A → m ^ 4 = 1) (h4B : ∀ m ∈ R, m ∈ P.B → m ^ 4 = 1) :
    (∀ m ∈ R, m ∈ P.A → m = 1 ∨ m = t) ∨ (∀ m ∈ R, m ∈ P.B → m = 1 ∨ m = t) := by
  by_contra h
  simp only [not_or, not_forall] at h
  obtain ⟨⟨a, haR, haA, ha1, hat⟩, ⟨b, hbR, hbB, hb1, hbt⟩⟩ := h
  have hsq : ∀ m ∈ R, m ^ 4 = 1 → m ≠ 1 → m ≠ t → m ^ 2 = t := fun m hm h4 hm1 hmt => by
    have h2 : m ^ 2 ≠ 1 := fun h2 => by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
      · exact hm1 (orderOf_eq_one_iff.mp h)
      · exact hmt (hD.eq_of_orderOf_eq_two hm h)
    exact hD.eq_of_orderOf_eq_two (pow_mem hm 2)
      (orderOf_eq_prime (by rw [← pow_mul]; exact h4) h2)
  have ht2 : t ^ 2 = 1 := by rw [← hD.order]; exact pow_orderOf_eq_one t
  have h1 : (a * b) ^ 2 = 1 := by
    rw [Commute.mul_pow (P.comm a haA b hbB), hsq a haR (h4A a haR haA) ha1 hat,
      hsq b hbR (h4B b hbR hbB) hb1 hbt, ← pow_two, ht2]
  have hne : a * b ≠ 1 := fun h' => by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h'
    exact (P.inter a haA (this ▸ inv_mem hbB)).elim ha1 hat
  have hab := hD.eq_of_orderOf_eq_two (mul_mem haR hbR) (orderOf_eq_prime h1 hne)
  have haB : a ∈ P.B := by
    rw [show a = t * b⁻¹ by rw [← hab]; group]
    exact mul_mem P.t_mem_B (inv_mem hbB)
  exact (P.inter a haA haB).elim ha1 hat

omit [Finite Y] in
theorem TightDatum.commute_A_of_inter (hD : TightDatum R S t) {N : Subgroup Y}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] (hF₁ : Nat.card F₁ = 3)
    {h3 : (3 : F₂) = 0} (P : CentShape Y (N ⊓ Subgroup.centralizer ({t} : Set Y)) t F₁ F₂ h3)
    (hA : ∀ m ∈ R, m ∈ P.A → m = 1 ∨ m = t) : ∀ m ∈ R, m ∈ N → ∀ a ∈ P.A, m * a = a * m := by
  intro m hm hmN
  have ht2 : t * t = 1 := by rw [← pow_two, ← hD.order]; exact pow_orderOf_eq_one t
  have htA : ∀ a ∈ P.A, a * t = t * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (P.le_A ha)).2
  refine SL3.commute_of_commutator_mem_sl23 hF₁ P.eA (Z := Subgroup.zpowers t) ?_ ?_ ?_
  · intro z hz hz3
    rcases mem_zpowers_of_sq ht2 hz with rfl | rfl
    · rfl
    · exfalso
      have : z = 1 := by
        calc z = z ^ 3 * (z * z)⁻¹ := by group
          _ = 1 := by rw [hz3, ht2]; group
      have := hD.order
      rw [‹z = 1›, orderOf_one] at this
      exact absurd this (by norm_num)
  · intro z hz a ha
    rcases mem_zpowers_of_sq ht2 hz with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (htA a ha).symm
  · intro a ha
    have haC := (Subgroup.mem_inf.mp (P.le_A ha)).2
    have hcR : m * a * m⁻¹ * a⁻¹ ∈ R := by
      rw [mul_assoc (m * a), show m * a * (m⁻¹ * a⁻¹) = m * (a * m⁻¹ * a⁻¹) by group]
      exact mul_mem hm ((Subgroup.mem_normalizer_iff.mp (hD.le_normalizer haC) _).mp
        (inv_mem hm))
    have hcA : m * a * m⁻¹ * a⁻¹ ∈ P.A :=
      mul_mem (P.normal_A m (Subgroup.mem_inf.mpr ⟨hmN, hD.cent hm⟩) a ha) (inv_mem ha)
    rcases hA _ hcR hcA with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t

theorem good_g23 [IsSimpleGroup ↥(genFittingFStar Y)]
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    (hm : LieModel ↥(genFittingFStar Y) .G2 0 3 1) (hD : TightDatum R S t) :
    GoodThreeElement R t := by
  have := genFittingFStar_normal Y
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) (outTwoCyclic_G2 (by decide)
      (Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide)))
  have ht : orderOf (⟨t, htN⟩ : genFittingFStar Y) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨F, _, _, Sh, hcard, hz⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_G2 Nat.prime_three (by decide) hm _ ht
  have hF : Nat.card F = 3 := by rw [hcard, pow_one]
  have h3 : (3 : F) = 0 := LieType.HighestRoot.three_eq_zero hF
  have hzt : ((Sh.z : genFittingFStar Y) : Y) = t := by rw [hz]
  let P := Q3Sh.toCentShape htN Sh hzt h3 (two_ne_zero_of_three h3)
  let P' := Q3Sh.toCentShape htN Sh.swap hzt h3 (two_ne_zero_of_three h3)
  rcases TightDatum.inter_eq_or_inter_eq hD P
      (fun m hm hmA => TightDatum.pow_four_of_mem_B hD hF P' inf_le_right hm hmA)
      (fun m hm hmB => TightDatum.pow_four_of_mem_B hD hF P inf_le_right hm hmB) with hA | hB
  · exact TightDatum.good_of_centShape hD hsR hsN hs4 hF P
      (TightDatum.commute_A_of_inter hD hF P hA)
  · exact TightDatum.good_of_centShape hD hsR hsN hs4 hF P'
      (TightDatum.commute_A_of_inter hD hF P' hB)

theorem smallSimpleLeaf_g23 : SmallSimpleLeaf fun F _ => LieModel F .G2 0 3 1 := by
  intro Y _ _ _ _ hnab _ hm R S t hD _ _
  exact Or.inr (good_g23 hnab hm hD)

end CFSG.ClassicalInvolution.Q3.TA3
