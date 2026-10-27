module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Lin

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Elements

@[expose] def vd4 (a b c d : ℤ) : Fin d4.rank → ℤ := ![a, b, c, d]

@[expose] def tdWA : WeylGroup d4 := simple d4 (nd 2)

@[expose] def tdWS : WeylGroup d4 := simple d4 (nd 0) * simple d4 (nd 1) * simple d4 (nd 3)

@[expose] def tdNhat : WeylGroup d4 :=
  simple d4 (nd 0) * simple d4 (nd 1) * simple d4 (nd 3) * simple d4 (nd 2)

@[expose] def tdWB : WeylGroup d4 := tdNhat * tdWS * tdNhat⁻¹

theorem simple_inv_td4 (i : Fin d4.rank) : (simple d4 i)⁻¹ = simple d4 i :=
  (coxeterSystem d4).inv_simple i

theorem tdNhat_inv : tdNhat⁻¹ =
    simple d4 (nd 2) * simple d4 (nd 3) * simple d4 (nd 1) * simple d4 (nd 0) := by
  rw [tdNhat, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, simple_inv_td4,
    simple_inv_td4, simple_inv_td4, simple_inv_td4]
  simp only [mul_assoc]

theorem tdWB_eq : tdWB = simple d4 (nd 0) * simple d4 (nd 1) * simple d4 (nd 3) *
    simple d4 (nd 2) * (simple d4 (nd 0) * simple d4 (nd 1) * simple d4 (nd 3)) *
    (simple d4 (nd 2) * simple d4 (nd 3) * simple d4 (nd 1) * simple d4 (nd 0)) := by
  rw [tdWB, tdNhat_inv, tdWS, tdNhat]

theorem tdWA_smul_single_zero :
    tdWA • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = vd4 1 0 1 0 := by
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdWA_smul_single_one :
    tdWA • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) = vd4 0 1 1 0 := by
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdWA_smul_single_two :
    tdWA • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = vd4 0 0 (-1) 0 := by
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdWA_smul_single_three :
    tdWA • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = vd4 0 0 1 1 := by
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdWB_smul_single_zero :
    tdWB • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = vd4 (-1) 0 (-1) 0 := by
  simp only [tdWB_eq, mul_smul, simple_smul]
  decide +kernel

theorem tdWB_smul_single_one :
    tdWB • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) = vd4 0 (-1) (-1) 0 := by
  simp only [tdWB_eq, mul_smul, simple_smul]
  decide +kernel

theorem tdWB_smul_single_two :
    tdWB • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = vd4 0 0 1 0 := by
  simp only [tdWB_eq, mul_smul, simple_smul]
  decide +kernel

theorem tdWB_smul_single_three :
    tdWB • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = vd4 0 0 (-1) (-1) := by
  simp only [tdWB_eq, mul_smul, simple_smul]
  decide +kernel

theorem sum_univ_d4 {M : Type*} [AddCommMonoid M] (f : Fin d4.rank → M) :
    ∑ j, f j = f (nd 0) + f (nd 1) + f (nd 2) + f (nd 3) :=
  Fin.sum_univ_four (fun j : Fin 4 => f j)

theorem vec_eq_sum_single_td4 (v : Fin d4.rank → ℤ) :
    v = ∑ j, v j • (Pi.single j 1 : Fin d4.rank → ℤ) := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem smul_eq_sum_single_td4 (w : WeylGroup d4) (v : Fin d4.rank → ℤ) :
    w • v = ∑ j, v j • (w • (Pi.single j 1 : Fin d4.rank → ℤ)) := by
  conv_lhs => rw [vec_eq_sum_single_td4 v]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (smul_comm w (v j) (Pi.single j 1 : Fin d4.rank → ℤ))

theorem tdW0_smul_single_zero :
    (tdWA * tdWB) • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = -Pi.single (nd 0) 1 := by
  rw [mul_smul, tdWB_smul_single_zero]
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdW0_smul_single_one :
    (tdWA * tdWB) • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) = -Pi.single (nd 1) 1 := by
  rw [mul_smul, tdWB_smul_single_one]
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdW0_smul_single_two :
    (tdWA * tdWB) • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = -Pi.single (nd 2) 1 := by
  rw [mul_smul, tdWB_smul_single_two]
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdW0_smul_single_three :
    (tdWA * tdWB) • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = -Pi.single (nd 3) 1 := by
  rw [mul_smul, tdWB_smul_single_three]
  simp only [tdWA, simple_smul]
  decide +kernel

theorem tdW0_smul (v : Fin d4.rank → ℤ) : (tdWA * tdWB) • v = -v := by
  rw [smul_eq_sum_single_td4]
  have hs : ∀ j, (tdWA * tdWB) • (Pi.single j 1 : Fin d4.rank → ℤ) = -Pi.single j 1 := by
    intro j
    match j with
    | ⟨0, _⟩ => exact tdW0_smul_single_zero
    | ⟨1, _⟩ => exact tdW0_smul_single_one
    | ⟨2, _⟩ => exact tdW0_smul_single_two
    | ⟨3, _⟩ => exact tdW0_smul_single_three
  simp only [hs, smul_neg, Finset.sum_neg_distrib]
  rw [← vec_eq_sum_single_td4]

end Elements

section Classify

theorem long_image_zero : ∀ r ∈ rootFinset d4, (r (nd 0) + r (nd 1) + r (nd 3)) % 2 = 1 →
    (r (nd 0) + rho r (nd 0)) % 2 = 1 → (r (nd 1) + rho r (nd 1)) % 2 = 1 →
    (r (nd 2) + rho r (nd 2)) % 2 = 0 → (r (nd 3) + rho r (nd 3)) % 2 = 0 →
    ∀ ε ∈ ({1, -1} : Finset ℤ),
      iform r (ε • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)) =
        iform (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) (Pi.single (nd 2) 1) →
      (r = vd4 1 0 0 0 ∧ ε = 1) ∨ (r = vd4 1 0 1 0 ∧ ε = -1) ∨
        (r = vd4 (-1) 0 (-1) 0 ∧ ε = 1) ∨ (r = vd4 (-1) 0 0 0 ∧ ε = -1) := by
  decide +kernel

theorem weyl_long_cases {K : Type} [Field K] (hK : (-1 : Kˣ) ≠ 1) {w : WeylGroup d4}
    (hwρ : weylTwist TwistTag.D4 w = w) (hwa : w ∈ rootCharStabilizer (aLongTD4 K)) :
    w = 1 ∨ w = tdWA ∨ w = tdWB ∨ w = tdWA * tdWB := by
  set r : Fin d4.rank → ℤ := w • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) with hr
  have hroot : IsRoot d4 r := IsRoot.smul (isRoot_single d4 (nd 0)) w
  have hw1 : w • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) = rho r := by
    rw [hr, ← smul_rho_td4 hwρ, rho_single, rhoPerm_zero]
  have hw3 : w • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = rho (rho r) := by
    have h3 : (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) = rho (Pi.single (nd 1) 1) := by
      rw [rho_single, rhoPerm_one]
    rw [h3, smul_rho_td4 hwρ, hw1]
  have hchar : rootChar (aLongTD4 K) r = -1 := by
    rw [hr, hwa, rootChar_single_td4]
    rfl
  have hpar : (r (nd 0) + r (nd 1) + r (nd 3)) % 2 = 1 := by
    by_contra hcon
    have h0 : (r (nd 0) + r (nd 1) + r (nd 3)) % 2 = 0 := by omega
    have := (rootChar_aLong_eq_one_iff hK r).2 h0
    rw [hchar] at this
    exact hK this
  have hrad := weyl_smul_radical w (Pi.single (nd 0) 1 + Pi.single (nd 1) 1) (by
    constructor
    · simp +decide
    · simp +decide)
  rw [smul_add, hw1] at hrad
  have e0 := hrad.2 (nd 0)
  have e1 := hrad.2 (nd 1)
  have e2 := hrad.2 (nd 2)
  have e3 := hrad.2 (nd 3)
  simp only [Pi.add_apply] at e0 e1 e2 e3
  have e0' : (r (nd 0) + rho r (nd 0)) % 2 = 1 := by rw [← hr] at e0; simpa +decide using e0
  have e1' : (r (nd 1) + rho r (nd 1)) % 2 = 1 := by rw [← hr] at e1; simpa +decide using e1
  have e2' : (r (nd 2) + rho r (nd 2)) % 2 = 0 := by rw [← hr] at e2; simpa +decide using e2
  have e3' : (r (nd 3) + rho r (nd 3)) % 2 = 0 := by rw [← hr] at e3; simpa +decide using e3
  obtain ⟨ε, hε, hε2⟩ : ∃ ε : ℤ, ε ∈ ({1, -1} : Finset ℤ) ∧
      w • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) = ε • Pi.single (nd 2) 1 := by
    rcases weyl_long_root hK hwρ hwa with h | h
    · exact ⟨1, by simp, by rw [h, one_smul]⟩
    · exact ⟨-1, by simp, by rw [h, neg_one_smul]⟩
  have hiso := iform_smul w (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) (Pi.single (nd 2) 1)
  rw [← hr, hε2] at hiso
  rcases long_image_zero r (mem_rootFinset.2 hroot) hpar e0' e1' e2' e3' ε hε hiso with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have c0 : vd4 1 0 0 0 = (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) := by decide +kernel
    have c1 : rho (vd4 1 0 0 0) = (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) := by decide +kernel
    have c3 : rho (rho (vd4 1 0 0 0)) = (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) := by
      decide +kernel
    refine ext_single fun i => ?_
    match i with
    | ⟨0, _⟩ => rw [one_smul]; exact h1.trans c0
    | ⟨1, _⟩ => rw [one_smul, hw1, h1]; exact c1
    | ⟨2, _⟩ => rw [one_smul, hε2, h2, one_smul]
    | ⟨3, _⟩ => rw [one_smul, hw3, h1]; exact c3
  · right; left
    refine ext_single fun i => ?_
    match i with
    | ⟨0, _⟩ => rw [tdWA_smul_single_zero]; exact h1
    | ⟨1, _⟩ => rw [tdWA_smul_single_one, hw1, h1]; decide +kernel
    | ⟨2, _⟩ => rw [tdWA_smul_single_two, hε2, h2]; decide +kernel
    | ⟨3, _⟩ => rw [tdWA_smul_single_three, hw3, h1]; decide +kernel
  · right; right; left
    refine ext_single fun i => ?_
    match i with
    | ⟨0, _⟩ => rw [tdWB_smul_single_zero]; exact h1
    | ⟨1, _⟩ => rw [tdWB_smul_single_one, hw1, h1]; decide +kernel
    | ⟨2, _⟩ => rw [tdWB_smul_single_two, hε2, h2]; decide +kernel
    | ⟨3, _⟩ => rw [tdWB_smul_single_three, hw3, h1]; decide +kernel
  · right; right; right
    refine ext_single fun i => ?_
    match i with
    | ⟨0, _⟩ => rw [tdW0_smul_single_zero]; exact h1.trans (by decide)
    | ⟨1, _⟩ => rw [tdW0_smul_single_one, hw1, h1]; decide +kernel
    | ⟨2, _⟩ => rw [tdW0_smul_single_two, hε2, h2]; decide +kernel
    | ⟨3, _⟩ => rw [tdW0_smul_single_three, hw3, h1]; decide +kernel

end Classify

end CFSG.ClassicalInvolution.G2D4Models
