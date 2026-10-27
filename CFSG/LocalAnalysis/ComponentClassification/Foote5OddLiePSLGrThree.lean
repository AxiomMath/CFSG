module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrSp
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrPerm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthThree

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Gr

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_one_of_commute_sign_three (h3 : Nat.card K = 3) (hn3 : 3 ≤ n) (hn4 : n ≤ 4)
    {w : Fin n → K} (hw : ∀ i, w i ≠ 0) {r : MulAut (projectiveSL n K)} (hodd : Odd (orderOf r))
    (hrt : r * (conjAut n K (diagGL hw)⁻¹ * dualAut n K) =
      conjAut n K (diagGL hw)⁻¹ * dualAut n K * r)
    {i j : Fin n} (hij : i ≠ j)
    (hcomm : conjProj n K (signPair (K := K) hij) * r = r * conjProj n K (signPair hij)) :
    r = 1 := by
  obtain ⟨D, τ, rfl⟩ := Burgoyne.PSL.exists_semilinear_of_odd hn3 hodd
  have hτ : τ = 1 := ringEquiv_eq_one_of_prime_card (by rw [h3]; exact Nat.prime_three) τ
  subst hτ
  rw [map_one, mul_one] at hodd hcomm hrt ⊢
  set S := signPair (K := K) hij with hS
  have hcS : conjProj n K S = conjAut n K (SpecialLinearGroup.toGL S) := (conjAut_toGL S).symm
  rw [hcS] at hcomm
  have hSS : ∃ ν : Kˣ, SpecialLinearGroup.toGL S * SpecialLinearGroup.toGL S =
      GeneralLinearGroup.scalar (Fin n) ν := ⟨1, by
    rw [← map_mul, hS, signPair_mul_self, map_one, map_one]⟩
  have hDS := commute_of_odd_conjAut hn3 hSS hodd hcomm.symm
  have hDSm : (D : Matrix (Fin n) (Fin n) K) * signMat K {i, j} = signMat K {i, j} * D := by
    have := congrArg Units.val hDS
    rw [Units.val_mul, Units.val_mul] at this
    exact this
  obtain ⟨c, hc⟩ := similitude_of_commute_conjAut_dualAut hn3 hrt
  have hsim : (D : Matrix (Fin n) (Fin n) K) * diagonal (fun x => (w x)⁻¹) *
      (D : Matrix (Fin n) (Fin n) K)ᵀ = diagonal fun x => (c : K) * (w x)⁻¹ := by
    have hAm : (((diagGL hw)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        diagonal fun x => (w x)⁻¹ := rfl
    rw [hAm, ← diagonal_smul] at hc
    exact hc
  have hD8 := pow_eight_eq_one_of_commute_sign h3 hn3 hn4 (fun x => inv_ne_zero (hw x))
    c.ne_zero hsim hij hDSm
  have hpow : conjAut n K D ^ 8 = 1 := by
    rw [← map_pow]
    have : D ^ 8 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hD8, Units.val_one])
    rw [this, map_one]
  have hdvd : orderOf (conjAut n K D) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.1 hk

omit [Finite K] in
theorem odd_orderOf_proj_of_pow_three {x : Matrix.SpecialLinearGroup (Fin n) K} (hx : x ^ 3 = 1) :
    Odd (orderOf (proj n K x)) := by
  have h : orderOf (proj n K x) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  exact Odd.of_dvd_nat (by decide) h

theorem eq_one_orth_three (h3 : Nat.card K = 3) (hn3 : 3 ≤ n) (hn4 : n ≤ 4)
    {w : Fin n → K} (hw : OrthNF w)
    {R : Subgroup (MulAut (projectiveSL n K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * (conjAut n K (diagGL hw.1)⁻¹ * dualAut n K) =
      conjAut n K (diagGL hw.1)⁻¹ * dualAut n K * r)
    (hRc : ∀ s, (conjAut n K (diagGL hw.1)⁻¹ * dualAut n K) s = s → Odd (orderOf s) →
      ∀ r ∈ R, MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  obtain ⟨I, hI3, -, hIw⟩ := hw.2
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.1 (by omega : 2 < I.card)
  obtain ⟨c, hcs, hc3, hca, hcb, hcd, hco⟩ := exists_three_cycle hab had hbd
  have hwc : ∀ x, w (c x) = w x := by
    intro x
    by_cases hxa : x = a
    · rw [hxa, hca]; exact hIw _ hb _ ha
    · by_cases hxb : x = b
      · rw [hxb, hcb]; exact hIw _ hd _ hb
      · by_cases hxd : x = d
        · rw [hxd, hcd]; exact hIw _ ha _ hd
        · rw [hco x hxa hxb hxd]
  set A := (diagGL hw.1)⁻¹ with hA
  have hfixt : ∀ g ∈ isometrySL n (diagGL hw.1),
      (conjAut n K A * dualAut n K) (proj n K g) = proj n K g := by
    intro g hg
    rw [conjAut_mul_dualAut_proj, (graphLift_eq_iff A g).2 (by rwa [hA, inv_inv])]
  set P := permSL (K := K) c hcs with hP
  have hPmem : P ∈ isometrySL n (diagGL hw.1) := permSL_mem_isometry hw.1 c hcs hwc
  have hP3 : P ^ 3 = 1 := permSL_pow_eq_one c hcs hc3
  have hnorm : ∀ {i j : Fin n} (hij : i ≠ j), ∀ r ∈ R,
      conjProj n K (P * signPair hij * P⁻¹ * (signPair hij)⁻¹) * r *
        (conjProj n K (P * signPair hij * P⁻¹ * (signPair hij)⁻¹))⁻¹ ∈ R := by
    intro i j hij r hr
    set y := signPair (K := K) hij * P⁻¹ * (signPair hij)⁻¹ with hy
    have hSmem := signPair_mem_isometry (K := K) hw.1 hij
    have hymem : y ∈ isometrySL n (diagGL hw.1) :=
      mul_mem (mul_mem hSmem (inv_mem hPmem)) (inv_mem hSmem)
    have hy3 : y ^ 3 = 1 := by
      rw [hy, conj_pow, inv_pow, hP3, inv_one, mul_one, mul_inv_cancel]
    have e : P * signPair hij * P⁻¹ * (signPair hij)⁻¹ = P * y := by rw [hy]; group
    rw [e, map_mul]
    have h1 := hRc _ (hfixt _ hymem) (odd_orderOf_proj_of_pow_three hy3) r hr
    have h2 := hRc _ (hfixt _ hPmem) (odd_orderOf_proj_of_pow_three hP3) _ h1
    have e2 : conjProj n K P * conjProj n K y * r * (conjProj n K P * conjProj n K y)⁻¹ =
        MulAut.conj (proj n K P) * (MulAut.conj (proj n K y) * r *
          (MulAut.conj (proj n K y))⁻¹) * (MulAut.conj (proj n K P))⁻¹ := by
      simp only [MonoidHom.comp_apply]
      group
    rw [e2]
    exact h2
  have hcomm₁ : P * signPair hab * P⁻¹ * (signPair hab)⁻¹ = signPair (K := K) had := by
    rw [conj_signSL_pair, signPair_inv, signPair_eq (c.injective.ne hab) hbd hca hcb,
      signPair_comm hbd, signPair_comm hab, signPair_mul hbd.symm hab.symm had.symm]
    exact (signPair_comm had).symm
  have hcomm₂ : P * signPair had * P⁻¹ * (signPair had)⁻¹ = signPair (K := K) hbd := by
    rw [conj_signSL_pair, signPair_inv, signPair_eq (c.injective.ne had) hab.symm hca hcd]
    exact signPair_mul hab.symm had hbd
  have hsq : ∀ {i j : Fin n} (hij : i ≠ j),
      conjProj n K (signPair (K := K) hij) * conjProj n K (signPair hij) = 1 := by
    intro i j hij
    rw [← map_mul, signPair_mul_self, map_one]
  have h12 : conjProj n K (signPair (K := K) had) * conjProj n K (signPair hbd) =
      conjProj n K (signPair hab) := by
    rw [← map_mul, signPair_comm hbd, signPair_mul had hbd.symm hab]
  have hRb : R = ⊥ := eq_bot_of_four_group (hsq had) (hsq hbd)
    (fun x hx => by
      have := hnorm hab x hx
      rwa [hcomm₁] at this)
    (fun x hx => by
      have := hnorm had x hx
      rwa [hcomm₂] at this)
    (fun x hx h => eq_one_of_commute_sign_three h3 hn3 hn4 hw.1 (odd_orderOf_of_mem hRodd hx)
      (hRi x hx) had h)
    (fun x hx h => eq_one_of_commute_sign_three h3 hn3 hn4 hw.1 (odd_orderOf_of_mem hRodd hx)
      (hRi x hx) hbd h)
    (fun x hx h => by
      rw [h12] at h
      exact eq_one_of_commute_sign_three h3 hn3 hn4 hw.1 (odd_orderOf_of_mem hRodd hx)
        (hRi x hx) hab h)
  intro r hr
  rw [hRb] at hr
  exact mem_bot.1 hr

end CFSG.ComponentClassification.Foote5.OddLieCore.Gr
