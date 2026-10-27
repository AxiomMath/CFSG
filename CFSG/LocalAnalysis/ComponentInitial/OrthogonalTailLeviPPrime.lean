module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCharTwoSign
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem tailDiag_one_one : tailDiag r (1 : Fin r → Kˣ) (1 : A ≃ₗ[K] A) = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [tailDiag_apply, map_one]
  rfl

theorem tailDiag_pow (t : Fin r → Kˣ) (h : A ≃ₗ[K] A) (n : ℕ) :
    tailDiag r t h ^ n = tailDiag r (t ^ n) (h ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, tailDiag_one_one]
  | succ n ih => rw [pow_succ, ih, tailDiag_mul, pow_succ, pow_succ]

theorem tailDiag_one_reflect {v : A} (hv : qA v ≠ 0) :
    tailDiag r 1 (reflect qA v) = reflect (quadTail r qA) ((0 : Fin r ⊕ Fin r → K), v) := by
  have hv' : quadTail r qA ((0 : Fin r ⊕ Fin r → K), v) ≠ 0 := by rwa [quadTail_tail]
  refine LinearEquiv.ext fun x => ?_
  rw [tailDiag_apply, map_one, reflect_apply hv, reflect_apply hv', polar_quadTail,
    polar_zero_left, zero_add, quadTail_tail]
  refine Prod.ext ?_ ?_ <;> simp

theorem eq_one_of_sub_one_sq_eq_zero (hani : qA.Anisotropic) (h2 : (2 : K) ≠ 0)
    {h : A ≃ₗ[K] A} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup qA)
    (hN : ((h : Module.End K A) - 1) ^ 2 = 0) : h = 1 := by
  refine LinearEquiv.ext fun x => ?_
  set v := ((h : Module.End K A) - 1) x with hv
  have hhx : h x = x + v := by
    rw [hv, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]
    abel
  have hNv : ((h : Module.End K A) - 1) v = 0 := by
    rw [hv, ← Module.End.mul_apply, ← pow_two, hN, LinearMap.zero_apply]
  have hhv : h v = v := by
    have := hNv
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, sub_eq_zero] at this
    exact this
  have hhhx : h (h x) = x + (2 : K) • v := by
    rw [hhx, map_add, hhx, hhv, two_smul]
    abel
  have e1 := map_of_mem hh x
  have e2 := (map_of_mem hh (h x)).trans (map_of_mem hh x)
  rw [hhx, QuadraticMap.map_add qA] at e1
  rw [hhhx, QuadraticMap.map_add qA, QuadraticMap.map_smul, polar_smul_right_eq] at e2
  have hq : qA v = 0 := by
    have : (2 : K) * qA v = 0 := by linear_combination e2 - 2 * e1
    exact (mul_eq_zero.1 this).resolve_left h2
  have hv0 : v = 0 := hani v hq
  rw [hhx, hv0, add_zero, LinearEquiv.coe_one, id_eq]

theorem orthogonal_geometry_tail_small_anisotropic_Levi_p_prime {K : Type*} [Field K] [Finite K]
    {p : ℕ} [hp : Fact p.Prime] [CharP K p] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
    (hr : 3 ≤ r) {qA : QuadraticForm K A} (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate) (hm : finrank K A = 1 ∨ finrank K A = 2) :
    ¬p ∣ Nat.card (tailTorus r qA) := by
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  have : FiniteDimensional K A := Module.finite_of_finrank_pos hpos
  have : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
  have : Finite A := Module.finite_of_finite K
  have : Finite (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _ =>
      (g : ((Fin r ⊕ Fin r → K) × A) → (Fin r ⊕ Fin r → K) × A)) DFunLike.coe_injective
  intro hdvd
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨hτE, t, h, hh, hτeq⟩ := mem_tailTorus.1 τ.2
  have hpow : tailDiag r (t ^ p) (h ^ p) = 1 := by
    rw [← tailDiag_pow, hτeq, ← Subgroup.coe_pow, ← hτ, pow_orderOf_eq_one, Subgroup.coe_one]
  have ht : t = 1 := by
    funext i
    have h1 := congrArg (fun g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _ =>
      (g (hypVec K A (.inl i))).1 (.inl i)) hpow
    simp only [tailDiag_apply, torusElt_apply, hypVec, Pi.single_eq_same, mul_one,
      Sum.elim_inl, LinearEquiv.coe_one, id_eq] at h1
    refine Units.ext ?_
    have h2 : ((t i : K) - 1) ^ p = 0 := by
      rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val]
      rw [Pi.pow_apply] at h1
      rw [h1, sub_self]
    rw [Pi.one_apply, Units.val_one]
    exact sub_eq_zero.1 (pow_eq_zero_iff hp.out.ne_zero |>.1 h2)
  have hhp : h ^ p = 1 := LinearEquiv.ext fun a => by
    have h1 := congrArg (fun g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _ =>
      (g ((0 : Fin r ⊕ Fin r → K), a)).2) hpow
    change (h ^ p) a = a
    simpa only [tailDiag_apply, LinearEquiv.coe_one, id_eq] using h1
  have hτ1 : (τ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ≠ 1 :=
    fun h1 => by
    have : τ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hτ
    exact hp.out.one_lt.ne hτ
  have hh1 : h ≠ 1 := fun h1 => hτ1 (by rw [← hτeq, ht, h1, tailDiag_one_one])
  have : CharP (Module.End K A) p :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K A)).injective p
  set N : Module.End K A := (h : Module.End K A) - 1 with hNdef
  have hNp : N ^ p = 0 := by
    have hφ : (h : Module.End K A) ^ p = 1 := LinearMap.ext fun a => by
      rw [Module.End.coe_pow, Module.End.one_apply, LinearEquiv.coe_coe, ← LinearEquiv.coe_pow,
        hhp, LinearEquiv.coe_one, id_eq]
    rw [hNdef, sub_pow_char_of_commute p (Commute.one_right _), hφ, one_pow, sub_self]
  have hN2 : N ^ 2 = 0 := by
    have hfin : N ^ finrank K A = 0 := by
      simpa only [IsNilpotent.charpoly_eq_X_pow_finrank ⟨p, hNp⟩, map_pow, Polynomial.aeval_X]
        using N.aeval_self_charpoly
    exact pow_eq_zero_of_le (by rcases hm with h | h <;> omega) hfin
  by_cases hp2 : p = 2
  · subst hp2
    have hdim : finrank K A = 2 := by
      rcases hm with h1 | h2
      · exfalso
        obtain ⟨a, ha⟩ := exists_ne (0 : A)
        obtain hspan := (finrank_eq_one_iff_of_nonzero' a ha).1 h1
        apply ha
        refine eq_zero_of_polar_eq_zero hreg fun b => ?_
        obtain ⟨c, rfl⟩ := hspan b
        rw [polar_smul_right_eq, polar_self_eq_two_mul,
          show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, mul_zero]
      · exact h2
    have hN0 : N ≠ 0 := fun h0 => hh1 (LinearEquiv.ext fun a => by
      have := LinearMap.congr_fun h0 a
      rw [hNdef, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
        LinearMap.zero_apply, sub_eq_zero] at this
      exact this)
    obtain ⟨x, hx⟩ : ∃ x, N x ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hN0 (LinearMap.ext hcon)
    set v := N x with hvdef
    have hNv : N v = 0 := by
      rw [hvdef, ← Module.End.mul_apply, ← pow_two, hN2, LinearMap.zero_apply]
    have hhv : h v = v := by
      have := hNv
      rw [hNdef, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
        sub_eq_zero] at this
      exact this
    have hqv : qA v ≠ 0 := fun h0 => hx (hani v h0)
    have hrefl : h = reflect qA v :=
      (orthogonal_char_two_plane_vector_stabilizer hdim hreg hqv hh hhv).resolve_left hh1
    have hτr : (τ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
        reflect (quadTail r qA) ((0 : Fin r ⊕ Fin r → K), v) := by
      rw [← hτeq, ht, hrefl, tailDiag_one_reflect hqv]
    obtain ⟨-, -, -, hsep⟩ := orthogonal_geometry_char_two_reflection_separation
      (nondegenerate_polarBilin_quadTail (r := r) hreg)
      ⟨tailFlag K A r 3, finrank_tailFlag hr, fun x hx => quadTail_eq_zero_of_mem_tailFlag hx⟩
    exact hsep _ (by rwa [quadTail_tail]) (hτr ▸ hτE)
  ·
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
    exact hh1 (eq_one_of_sub_one_sq_eq_zero hani h2 hh hN2)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
