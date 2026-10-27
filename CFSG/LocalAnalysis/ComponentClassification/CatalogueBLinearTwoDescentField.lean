module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoDescent

noncomputable section

universe u

@[expose] def fixedSubfield (K : Type u) [Field K] (sigma : K ≃+* K) : Subfield K :=
  FixedPoints.subfield (Subgroup.zpowers sigma) K

theorem mem_fixedSubfield (K : Type u) [Field K] (sigma : K ≃+* K) (x : K) :
    x ∈ fixedSubfield K sigma ↔ sigma x = x := by
  constructor
  · intro hx
    exact hx ⟨sigma, Subgroup.mem_zpowers sigma⟩
  · intro hx g
    have hle : Subgroup.zpowers sigma ≤ MulAction.stabilizer (K ≃+* K) x :=
      Subgroup.zpowers_le.mpr hx
    exact hle g.property

theorem fixedSubfield_finrank (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Module.finrank (fixedSubfield K sigma) K = 2 := by
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  let : IsGaloisGroup (Subgroup.zpowers sigma) (fixedSubfield K sigma) K :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers sigma) K
  calc
    Module.finrank (fixedSubfield K sigma) K = Nat.card (Subgroup.zpowers sigma) :=
      (IsGaloisGroup.card_eq_finrank (Subgroup.zpowers sigma) (fixedSubfield K sigma) K).symm
    _ = orderOf sigma := Nat.card_zpowers sigma
    _ = 2 := orderOf_eq_prime hsigma hne

@[expose] def fixedSubfieldAut (K : Type u) [Field K] (sigma : K ≃+* K) :
    K ≃ₐ[fixedSubfield K sigma] K where
  toRingEquiv := sigma
  commutes' x := (mem_fixedSubfield K sigma x).mp x.property

theorem fixedSubfieldAut_apply (K : Type u) [Field K] (sigma : K ≃+* K) (x : K) :
    fixedSubfieldAut K sigma x = sigma x := rfl

theorem fixedSubfield_norm (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (x : K) :
    ((Algebra.norm (fixedSubfield K sigma) x : fixedSubfield K sigma) : K) =
      x * sigma x := by
  classical
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  let F := fixedSubfield K sigma
  let : IsGaloisGroup (Subgroup.zpowers sigma) F K :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers sigma) K
  let tau : K ≃ₐ[F] K := fixedSubfieldAut K sigma
  have htau : tau ≠ 1 := by
    intro h
    apply hne
    ext x
    exact DFunLike.congr_fun h x
  have hcard : Nat.card (K ≃ₐ[F] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank F K]
    exact fixedSubfield_finrank K sigma hsigma hne
  have hcases (g : K ≃ₐ[F] K) : g = 1 ∨ g = tau := by
    obtain ⟨_y, _hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[F] K)).mp hcard
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((huniq g hg).trans (huniq tau htau).symm)
  have huniv : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, tau} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcases g
  change algebraMap F K (Algebra.norm F x) = x * sigma x
  rw [Algebra.norm_eq_prod_automorphisms, huniv,
    Finset.prod_insert (by simpa using htau.symm)]
  simp [tau, fixedSubfieldAut]

theorem fixedSubfield_frobenius (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (x : K) :
    sigma x = x ^ Nat.card (fixedSubfield K sigma) := by
  let F := fixedSubfield K sigma
  let : Fintype F := Fintype.ofFinite F
  let tau : K ≃ₐ[F] K := fixedSubfieldAut K sigma
  let phi : K ≃ₐ[F] K := FiniteField.frobeniusAlgEquivOfAlgebraic F K
  have htau : tau ≠ 1 := by
    intro h
    apply hne
    ext x
    exact DFunLike.congr_fun h x
  have hphi : phi ≠ 1 := by
    have ho : orderOf phi = 2 := by
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
      exact fixedSubfield_finrank K sigma hsigma hne
    intro h
    rw [h, orderOf_one] at ho
    omega
  have hcard : Nat.card (K ≃ₐ[F] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank F K]
    exact fixedSubfield_finrank K sigma hsigma hne
  obtain ⟨_y, _hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[F] K)).mp hcard
  have heq : tau = phi := (huniq tau htau).trans (huniq phi hphi).symm
  have h := DFunLike.congr_fun heq x
  simpa [tau, phi, fixedSubfieldAut, Nat.card_eq_fintype_card,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using h

theorem quadraticField_parameters (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hcard : Nat.card K = p ^ f)
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Even f ∧ (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
      Nat.card (fixedSubfield K sigma) = p ^ (f / 2) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow
    (show Fintype.card K = p ^ f by simpa [Nat.card_eq_fintype_card] using hcard)
  let F := fixedSubfield K sigma
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := Subfield.charP F p
  obtain ⟨m, _hp, hm⟩ := FiniteField.card F p
  have hmcard : Nat.card F = p ^ (m : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hm
  have hdegree : Module.finrank F K = 2 :=
    fixedSubfield_finrank K sigma hsigma hne
  have hpow : p ^ f = p ^ ((m : ℕ) * 2) := by
    calc
      p ^ f = Nat.card K := hcard.symm
      _ = Nat.card F ^ Module.finrank F K := Module.natCard_eq_pow_finrank
      _ = (p ^ (m : ℕ)) ^ 2 := by rw [hdegree, hmcard]
      _ = p ^ ((m : ℕ) * 2) := (pow_mul p (m : ℕ) 2).symm
  have hf : f = (m : ℕ) * 2 := Nat.pow_right_injective hp.two_le hpow
  have hhalf : f / 2 = (m : ℕ) := by omega
  have hfixed : Nat.card F = p ^ (f / 2) := by rw [hhalf]; exact hmcard
  refine ⟨⟨(m : ℕ), by omega⟩, ?_, hfixed⟩
  intro x
  rw [fixedSubfield_frobenius K sigma hsigma hne x, hfixed]

theorem exists_norm_unit (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (lambda : Kˣ) (hfixed : sigma (lambda : K) = lambda) :
    ∃ b : Kˣ, (b : K) * sigma (b : K) = (lambda : K) := by
  let F := fixedSubfield K sigma
  let lam : F := ⟨(lambda : K), (mem_fixedSubfield K sigma lambda).mpr hfixed⟩
  obtain ⟨b, hb⟩ := FiniteField.norm_surjective F K lam
  have hbne : b ≠ 0 := by
    intro h
    rw [h, Algebra.norm_zero] at hb
    exact Units.ne_zero lambda (congrArg Subtype.val hb.symm)
  refine ⟨Units.mk0 b hbne, ?_⟩
  change b * sigma b = (lambda : K)
  rw [← fixedSubfield_norm K sigma hsigma hne b, hb]

end

end CFSG.ComponentClassification.CatalogueBLinearTwoDescent
