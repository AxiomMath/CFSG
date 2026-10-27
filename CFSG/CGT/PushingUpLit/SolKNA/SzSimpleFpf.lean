module

public import CFSG.Quasithin.Background.SmithB45SzNat
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleCharpoly
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleKron

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Quasithin.B45Sz CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.Blueprint CFSG.ComponentClassification.UnbalancedCatalog.SpChain Matrix

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]

theorem szT_apply_eq (hK : Nat.card K = 2 ^ (2 * a + 1))
    (E : Type) [Field E] [Algebra K E] (A : Finset ℕ) (g : ↥(suzukiGroup a K)) :
    szT E hK A g = Matrix.of fun x' x : (↥A → Fin 4) => ∏ i : ↥A,
      ((glMat (g : GL (Fin 4) K)).map
        (fun y => algebraMap K E (y ^ 2 ^ ((a + 1) * (i : ℕ))))) (x' i) (x i) := by
  ext x' x
  rw [szT_apply, tensorRepS_apply]
  simp only [natRepS_szIncl E hK, Matrix.of_apply]

theorem finrank_eq_four_of_fpf (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M)) [Fact (repOfG π).IsIrreducible]
    (hnt : ∃ g, repOfG π g ≠ 1) {z : ↥(suzukiGroup a K)} (hz : orderOf z = 5)
    (hfpf : ∀ w, repOfG π z w = w → w = 0) :
    Module.finrank (EndRing (repOfG π)) M = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sz_descent hK hnt
  have : Module.Finite (EndRing (repOfG π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιK, ιD, A, hAne, hA, ⟨Φ⟩, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOfG π)) M)
  let _ : Algebra K E := ιK.toAlgebra
  by_contra hne
  have hm2 : 2 ≤ A.card := by
    have h1 : 1 ≤ A.card := Finset.card_pos.mpr hAne
    by_contra h
    have h2 : A.card = 1 := by omega
    rw [h2, pow_one] at hdimW
    exact hne hdimW
  have hz5 : z ^ 5 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz
    omega
  have hC5 : (glMat (z : GL (Fin 4) K)) ^ 5 = 1 := by
    have h : (z : GL (Fin 4) K) ^ 5 = 1 := by
      have := congrArg (fun w : ↥(suzukiGroup a K) => (w : GL (Fin 4) K)) hz5
      simpa using this
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h
    simpa [Units.val_pow_eq_pow_val] using this
  have hC1 : glMat (z : GL (Fin 4) K) ≠ 1 := fun h => hz1 (Subtype.ext (Units.ext h))
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have hχ := charpoly_eq_cyclotomic_five (odd_two_mul_add_one a) hcard _ hC5 hC1
  have hCi : ∀ i : ↥A, ((glMat (z : GL (Fin 4) K)).map
      (fun y => algebraMap K E (y ^ 2 ^ ((a + 1) * (i : ℕ))))).charpoly =
        Polynomial.cyclotomic 5 E := by
    intro i
    have hfun : (fun y : K => algebraMap K E (y ^ 2 ^ ((a + 1) * (i : ℕ)))) =
        ⇑((algebraMap K E).comp (iterateFrobenius K 2 ((a + 1) * (i : ℕ)))) := by
      funext y
      simp [iterateFrobenius_def]
    rw [hfun, Matrix.charpoly_map, hχ, Polynomial.map_cyclotomic]
  have hι : 2 ≤ Fintype.card ↥A := by
    rw [Fintype.card_coe]
    exact hm2
  obtain ⟨y, hy0, hy⟩ := exists_fixed_kron hι
    (fun i : ↥A => (glMat (z : GL (Fin 4) K)).map
      (fun y => algebraMap K E (y ^ 2 ^ ((a + 1) * (i : ℕ))))) hCi
  have hyfix : (szT E hK A z).mulVec y = y := by
    rw [szT_apply_eq]
    exact hy
  have hcount := natCard_fix_pow_gen (Module.finBasis (EndRing (repOfG π)) M) ιD
    (szT E hK A) Φ z
  have hW1 : Nat.card {w : M // repOfG π z w = w} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, map_zero _⟩⟩⟩
    rw [hfpf x.1 x.2, hfpf y.1 y.2]
  have h2 : 1 < Nat.card {y' : (↥A → Fin 4) → E // (szT E hK A z).mulVec y' = y'} := by
    have : Finite {y' : (↥A → Fin 4) → E // (szT E hK A z).mulVec y' = y'} := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.mpr
      ⟨⟨⟨y, hyfix⟩, ⟨0, by simp⟩, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  rw [hW1, one_pow] at hcount
  omega

end CFSG.CGT.PushingUpLit.SolKNA
