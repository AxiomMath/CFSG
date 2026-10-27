module

public import CFSG.RankThree.PartOne.KE.E8FiveFamily
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TenArith

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot weylMatrix)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open CFSG.RankThree.Classical2 (unitarySet sln_root_permuting_frobenius_fixed_unitary)
open CFSG.RankThree.PartOne.KE
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


theorem e8Ten_family {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {L : Type} [Field L] [IsAlgClosed L] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : ∀ u, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • u = ((-1 : ℤ) • weylMatrix e8F5U) *ᵥ u)
    (v : WeylGroup Tag.E8)
    (hunit : ∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
      (-weylMatrix e8F5U) *ᵥ sigmaRootE8A4 v i j = sigmaRootE8A4 v (π j) (π i))
    {p : ℕ} (hpd : p ∣ Nat.card k ^ 5 + 1) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n Fr (sigmaSetE8A4 v) P ∧
      P () = rootSpan Tag.E8 L (sigmaSetE8A4 v) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      (∃ h₀ : ModGL Tag.E8 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E8 L (e8Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P ()) ∧
      p ∣ Nat.card (P ()) := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 5) (hij : i ≠ j) =>
    rhoSigmaE8A4_transvection (L := L) v i j hij
  have htor : ∀ b : Fin Tag.E8.rank → Lˣ, ∃ d : Fin 5 → Lˣ, ∀ A : SL(5, L),
      rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L v A * (rootDiagUnit Tag.E8 b)⁻¹ =
        rhoSigmaE8A4 L v (conjDiagn d A) := fun b =>
    ⟨fun i => rootChar b (wbE8A4 v i), fun A => rhoSigmaE8A4_torus v b A⟩
  have hdiag : ∀ A : SL(5, L), (∀ i j, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) →
      rhoSigmaE8A4 L v A ∈ torusGroup Tag.E8 L := fun A hA => rhoSigmaE8A4_diagonal v A hA
  have hrange := rhoSigmaE8A4_range (L := L) v
  have hh₀ : ∀ (J : SL(5, L)) (Y : SL(2, k)),
      rhoSigmaE8A4 L v (J * blockSL L 2 3 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          J⁻¹) =
        (canonicalRep (coxeterSystem Tag.E8) L v * e8rhoJ4 L J) *
          simpleRootSL2 Tag.E8 L (e8Index 0)
            (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          (canonicalRep (coxeterSystem Tag.E8) L v * e8rhoJ4 L J)⁻¹ := by
    intro J Y
    have h1 : e8rhoJ4 L (J * blockSL L 2 3 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
        J⁻¹) = e8rhoJ4 L J * simpleRootSL2 Tag.E8 L (e8Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * (e8rhoJ4 L J)⁻¹ := by
      rw [map_mul, map_mul, map_inv, e8rhoJ4_blockSL]
    change (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L v))
      (e8rhoJ4 L (J * blockSL L 2 3 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
        J⁻¹)) = _
    rw [h1, MulAut.conj_apply]
    group
  obtain ⟨π, hπ⟩ := hunit
  have hconj : ∀ i j : Fin 5, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n * pinnedX Tag.E8 L (sigmaRootE8A4 v i j) c * n⁻¹ =
        pinnedX Tag.E8 L (sigmaRootE8A4 v (π j) (π i)) ((b : L) * c) := fun i j hij => by
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRootE8A4 v hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, hnW, neg_one_smul, hπ i j hij]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E8) (ν := 5)
    (rhoSigmaE8A4 L v) (rhoSigmaE8A4_injective v) (sigmaRootE8A4 v) ε hε Fr hFrbij n
    (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
    (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin 5) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(5, L)) :
        Matrix (Fin 5) (Fin 5) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨P, hP, hP1, hP2⟩ := an_family_unitary hℓ hf hk (Or.inl (by norm_num))
    (by norm_num) (sigmaSetE8A4_isRoot v) (rhoSigmaE8A4 L v) (rhoSigmaE8A4_injective v)
    hrange htor hdiag Fr n Φ' hΦ' π b hshape'
  obtain ⟨J, hJ⟩ := sln_fixed_contains_block_unitary hℓ hf hk (m := 3) (by norm_num) π Φ' b
    hshape'
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ := sln_root_permuting_frobenius_fixed_unitary hℓ hf hk
    (by norm_num) π Φ' b hshape'
  refine ⟨P, hP, by rw [hP1, hrange], ⟨canonicalRep (coxeterSystem Tag.E8) L v * e8rhoJ4 L J,
    fun Y => ?_⟩, ?_⟩
  · rw [hP2, ← hh₀ J Y]
    exact ⟨_, hJ Y, rfl⟩
  · haveI : Finite (P ()) := hP.1 ()
    haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    refine e8Ten_p_dvd_card_of_unitary_family (K := k) hf hk hpd (rhoSigmaE8A4 L v)
      (rhoSigmaE8A4_injective v) (P ()) H fun Z hZ => ?_
    rw [hP2]
    exact ⟨Z, (hH Z).2 (by rwa [hk] at hZ), rfl⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
