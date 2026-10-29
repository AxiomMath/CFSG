module

public import CFSG.LinearAlgebra.SemilinearSingerExclusion
public import CFSG.LinearAlgebra.SemilinearDeterminantKernel
public import CFSG.RankThree.SubgroupLists.OddCharacteristicExtraspecial
public import CFSG.RankThree.SubgroupLists.MonomialFourDeterminant
public import CFSG.Monster.B.Short.Extraspecial
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.GroupTheory.PRankLeOneOfIsCyclic

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCLinComm

variable {A : Type*} [Group A] [Finite A] {K : Type} [Field K] [Finite K]

private theorem semilinear_rank_three_kernel_transports
    (ρ : A →* coordinateSemilinearGroup 3 K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →* GL (Fin 3) K)
    (hτinj : Function.Injective τ)
    (hJodd : Odd (Nat.card (SemidirectProduct.rightHom.comp ρ).ker))
    (hirr : IsIrreducibleMatrixRep τ.range.subtype)
    (hrank : 2 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (SemidirectProduct.rightHom.comp ρ).ker))
    (Z : Subgroup (SemidirectProduct.rightHom.comp ρ).ker)
    (hZcard : Nat.card Z = 3)
    (hZscalar : ∀ z ∈ Z, ∃ c : Kˣ,
      τ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    Odd (Nat.card τ.range) ∧
      2 ≤ CFSG.Open.pRank 3 τ.range ∧
      (∃ x y : (SemidirectProduct.rightHom.comp ρ).ker, x * y ≠ y * x) ∧
      (Z.map τ ≤ τ.range ∧
        (∀ M ∈ Z.map τ, ∃ c : K, (M : Matrix (Fin 3) (Fin 3) K) =
          Matrix.scalar (Fin 3) c) ∧
        (∀ M ∈ Z.map τ, M ^ 3 = 1)) := by
  classical
  let J : Subgroup A := (SemidirectProduct.rightHom.comp ρ).ker
  let Jmat : Subgroup (GL (Fin 3) K) := τ.range
  let Zmat : Subgroup (GL (Fin 3) K) := Z.map τ
  let eJ : J ≃* Jmat := MonoidHom.ofInjective hτinj
  have hcardJmat : Nat.card Jmat = Nat.card J := (Nat.card_congr eJ.toEquiv).symm
  have hoddMat : Odd (Nat.card Jmat) := by
    rw [hcardJmat]
    exact hJodd
  have hrankTop : CFSG.Open.pRank 3 (⊤ : Subgroup J) =
      CFSG.Open.pRank 3 (⊤ : Subgroup Jmat) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eJ
  have hrankMatTop : CFSG.Open.pRank 3 Jmat =
      CFSG.Open.pRank 3 (⊤ : Subgroup Jmat) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Jmat
  have hrankMat : 2 ≤ CFSG.Open.pRank 3 Jmat := by
    rw [hrankMatTop, ← hrankTop]
    exact hrank
  have hZmatJ : Zmat ≤ Jmat := Subgroup.map_le_range τ Z
  have hZscalarMat : ∀ M ∈ Zmat, ∃ c : K,
      (M : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
    intro M hM
    rw [Subgroup.mem_map] at hM
    obtain ⟨z, hz, rfl⟩ := hM
    obtain ⟨c, hc⟩ := hZscalar z hz
    refine ⟨(c : K), ?_⟩
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hZcubeMat : ∀ M ∈ Zmat, M ^ 3 = 1 := by
    intro M hM
    rw [Subgroup.mem_map] at hM
    obtain ⟨z, hz, rfl⟩ := hM
    let zZ : Z := ⟨z, hz⟩
    have hz3 : z ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := zZ)
      rw [hZcard] at h
      exact congrArg (fun w : Z => (w : J)) h
    calc
      (τ z) ^ 3 = τ (z ^ 3) := (map_pow τ z 3).symm
      _ = τ 1 := by rw [hz3]
      _ = 1 := map_one τ
  have hncJ : ∃ x y : J, x * y ≠ y * x := by
    by_contra h
    push Not at h
    have hcommJ : ∀ x y : J, x * y = y * x := fun x y => h x y
    have hcommMat : ∀ a ∈ Jmat, ∀ b ∈ Jmat, a * b = b * a := by
      rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩
      calc τ x * τ y = τ (x * y) := (map_mul τ x y).symm
        _ = τ (y * x) := by rw [hcommJ x y]
        _ = τ y * τ x := map_mul τ y x
    have hcyc : IsCyclic Jmat :=
      (cyclic_of_irreducible_of_commute (K := K) (n := 3) Nat.prime_three hirr hcommMat).1
    have hrankLe : CFSG.Open.pRank 3 Jmat ≤ 1 := by
      have h := CFSG.pRank_le_one_of_isCyclic (p := 3) Nat.prime_three hcyc
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Jmat] at h
      exact h
    omega
  exact ⟨hoddMat, hrankMat, hncJ, hZmatJ, hZscalarMat, hZcubeMat⟩

private theorem exists_invariant_isPOnePlusTwo_of_reduction
    (hK : Nat.card K = 4)
    (ρ : A →* coordinateSemilinearGroup 3 K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →* GL (Fin 3) K)
    (hτinj : Function.Injective τ)
    (hτ : ∀ j : (SemidirectProduct.rightHom.comp ρ).ker,
      ρ (j : A) = SemidirectProduct.inl (τ j))
    (hJodd : Odd (Nat.card (SemidirectProduct.rightHom.comp ρ).ker))
    (hJindex : (SemidirectProduct.rightHom.comp ρ).ker.index = 2)
    (hirr : IsIrreducibleMatrixRep τ.range.subtype)
    (hrank : 2 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (SemidirectProduct.rightHom.comp ρ).ker))
    (hno : ∀ N : Subgroup A, N.Normal → N.index ≠ 3)
    (Z : Subgroup (SemidirectProduct.rightHom.comp ρ).ker)
    (hZcard : Nat.card Z = 3)
    (hZscalar : ∀ z ∈ Z, ∃ c : Kˣ,
      τ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hSinger : ∀ C : Subgroup (GL (Fin 3) K), C ≤ τ.range →
      (∀ g ∈ τ.range, ∀ x ∈ C, g * x * g⁻¹ ∈ C) →
      IsIrreducibleMatrixRep C.subtype → IsCyclic C → False) :
    ∃ Hmat : Subgroup (GL (Fin 3) K),
      Hmat ≤ τ.range ∧
      (∀ a : A, Hmat.map
        (coordinateSemilinearGLAct 3 K (ρ a)).toMonoidHom = Hmat) ∧
      Z.map τ ≤ Hmat ∧
      CFSG.Quasithin.IsPOnePlusTwo 3 ↥Hmat := by
  classical
  obtain ⟨hoddMat, hrankMat, hncJ, hZmatJ, hZscalarMat, hZcubeMat⟩ :=
    semilinear_rank_three_kernel_transports ρ τ hτinj hJodd hirr hrank Z hZcard hZscalar
  let α : A →* MulAut (GL (Fin 3) K) := (coordinateSemilinearGLAct 3 K).comp ρ
  have hAJ : ∀ a : A, τ.range.map (α a).toMonoidHom = τ.range := by
    intro a
    simpa [α] using tau_range_map_coordinateSemilinearGLAct_eq 3 K ρ τ hτ a
  have hshape : ∀ (H : Subgroup (GL (Fin 3) K)),
      CFSG.IsExtraspecialPGroup 3 H → Nat.card H = 3 ^ 3 → (∀ x ∈ H, x ^ 3 = 1) →
      CFSG.Quasithin.IsPOnePlusTwo 3 ↥H := by
    intro H hHex hHcard hHcube
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine ⟨hHex.isExtraspecial, ?_, ?_⟩
    · simpa using hHcard
    · intro x
      exact Subtype.ext (by simpa using hHcube (x : GL (Fin 3) K) x.2)
  rcases irreducible_prime_degree_reduction (K := K) (n := 3) Nat.prime_three hirr with
    hS | hmono | hstrong
  ·
    obtain ⟨C, hC_le, hC_norm, hC_irr, hC_cyc, -⟩ := hS
    exact (hSinger C hC_le hC_norm hC_irr hC_cyc).elim
  ·
    rcases card_eq_twenty_seven_or_eighty_one_of_odd_monomial_irreducible_rank
        hK hmono hoddMat hirr hrankMat with hcard27 | hcard81
    ·
      have hcardJ : Nat.card (SemidirectProduct.rightHom.comp ρ).ker = 27 := by
        have hcard := (Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv).symm
        rw [← hcard]
        exact hcard27
      obtain ⟨N, hN, hNindex⟩ :=
        CFSG.LinearAlgebra.exists_normal_index_three_of_semilinear_card_twenty_seven_index_two
          (A := A) (K := K) hK ρ τ hτ hτinj hJindex hcardJ hncJ Z hZcard hZscalar
      exact (hno N hN hNindex).elim
    ·
      let Hmat : Subgroup (GL (Fin 3) K) :=
        τ.range ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker
      have hstruct :=
        det_kernel_structure_of_transitive_monomial_card_eighty_one hK hmono hcard81
      dsimp only at hstruct
      obtain ⟨hHcard, hHcube, -, hHex, hHscalarMem⟩ := hstruct
      refine ⟨Hmat, inf_le_left, ?_, ?_, hshape Hmat hHex hHcard hHcube⟩
      · intro a
        let ρS : A →* SemiGL (Fin 3) K :=
          (coordinateSemilinearEquivSemiGL 3 K).toMonoidHom.comp ρ
        have hJ : ∀ b : A,
            τ.range.map (semilinGLAct 3 K (ρS b)).toMonoidHom = τ.range := by
          intro b
          simpa [α, ρS, coordinateSemilinearGLAct] using hAJ b
        have hmain := map_inf_det_ker_semilinGLAct_of_normalizes (n := 3) (K := K)
          ρS τ.range hJ a
        simpa [Hmat, ρS, coordinateSemilinearGLAct] using hmain
      · intro M hM
        rw [Subgroup.mem_map] at hM
        obtain ⟨z, hz, rfl⟩ := hM
        obtain ⟨c, hc⟩ := hZscalar z hz
        rw [hc]
        exact hHscalarMem c
  ·
    let A' : Subgroup (MulAut (GL (Fin 3) K)) := α.range
    let α' : A' →* MulAut (GL (Fin 3) K) := A'.subtype
    have hAJ' : ∀ g : A', τ.range.map (α' g).toMonoidHom = τ.range := by
      intro g
      obtain ⟨a, ha⟩ := g.2
      simpa [α', ← ha] using hAJ a
    obtain ⟨-, Hmat, hHJ, hZH, -, hHinv', -, hHcard, hHex, hHcube, -⟩ :=
      exists_extraspecial_gl3_of_odd_of_normalized (K := K) (A := A') α' hirr hoddMat
        hstrong.2.1 hstrong.2.2 hAJ' hZmatJ hZscalarMat hZcubeMat
    have hHinv : ∀ a : A, Hmat.map (α a).toMonoidHom = Hmat := by
      intro a
      have h := hHinv' ⟨α a, ⟨a, rfl⟩⟩
      simpa [α'] using h
    exact ⟨Hmat, hHJ, hHinv, hZH, hshape Hmat hHex hHcard hHcube⟩

theorem exists_invariant_isPOnePlusTwo_of_semilinear_rank_three
    (hK : Nat.card K = 4)
    (ρ : A →* coordinateSemilinearGroup 3 K)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →* GL (Fin 3) K)
    (hτinj : Function.Injective τ)
    (hτ : ∀ j : (SemidirectProduct.rightHom.comp ρ).ker,
      ρ (j : A) = SemidirectProduct.inl (τ j))
    (hJodd : Odd (Nat.card (SemidirectProduct.rightHom.comp ρ).ker))
    (hJindex : (SemidirectProduct.rightHom.comp ρ).ker.index = 2)
    (hirr : IsIrreducibleMatrixRep τ.range.subtype)
    (hrank : 2 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (SemidirectProduct.rightHom.comp ρ).ker))
    (hno : ∀ N : Subgroup A, N.Normal → N.index ≠ 3)
    (Z : Subgroup (SemidirectProduct.rightHom.comp ρ).ker)
    (hZcard : Nat.card Z = 3)
    (hZscalar : ∀ z ∈ Z, ∃ c : Kˣ,
      τ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ Hmat : Subgroup (GL (Fin 3) K),
      Hmat ≤ τ.range ∧
      (∀ a : A, Hmat.map
        (coordinateSemilinearGLAct 3 K (ρ a)).toMonoidHom = Hmat) ∧
      Z.map τ ≤ Hmat ∧
      CFSG.Quasithin.IsPOnePlusTwo 3 ↥Hmat := by
  exact exists_invariant_isPOnePlusTwo_of_reduction hK ρ τ hτinj hτ hJodd hJindex hirr hrank hno
    Z hZcard hZscalar
    (fun C hC_le hC_norm hC_irr hC_cyc =>
      no_cyclic_irreducible_normal_of_semilinear_rank hK ρ τ hτ hτinj hJindex hirr hrank
        Z hZcard hZscalar hno C hC_le hC_cyc hC_irr hC_norm)

end CFSG.LinearAlgebra
