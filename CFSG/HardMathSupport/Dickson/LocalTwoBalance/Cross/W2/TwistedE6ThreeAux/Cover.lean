module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.SteinbergCDCyclicNormalHall
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartOne.KE.E6TwThreeLayer
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω}

private theorem exists_ne_one_mem_phi3Line [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0) (k : Fin 8) :
    ∃ y ∈ phi3TorusTorsion Ω Fr p, y ≠ 1 ∧ ∃ ab : ZMod p × ZMod p, ab ≠ 0 ∧
      eisensteinLineForm (-(q : ZMod p)) ab.1 ab.2 k = 0 ∧
      torusRootKernel y =
        CFSG.RankThree.E6.rootKernel (eisensteinColumn (-(q : ZMod p)) ab.1 ab.2) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨hle, hcard, hspec, -⟩ := phi3Line_spec (Fr := Fr) hp3 hFr hζ hr k
  rcases Subgroup.bot_or_exists_ne_one (phi3Line ζ hζ.pow_eq_one (-(q : ZMod p)) k) with
    h | ⟨y, hy, hy1⟩
  · rw [h, Subgroup.card_bot] at hcard
    exact absurd hcard (Fact.out : p.Prime).one_lt.ne
  · exact ⟨y, hle hy, hy1, hspec y hy hy1⟩

private theorem phi3_cover_setup (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) :
    IsAlgClosed Ω ∧ (∃ ζ : Ωˣ, IsPrimitiveRoot ζ p) ∧
      (-((ℓ ^ f : ℕ) : ZMod p)) ^ 2 - -((ℓ ^ f : ℕ) : ZMod p) + 1 = 0 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨-, hζ, hr⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  exact ⟨inferInstance, hζ, hr⟩

theorem exists_mem_torsion_kernel (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ y ∈ phi3TorusTorsion Ω Fr p, y ≠ 1 ∧ α ∈ torusRootKernel y := by
  obtain ⟨hΩ, ⟨ζ, hζ⟩, hr⟩ := phi3_cover_setup (K := K) (Ω := Ω) hℓ hf hK hp hpq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, h⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, -, hroot, -, -⟩ := h p hp3 _ hr
  obtain ⟨k, hk, -⟩ := hroot α hα
  obtain ⟨y, hy, hy1, ab, hab, hline, hker⟩ := exists_ne_one_mem_phi3Line hp3 hFr hζ hr k
  refine ⟨y, hy, hy1, ?_⟩
  rw [hker]
  exact hk ab.1 ab.2 hab hline

theorem exists_A2_in_torsion (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) :
    ∃ y ∈ phi3TorusTorsion Ω Fr p, y ≠ 1 ∧
      ∃ w : WeylGroup Tag.E6, (w • ·) '' torusRootKernel y = parabolicRoots Tag.E6 support13 := by
  obtain ⟨hΩ, ⟨ζ, hζ⟩, hr⟩ := phi3_cover_setup (K := K) (Ω := Ω) hℓ hf hK hp hpq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, h⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, -, -, -, hA2⟩ := h p hp3 _ hr
  obtain ⟨w, hw, -⟩ := hA2 4 (by decide)
  obtain ⟨y, hy, hy1, ab, hab, hline, hker⟩ := exists_ne_one_mem_phi3Line hp3 hFr hζ hr 4
  refine ⟨y, hy, hy1, w, ?_⟩
  rw [hker]
  exact (hw ab.1 ab.2 hab hline).1

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
