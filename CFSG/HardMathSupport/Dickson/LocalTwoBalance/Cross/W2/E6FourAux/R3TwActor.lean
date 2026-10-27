module

public import CFSG.RankThree.PartOne.KE.E6TwFourData
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.SlOrder
public import CFSG.RankThree.PartOne.KE.E8FiveData

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_smul charVal_single)
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (weylMatrix e6Index dualMatrix e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise commutatorElement Matrix MatrixGroups

theorem e6_tw_four_exists_nonregular_at {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (g0 : ModGL Tag.E6 L)
    (A₀ : Subgroup (twistedE6RootGroup K σ)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : twistedE6RootGroup K σ)
    (hc : ∀ q ∈ A₀, g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f))) (i : Fin Tag.E6.rank) :
    ∃ q ∈ A₀, q ≠ 1 ∧ ∃ b : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit Tag.E6 b = g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∧
        (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hA₀fin : Finite A₀ := Finite.of_injective _ A₀.subtype_injective
  let φ : A₀ →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((twE6Emb K σ L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * twE6Emb K σ L (c * (q : twistedE6RootGroup K σ) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) :=
    fun q => by
      rw [hφ]
      exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E6.rank → Lˣ, φ q = rootDiagUnit Tag.E6 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => β q i
      map_one' := by rw [hβone]; rfl
      map_mul' := fun q q' => by rw [hβmul]; rfl }
  obtain ⟨q, hq1, hqi⟩ := exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => by
    have h1 : rootDiagUnit Tag.E6 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  refine ⟨q, q.2, fun h => hq1 (Subtype.ext h), β q, by rw [← hβ, hφ], ?_⟩
  refine ⟨IsRoot.basis i, ?_⟩
  rw [CTTorus.rootChar_single]
  exact hqi

theorem e6_tw_four_derived {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((ℓ ^ f : ℕ) : ZMod p) = 4) (hΦ : ((ℓ ^ f : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x)
    (g0 : ModGL Tag.E6 L) (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    (hT : twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) =
      (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom Tag.E6 L))
    {x : twistedE6RootGroup K σ} (hx : orderOf x = p) (c : twistedE6RootGroup K σ)
    (hh : g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)))
    {b : Fin Tag.E6.rank → Lˣ}
    (hb : rootDiagUnit Tag.E6 b = g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0)
    (hne : (rootCharKernel b).Nonempty)
    :
    CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
      Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
        Subgroup (twistedE6RootGroup K σ)) ∧
    ¬ Nat.Coprime p (Nat.card (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
      Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
        Subgroup (twistedE6RootGroup K σ))) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hpd : p ∣ (ℓ ^ f) ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact_mod_cast hΦ
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_tw_four_perx K hf hK σ hσ hp hp3 hord hΦ L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  obtain ⟨-, hψne⟩ := hψb b hb
  obtain ⟨Pt, hPq, hcomm, ⟨h₀, hh₀⟩, v, hSeq, H, hH⟩ := hψne hne
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  refine ⟨hq, ?_⟩
  set T' : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) :=
    ⁅(⊤ : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)))), ⊤⁆ with hT'
  have hcPt : Nat.card Pt = Nat.card T' := by
    rw [← h2]
    exact Subgroup.card_map_of_injective hψinj
  have hcD : Nat.card (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
      Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
        Subgroup (twistedE6RootGroup K σ)) = Nat.card T' := by
    rw [← h1]
    exact Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set _)).subtype_injective
  have : Finite Pt := by
    rw [← h2]
    exact Finite.of_equiv T' (Subgroup.equivMapOfInjective T' ψ hψinj).toEquiv
  have hkcard : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  have hpd' : p ∣ Nat.card (fixSubfield σ) ^ 2 + 1 := by rw [hkcard]; exact hpd
  have hdvd : p ∣ Nat.card Pt :=
    e6Four_p_dvd_card_of_sl4_family ((algebraMap K L).comp (fixSubfield σ).subtype) hpd'
      (rhoSigmaE6A3 L v) (rhoSigmaE6A3_injective v) Pt H hH
  rw [hcD, ← hcPt]
  exact fun hc => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc dvd_rfl hdvd)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
