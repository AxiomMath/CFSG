module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3Normal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3Coord
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.UnitaryOrder
public import CFSG.RankThree.PartOne.KE.E8FiveData

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_smul charVal_single)
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (weylMatrix e6Index dualMatrix)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (unitarySet)
open scoped Pointwise commutatorElement Matrix MatrixGroups

theorem e6_four_exists_nonregular_at (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} (hp : p.Prime)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (g0 : ModGL .E6 L)
    (A₀ : Subgroup (adjointGroup .E6 K)) (hA₀ : Nat.card A₀ = p ^ 2)
    (hA₀exp : ∀ q ∈ A₀, q ^ p = 1) (c : adjointGroup .E6 K)
    (hc : ∀ q ∈ A₀, g0⁻¹ * adjEmb .E6 K L (c * q * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) (i : Fin Tag.E6.rank) :
    ∃ q ∈ A₀, q ≠ 1 ∧ ∃ b : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * q * c⁻¹) * g0 ∧
        (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hA₀fin : Finite A₀ := Finite.of_injective _ A₀.subtype_injective
  let φ : A₀ →* ModGL .E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E6 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q = g0⁻¹ * adjEmb .E6 K L (c * (q : adjointGroup .E6 K) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
    fun q => by
      rw [hφ]
      exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E6.rank → Lˣ, φ q = rootDiagUnit .E6 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => β q i
      map_one' := by rw [hβone]; rfl
      map_mul' := fun q q' => by rw [hβmul]; rfl }
  obtain ⟨q, hq1, hqi⟩ := exists_ne_one_ker_of_card_sq hp hA₀ χ fun q => by
    have h1 : rootDiagUnit .E6 (β q) ^ p = 1 := by
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

theorem e6_four_actor (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u)
    (g0 : ModGL .E6 L) (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L))
    {x : adjointGroup .E6 K} (hx : orderOf x = p) (c : adjointGroup .E6 K)
    (hh : g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E6.rank → Lˣ}
    (hb : rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0)
    (hne : (rootCharKernel b).Nonempty)
    :
    CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K)) ∧
    ¬ Nat.Coprime p (Nat.card (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K))) ∧
    ∀ (η : MulAut (adjointGroup .E6 K)) (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ)
      (σ : K ≃+* K) (ε : Fin (exactE .E6)), η x = x →
      (∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K)),
          η d = d) →
      (∀ y : adjointGroup .E6 K, (η y : ModGL .E6 K) = (g : ModGL .E6 K) *
        rootDiagUnit .E6 a * exactQ .E6 K ε * Units.map (entrywiseHom σ.toRingHom)
          (y : ModGL .E6 K) * (exactQ .E6 K ε)⁻¹ * (rootDiagUnit .E6 a)⁻¹ *
            (g : ModGL .E6 K)⁻¹) →
      σ = 1 ∧ (ε : ℕ) = 0 ∧ ∃ a' : Fin Tag.E6.rank → Lˣ,
        rootDiagUnit .E6 a' = g0⁻¹ * adjEmb .E6 K L c *
          baseChangeGL (algebraMap K L) ((g : ModGL .E6 K) * rootDiagUnit .E6 a) *
            (adjEmb .E6 K L c)⁻¹ * g0 ∧ ∀ α ∈ rootCharKernel b, rootChar a' α = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpd : p ∣ Nat.card K ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact hΦ
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_four_perx K hf hK hp hp3 hord hΦ L n hnm hnW g0 hg0C hg0 hperf
    hT hx c hh
  obtain ⟨-, hψne⟩ := hψb b hb
  obtain ⟨Pt, hPq, hcomm, ⟨h₀, hh₀⟩, v, hSeq, H, hH⟩ := hψne hne
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  refine ⟨hq, ?_, ?_⟩
  ·
    set T' : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) :=
      ⁅(⊤ : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)))), ⊤⁆ with hT'
    have hcPt : Nat.card Pt = Nat.card T' := by
      rw [← h2]
      exact Subgroup.card_map_of_injective hψinj
    have hcD : Nat.card (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K)) =
          Nat.card T' := by
      rw [← h1]
      exact Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set _)).subtype_injective
    have : Finite Pt := by
      rw [← h2]
      exact Finite.of_equiv T' (Subgroup.equivMapOfInjective T' ψ hψinj).toEquiv
    have hdvd : p ∣ Nat.card Pt :=
      e6Four_p_dvd_card_of_unitary_family hf hK hpd (rhoSigmaE6A3 L v) (rhoSigmaE6A3_injective v) Pt H hH
    rw [hcD, ← hcPt]
    exact fun hc => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc dvd_rfl hdvd)
  · intro η g a σ ε hηx hηd hexpr
    obtain ⟨hσ, hε⟩ := e6_four_normal_of_fixes K hf hK hp hp3 hord hΦ L n hnm hnW g0 hg0C hg0 hperf
      hT hx c hh hb hne hηx hηd g a σ ε hexpr
    refine ⟨hσ, hε, ?_⟩
    have hid : ∀ y : ModGL .E6 K, Units.map (entrywiseHom σ.toRingHom) y = y := fun y => by
      subst hσ
      exact Units.ext (entrywise_id _)
    have hQ0 : exactQ .E6 K ε = 1 := by
      rw [hε]
      exact exactQ_zero .E6 K
    have hη' : ∀ y : adjointGroup .E6 K, (η y : ModGL .E6 K) =
        ((g : ModGL .E6 K) * rootDiagUnit .E6 a) * (y : ModGL .E6 K) *
          ((g : ModGL .E6 K) * rootDiagUnit .E6 a)⁻¹ := by
      intro y
      rw [hexpr y, hid, hQ0]
      group
    refine e6_four_coordinates K hf hK hp hp3 hord hΦ L n hnm hnW g0 hg0C hg0 hperf hT hx c hh hb
      hne ((g : ModGL .E6 K) * rootDiagUnit .E6 a) ?_ ?_ ?_
    · rw [map_mul]
      refine mul_mem (adjEmb_mem g) ?_
      rw [baseChangeGL_rootDiagUnit]
      exact torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _)
    · rw [← hη' x, hηx]
    · intro d hd
      rw [← hη' d, hηd d hd]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
