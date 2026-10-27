module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerUnitary
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitary
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

section Generic

theorem OddPCoreInClosure.of_inf_normal {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (U N : Subgroup G) [N.Normal] (h : OddPCoreInClosure p ↥U) : OddPCoreInClosure p ↥(U ⊓ N) := by
  have heq : (U ⊓ N).subgroupOf U = N.subgroupOf U := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  haveI hN : ((U ⊓ N).subgroupOf U).Normal := by
    rw [heq]
    exact Subgroup.Normal.subgroupOf inferInstance U
  exact OddPCoreInClosure.of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left)
    (OddPCoreInClosure.of_normal hp ((U ⊓ N).subgroupOf U) h)

theorem subgroupOf_inf_centralizer_singleton {G : Type*} [Group G] (S : Subgroup G) (y : ↥S) :
    (S ⊓ Subgroup.centralizer ({(y : G)} : Set G)).subgroupOf S =
      Subgroup.centralizer ({y} : Set ↥S) := by
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hg⟩
    exact Subtype.ext hg
  · intro hg
    exact ⟨g.2, congrArg Subtype.val hg⟩

noncomputable def centralizerSubtypeEquiv {G : Type*} [Group G] (S : Subgroup G) (y : ↥S) :
    ↥(Subgroup.centralizer ({y} : Set ↥S)) ≃*
      ↥(S ⊓ Subgroup.centralizer ({(y : G)} : Set G)) :=
  (MulEquiv.subgroupCongr (subgroupOf_inf_centralizer_singleton S y).symm).trans
    (Subgroup.subgroupOfEquivOfLe inf_le_left)

end Generic

section Special

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem oddPCoreInClosure_centralizer_sesqSpecial_of_squarefree {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hℓ : ℓ = 2) (hK : UnitaryFieldData ℓ f K) {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (y : ↥(sesqSpecialUnitaryGroup B))
    (hsq : Squarefree (minpoly K ((y : LinearMap.GeneralLinearGroup K V) : Module.End K V))) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({y} : Set ↥(sesqSpecialUnitaryGroup B))) := by
  haveI : Finite K := hK.finite
  haveI : Finite (LinearMap.GeneralLinearGroup K V) := finite_generalLinearGroup'
  have hx : (y : LinearMap.GeneralLinearGroup K V) ∈ sesqUnitaryGroup B :=
    sesqSpecialUnitaryGroup_le B y.2
  have hU := oddPCoreInClosure_unitaryCentralizer_of_squarefree hp hp2 hℓ hK B hB hBl hx hsq
  have hUN := OddPCoreInClosure.of_inf_normal hp
    (unitaryCentralizer B (y : LinearMap.GeneralLinearGroup K V))
    (Units.map (LinearMap.det : Module.End K V →* K)).ker hU
  have heq : sesqSpecialUnitaryGroup B ⊓
      Subgroup.centralizer ({(y : LinearMap.GeneralLinearGroup K V)} :
        Set (LinearMap.GeneralLinearGroup K V)) =
      unitaryCentralizer B (y : LinearMap.GeneralLinearGroup K V) ⊓
        (Units.map (LinearMap.det : Module.End K V →* K)).ker := by
    ext g
    simp only [sesqSpecialUnitaryGroup, unitaryCentralizer, gl_centralizer, Subgroup.mem_inf]
    tauto
  exact OddPCoreInClosure.of_mulEquiv
    ((centralizerSubtypeEquiv (sesqSpecialUnitaryGroup B) y).trans
      (MulEquiv.subgroupCongr heq)).symm hUN

theorem oddPCoreInClosure_centralizer_sesqSpecial {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ = 2) (hK : UnitaryFieldData ℓ f K) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (y : ↥(sesqSpecialUnitaryGroup B)) (hyp : y ^ p = 1) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({y} : Set ↥(sesqSpecialUnitaryGroup B))) := by
  haveI : Finite K := hK.finite
  haveI : CharP K 2 := hℓ ▸ hK.charP
  have hxp : (y : LinearMap.GeneralLinearGroup K V) ^ p = 1 := by
    simpa using congrArg Subtype.val hyp
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  have hsq : Squarefree (minpoly K ((y : LinearMap.GeneralLinearGroup K V) : Module.End K V)) := by
    refine CFSG.RankThree.PartOne.KCPrimary.squarefree_minpoly_of_aeval_eq_zero
      (p := Polynomial.X ^ p - Polynomial.C 1)
      (Polynomial.separable_X_pow_sub_C (1 : K) hpK one_ne_zero).squarefree ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one,
      ← Units.val_pow_eq_pow_val, hxp, Units.val_one, sub_self]
  exact oddPCoreInClosure_centralizer_sesqSpecial_of_squarefree hp hp2 hℓ hK B hB hBl y hsq

end Special

section Model

variable {ℓ f : ℕ} {K : Type} [Field K]

noncomputable def unitarySUEquivSesq (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    ↥(unitarySU ℓ f K n) ≃* ↥(sesqSpecialUnitaryGroup (idForm h n)) :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)).subgroupMap (unitarySU ℓ f K n)).trans
    (MulEquiv.subgroupCongr (by
      ext g'
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' : g ∈ gramSU h (idGram K n) := by
          have := (unitarySU_eq_gramSU h n) ▸ hg
          exact this
        exact (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) g).2 hg'
      · intro hg'
        refine ⟨Matrix.GeneralLinearGroup.toLin.symm g', ?_, MulEquiv.apply_symm_apply _ _⟩
        have h1 : Matrix.GeneralLinearGroup.toLin.symm g' ∈ gramSU h (idGram K n) := by
          rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n), MulEquiv.apply_symm_apply]
          exact hg'
        rw [unitarySU_eq_gramSU h n]
        exact h1))

theorem oddPCoreInClosure_centralizer_unitarySU_of_squarefree {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hℓ : ℓ = 2) (h : UnitaryFieldData ℓ f K) (n : ℕ)
    (x : ↥(unitarySU ℓ f K n))
    (hsq : Squarefree (minpoly K ((Matrix.GeneralLinearGroup.toLin (x : GL (Fin n) K) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set ↥(unitarySU ℓ f K n))) := by
  have h1 := oddPCoreInClosure_centralizer_sesqSpecial_of_squarefree hp hp2 hℓ h (idForm h n)
    (idForm_isSymm h n) (idForm_separatingLeft h n) (unitarySUEquivSesq h n x) hsq
  exact OddPCoreInClosure.of_mulEquiv (centralizerSingletonEquiv (unitarySUEquivSesq h n) x).symm h1

theorem oddPCoreInClosure_centralizer_unitarySU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ = 2)
    (h : UnitaryFieldData ℓ f K) (n : ℕ) (x : ↥(unitarySU ℓ f K n)) (hxp : x ^ p = 1) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set ↥(unitarySU ℓ f K n))) := by
  have h1 := oddPCoreInClosure_centralizer_sesqSpecial hp hp2 hℓ h (idForm h n)
    (idForm_isSymm h n) (idForm_separatingLeft h n) (unitarySUEquivSesq h n x)
    (by rw [← map_pow, hxp, map_one])
  exact OddPCoreInClosure.of_mulEquiv (centralizerSingletonEquiv (unitarySUEquivSesq h n) x).symm h1

theorem pClosureOdd_unitaryPSU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ = 2)
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 1 ≤ n) (hZ : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) :
    PClosureOdd p (unitaryPSU h n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  have hZ' : ∀ z ∈ unitaryScalars h n, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    by_contra hz1
    have hord : orderOf z = p := orderOf_eq_prime hzp hz1
    have hdvd := Subgroup.orderOf_dvd_natCard (unitaryScalars h n) hz
    rw [hord, card_unitaryScalars h hn] at hdvd
    exact hZ hdvd
  exact pClosureOdd_quotient_of_central hp (unitaryScalars h n) (unitaryScalars_le_center h n) hZ'
    fun x hx => oddPCoreInClosure_centralizer_unitarySU hp hp2 hℓ h n x hx

end Model

section Family

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

theorem chevTwoPClosureOddFamily_unitary : ChevTwoPClosureOddFamily LieFamilyUnitary := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | twistedA r q =>
    obtain ⟨e⟩ := he
    have hF' : ¬ p ∣ Nat.gcd (r + 1) (q.card + 1) := hF
    have hdi' : q.p = 2 := hdi
    obtain ⟨-, K, _, _, hcard, ⟨e1⟩⟩ := statedClassicalModel_of_twistedA r q hv e
    have hU : UnitaryFieldData q.p q.exponent K :=
      ⟨q.prime_p, q.exponent_pos, by rw [hcard, ← pow_mul, mul_comm]⟩
    have hn : 1 ≤ r + 1 := by omega
    have hcq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    have hPSU := pClosureOdd_unitaryPSU hp hp2 hdi' hU hn (by rw [← hcq]; exact hF')
    exact PClosureOdd.of_mulEquiv ((unitaryPSUEquiv hU hn).trans e1.symm) hPSU
  | _ => exact absurd hF (by simp [LieFamilyUnitary])

end Family

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
