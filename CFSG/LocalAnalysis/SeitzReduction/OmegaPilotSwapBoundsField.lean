module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.Open (ordD ordTwistedD)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry (derivedOrthogonal_map_isometry)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
  (conj_injective_matrixProjectiveDerived)

theorem card_derivedOrthogonal_of_regular {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {g n : ℕ} (hg : 1 ≤ g) (hk : Nat.card k = 2 ^ g)
    (hn : 4 ≤ n) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : finrank k W = 2 * n) :
    Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ = ordD n (2 ^ g) ∨
      Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ = ordTwistedD n (2 ^ g) := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have key : ∀ (Qc : QuadraticForm k (Fin (2 * n) → k)), Q₀.IsometryEquiv Qc →
      Qc.polarBilin.Nondegenerate →
      (∃ T : Submodule k (Fin (2 * n) → k), finrank k T = 3 ∧ ∀ x ∈ T, Qc x = 0) →
      ⁅TauCeti.QuadraticMap.orthogonalGroup Qc, TauCeti.QuadraticMap.orthogonalGroup Qc⁆ =
        elementaryGroup Qc →
      Nonempty (↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ ≃* matrixProjectiveDerived Qc) := by
    intro Qc ψ hQc hTc hEc
    have hZ := (evenOrthogonalRealization_of_regular hg hk (by omega) Qc hQc hTc hEc).1
    have e1 := (Subgroup.equivMapOfInjective _
      (LinearEquiv.autCongr ψ.toLinearEquiv).toMonoidHom
      (LinearEquiv.autCongr ψ.toLinearEquiv).injective).trans
        (MulEquiv.subgroupCongr
          (derivedOrthogonal_map_isometry ψ))
    have e2 := ((matrixDerived Qc).equivMapOfInjective matrixLinearIso.toMonoidHom
      matrixLinearIso.injective).trans
        (MulEquiv.subgroupCongr
          (CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.matrixDerived_map Qc))
    exact ⟨e1.trans (e2.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)⟩
  rcases (finite_even_regular_quadratic_normal_forms Q₀ hQ₀).2.2.1 n (by omega) hdim with
    ⟨b, hb⟩ | ⟨β, γ, -, hroot, b, hb⟩
  · have hreg := regular_coordinateQuadPlus n k (by omega)
    obtain ⟨e⟩ := key _ ((plusBasisIsometry b hb).trans (coordinatePlusIsometry n k)) hreg.1
      hreg.2 (commutator_coordinateQuadPlus n k (by omega))
    exact Or.inl ((Nat.card_congr e.toEquiv).trans (card_coordinatePlus hg hk hn))
  · have hreg := regular_coordinateQuadMinus n k β γ hn hroot
    obtain ⟨e⟩ := key _ ((minusBasisIsometry b hb).trans
      (coordinateMinusIsometry n k (by omega) β γ)) hreg.1 hreg.2
      (commutator_coordinateQuadMinus n k β γ hn hroot)
    exact Or.inr ((Nat.card_congr e.toEquiv).trans (card_coordinateMinus hg hk hn _ hroot))

theorem commutator_eq_self_of_isSimpleGroup {X : Type*} [Group X] {N : Subgroup X}
    (hN : IsSimpleGroup N) (h4 : 4 ∣ Nat.card N) : ⁅N, N⁆ = N := by
  have h := F4Pilot.commutator_eq_top_of_isSimpleGroup_of_four_dvd hN h4
  rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem card_dvd_card_perfectCore_fixedSubgroup {P : Type*} [Group P] [Finite P]
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) (α : MulAut P)
    {N : Subgroup (MulAut P)}
    (hN : N ≤ inner P ⊓ Subgroup.centralizer {α})
    (hNs : IsSimpleGroup N) (h4 : 4 ∣ Nat.card N) :
    Nat.card N ∣ Nat.card (perfectCore (fixedSubgroup α)) := by
  set E := CFSG.ComponentClassification.CatLeafProof.fixedInnerEquiv hcj α with hE
  set Y := inner P ⊓ Subgroup.centralizer {α} with hY
  set M : Subgroup (fixedSubgroup α) := (N.subgroupOf Y).comap E.toMonoidHom with hM
  have hmap : M.map E.toMonoidHom = N.subgroupOf Y :=
    Subgroup.map_comap_eq_self_of_surjective E.surjective _
  have eM : M ≃* N := (M.equivMapOfInjective E.toMonoidHom E.injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (Subgroup.subgroupOfEquivOfLe hN))
  set M' : Subgroup P := M.map (fixedSubgroup α).subtype with hM'
  have eM' : M' ≃* N := (M.equivMapOfInjective _ (fixedSubgroup α).subtype_injective).symm.trans
    eM
  have : IsSimpleGroup N := hNs
  have hsM : IsSimpleGroup M' := eM'.isSimpleGroup
  have h4' : 4 ∣ Nat.card M' := by rw [Nat.card_congr eM'.toEquiv]; exact h4
  have hperf := commutator_eq_self_of_isSimpleGroup hsM h4'
  have hle : M' ≤ fixedSubgroup α := by
    rw [hM']
    exact Subgroup.map_subtype_le M
  have h1 := le_perfectCore_of_perfect hle hperf
  rw [← Nat.card_congr eM'.toEquiv]
  exact Subgroup.card_dvd_of_le h1

theorem four_dvd_of_eq_ord {g n A : ℕ} (hg : 1 ≤ g) (hn : 2 ≤ n) (hA0 : A ≠ 0)
    (hA : A = ordD n (2 ^ g) ∨ A = ordTwistedD n (2 ^ g)) : 4 ∣ A := by
  have hv : 2 ≤ A.factorization 2 := by
    have hnn : 2 ≤ n * (n - 1) := by
      have : 1 ≤ n - 1 := by omega
      nlinarith
    rcases hA with rfl | rfl
    · rw [factorization_two_ordD hg (by omega)]
      nlinarith
    · rw [factorization_two_ordTwistedD hg (by omega)]
      nlinarith
  have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hA0).2 hv
  simpa using h

theorem exists_dvd_card_perfectCore_fixedSubgroup_of_field {K : Type} [Field K] [Finite K]
    {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) :
    ∃ g : ℕ, f = 2 * g ∧ (ordD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup α)) ∨
      ordTwistedD n (2 ^ g) ∣ Nat.card (perfectCore (fixedSubgroup α))) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  have hd : 1 ≤ 2 * n := by omega
  obtain ⟨hfeven, hk, hsimple, -, ext, -, -, hinj, hinn, hNC, -, -⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α hα hα2 S hS hSα hσ1
  have hcj := conj_injective_matrixProjectiveDerived hQ hT hE
  set N := (extKappa Q ext).range with hNdef
  have eJ : ↥(pairDescentDerived hS) ≃* N := MonoidHom.ofInjective hinj
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ := evenOrthogonalRealization_of_regular hf hK hd Q hQ hT hE
  obtain ⟨hSS, hTT, -⟩ := hinv α hα hα2 S hS hSα
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs Q => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent
    hσσ hσ1 hQ (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  have hcardJ := card_derivedOrthogonal_of_regular hk2 hk hn (pairDescentForm hS) hQ₀ hdim
  have hNle : N ≤ inner
      (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {α} := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hinn hx, (Subgroup.mem_inf.mp (hNC hx)).2⟩
  have : IsSimpleGroup ↥(pairDescentDerived hS) := hsimple
  have hNs : IsSimpleGroup N := eJ.symm.isSimpleGroup
  have hJN : Nat.card ↥(pairDescentDerived hS) = Nat.card N := Nat.card_congr eJ.toEquiv
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have h4 : 4 ∣ Nat.card N := by
    rw [← hJN]
    exact four_dvd_of_eq_ord hk2 (by omega) (by rw [hJN]; exact hN0) hcardJ
  have hdvd := card_dvd_card_perfectCore_fixedSubgroup hcj α hNle hNs h4
  rw [← hJN] at hdvd
  refine ⟨f / 2, by obtain ⟨m, hm⟩ := hfeven; omega, ?_⟩
  rcases hcardJ with h | h
  · exact Or.inl (h ▸ hdvd)
  · exact Or.inr (h ▸ hdvd)

end CFSG.SeitzReduction.OmegaPilot
