module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.RankTwoExceptional (odd_card_commutator_outer_of_quot
  odd_card_commutator_outer_of_equiv odd_card_commutator_of_comm)
open scoped commutatorElement

section Criteria

theorem odd_card_commutator_outer_of_tower {X : Type*} [Group X] [Finite (MulAut X)]
    {D : Subgroup (MulAut X)} (hcomm : ∀ a b : MulAut X, ⁅a, b⁆ ∈ D)
    (h2 : ∀ δ ∈ D, δ ^ 2 ∈ OuterAutomorphisms.inner X → δ ∈ OuterAutomorphisms.inner X) :
    Odd (Nat.card (commutator (Outer X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : commutator (Outer X) ≤ D.map (QuotientGroup.mk' (OuterAutomorphisms.inner X)) := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective
      (QuotientGroup.mk' (OuterAutomorphisms.inner X)) (QuotientGroup.mk'_surjective _),
      ← Subgroup.map_commutator]
    refine Subgroup.map_mono ?_
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a b
  refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le hle)
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hne)
  obtain ⟨δ, hδD, hδx⟩ := Subgroup.mem_map.1 x.2
  have hx2 : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hδ2 : δ ^ 2 ∈ OuterAutomorphisms.inner X := by
    rw [← QuotientGroup.ker_mk' (OuterAutomorphisms.inner X), MonoidHom.mem_ker, map_pow, hδx]
    exact congrArg Subtype.val hx2
  have hx1 : x = 1 := Subtype.ext (by
    rw [← hδx, OneMemClass.coe_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h2 δ hδD hδ2)
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem isPGroup_zpowers_of_pow_two {G : Type*} [Group G] {x : G} {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : IsPGroup 2 (zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy
  refine ⟨k, Subtype.ext ?_⟩
  change (x ^ i) ^ 2 ^ k = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem odd_card_commutator_of_burnside {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hidx : ¬ 2 ∣ E.index) {s : G} (hsE : s ∈ E)
    {k : ℕ} (hs2 : s ^ 2 ^ k = 1) (hs : ∀ g : G, g * s * g⁻¹ ∈ E → g ∈ E) :
    Odd (Nat.card (commutator G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2' : (⟨s, hsE⟩ : E) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hs2)
  obtain ⟨P₀, hP₀⟩ := (isPGroup_zpowers_of_pow_two hs2').exists_le_sylow
  have hPE : (P₀ : Subgroup E).map E.subtype ≤ E := Subgroup.map_subtype_le _
  have hsP : s ∈ (P₀ : Subgroup E).map E.subtype := ⟨⟨s, hsE⟩, hP₀ (mem_zpowers _), rfl⟩
  have hPp : IsPGroup 2 ((P₀ : Subgroup E).map E.subtype) := P₀.isPGroup'.map E.subtype
  have hPidx : ¬ 2 ∣ ((P₀ : Subgroup E).map E.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h1 | h1
    · exact P₀.not_dvd_index h1
    · exact hidx h1
  have hN : normalizer ((hPp.toSylow hPidx : Subgroup G) : Set G) ≤
      centralizer ((hPp.toSylow hPidx : Subgroup G) : Set G) := by
    intro g hg
    have hgE : g ∈ E := hs g (hPE ((mem_normalizer_iff.1 hg s).1 hsP))
    rw [mem_centralizer_iff]
    intro h hh
    exact hE h (hPE hh) g hgE
  have hker := MonoidHom.not_dvd_card_ker_transferSylow (hPp.toSylow hPidx) hN
  have hle : commutator G ≤ (MonoidHom.transferSylow (hPp.toSylow hPidx) hN).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hE _ (hPE (MonoidHom.transferSylow (hPp.toSylow hPidx) hN a).2) _
      (hPE (MonoidHom.transferSylow (hPp.toSylow hPidx) hN b).2))
  rw [Nat.odd_iff]
  by_contra h
  exact hker ((Nat.dvd_of_mod_eq_zero (by omega)).trans (Subgroup.card_dvd_of_le hle))

theorem pow_odd_smul {A X : Type*} [Group A] [MulAction A X] {κ : A} {y z : X}
    (hκy : κ • y = z) (hκz : κ • z = y) {m : ℕ} (hm : Odd m) : κ ^ m • y = z := by
  obtain ⟨j, rfl⟩ := hm
  have hz : κ ^ 2 • z = z := by rw [sq, mul_smul, hκz, hκy]
  have h2 : ∀ j : ℕ, (κ ^ 2) ^ j • z = z := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_smul]
    | succ j ih => rw [pow_succ, mul_smul, hz, ih]
  rw [pow_succ, mul_smul, hκy, pow_mul, h2]

theorem odd_card_commutator_of_three_point_orbit {A X : Type*} [Group A] [Finite A]
    [MulAction A X] (N : Subgroup A) [N.Normal] {F y z : X}
    (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    (hN : ∀ n ∈ N, n • F = F)
    (hE : ∀ a b : A, a • F = F → b • F = F → ⁅a, b⁆ ∈ N) :
    Odd (Nat.card (commutator (A ⧸ N))) := by
  have hNS : N ≤ MulAction.stabilizer A F := fun n hn => hN n hn
  have hker : (QuotientGroup.mk' N).ker ≤ MulAction.stabilizer A F := by
    rw [QuotientGroup.ker_mk']
    exact hNS
  have hFy : F ≠ y := fun h => hyz (by rw [← hκy, ← h, hκF, h])
  have hFz : F ≠ z := fun h => hyz (by rw [← hκz, ← h, hκF, h])
  obtain ⟨j, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos κ).ne'
  have hκS : κ ^ m ∈ MulAction.stabilizer A F := pow_mem (MulAction.mem_stabilizer_iff.2 hκF) m
  refine odd_card_commutator_of_burnside (E := (MulAction.stabilizer A F).map (QuotientGroup.mk' N))
    ?_ ?_ (s := QuotientGroup.mk' N (κ ^ m)) (mem_map_of_mem _ hκS) (k := j) ?_ ?_
  ·
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : QuotientGroup.mk' N ⁅a, b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hE a b (MulAction.mem_stabilizer_iff.1 ha)
        (MulAction.mem_stabilizer_iff.1 hb))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  ·
    rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N) hker,
      MulAction.index_stabilizer]
    by_cases hall : ∀ a : A, a • F = F
    · have horb : MulAction.orbit A F = {F} := by
        ext x
        simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
        exact ⟨fun ⟨a, ha⟩ => by rw [← ha, hall a], fun hx => ⟨1, by rw [hx, one_smul]⟩⟩
      rw [horb, Set.ncard_singleton]
      omega
    · obtain ⟨a₀, ha₀⟩ := not_forall.1 hall
      have hy : y ∈ MulAction.orbit A F := by
        rcases hO a₀ with h | h | h
        · exact absurd h ha₀
        · exact MulAction.mem_orbit_iff.2 ⟨a₀, h⟩
        · exact MulAction.mem_orbit_iff.2 ⟨κ * a₀, by rw [mul_smul, h, hκz]⟩
      have hz : z ∈ MulAction.orbit A F := by
        obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.1 hy
        exact MulAction.mem_orbit_iff.2 ⟨κ * b, by rw [mul_smul, hb, hκy]⟩
      have horb : MulAction.orbit A F = {F, y, z} := by
        ext x
        constructor
        · intro hx
          obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.1 hx
          rcases hO a with h | h | h <;> simp [h]
        · rintro (rfl | rfl | rfl)
          · exact MulAction.mem_orbit_self _
          · exact hy
          · exact hz
      rw [horb, Set.ncard_insert_of_notMem (by simp [hFy, hFz]),
        Set.ncard_pair hyz]
      omega
  · rw [← map_pow, ← pow_mul, mul_comm, ← hjm, pow_orderOf_eq_one, map_one]
  ·
    intro g hg
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N g
    rw [← map_inv, ← map_mul, ← map_mul, ← Subgroup.mem_comap, Subgroup.comap_map_eq,
      sup_eq_left.2 hker] at hg
    have hfix : κ ^ m • (b⁻¹ • F) = b⁻¹ • F := by
      have h1 := MulAction.mem_stabilizer_iff.1 hg
      rw [mul_smul, mul_smul] at h1
      calc κ ^ m • (b⁻¹ • F) = b⁻¹ • (b • (κ ^ m • (b⁻¹ • F))) := (inv_smul_smul b _).symm
        _ = b⁻¹ • F := by rw [h1]
    have hbF : b⁻¹ • F = F := by
      rcases hO b⁻¹ with h | h | h
      · exact h
      · rw [h, pow_odd_smul hκy hκz hm] at hfix
        exact absurd hfix.symm hyz
      · rw [h, pow_odd_smul hκz hκy hm] at hfix
        exact absurd hfix hyz
    refine mem_map_of_mem _ ?_
    rw [← inv_mem_iff]
    exact MulAction.mem_stabilizer_iff.2 hbF

end Criteria

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartOne.OutStructure (linear_D2 ringAut_comm)

theorem odd_card_commutator_outer_projectiveSL {n m : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 3 ≤ n) (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (commutator (Outer (projectiveSL n K)))) := by
  have : Finite (MulAut (projectiveSL n K)) := ProjectivePlane.finite_mulAut_projectiveSL n
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDn, -⟩ := standard_outer_quotients (n := n) (K := K)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  have hdiag : ¬ 2 ∣ Nat.gcd n (Nat.card K - 1) := by
    intro h
    have h1 := h.trans (Nat.gcd_dvd_right _ _)
    rw [hK] at h1
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have h3 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  refine odd_card_commutator_outer_of_tower (D := linearAutGroup n K) (fun γ α => ?_)
    (fun δ hδ h2 => linear_D2 Nat.prime_two hn hdiag δ hδ 1 (by rwa [pow_one]))
  obtain ⟨A, σ, ε, -, rfl⟩ := hgen γ
  obtain ⟨B, τ, ε', -, rfl⟩ := hgen α
  have hπc : ∀ C : GL (Fin n) K, QuotientGroup.mk' (linearAutGroup n K) (conjAut n K C) = 1 :=
    fun C => (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup C)
  have hff : ∀ σ τ : K ≃+* K, Commute (QuotientGroup.mk' (linearAutGroup n K) (fieldAut n K σ))
      (QuotientGroup.mk' (linearAutGroup n K) (fieldAut n K τ)) := by
    intro σ τ
    have h1 : fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ := by
      rw [htrans.2.1, htrans.2.1, ringAut_comm K σ τ]
    have h3 := congrArg (QuotientGroup.mk' (linearAutGroup n K)) h1
    rw [map_mul, map_mul] at h3
    exact h3
  have hδf : ∀ τ : K ≃+* K, Commute (QuotientGroup.mk' (linearAutGroup n K) (dualAut n K))
      (QuotientGroup.mk' (linearAutGroup n K) (fieldAut n K τ)) := by
    intro τ
    have h1 : dualAut n K * fieldAut n K τ = fieldAut n K τ * dualAut n K := by
      have h2 := htrans.2.2.2.2.2.1 τ
      calc dualAut n K * fieldAut n K τ
          = (dualAut n K * fieldAut n K τ * dualAut n K) * dualAut n K := by
            rw [mul_assoc (dualAut n K * fieldAut n K τ), htrans.2.2.2.1, mul_one]
        _ = fieldAut n K τ * dualAut n K := by rw [h2]
    have h3 := congrArg (QuotientGroup.mk' (linearAutGroup n K)) h1
    rw [map_mul, map_mul] at h3
    exact h3
  have hc : Commute
      (QuotientGroup.mk' (linearAutGroup n K) (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε))
      (QuotientGroup.mk' (linearAutGroup n K) (conjAut n K B * fieldAut n K τ * dualAut n K ^ ε'))
      := by
    rw [map_mul, map_mul, map_mul, map_mul, hπc, hπc, one_mul, one_mul, map_pow, map_pow]
    exact ((hff σ τ).mul_left ((hδf τ).pow_left ε)).mul_right
      (((hδf σ).symm.pow_right ε').mul_left ((Commute.refl _).pow_pow ε ε'))
  have h1 : QuotientGroup.mk' (linearAutGroup n K)
      ⁅conjAut n K A * fieldAut n K σ * dualAut n K ^ ε,
        conjAut n K B * fieldAut n K τ * dualAut n K ^ ε'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hc
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem odd_card_commutator_outer_of_psl_model {S : Type} [Group S] {n m : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel S .PSL n 2 m) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨⟨-, hm, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : S ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  exact odd_card_commutator_outer_of_equiv e' (odd_card_commutator_outer_projectiveSL hn hm hK)

end Linear

section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.OutStructure (ringAut_comm)

theorem odd_card_commutator_outer_primeFormP {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    Odd (Nat.card (commutator
      (Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))) := by
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  have hring := card_ringAut_and_isCyclic h.prime K h.card
  have hID : OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≤
      primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  refine odd_card_commutator_outer_of_tower
    (D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (fun a b => ?_)
    (fun δ hδ h2 => ?_)
  · rw [← hFker, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact ringAut_comm K _ _
  ·
    have hodd : Odd (Nat.gcd n (2 ^ f + 1)) :=
      Odd.of_dvd_nat (Even.add_one ((Nat.even_pow' (by have := h.one_le; omega)).2 even_two))
        (Nat.gcd_dvd_right _ _)
    set x : primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
        (OuterAutomorphisms.inner
          (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
          (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      QuotientGroup.mk (⟨δ, hδ⟩ : primeFormD h _) with hx
    have hx2 : x ^ 2 = 1 := by
      rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h2
    have hdvd1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hdvd2 : orderOf x ∣ Nat.gcd n (2 ^ f + 1) := hcard ▸ orderOf_dvd_natCard x
    have hx1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd1 with h1 | h1
      · exact h1
      · rw [h1] at hdvd2
        exact absurd (even_iff_two_dvd.2 hdvd2) (Nat.not_even_iff_odd.2 hodd)
    have h1 : x = 1 := orderOf_eq_one_iff.mp hx1
    have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : primeFormD h _)).mp h1
    exact Subgroup.mem_subgroupOf.mp hmem

theorem odd_card_commutator_outer_of_psu_model {S : Type} [Group S] {n m : ℕ}
    (h : StatedClassicalModel S .PSU n 2 m) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 2 m K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ 2 ^ m = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  have e' : S ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact odd_card_commutator_outer_of_equiv e' (odd_card_commutator_outer_primeFormP hU hn3 hq)

end Unitary

section Symplectic

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartOne.OutStructure (commutator_mem_of_cyclic_quotient)

theorem odd_card_commutator_outer_statedSp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    (hr : 3 ≤ r) : Odd (Nat.card (commutator (Outer (StatedProj (StatedSp r K))))) := by
  have : NeZero r := ⟨by omega⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hr
  obtain ⟨-, -, hDn, -, ⟨g, -, hg⟩, -⟩ := standard_outer_quotient (K := K) (r := r) (by omega)
  have : (spLinearAutGroup r K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ spSemilinearAutGroup r K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ spSemilinearAutGroup r K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  have hDle : spLinearAutGroup r K ≤ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) := by
    intro δ hδ
    obtain ⟨A, rfl⟩ := (mem_spLinearAutGroup_iff).mp hδ
    exact conjAut_mem_inner_of_isSquare
      (FiniteField.isSquare_of_char_two (ringChar.eq K 2) (multiplier r K A : K))
  have hgE : ∀ α : MulAut (StatedProj (StatedSp r K)),
      ∃ k : ℤ, g ^ k * α ∈ spLinearAutGroup r K :=
    fun α => hg α (hgenTop ▸ Subgroup.mem_top α)
  exact odd_card_commutator_outer_of_tower (D := OuterAutomorphisms.inner _)
    (fun γ α => hDle (commutator_mem_of_cyclic_quotient g hgE γ α)) (fun δ hδ _ => hδ)

theorem odd_card_commutator_outer_statedSp_two {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (commutator (Outer (StatedProj (StatedSp 2 K))))) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hm hK
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hm hK
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hm hFr hord
      hzp
  let : CommGroup (Outer (StatedProj (StatedSp 2 K))) := IsCyclic.commGroup
  exact odd_card_commutator_of_comm fun a b => mul_comm a b

theorem odd_card_commutator_outer_of_psp_model {S : Type} [Group S] {n m : ℕ} (hn : 2 ≤ n)
    (h : StatedClassicalModel S .PSp n 2 m) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hm hK
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    exact odd_card_commutator_outer_of_equiv e (odd_card_commutator_outer_statedSp_two hm hK)
  · exact odd_card_commutator_outer_of_equiv e (odd_card_commutator_outer_statedSp hn3)

end Symplectic

section Orthogonal

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartOne.KLC (matrixProjectiveImage_commutator_mem_inner swap_data_coordinate
  inner_smul_pointFamily_coordinate)
open scoped Pointwise

theorem odd_card_commutator_outer_of_image_top {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0)
    (hA : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (htop : matrixProjectiveImage Q = ⊤) :
    Odd (Nat.card (commutator (Outer (matrixProjectiveDerived Q)))) := by
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  exact odd_card_commutator_outer_of_tower (D := OuterAutomorphisms.inner _)
    (fun a b => matrixProjectiveImage_commutator_mem_inner Q hQ hA (htop ▸ mem_top a)
      (htop ▸ mem_top b)) (fun δ hδ _ => hδ)

theorem odd_card_commutator_outer_POmegaPlus {S : Type} [Group S] {n m : ℕ} (hn : 5 ≤ n)
    (h : StatedClassicalModel S .POmegaPlus n 2 m) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound S .POmegaPlus (.inr (.inl rfl))
    n 2 m h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  exact odd_card_commutator_outer_of_equiv (coordinatePlusWitnessEquiv K e)
    (odd_card_commutator_outer_of_image_top hQ hA
      (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn))

theorem odd_card_commutator_outer_POmegaMinus {S : Type} [Group S] {n m : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel S .POmegaMinus n 2 m) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound S .POmegaMinus
    (.inr (.inr rfl)) n 2 m h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hA : Nat.card (Abelianization (matrixIsometries
      (coordinateQuadMinus n K (by omega) b c))) ≤ 2 := by
    rw [coordinateQuadMinus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  exact odd_card_commutator_outer_of_equiv (coordinateMinusWitnessEquiv K (by omega) b c e)
    (odd_card_commutator_outer_of_image_top hQ hA
      (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr))

theorem odd_card_commutator_outer_POmegaPlus_four {S : Type} [Group S] {m : ℕ}
    (h : StatedClassicalModel S .POmegaPlus 4 2 m) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound S .POmegaPlus (.inr (.inl rfl))
    4 2 m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := swap_data_coordinate K
  have : Finite (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := inferInstance
  refine odd_card_commutator_outer_of_equiv (coordinatePlusWitnessEquiv K e)
    (odd_card_commutator_of_three_point_orbit (OuterAutomorphisms.inner _)
      (F := projectivePointFamily (coordinateQuadPlus 4 K)) (y := plusCX 4 K)
      (z := plusCXstar 4 K (by omega)) ?_ hκF hκy hκz hyz ?_ ?_)
  · intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  · rintro _ ⟨g, rfl⟩
    exact inner_smul_pointFamily_coordinate K g
  · intro a b ha hb
    refine matrixProjectiveImage_commutator_mem_inner _ hQ hA ?_ ?_
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 ha
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 hb

end Orthogonal

theorem odd_card_commutator_outer_of_classicalEvenType {S : Type} [Group S]
    (hT : RankTwoClassicalEvenType S) : Odd (Nat.card (commutator (Outer S))) := by
  obtain ⟨hfam, -, -⟩ := hT
  rcases hfam with ⟨n, m, hn, h⟩ | ⟨n, m, hn, h⟩ | ⟨n, m, hn, h⟩ | ⟨n, m, hn, h | h⟩
  · exact odd_card_commutator_outer_of_psl_model (by omega) h
  · exact odd_card_commutator_outer_of_psu_model h
  · exact odd_card_commutator_outer_of_psp_model hn h
  · rcases Nat.lt_or_ge n 5 with hn5 | hn5
    · obtain rfl : n = 4 := by omega
      exact odd_card_commutator_outer_POmegaPlus_four h
    · exact odd_card_commutator_outer_POmegaPlus hn5 h
  · exact odd_card_commutator_outer_POmegaMinus hn h

theorem classicalOutCommOdd : ClassicalOutCommOdd := fun _ _ _ hA hT =>
  odd_card_commutator_outer_of_quot hA (odd_card_commutator_outer_of_classicalEvenType hT)

end CFSG.ComponentClassification.RankTwoClassical
