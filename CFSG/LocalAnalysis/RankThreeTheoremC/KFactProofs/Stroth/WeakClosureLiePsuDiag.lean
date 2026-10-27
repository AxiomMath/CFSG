module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslQuot
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslDiag
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicNine
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open scoped Matrix
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Quasithin (StatedGU)
open CFSG.LocalAnalysis.RankThreeTheoremC.NineSubgroup (dglHom coe_dglHom dglHom_unitary)

private noncomputable def pdPerm (n : ℕ) (L : Type) [Field L] :
    Equiv.Perm (Fin n) →* GL (Fin n) L :=
  (Matrix.permMatrixHom : Equiv.Perm (Fin n) →* Matrix (Fin n) (Fin n) L).toHomUnits

private theorem coe_pdPerm {n : ℕ} (L : Type) [Field L] (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    ((pdPerm n L σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      if i = σ j then 1 else 0 := by
  simp only [pdPerm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]

private theorem det_pdPerm {n : ℕ} (L : Type) [Field L] (σ : Equiv.Perm (Fin n)) :
    ((pdPerm n L σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : L) := by
  simp [pdPerm, Matrix.det_permutation]

private theorem det_pdPerm_of_sign {n : ℕ} (L : Type) [Field L] {σ : Equiv.Perm (Fin n)}
    (hσ : Equiv.Perm.sign σ = 1) :
    ((pdPerm n L σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
  rw [det_pdPerm, hσ]
  simp

private theorem det_pdPerm_swap {n : ℕ} (L : Type) [Field L] {i j : Fin n} (hij : i ≠ j) :
    ((pdPerm n L (Equiv.swap i j) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = -1 := by
  rw [det_pdPerm, Equiv.Perm.sign_swap hij]
  simp

private theorem pdPerm_unitary {n q : ℕ} (L : Type) [Field L] (hq : q ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    (((pdPerm n L σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((pdPerm n L σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, coe_pdPerm, ite_pow,
    one_pow, zero_pow hq, ite_mul, one_mul, zero_mul, Matrix.one_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, EmbeddingLike.apply_eq_iff_eq]

private theorem pdPerm_mem_GU {n q : ℕ} (L : Type) [Field L] (hq : q ≠ 0)
    (σ : Equiv.Perm (Fin n)) : pdPerm n L σ ∈ StatedGU n q L :=
  Subgroup.subset_closure (pdPerm_unitary L hq σ)

private theorem pdSign_eq_one {n p : ℕ} (hp : Odd p) {σ : Equiv.Perm (Fin n)}
    (h : σ ^ p = 1) : Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ p = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h'
  · exact h'
  · rw [h', hp.neg_one_pow] at h1
    exact absurd h1 (by decide)

private theorem pdPerm_mem_SU {n q p : ℕ} (L : Type) [Field L] (hq : q ≠ 0) (hp : Odd p)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ^ p = 1) : pdPerm n L σ ∈ StatedSU n q L :=
  Subgroup.subset_closure
    ⟨det_pdPerm_of_sign L (pdSign_eq_one hp hσ), pdPerm_unitary L hq σ⟩

private theorem pdPerm_mul_dglHom {n : ℕ} (L : Type) [Field L] (σ : Equiv.Perm (Fin n))
    (t : Fin n → Lˣ) :
    pdPerm n L σ * dglHom n t = dglHom n (fun i => t (σ⁻¹ i)) * pdPerm n L σ := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, coe_dglHom, coe_dglHom, Matrix.mul_diagonal,
    Matrix.diagonal_mul, coe_pdPerm]
  by_cases h : i = σ j
  · subst h
    simp
  · simp [h]

private noncomputable def pdTorus (n : ℕ) (L : Type) [Field L] {G : Type} [Group G]
    (ρ : G →* Lˣ) : (Fin n → G) →* GL (Fin n) L :=
  (dglHom n).comp (MonoidHom.pi fun i : Fin n => ρ.comp (Pi.evalMonoidHom (fun _ : Fin n => G) i))

private theorem pdTorus_apply {n : ℕ} (L : Type) [Field L] {G : Type} [Group G] (ρ : G →* Lˣ)
    (c : Fin n → G) : pdTorus n L ρ c = dglHom n (fun i => ρ (c i)) := rfl

private theorem dglHom_eq_one_iff {n : ℕ} (L : Type) [Field L] (u : Fin n → Lˣ) :
    dglHom n u = (1 : GL (Fin n) L) ↔ u = 1 := by
  constructor
  · intro hu
    funext i
    apply Units.ext
    have h := congrArg (fun g : GL (Fin n) L => ((g : Matrix (Fin n) (Fin n) L) i i)) hu
    simpa [coe_dglHom] using h
  · rintro rfl
    rw [map_one]

private theorem pdTorus_injective {n : ℕ} (L : Type) [Field L] {G : Type} [Group G]
    {ρ : G →* Lˣ} (hρ : Function.Injective ρ) : Function.Injective (pdTorus n L ρ) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  rw [pdTorus_apply, dglHom_eq_one_iff] at hc
  funext i
  show c i = 1
  apply hρ
  rw [map_one]
  exact congrFun hc i

private theorem pdTorus_mem_SU {n q : ℕ} (L : Type) [Field L] {G : Type} [CommGroup G]
    {ρ : G →* Lˣ} (hq : q ≠ 0) (hρ : ∀ x : G, ρ x ^ (q + 1) = 1) (c : Fin n → G)
    (hc : ∏ i, c i = 1) : pdTorus n L ρ c ∈ StatedSU n q L := by
  have hdiag : ∀ i, ((ρ (c i) : Lˣ) : L) ^ (q + 1) = 1 := fun i => by
    rw [← Units.val_pow_eq_pow_val, hρ (c i), Units.val_one]
  refine Subgroup.subset_closure ⟨?_, dglHom_unitary hq (fun i => ρ (c i)) hdiag⟩
  rw [pdTorus_apply, coe_dglHom, Matrix.det_diagonal]
  show ∏ i, ((ρ (c i) : Lˣ) : L) = 1
  rw [← Units.coe_prod, ← map_prod, hc, map_one, Units.val_one]

private theorem pdPerm_conj {n : ℕ} (L : Type) [Field L] {G : Type} [Group G] (ρ : G →* Lˣ)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → G) :
    pdPerm n L σ * pdTorus n L ρ c * (pdPerm n L σ)⁻¹ = pdTorus n L ρ (c ∘ ⇑σ⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul, pdTorus_apply, pdTorus_apply]
  exact pdPerm_mul_dglHom L σ (fun i => ρ (c i))

private noncomputable def pdCorr (n : ℕ) (L : Type) [Field L] (k : Fin n) (u : Lˣ) :
    GL (Fin n) L :=
  dglHom n (Pi.mulSingle k u)

private theorem det_pdCorr {n : ℕ} (L : Type) [Field L] (k : Fin n) (u : Lˣ) :
    ((pdCorr n L k u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = (u : L) := by
  rw [pdCorr, coe_dglHom, Matrix.det_diagonal, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.mulSingle_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

private theorem pdCorr_mem_GU {n q : ℕ} (L : Type) [Field L] (hq : q ≠ 0) (k : Fin n) {u : Lˣ}
    (hu : (u : L) ^ (q + 1) = 1) : pdCorr n L k u ∈ StatedGU n q L := by
  have hdiag : ∀ i, (((Pi.mulSingle k u : Fin n → Lˣ) i : Lˣ) : L) ^ (q + 1) = 1 := fun i => by
    by_cases hi : i = k
    · subst hi
      simpa using hu
    · simp [Pi.mulSingle_eq_of_ne hi]
  exact Subgroup.subset_closure (dglHom_unitary hq (Pi.mulSingle k u : Fin n → Lˣ) hdiag)

private theorem pdCorr_comm {n : ℕ} (L : Type) [Field L] {G : Type} [CommGroup G]
    (ρ : G →* Lˣ) (k : Fin n) (u : Lˣ) (c : Fin n → G) :
    pdCorr n L k u * pdTorus n L ρ c = pdTorus n L ρ c * pdCorr n L k u := by
  rw [pdCorr, pdTorus_apply, ← map_mul, ← map_mul, mul_comm]

private theorem pdNegOne_pow {p f q : ℕ} {L : Type} [Field L] (h : UnitaryFieldData p f L)
    (hq : q = p ^ f) : ((-1 : Lˣ) : L) ^ (q + 1) = 1 := by
  rw [Units.val_neg, Units.val_one]
  haveI := h.charP
  rcases h.prime.eq_two_or_odd' with h2 | hodd
  · have h3 : ((2 : ℕ) : L) = 0 := by
      rw [← h2]
      exact CharP.cast_eq_zero L p
    have h4 : (1 : L) + 1 = 0 := by
      rw [one_add_one_eq_two]
      exact_mod_cast h3
    rw [neg_eq_iff_add_eq_zero.2 h4, one_pow]
  · have hqodd : Odd q := by
      rw [hq]
      exact hodd.pow
    exact (Nat.even_add_one.2 (Nat.not_even_iff_odd.2 hqodd)).neg_one_pow

private theorem pdSU_le_GU (n q : ℕ) (L : Type) [Field L] : StatedSU n q L ≤ StatedGU n q L :=
  (Subgroup.closure_le _).2 fun _ hA => Subgroup.subset_closure hA.2

private theorem pdNotDvd_scalars {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [Finite L] {q n : ℕ}
    (hpn : ¬ p ∣ n) : ¬ p ∣ Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L)) :=
  CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSU n q L) Fact.out hpn
    (fun c hc => by
      have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU hc
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      exact Units.ext (by simpa using hdet))

private theorem pdDet_eq_one_iff {n : ℕ} (L : Type) [Field L] (A : GL (Fin n) L) :
    Matrix.GeneralLinearGroup.det A = 1 ↔ (A : Matrix (Fin n) (Fin n) L).det = 1 := by
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

private theorem pdCard_statedGU_eq {p₀ f : ℕ} {L : Type} [Field L] [Finite L] {q n : ℕ}
    (h : UnitaryFieldData p₀ f L) (hqf : q = p₀ ^ f) :
    Nat.card (StatedGU n q L) =
      Nat.card ((Matrix.GeneralLinearGroup.det : GL (Fin n) L →* Lˣ).comp
        (StatedGU n q L).subtype).range * Nat.card (StatedSU n q L) := by
  set φ := (Matrix.GeneralLinearGroup.det : GL (Fin n) L →* Lˣ).comp (StatedGU n q L).subtype
    with hφ
  have hker : φ.ker = (StatedSU n q L).subgroupOf (StatedGU n q L) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Matrix.GeneralLinearGroup.det (x : GL (Fin n) L) = 1 ↔
      (x : GL (Fin n) L) ∈ StatedSU n q L
    constructor
    · intro hx
      exact mem_statedSU_of_mem_statedGU h hqf x.2 ((pdDet_eq_one_iff L _).1 hx)
    · intro hx
      exact (pdDet_eq_one_iff L _).2 (CFSG.Open.StatedAPI.det_of_mem_statedSU hx)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pdSU_le_GU n q L)).toEquiv] at h1
  exact h1

private theorem pdCard_range_dvd {p₀ f : ℕ} {L : Type} [Field L] [Finite L] {q n : ℕ}
    (h : UnitaryFieldData p₀ f L) (hqf : q = p₀ ^ f) :
    Nat.card ((Matrix.GeneralLinearGroup.det : GL (Fin n) L →* Lˣ).comp
      (StatedGU n q L).subtype).range ∣ q + 1 := by
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hx
  refine Subtype.ext (Units.ext ?_)
  show ((Matrix.GeneralLinearGroup.det (g : GL (Fin n) L) : Lˣ) : L) ^ (q + 1) = 1
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact det_pow_card_add_one_of_mem_statedGU h hqf g.2

private theorem pdDvd_units {p : ℕ} [Fact p.Prime] {L : Type} [Field L] {q : ℕ}
    (hq : Nat.card L = q ^ 2) (hpq : p ∣ q + 1) :
    p ^ padicValNat p (q + 1) ∣ Nat.card L - 1 := by
  rw [hq]
  have h1 := Nat.sq_sub_sq q 1
  rw [one_pow] at h1
  rw [h1]
  exact Dvd.dvd.mul_right pow_padicValNat_dvd _

private theorem pdCard_projSU {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type} [Field L]
    [Finite L] {q n : ℕ} (hq : Nat.card L = q ^ 2) (hn : 1 ≤ n) (hpq : p ∣ q + 1)
    (hpn : ¬ p ∣ n) :
    padicValNat p (Nat.card (StatedProj (StatedSU n q L))) + padicValNat p (q + 1) =
      padicValNat p (q + 1) * n + padicValNat p n.factorial := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hq1 : 1 < Nat.card L := Finite.one_lt_card
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [hq] at hq1
    simp at hq1
  have hpq' : ¬ p ∣ q := fun h' => hp.not_dvd_one ((Nat.dvd_add_right h').1 hpq)
  haveI : Fintype L := Fintype.ofFinite L
  have hqL : Fintype.card L = q ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hq
  obtain ⟨f, hqf, h⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData L hqL
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨k₀⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hord1 : orderOf (-(q : ZMod p)) = 1 := by
    have h1 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h1
    have h2 : -(q : ZMod p) = 1 := neg_eq_iff_add_eq_zero.2 h1
    rw [h2, orderOf_one]
  have h3 : padicValInt p ((-(q : ℤ)) ^ 1 - 1) = padicValNat p (q + 1) := by
    have : (-(q : ℤ)) ^ 1 - 1 = -((q + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
    show padicValNat p (-((q + 1 : ℕ) : ℤ)).natAbs = padicValNat p (q + 1)
    rw [Int.natAbs_neg]
    rfl
  have hGU : padicValNat p (Nat.card (StatedGU n q L)) =
      padicValNat p (q + 1) * n + padicValNat p n.factorial := by
    have h2 := CFSG.GroupTheory.WeirSylow.factorization_card_statedGU hodd L hqL hpq' hn
    rw [hord1, Nat.div_one, h3] at h2
    rw [← Nat.factorization_def (Nat.card (StatedGU n q L)) hp, h2]
  set D := (Matrix.GeneralLinearGroup.det : GL (Fin n) L →* Lˣ).comp (StatedGU n q L).subtype
    |>.range
  have hGU1 : Nat.card (StatedGU n q L) = Nat.card D * Nat.card (StatedSU n q L) :=
    pdCard_statedGU_eq h hqf
  have hD' : Nat.card D ∣ q + 1 := pdCard_range_dvd h hqf
  have hdvdL := pdDvd_units hq hpq
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq hdvdL
  have hζpow : ζ ^ (q + 1) = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hζ]
    exact pow_padicValNat_dvd
  have hζq : ((ζ : Lˣ) : L) ^ (q + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζpow, Units.val_one]
  have hζD : ζ ∈ D := by
    refine MonoidHom.mem_range.2 ⟨⟨pdCorr n L k₀ ζ, pdCorr_mem_GU L hq0 k₀ hζq⟩, ?_⟩
    exact Units.ext ((Matrix.GeneralLinearGroup.val_det_apply _).trans (det_pdCorr L k₀ ζ))
  have hpaD : p ^ padicValNat p (q + 1) ∣ Nat.card D := by
    have h1 := orderOf_dvd_natCard (⟨ζ, hζD⟩ : D)
    rwa [Subgroup.orderOf_mk, hζ] at h1
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have hDval : padicValNat p (Nat.card D) = padicValNat p (q + 1) := by
    apply le_antisymm
    · exact (padicValNat_dvd_iff_le (by omega : q + 1 ≠ 0)).1 ((pow_padicValNat_dvd).trans hD')
    · exact (padicValNat_dvd_iff_le hD0).1 hpaD
  have hSU2 : Nat.card (StatedSU n q L) = Nat.card (StatedProj (StatedSU n q L)) *
      Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hZ : padicValNat p (Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))) = 0 :=
    padicValNat.eq_zero_of_not_dvd (pdNotDvd_scalars hpn)
  have hK0 : Nat.card (StatedProj (StatedSU n q L)) ≠ 0 := Nat.card_pos.ne'
  have hZ0 : Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L)) ≠ 0 :=
    Nat.card_pos.ne'
  have hSU0 : Nat.card (StatedSU n q L) ≠ 0 := Nat.card_pos.ne'
  have hA : padicValNat p (Nat.card (StatedGU n q L)) =
      padicValNat p (Nat.card D) + padicValNat p (Nat.card (StatedSU n q L)) := by
    rw [hGU1, padicValNat.mul hD0 hSU0]
  have hB : padicValNat p (Nat.card (StatedSU n q L)) =
      padicValNat p (Nat.card (StatedProj (StatedSU n q L))) + 0 := by
    rw [hSU2, padicValNat.mul hK0 hZ0, hZ]
  omega

private noncomputable def pdSUProj (n q : ℕ) (L : Type) [Field L] :
    StatedSU n q L →* StatedProj (StatedSU n q L) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))

private noncomputable def pdLiftSU {A : Type} [Group A] {n q : ℕ} {L : Type} [Field L]
    (T : A →* GL (Fin n) L) (hT : ∀ a, T a ∈ StatedSU n q L) :
    A →* StatedProj (StatedSU n q L) :=
  (pdSUProj n q L).comp (T.codRestrict (StatedSU n q L) hT)

private theorem pdLiftSU_apply {A : Type} [Group A] {n q : ℕ} {L : Type} [Field L]
    (T : A →* GL (Fin n) L) (hT : ∀ a, T a ∈ StatedSU n q L) (a : A) :
    pdLiftSU T hT a = pdSUProj n q L ⟨T a, hT a⟩ := rfl

private theorem pdLiftSU_conj {A : Type} [Group A] {n q : ℕ} {L : Type} [Field L]
    {T : A →* GL (Fin n) L} {hT : ∀ a, T a ∈ StatedSU n q L} {g : GL (Fin n) L}
    (hg : g ∈ StatedSU n q L) {a a' : A} (h : g * T a * g⁻¹ = T a') :
    pdSUProj n q L ⟨g, hg⟩ * pdLiftSU T hT a * (pdSUProj n q L ⟨g, hg⟩)⁻¹ =
      pdLiftSU T hT a' := by
  rw [pdLiftSU_apply, pdLiftSU_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg (pdSUProj n q L) (Subtype.ext ?_)
  simpa using h

private theorem pdLiftSU_injective {p : ℕ} [Fact p.Prime] {A : Type} [Group A] {n q : ℕ}
    {L : Type} [Field L] {T : A →* GL (Fin n) L} {hT : ∀ a, T a ∈ StatedSU n q L}
    (hTinj : Function.Injective T) (hA : ∀ a : A, ∃ k : ℕ, a ^ p ^ k = 1)
    (hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))) :
    Function.Injective (pdLiftSU T hT) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨k, hk⟩ := hA a
  have ha' : (⟨T a, hT a⟩ : StatedSU n q L) ∈
      (StatedScalars (Fin n) L).subgroupOf (StatedSU n q L) :=
    (QuotientGroup.eq_one_iff _).1 ((pdLiftSU_apply T hT a).symm.trans ha)
  have hpow : (⟨T a, hT a⟩ : StatedSU n q L) ^ p ^ k = 1 := by
    apply Subtype.ext
    show T a ^ p ^ k = 1
    rw [← map_pow, hk, map_one]
  have h1 := eq_one_of_mem_of_pow_eq_one _ hN ha' hpow
  have h2 : T a = 1 := congrArg Subtype.val h1
  exact hTinj (by rw [h2, map_one])

private theorem pdNonscalar_of_frame {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type} [Field L]
    [Finite L] {q n a : ℕ} (hq0 : q ≠ 0) (ha : 1 ≤ a) (hpr : p ≤ n) (hpn : ¬ p ∣ n)
    (T : (Fin n → Multiplicative (ZMod (p ^ a))) →* GL (Fin n) L) (hTinj : Function.Injective T)
    (hTpow : ∀ c : Fin n → Multiplicative (ZMod (p ^ a)), T c ^ p ^ a = 1)
    (hTSU : ∀ c : Fin n → Multiplicative (ZMod (p ^ a)), ∏ i, c i = 1 → T c ∈ StatedSU n q L)
    (hS : ∀ (σ : Equiv.Perm (Fin n)) (c : Fin n → Multiplicative (ZMod (p ^ a))),
      pdPerm n L σ * T c * (pdPerm n L σ)⁻¹ = T (c ∘ ⇑σ⁻¹)) :
    NonscalarPPair p (StatedSU n q L) := by
  have hp := (Fact.out : p.Prime)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), orderOf σ = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact (Nat.Prime.dvd_factorial hp).2 hpr
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, σ i₀ ≠ i₀ := by
    by_contra hcon
    push Not at hcon
    have h1 : σ = 1 := Equiv.ext hcon
    rw [h1, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  set g : Multiplicative (ZMod (p ^ a)) := Multiplicative.ofAdd 1
  have hgord : ∀ m : ℕ, g ^ m = 1 ↔ p ^ a ∣ m := pow_eq_one_iff_zmod
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) ((hgord 2).1 h)
    have h3 : p ≤ p ^ a := Nat.le_self_pow (by omega) p
    omega
  set c : Fin n → Multiplicative (ZMod (p ^ a)) :=
    Pi.mulSingle i₀ g * Pi.mulSingle (σ i₀) g⁻¹ with hc
  have hci₀ : c i₀ = g := by
    simp [hc, Pi.mulSingle_eq_of_ne (Ne.symm hi₀)]
  have hcσ : c (σ i₀) = g⁻¹ := by
    simp [hc, Pi.mulSingle_eq_of_ne hi₀]
  have hprod : ∀ (j : Fin n) (x : Multiplicative (ZMod (p ^ a))),
      ∏ i, (Pi.mulSingle j x : Fin n → Multiplicative (ZMod (p ^ a))) i = x := by
    intro j x
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hi
      exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod (p ^ a))) hi x
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hcprod : ∏ i, c i = 1 := by
    rw [hc]
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, hprod]
    simp
  set d : Fin n → Multiplicative (ZMod (p ^ a)) := fun i => (c (σ i))⁻¹ * c i with hd
  have hdi₀ : d i₀ = g ^ 2 := by
    rw [hd]
    simp only [hcσ, hci₀, inv_inv, pow_two]
  have hdprod : ∏ i, d i = 1 := by
    rw [hd, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ c, hcprod]
    simp
  have hSσ : (pdPerm n L σ) ^ p = 1 := by rw [← map_pow, hσp, map_one]
  have hSinv : ∀ c' : Fin n → Multiplicative (ZMod (p ^ a)),
      (pdPerm n L σ)⁻¹ * T c' * pdPerm n L σ = T (c' ∘ ⇑σ) := by
    intro c'
    have h := hS σ⁻¹ c'
    rw [map_inv, inv_inv, inv_inv] at h
    exact h
  have hcomm : (T c * pdPerm n L σ)⁻¹ * (pdPerm n L σ * T c) = T d := by
    calc (T c * pdPerm n L σ)⁻¹ * (pdPerm n L σ * T c)
        = ((pdPerm n L σ)⁻¹ * T c * pdPerm n L σ)⁻¹ * T c := by group
      _ = (T (c ∘ ⇑σ))⁻¹ * T c := by rw [hSinv]
      _ = T d := by
        rw [← map_inv, ← map_mul]
        rfl
  have hTrange : IsPGroup p (T.range : Subgroup (GL (Fin n) L)) := by
    intro x
    obtain ⟨c', hc'⟩ := x.2
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hc']
    exact hTpow c'
  have hZp : IsPGroup p (Subgroup.zpowers (pdPerm n L σ)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hSσ
  have hnorm : pdPerm n L σ ∈ Subgroup.normalizer (T.range : Set (GL (Fin n) L)) := by
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨c', rfl⟩
    rw [hS]
    exact ⟨_, rfl⟩
  have hsup : IsPGroup p (Subgroup.zpowers (pdPerm n L σ) ⊔ T.range : Subgroup (GL (Fin n) L)) :=
    hZp.to_sup_of_normal_right' hTrange (Subgroup.zpowers_le.2 hnorm)
  have hxSU : T c ∈ StatedSU n q L := hTSU c hcprod
  have hySU : pdPerm n L σ ∈ StatedSU n q L := pdPerm_mem_SU L hq0 hodd hσp
  refine ⟨T c, pdPerm n L σ, hxSU, hySU, hsup.to_le ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_right ⟨c, rfl⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [hcomm]
    intro hmem
    have hcen : T d ∈ Subgroup.center (GL (Fin n) L) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hmem
    have hconst : ∀ i j : Fin n, d i = d j := by
      intro i j
      have h1 : pdPerm n L (Equiv.swap i j) * T d = T d * pdPerm n L (Equiv.swap i j) :=
        Subgroup.mem_center_iff.1 hcen _
      have h2 : pdPerm n L (Equiv.swap i j) * T d * (pdPerm n L (Equiv.swap i j))⁻¹ = T d := by
        rw [h1, mul_inv_cancel_right]
      rw [hS, Equiv.swap_inv] at h2
      have h3 := hTinj h2
      have h4 := congrFun h3 i
      simpa [Function.comp_apply, Equiv.swap_apply_left] using h4.symm
    have hdr : (g ^ 2) ^ n = 1 := by
      rw [← hdi₀, ← hdprod]
      rw [Finset.prod_congr rfl (fun i _ => hconst i i₀)]
      simp
    rw [← pow_mul] at hdr
    have h5 : p ^ a ∣ 2 * n := (hgord _).1 hdr
    have h6 : p ∣ 2 * n := (dvd_pow_self p (by omega)).trans h5
    rcases (Nat.Prime.dvd_mul hp).1 h6 with h7 | h7
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h7)
    · exact hpn h7

private theorem pdWCOn_of_lt {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [Finite L] {q n a : ℕ}
    (hq : Nat.card L = q ^ 2) (hq0 : q ≠ 0) (hn : 3 ≤ n) (hnp : n < p) (hpn : ¬ p ∣ n)
    (ha : 1 ≤ a) (ρ : Multiplicative (ZMod (p ^ a)) →* Lˣ) (hρinj : Function.Injective ρ)
    (hρq : ∀ x : Multiplicative (ZMod (p ^ a)), ρ x ^ (q + 1) = 1)
    (hord : padicValNat p (Nat.card (StatedProj (StatedSU n q L))) + a =
      a * n + padicValNat p n.factorial) :
    WCOn p (StatedProj (StatedSU n q L)) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fintype L := Fintype.ofFinite L
  have hqL : Fintype.card L = q ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hq
  obtain ⟨f, hqf, hU⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData L hqL
  obtain ⟨k₀⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hpn0 : padicValNat p n.factorial = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd'
    have := (Nat.Prime.dvd_factorial hp).1 hdvd'
    omega
  have hv : padicValNat p (Nat.card (StatedProj (StatedSU n q L))) = a * (n - 1) := by
    rw [hpn0, add_zero] at hord
    rw [Nat.mul_sub_one]
    omega
  have hCcard : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hTinj : Function.Injective (pdTorus n L ρ) := pdTorus_injective (n := n) L hρinj
  set A := prodOneSubgroup (Multiplicative (ZMod (p ^ a))) n
  have hmemA : ∀ c : A, (pdTorus n L ρ).comp A.subtype c ∈ StatedSU n q L := fun c =>
    pdTorus_mem_SU L hq0 hρq c.1 (mem_prodOneSubgroup.1 c.2)
  have hTA : Function.Injective ((pdTorus n L ρ).comp A.subtype) :=
    hTinj.comp Subtype.val_injective
  have hΨ := pdLiftSU_injective (p := p) (hT := hmemA) hTA
    (fun c => ⟨a, Subtype.ext (pow_pPow_eq_one_pi c.1)⟩) (pdNotDvd_scalars (q := q) hpn)
  have hcard : Nat.card A = p ^ (Nat.card (StatedProj (StatedSU n q L))).factorization p := by
    have h1 := card_prodOneSubgroup_mul (Multiplicative (ZMod (p ^ a))) (r := n) (by omega)
    rw [hCcard] at h1
    rw [Nat.factorization_def _ hp, hv]
    have hpos : 0 < p ^ a := pow_pos hp.pos _
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    have h2 : a * (n - 1) + a = a * n := by
      rw [Nat.mul_sub_one]
      have : a ≤ a * n := Nat.le_mul_of_pos_right a (by omega)
      omega
    rw [h1, ← pow_mul, ← pow_add, h2]
  refine wcOn_of_range_nml (pdLiftSU ((pdTorus n L ρ).comp A.subtype) hmemA) hΨ hcard
    (normalizerMovesLines_range_sumZero (by omega) hpn _ hΨ ?_)
  intro i j
  by_cases hij : i = j
  · subst hij
    refine ⟨1, fun c => ⟨c, ?_, ?_⟩⟩
    · rw [Equiv.swap_self]
      rfl
    · simp
  · have hcorrGU : pdCorr n L k₀ (-1) ∈ StatedGU n q L :=
      pdCorr_mem_GU L hq0 k₀ (pdNegOne_pow hU hqf)
    have hg'GU : pdPerm n L (Equiv.swap i j) * pdCorr n L k₀ (-1) ∈ StatedGU n q L :=
      Subgroup.mul_mem _ (pdPerm_mem_GU L hq0 _) hcorrGU
    have hg'det : ((pdPerm n L (Equiv.swap i j) * pdCorr n L k₀ (-1) : GL (Fin n) L) :
        Matrix (Fin n) (Fin n) L).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, det_pdPerm_swap L hij, det_pdCorr]
      simp
    have hg'SU := mem_statedSU_of_mem_statedGU hU hqf hg'GU hg'det
    have hconj : ∀ c : Fin n → Multiplicative (ZMod (p ^ a)),
        pdPerm n L (Equiv.swap i j) * pdCorr n L k₀ (-1) * pdTorus n L ρ c *
          (pdPerm n L (Equiv.swap i j) * pdCorr n L k₀ (-1))⁻¹ =
          pdTorus n L ρ (c ∘ ⇑(Equiv.swap i j)) := by
      intro c
      have hcomm : pdCorr n L k₀ (-1) * pdTorus n L ρ c * (pdCorr n L k₀ (-1))⁻¹ =
          pdTorus n L ρ c := by
        rw [pdCorr_comm, mul_inv_cancel_right]
      calc pdPerm n L (Equiv.swap i j) * pdCorr n L k₀ (-1) * pdTorus n L ρ c *
            (pdPerm n L (Equiv.swap i j) * pdCorr n L k₀ (-1))⁻¹
          = pdPerm n L (Equiv.swap i j) * (pdCorr n L k₀ (-1) * pdTorus n L ρ c *
              (pdCorr n L k₀ (-1))⁻¹) * (pdPerm n L (Equiv.swap i j))⁻¹ := by group
        _ = pdPerm n L (Equiv.swap i j) * pdTorus n L ρ c * (pdPerm n L (Equiv.swap i j))⁻¹ := by
              rw [hcomm]
        _ = pdTorus n L ρ (c ∘ ⇑(Equiv.swap i j)⁻¹) := pdPerm_conj L ρ _ c
        _ = pdTorus n L ρ (c ∘ ⇑(Equiv.swap i j)) := by rw [Equiv.swap_inv]
    refine ⟨pdSUProj n q L ⟨_, hg'SU⟩, fun c => ⟨⟨(c : Fin n → Multiplicative (ZMod (p ^ a))) ∘
      ⇑(Equiv.swap i j), ?_⟩, rfl, ?_⟩⟩
    · exact (Equiv.prod_comp (Equiv.swap i j) (c : Fin n → Multiplicative (ZMod (p ^ a)))).trans
        (mem_prodOneSubgroup.1 c.2)
    · exact pdLiftSU_conj hg'SU (hconj c)

theorem wcOn_projSU_of_dvd_add_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type} [Field L]
    [Finite L] {q n : ℕ} (hq : Nat.card L = q ^ 2) (hn : 3 ≤ n) (hpq : p ∣ q + 1)
    (hpn : ¬ p ∣ n) : WCOn p (StatedProj (StatedSU n q L)) := by
  have hp : p.Prime := Fact.out
  have hq1 : 1 < Nat.card L := Finite.one_lt_card
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [hq] at hq1
    simp at hq1
  have hord := pdCard_projSU hp2 hq (by omega) hpq hpn
  obtain ⟨a, ha⟩ : ∃ a, padicValNat p (q + 1) = a := ⟨_, rfl⟩
  rw [ha] at hord
  have ha1 : 1 ≤ a := by
    rw [← ha]
    exact one_le_padicValNat_of_dvd (by omega) hpq
  have hpa : p ^ a ∣ q + 1 := by
    rw [← ha]
    exact pow_padicValNat_dvd
  have hdvdL : p ^ a ∣ Nat.card L - 1 := by
    rw [← ha]
    exact pdDvd_units hq hpq
  obtain ⟨ρ, hρinj⟩ : ∃ ρ : Multiplicative (ZMod (p ^ a)) →* Lˣ, Function.Injective ρ := by
    obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq hdvdL
    haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
    obtain ⟨ρ₀, hρ₀⟩ := CFSG.GroupTheory.WeirSylow.exists_injective_hom_of_orderOf_eq
      (H := (⊤ : Subgroup Lˣ)) (Subgroup.mem_top ζ) hζ
    exact ⟨(⊤ : Subgroup Lˣ).subtype.comp ρ₀, Subtype.val_injective.comp hρ₀⟩
  have hρq : ∀ x : Multiplicative (ZMod (p ^ a)), ρ x ^ (q + 1) = 1 := by
    intro x
    obtain ⟨k, hk⟩ := hpa
    have h1 : ρ x ^ p ^ a = 1 := by rw [← map_pow, pow_pPow_eq_one_zmod x, map_one]
    rw [hk, pow_mul, h1, one_pow]
  by_cases hnp : p ≤ n
  · exact (pdNonscalar_of_frame hp2 hq0 ha1 hnp hpn (pdTorus n L ρ)
      (pdTorus_injective (n := n) L hρinj)
      (fun c => by rw [← map_pow, pow_pPow_eq_one_pi, map_one])
      (fun c hc => pdTorus_mem_SU L hq0 hρq c hc)
      (fun σ c => pdPerm_conj L ρ σ c)).wcOn_statedProj
  · exact pdWCOn_of_lt hq hq0 hn (by omega) hpn ha1 ρ hρinj hρq hord

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
