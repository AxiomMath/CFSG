module

public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutFactsCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutSemilinear
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreUnitary
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
import CFSG.RankThree.PartOne.MB3.OddOutLinear

public section

namespace CFSG.AGLEmbedding.RankOneAut

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.AGLEmbedding.UnitaryModel CFSG.AGLEmbedding.KFactProofs.RankOneCore
open CFSG.LocalAnalysis.ComponentInitial
  (scalarSemilinearPerm derivedSeries_two_scalarSemilinearPerm)
open scoped commutatorElement

theorem commutatorElement_central_mul_central {G : Type*} [Group G] {a b z w : G}
    (hza : Commute z a) (hzb : Commute z b) (hzw : Commute z w) (hwa : Commute w a)
    (hwb : Commute w b) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹ =
      z * (a * w * b * a⁻¹) * z⁻¹ * (b⁻¹ * w⁻¹) := by group
  have hz : Commute z (a * w * b * a⁻¹) :=
    ((hza.mul_right hzw).mul_right hzb).mul_right hza.inv_right
  have hw : Commute w (a * b * a⁻¹ * b⁻¹) :=
    ((hwa.mul_right hwb).mul_right hwa.inv_right).mul_right hwb.inv_right
  have e2 : a * w * b * a⁻¹ * (b⁻¹ * w⁻¹) = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by
    have : a * w * b * a⁻¹ * (b⁻¹ * w⁻¹) = (a * w) * (b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    rw [this, ← hwa.eq]
    group
  rw [e1, hz.eq, mul_inv_cancel_right, e2, hw.eq, mul_inv_cancel_right]

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem exists_torus_correction (hq : 2 < p ^ f)
    (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hαR : ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ)
    (hαR' : ∀ r ∈ rootGroup J hJ, α⁻¹ r ∈ rootGroup J hJ) :
    ∃ u ∈ rootGroup J hJ,
      ∃ hγR : ∀ r ∈ rootGroup J hJ, ((MulAut.conj u)⁻¹ * α) r ∈ rootGroup J hJ,
      (∀ r ∈ rootGroup J hJ, ((MulAut.conj u)⁻¹ * α)⁻¹ r ∈ rootGroup J hJ) ∧
      (∀ t ∈ torusGroup J hJ, ((MulAut.conj u)⁻¹ * α) t ∈ torusGroup J hJ) ∧
      ∀ r : rootGroup J hJ, fstAdd J hJ ⟨((MulAut.conj u)⁻¹ * α) r, hγR r r.2⟩ =
        fstAdd J hJ ⟨α r, hαR r r.2⟩ := by
  obtain ⟨u, huR, huT⟩ := exists_mem_rootGroup_torus_stable J hJ hK hfix hq α hαR
  have hγapp : ∀ g, ((MulAut.conj u)⁻¹ * α) g = u⁻¹ * α g * u := fun g => by
    rw [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
  have hγR : ∀ r ∈ rootGroup J hJ, ((MulAut.conj u)⁻¹ * α) r ∈ rootGroup J hJ := fun r hr => by
    rw [hγapp]
    exact mul_mem (mul_mem (inv_mem huR) (hαR r hr)) huR
  refine ⟨u, huR, hγR, fun r hr => ?_, fun t ht => by rw [hγapp]; exact huT t ht, fun r => ?_⟩
  · have h1 : ((MulAut.conj u)⁻¹ * α)⁻¹ r = α⁻¹ (u * r * u⁻¹) := by
      rw [mul_inv_rev, inv_inv, MulAut.mul_apply, MulAut.conj_apply]
    rw [h1]
    exact hαR' _ (mul_mem (mul_mem huR hr) (inv_mem huR))
  · have h1 : (⟨((MulAut.conj u)⁻¹ * α) r, hγR r r.2⟩ : rootGroup J hJ) =
        ⟨u, huR⟩⁻¹ * ⟨α r, hαR r r.2⟩ * (⟨u, huR⟩⁻¹)⁻¹ := by
      apply Subtype.ext
      simp [hγapp]
    rw [h1, fstAdd_mul_mul_inv]

theorem exists_fstAdd_semilinear (hq : 2 < p ^ f)
    (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hαR : ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ)
    (hαR' : ∀ r ∈ rootGroup J hJ, α⁻¹ r ∈ rootGroup J hJ) :
    ∃ (c : Kˣ) (σ : K ≃+* K), ∀ r : rootGroup J hJ,
      fstAdd J hJ ⟨α r, hαR r r.2⟩ = (c : K) * σ (fstAdd J hJ r) := by
  obtain ⟨u, -, hγR, hγR', hγT, hfst⟩ := exists_torus_correction J hJ hK hfix hq α hαR hαR'
  obtain ⟨c, σ, hrel, -⟩ := exists_semilinear J hJ hK hfix hq _ hγR hγR' hγT
  exact ⟨c, σ, fun r => (hfst r).symm.trans (hrel r)⟩

theorem eq_conj_of_fstAdd_eq (hq : 2 < p ^ f) (hp2 : p ≠ 2)
    (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hαR : ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ)
    (hαR' : ∀ r ∈ rootGroup J hJ, α⁻¹ r ∈ rootGroup J hJ)
    (hfst : ∀ r : rootGroup J hJ, fstAdd J hJ ⟨α r, hαR r r.2⟩ = fstAdd J hJ r) :
    ∃ r ∈ rootGroup J hJ, α = MulAut.conj r := by
  have : CharP K p := charP_of_card Fact.out hK
  obtain ⟨u, huR, hγR, hγR', hγT, hfstγ⟩ := exists_torus_correction J hJ hK hfix hq α hαR hαR'
  set γ := (MulAut.conj u)⁻¹ * α with hγdef
  obtain ⟨c, σ, hrel, hlam⟩ := exists_semilinear J hJ hK hfix hq γ hγR hγR' hγT
  have hγfst : ∀ r : rootGroup J hJ, fstAdd J hJ ⟨γ r, hγR r r.2⟩ = fstAdd J hJ r :=
    fun r => (hfstγ r).trans (hfst r)
  have hcσ : ∀ x : K, (c : K) * σ x = x := by
    intro x
    obtain ⟨r, rfl⟩ := fstAdd_surjective J hJ hK hfix x
    rw [← hrel r, hγfst r]
  have hc1 : (c : K) = 1 := by simpa using hcσ 1
  have hσ1 : ∀ x, σ x = x := fun x => by simpa [hc1] using hcσ x
  have hγT1 : ∀ t ∈ torusGroup J hJ, γ t = t := by
    intro t ht
    obtain ⟨k, rfl⟩ := (mem_torusGroup J hJ).1 ht
    obtain ⟨k', hk'⟩ := (mem_torusGroup J hJ).1 (hγT _ (torus_mem_torusGroup J hJ k))
    have h1 := hlam hk'.symm
    rw [hσ1] at h1
    rw [← hk', torus_eq_of_lamUnit_eq J hJ hK hfix k k' (Units.ext h1)]
  have hδ : ∀ x ∈ rootGroup J hJ, γ x * x⁻¹ ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro x hx
    have h1 : fstAdd J hJ (⟨γ x, hγR x hx⟩ * (⟨x, hx⟩ : rootGroup J hJ)⁻¹) = 0 := by
      rw [fstAdd_mul, fstAdd_inv, hγfst ⟨x, hx⟩, add_neg_cancel]
    exact (fstAdd_eq_zero_iff J hJ hK hfix _).1 h1
  have hcomm : ∀ x ∈ rootGroup J hJ, ∀ y ∈ rootGroup J hJ, Commute (γ x * x⁻¹) y :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hδ x hx).2 y hy).symm
  have hγZ : ∀ z ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      γ z = z := by
    intro z hz
    rw [← commutator_rootGroup J hJ hK hfix] at hz
    have hle : ⁅rootGroup J hJ, rootGroup J hJ⁆ ≤
        γ.toMonoidHom.eqLocus (MonoidHom.id (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show γ ⁅a, b⁆ = ⁅a, b⁆
      have ha' : γ a = (γ a * a⁻¹) * a := by group
      have hb' : γ b = (γ b * b⁻¹) * b := by group
      rw [map_commutatorElement, ha', hb']
      exact commutatorElement_central_mul_central (hcomm a ha a ha) (hcomm a ha b hb)
        (hcomm a ha _ (hδ b hb).1) (hcomm b hb a ha) (hcomm b hb b hb)
    exact hle hz
  have hpow : ∀ x ∈ rootGroup J hJ, ∀ n : ℕ, (γ ^ n) x = (γ x * x⁻¹) ^ n * x := by
    intro x hx n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hγZ _ (hδ x hx), pow_succ,
        mul_assoc, inv_mul_cancel_right]
  have hfixp : ∀ x ∈ rootGroup J hJ, (γ ^ p) x = x := fun x hx => by
    rw [hpow x hx, pow_prime_of_mem_rootGroup J hJ Fact.out hp2 (hδ x hx).1, one_mul]
  obtain ⟨r, hr, hγr⟩ := eq_conj_of_fixes_rootGroup J hJ hK hfix hq (γ ^ p) hfixp
  have hγp : γ ^ p ^ 2 = 1 := by
    rw [sq, pow_mul, hγr, ← map_pow, pow_prime_of_mem_rootGroup J hJ Fact.out hp2 hr, map_one]
  obtain ⟨r', hr', hγr'⟩ := eq_conj_of_pElement J hJ hK hfix hq γ hγp hγR hγT1
  refine ⟨u * r', mul_mem huR hr', ?_⟩
  rw [map_mul, ← hγr', hγdef, mul_inv_cancel_left]

theorem borelMetabelianAt_rootGroup (hq : 2 < p ^ f) (hp2 : p ≠ 2) :
    BorelMetabelianAt (ProjectiveSpecialUnitaryMatrixGroup J) (rootGroup J hJ) := by
  have hinj := mulAutConj_injective_of_center_eq_bot (center_eq_bot J hJ hK hfix hq)
  set G := ProjectiveSpecialUnitaryMatrixGroup J
  set N : Subgroup (MulAut G) := Subgroup.normalizer
    (((rootGroup J hJ).map (MulAut.conj : G →* MulAut G) : Subgroup (MulAut G)) : Set (MulAut G))
  have hR : ∀ α : N, ∀ r ∈ rootGroup J hJ, (α : MulAut G) r ∈ rootGroup J hJ :=
    fun α r hr => (mem_of_mem_normalizer_map_conj hinj α.2).2 hr
  have hR' : ∀ α : N, ∀ r ∈ rootGroup J hJ, (α : MulAut G)⁻¹ r ∈ rootGroup J hJ :=
    fun α r hr => (mem_of_mem_normalizer_map_conj hinj (inv_mem α.2)).2 hr
  choose A hA using fun α => exists_indAdd J hJ hK hfix _ (hR α) (hR' α)
  have hsurj := fstAdd_surjective J hJ hK hfix
  let Ψ : N →* Equiv.Perm K :=
    { toFun := fun α => (A α).toEquiv
      map_one' := Equiv.ext fun x => by
        obtain ⟨r, rfl⟩ := hsurj x
        exact (hA 1 r).trans (congrArg (fstAdd J hJ) (Subtype.ext rfl))
      map_mul' := fun α β => Equiv.ext fun x => by
        obtain ⟨r, rfl⟩ := hsurj x
        change A (α * β) (fstAdd J hJ r) = A α (A β (fstAdd J hJ r))
        rw [hA, hA, hA]
        rfl }
  have hmem : ∀ α, Ψ α ∈ scalarSemilinearPerm K := by
    intro α
    obtain ⟨c, σ, hcσ⟩ := exists_fstAdd_semilinear J hJ hK hfix hq _ (hR α) (hR' α)
    refine ⟨c, σ, fun x => ?_⟩
    obtain ⟨r, rfl⟩ := hsurj x
    exact (hA α r).trans (hcσ r)
  refine borelMetabelianAt_of_hom (Ψ.codRestrict _ hmem)
    (derivedSeries_two_scalarSemilinearPerm K) fun α hα => ?_
  have h1 : ∀ x, A α x = x := fun x =>
    Equiv.ext_iff.1 (congrArg Subtype.val hα : Ψ α = 1) x
  obtain ⟨r, hr, hαr⟩ := eq_conj_of_fstAdd_eq J hJ hK hfix hq hp2 _ (hR α) (hR' α)
    fun r => (hA α r).symm.trans (h1 _)
  exact ⟨r, hr, hαr.symm⟩

end Model

theorem rankOneLieAutFacts_unitary {L : Type} [Group L] [Finite L] {p : ℕ} (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d)) :
    RankOneLieAutFacts p L := by
  have hmodel := UnitaryModel.statedClassicalModel hd h
  obtain ⟨hp, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ := UnitaryModel.exists_equiv_psu hmodel
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, kSylowTI_of_rankOneCoreData (rankOneCoreData_unitary hd h), ?_⟩
  · refine kOutRankLeOne_of_outPChain hp
      (CFSG.RankThree.PartOne.OutStructure.outPNice_PSU_odd hp hmodel ?_).toChain
    intro hdvd
    have h1 : p ∣ p ^ d.1.fieldExponent + 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
    have h2 : p ∣ p ^ d.1.fieldExponent := dvd_pow_self p (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
  · intro U
    obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
    obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
    exact BorelMetabelianAt.of_equiv e' (he'.trans hS)
      (borelMetabelianAt_rootGroup J hJ hK hfix hq hp2)

end CFSG.AGLEmbedding.RankOneAut
