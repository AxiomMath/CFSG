module

public import CFSG.ClassicalInvolution.SmallCases.NobqBender
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverRootData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_4
public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
  CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped commutatorElement

section Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] (J : HermitianForm 3 K)

omit [CharP K 2] in
theorem exists_fixed_ne_zero_ne_one {f : ℕ} (hf : 2 ≤ f)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) :
    ∃ r : K, J.conj r = r ∧ r ≠ 0 ∧ r ≠ 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : 4 ≤ Fintype.card {x : K // J.conj x = x} := by
    rw [← Nat.card_eq_fintype_card, hfixed]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h0 : J.conj (0 : K) = 0 := map_zero _
  have h1 : J.conj (1 : K) = 1 := map_one _
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({⟨0, h0⟩, ⟨1, h1⟩} : Finset {x : K // J.conj x = x})) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  refine ⟨r.1, r.2, fun h => hr.1 (Subtype.ext h), fun h => hr.2 (Subtype.ext h)⟩

theorem not_uniqueInvNormal_unitary_of_mem_root {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {z : ProjectiveSpecialUnitaryMatrixGroup J} (hzQ : z ∈ unitaryCoverRoot J hJ)
    (hz : orderOf z = 2) (N : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ UniqueInvNormal z N := by
  intro h
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  obtain ⟨s, hsN, hss, hs4⟩ := h.exists_sq_eq
  have hs4' : s ^ 4 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs4] at this
  have hsQ : s ∈ unitaryCoverRoot J hJ := by
    have hM := (CFSG.Open.bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ
      (unitaryCoverSylow J f hf hcard hfixed hJ)).1
    have hzM : z ∈ Subgroup.normalizer
        ((unitaryCoverSylow J f hf hcard hfixed hJ :
          Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      Subgroup.le_normalizer (H := (unitaryCoverSylow J f hf hcard hfixed hJ :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) hzQ
    have hsM := centralizer_le_of_fusionStronglyEmbedded hM hzM hz (h.le_centralizer hsN)
    exact mem_sylow_of_mem_normalizer_of_pow_four (unitaryCoverSylow J f hf hcard hfixed hJ) hsM
      hs4'
  let ρ := unitaryCoverRootEquiv J hJ
  set sc : hermitianUnipotentCoord J := ρ.symm ⟨s, hsQ⟩ with hsc
  set zc : hermitianUnipotentCoord J := ρ.symm ⟨z, hzQ⟩ with hzc
  have hzs : zc = sc ^ 2 := by
    rw [hzc, hsc, ← map_pow]
    congr 1
    exact Subtype.ext (by rw [pow_two]; exact hss.symm)
  have hzc0 : zc.1.1 = 0 := by rw [hzs]; exact fst_pow_two J sc
  have hzc2 : zc.1.2 = sc.1.1 * J.conj sc.1.1 := by rw [hzs]; exact snd_pow_two J sc
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have ha : sc.1.1 ≠ 0 := by
    intro ha0
    apply hz1
    have : zc = 1 := coord_ext hzc0 (by rw [hzc2, ha0, zero_mul]; rfl)
    have h2 : (⟨z, hzQ⟩ : unitaryCoverRoot J hJ) = ρ zc := by rw [hzc]; simp
    rw [this, map_one] at h2
    exact congrArg Subtype.val h2
  have hconja : J.conj sc.1.1 ≠ 0 := fun h0 => ha ((map_eq_zero_iff _ J.conj.injective).1 h0)
  obtain ⟨r', hr'fix, hr'0, hr'1⟩ := exists_fixed_ne_zero_ne_one J hf hfixed
  obtain ⟨b₀, hb₀⟩ := huppert_II_10_4_trace_surjective J (2 ^ f) hcard hfixed r' hr'fix
  set c : K := b₀ * sc.1.1 with hc
  have hcfix : J.conj (c * J.conj c) = c * J.conj c := by
    rw [map_mul, J.conj_involutive, mul_comm]
  obtain ⟨d, hd⟩ := huppert_II_10_4_trace_surjective J (2 ^ f) hcard hfixed (c * J.conj c) hcfix
  let gc : hermitianUnipotentCoord J := ⟨(c, d), by
    change d + J.conj d + c * J.conj c = 0
    rw [hd, CharTwo.add_self_eq_zero]⟩
  set g : ProjectiveSpecialUnitaryMatrixGroup J := ((ρ gc : unitaryCoverRoot J hJ) :
    ProjectiveSpecialUnitaryMatrixGroup J) with hg
  have hgz : g ∈ Subgroup.centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg ρ (mul_comm_of_fst_eq_zero J hzc0 gc)
    rw [map_mul, map_mul] at this
    have h2 : (ρ zc : unitaryCoverRoot J hJ) = ⟨z, hzQ⟩ := by rw [hzc]; simp
    rw [h2] at this
    exact congrArg Subtype.val this.symm
  have hconj := h.conj_mem g hgz s hsN
  set xc : hermitianUnipotentCoord J := ⁅gc, sc⁆ with hxc
  have hxL : ((ρ xc : unitaryCoverRoot J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) =
      g * s * g⁻¹ * s⁻¹ := by
    rw [hxc, map_commutatorElement, commutatorElement_def]
    simp [hg, hsc]
  have hxN : ((ρ xc : unitaryCoverRoot J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) ∈ N := by
    rw [hxL]
    exact N.mul_mem hconj (N.inv_mem hsN)
  have hx0 : xc.1.1 = 0 := fst_commutator J gc sc
  have hx2 : xc.1.2 = (sc.1.1 * J.conj sc.1.1) * r' := by
    rw [hxc, snd_commutator J gc sc]
    have : J.conj c = J.conj b₀ * J.conj sc.1.1 := by rw [hc, map_mul]
    show sc.1.1 * J.conj c + c * J.conj sc.1.1 = _
    rw [this, hc, ← hb₀]
    ring
  have hx1 : (ρ xc : unitaryCoverRoot J hJ) ≠ 1 := by
    intro h1
    have : xc = 1 := ρ.injective (h1.trans (map_one ρ).symm)
    have h3 : xc.1.2 = 0 := by rw [this]; rfl
    rw [hx2] at h3
    exact mul_ne_zero (mul_ne_zero ha hconja) hr'0 h3
  have hx1' : ((ρ xc : unitaryCoverRoot J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) ≠ 1 :=
    fun h1 => hx1 (Subtype.ext h1)
  have hxsq : ((ρ xc : unitaryCoverRoot J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) *
      ((ρ xc : unitaryCoverRoot J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) = 1 := by
    have : xc ^ 2 = 1 := (pow_two_eq_one_iff J xc).2 hx0
    have h3 := congrArg (fun y => ((ρ y : unitaryCoverRoot J hJ) :
      ProjectiveSpecialUnitaryMatrixGroup J)) this
    simpa [pow_two] using h3
  have hord : orderOf ((ρ xc : unitaryCoverRoot J hJ) :
      ProjectiveSpecialUnitaryMatrixGroup J) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hx1'
  have hxz := h.eq_of_orderOf_eq_two _ hxN hord
  have hxzc : xc = zc := by
    apply ρ.injective
    rw [hzc]
    simp only [MulEquiv.apply_symm_apply]
    exact Subtype.ext hxz
  have h5 : (sc.1.1 * J.conj sc.1.1) * r' = sc.1.1 * J.conj sc.1.1 := by
    rw [← hx2, ← hzc2, hxzc]
  exact hr'1 (mul_left_cancel₀ (mul_ne_zero ha hconja) (by rw [h5, mul_one]))

theorem noUniqueInvNormal_projectiveSpecialUnitary {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    NoUniqueInvNormal (ProjectiveSpecialUnitaryMatrixGroup J) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  refine NoUniqueInvNormal.of_conj_reps
    {r | r ∈ unitaryCoverRoot J hJ ∧ orderOf r = 2} ?_ ?_
  · intro u hu
    obtain ⟨c, s, hs, hs2, hcs⟩ := CFSG.ClassicalInvolution.exists_conj_mem_sylow_of_orderOf_eq_two
      (unitaryCoverSylow J f hf hcard hfixed hJ) hu
    exact ⟨s, ⟨hs, hs2⟩, c, hcs.symm⟩
  · rintro r ⟨hr, hr2⟩ - N
    exact not_uniqueInvNormal_unitary_of_mem_root J hf hcard hfixed hJ hr hr2 N

end Unitary

section Outer

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.OuterAutomorphisms

theorem isCyclic_outer_unitaryPSU_of_gcd_eq_one {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hg : Nat.gcd n (ℓ ^ f + 1) = 1) : IsCyclic (Outer (unitaryPSU h n)) := by
  classical
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨eT⟩, -, -, -, -, -, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, -, hcardDI, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set I := inner T
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have hDI : D ≤ I := by
    intro x hx
    have h1 : (I.subgroupOf D).index = 1 := by
      rw [Subgroup.index_eq_card]
      exact hcardDI.trans hg
    have h2 : I.subgroupOf D = ⊤ := Subgroup.index_eq_one.1 h1
    have : (⟨x, hx⟩ : D) ∈ I.subgroupOf D := by rw [h2]; trivial
    exact this
  let ψ : Outer T →* (K ≃+* K) := QuotientGroup.lift I (primeFormFieldFactor h hC hn hq)
    (fun x hx => by rw [hFker]; exact hID hx)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, QuotientGroup.lift_mk] at hq'
    have hxD : x ∈ D := by rw [← hFker]; exact hq'
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hDI hxD
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hcycT : IsCyclic (Outer T) := isCyclic_of_injective_hom ψ hψ
  exact isCyclic_of_surjective (equivalence eT).toMonoidHom (equivalence eT).surjective

end Outer

section Model

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.BenderSuzuki

theorem nonempty_mulEquiv_unitaryPSU_of_statedPSU (F : Type) [Group F]
    (h : StatedClassicalModel F .PSU 3 2 2) :
    Nonempty (F ≃* unitaryPSU
      (CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField
        (f := 2) (by norm_num)) 3) := by
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff F 2 le_rfl).1 h
  have hmodel : PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [PSU3Model, CFSG.Theory.Comparator.PSU3Model, CFSG.Open.PSU3]
  exact ⟨(e.trans (MulEquiv.subgroupCongr hmodel)).trans
    ((CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative 2).symm.trans
      (unitaryPSUEquiv _ (by norm_num)).symm)⟩

theorem outTwoCyclic_of_statedPSU (F : Type) [Group F] (h : StatedClassicalModel F .PSU 3 2 2) :
    OutTwoCyclic F := by
  obtain ⟨e⟩ := nonempty_mulEquiv_unitaryPSU_of_statedPSU F h
  have hcyc := isCyclic_outer_unitaryPSU_of_gcd_eq_one
    (CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField
      (f := 2) (by norm_num)) (n := 3) (by norm_num) (by norm_num) (by norm_num)
  exact OutTwoCyclic.of_mulEquiv e fun P _ => Subgroup.isCyclic P

theorem noUniqueInvNormal_of_statedPSU (F : Type) [Group F]
    (h : StatedClassicalModel F .PSU 3 2 2) : NoUniqueInvNormal F := by
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff F 2 le_rfl).1 h
  let J := binaryQuadraticHermitian 2 (by omega)
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 2) 2 2) = (2 ^ 2) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 2 (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 2) 2 2 // J.conj x = x} =
      2 ^ 2 := quadraticBinaryFrobenius_fixed_card 2 (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e'⟩ := projectiveSpecialUnitary_equiv_PSU3Model J 2 le_rfl hJ hEcard hfixed
  have : Fintype (FiniteField.Extension (GaloisField 2 2) 2 2) := Fintype.ofFinite _
  have : CharP (FiniteField.Extension (GaloisField 2 2) 2 2) 2 :=
    charP_of_card_eq_prime_pow (f := 4) (by
      rw [← Nat.card_eq_fintype_card, hEcard]
      norm_num)
  exact NoUniqueInvNormal.of_mulEquiv (e.trans e'.symm)
    (noUniqueInvNormal_projectiveSpecialUnitary J le_rfl hEcard hfixed hJ)

theorem noDatum_of_statedPSU (F : Type) [Group F] (h : StatedClassicalModel F .PSU 3 2 2) :
    NoDatum F :=
  noDatum_of_noUniqueInvNormal (noUniqueInvNormal_of_statedPSU F h) (outTwoCyclic_of_statedPSU F h)

end Model

end CFSG.ClassicalInvolution.Nobq
