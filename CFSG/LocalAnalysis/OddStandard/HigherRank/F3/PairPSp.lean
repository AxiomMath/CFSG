module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockSp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockEquiv

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

section Neg

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def negOneSp (n : ℕ) (K : Type) [Field K] : StatedSp n K :=
  ⟨-1, mem_statedSp_iff.mpr (by simp)⟩

theorem mat_negOneSp : mat n K (negOneSp n K) = -1 := by
  simp [mat_apply, negOneSp]

theorem negOneSp_mem_center : negOneSp n K ∈ center (StatedSp n K) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply mat_injective
  rw [map_mul, map_mul, mat_negOneSp]
  simp

end Neg

section Compl

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def negLongInv (k : Fin n) : StatedSp n K :=
  negOneSp n K * longInv K n k

theorem mat_negLongInv (k : Fin n) :
    mat n K (negLongInv k) = -mat n K (longInv K n k) := by
  rw [negLongInv, map_mul, mat_negOneSp, neg_mul, one_mul]

theorem longInv_mul_self (k : Fin n) : longInv K n k * longInv K n k = 1 := by
  apply mat_injective
  rw [map_mul, mat_longInv, Matrix.diagonal_mul_diagonal, map_one, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem negLongInv_mul_self (k : Fin n) : negLongInv k * negLongInv k = (1 : StatedSp n K) := by
  apply mat_injective
  rw [map_mul, mat_negLongInv, neg_mul_neg, ← map_mul, longInv_mul_self, map_one]

theorem negLongInv_mem_complGroup (k : Fin n) :
    negLongInv k ∈ complGroup (longInv K n k) := by
  intro v hv
  rw [mat_negLongInv, Matrix.neg_mulVec, mem_minusSpace.1 hv, neg_neg]

theorem negLongInv_ne_one (h2 : (2 : K) ≠ 0) {k k' : Fin n} (hk : k' ≠ k) :
    negLongInv k ≠ (1 : StatedSp n K) := by
  intro h
  have h1 := congrFun (congrFun (congrArg (mat n K) h) (Sum.inl k')) (Sum.inl k')
  have hk'' : (Sum.inl k' : Fin n ⊕ Fin n) ∉ coords k := by
    intro h'
    rcases mem_coords.1 h' with h'' | h''
    · exact hk (Sum.inl_injective h'')
    · exact Sum.inl_ne_inr h''
  rw [mat_negLongInv, mat_longInv, map_one] at h1
  simp [Matrix.diagonal_apply_eq, hk''] at h1
  exact h2 (by linear_combination -h1)

theorem orderOf_negLongInv (h2 : (2 : K) ≠ 0) {k k' : Fin n} (hk : k' ≠ k) :
    orderOf (negLongInv k : StatedSp n K) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact negLongInv_mul_self k) (negLongInv_ne_one h2 hk)

theorem comm_of_mem_complGroup_longInv (h2 : (2 : K) ≠ 0) (k : Fin n) {x : StatedSp n K}
    (hx : x ∈ complGroup (longInv K n k)) : x * longInv K n k = longInv K n k * x :=
  ((isLongRootSp2_standard k).commute_of_mem_complGroup h2 (longInv_mem_longRootSp2 k) hx).symm.eq

theorem negLongInv_mem_center (h2 : (2 : K) ≠ 0) (k : Fin n) :
    (⟨negLongInv k, negLongInv_mem_complGroup k⟩ : complGroup (longInv K n k)) ∈
      center (complGroup (longInv K n k)) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  change (x : StatedSp n K) * (negOneSp n K * longInv K n k) =
    (negOneSp n K * longInv K n k) * (x : StatedSp n K)
  have hn : (x : StatedSp n K) * negOneSp n K = negOneSp n K * x :=
    Subgroup.mem_center_iff.mp (negOneSp_mem_center (n := n) (K := K)) (x : StatedSp n K)
  have hz := comm_of_mem_complGroup_longInv h2 k x.2
  calc (x : StatedSp n K) * (negOneSp n K * longInv K n k)
      = ((x : StatedSp n K) * negOneSp n K) * longInv K n k := by rw [mul_assoc]
    _ = negOneSp n K * ((x : StatedSp n K) * longInv K n k) := by rw [hn, mul_assoc]
    _ = negOneSp n K * (longInv K n k * x) := by rw [hz]
    _ = (negOneSp n K * longInv K n k) * x := by rw [mul_assoc]

theorem conj_mem_complGroup_of_commute {i c x : StatedSp n K} (hc : c * i = i * c)
    (hx : x ∈ complGroup i) : c * x * c⁻¹ ∈ complGroup i := by
  have hc' : c⁻¹ * i = i * c⁻¹ := (Commute.inv_left (show Commute c i from hc)).eq
  intro v hv
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mem_complGroup.1 hx _ (mulVec_mem_minusSpace hc' hv), Matrix.mulVec_mulVec, ← map_mul,
    mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem commute_longInv_of_mem_centralizer_negLongInv (k : Fin n) {g : StatedSp n K}
    (hg : g ∈ centralizer ({negLongInv k} : Set (StatedSp n K))) :
    g * longInv K n k = longInv K n k * g := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hn : g * negOneSp n K = negOneSp n K * g :=
    Subgroup.mem_center_iff.mp negOneSp_mem_center g
  rw [negLongInv, ← mul_assoc, hn, mul_assoc, mul_assoc] at h
  exact mul_left_cancel h

theorem normal_complGroup_negLongInv (h2 : (2 : K) ≠ 0) (k : Fin n) :
    ((complGroup (longInv K n k)).subgroupOf
      (centralizer ({negLongInv k} : Set (StatedSp n K)))).Normal := by
  have hle : complGroup (longInv K n k) ≤ centralizer ({negLongInv k} : Set (StatedSp n K)) := by
    intro x hx
    have hn : x * negOneSp n K = negOneSp n K * x :=
      Subgroup.mem_center_iff.mp negOneSp_mem_center x
    rw [Subgroup.mem_centralizer_singleton_iff, negLongInv, ← mul_assoc, hn, mul_assoc,
      comm_of_mem_complGroup_longInv h2 k hx, mul_assoc]
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun g hg => ?_
  have hg' : g * longInv K n k = longInv K n k * g :=
    commute_longInv_of_mem_centralizer_negLongInv k hg
  have hg'' : g⁻¹ * longInv K n k = longInv K n k * g⁻¹ :=
    (Commute.inv_left (show Commute g (longInv K n k) from hg')).eq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_complGroup_of_commute hg', fun hx => ?_⟩
  have h1 := conj_mem_complGroup_of_commute hg'' hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem injective_comp_complGroup (h2 : (2 : K) ≠ 0) (k : Fin n) :
    Function.Injective
      ((QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))).comp
        (complGroup (longInv K n k)).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxs : ((x : StatedSp n K) : GL (Fin n ⊕ Fin n) K) ∈ StatedScalars (Fin n ⊕ Fin n) K :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (x : StatedSp n K)).mp hx)
  obtain ⟨u, hu⟩ := hxs
  have hmat : mat n K (x : StatedSp n K) = Matrix.scalar (Fin n ⊕ Fin n) (u : K) := by
    rw [mat_apply, ← hu, Matrix.GeneralLinearGroup.coe_scalar]
  have hv : (Pi.single (Sum.inl k) (1 : K) : Fin n ⊕ Fin n → K) ∈
      minusSpace (longInv K n k) := by
    rw [mem_minusSpace_longInv h2]
    intro t ht
    exact Pi.single_eq_of_ne (fun h => ht (by rw [h]; exact inl_mem_coords k)) _
  have hfix := congrFun (mem_complGroup.1 x.2 _ hv) (Sum.inl k)
  rw [mulVec_single_one_apply, hmat] at hfix
  have hu1 : (u : K) = 1 := by simpa using hfix
  have hx1 : mat n K (x : StatedSp n K) = 1 := by
    rw [hmat, hu1, map_one]
  exact Subtype.ext (mat_injective (by rw [hx1, Subgroup.coe_one, map_one]))

theorem blockData_complGroup_longInv
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) [Finite K]
    (hK : Nat.card K = 3) {m : ℕ} (hm : 2 ≤ m) (k : Fin (m + 1)) :
    BlockData ↥(complGroup (longInv K (m + 1) k)) := by
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  obtain ⟨e⟩ := nonempty_mulEquiv_complGroup_longInv h2 k
  exact BlockData.of_mulEquiv e (blockData_statedSp hGA hK hm)

end Compl

theorem hasCleanFullClassBMember_psp
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 3) {n : ℕ} (hn : 3 ≤ n)
    [IsSimpleGroup (StatedProj (StatedSp n K))] :
    HasCleanFullClassBMember (StatedProj (StatedSp n K)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  set k : Fin (m + 1) := 0 with hk
  have hk' : (⟨1, by omega⟩ : Fin (m + 1)) ≠ k := fun h =>
    absurd (congrArg Fin.val h) (by simp [hk])
  haveI : Finite ↥(complGroup (longInv K (m + 1) k)) := inferInstance
  haveI : Finite (StatedProj (StatedSp (m + 1) K)) := inferInstance
  refine hasCleanFullClassBMember_of_block
    (QuotientGroup.mk' ((StatedScalars (Fin (m + 1) ⊕ Fin (m + 1)) K).subgroupOf
      (StatedSp (m + 1) K))) (QuotientGroup.mk'_surjective _) ?_
    (complGroup (longInv K (m + 1) k)).subtype (injective_comp_complGroup h2 k)
    (c := ⟨negLongInv k, negLongInv_mem_complGroup k⟩) ?_ (negLongInv_mem_center h2 k) ?_
    (blockData_complGroup_longInv hGA hK (by omega) k)
  · rw [QuotientGroup.ker_mk', LieType.Universal.Symplectic.center_eq]
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_negLongInv h2 hk'
  · rw [Subgroup.range_subtype]
    exact normal_complGroup_negLongInv h2 k

theorem hasCleanFullClassBMember_of_lieModel_psp
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q] {n : ℕ} (hn : 3 ≤ n)
    (h : CFSG.Blueprint.LieModel Q .PSp n 3 1) : HasCleanFullClassBMember Q := by
  have hcm := h.statedClassicalModel (by decide)
  unfold CFSG.Open.StatedClassicalModel at hcm
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hcm
  have hK : Nat.card K = 3 := by simpa using hKcard
  haveI : IsSimpleGroup (StatedProj (StatedSp n K)) := e.symm.isSimpleGroup
  exact HasCleanFullClassBMember.of_mulEquiv e.symm (hasCleanFullClassBMember_psp hGA hK hn)

end CFSG.OddStandard.HigherRank.F3
