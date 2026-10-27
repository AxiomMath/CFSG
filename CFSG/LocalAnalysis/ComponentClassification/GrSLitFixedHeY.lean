module

public import CFSG.Sporadic.HeldB.OuterCentQS
public import CFSG.Adapters.GorensteinWalter
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitProd
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

theorem exists_sylow_dihedral_eight {M : Type*} [Group M] [Finite M] {Y : Subgroup M} {x y : M}
    (hxY : x ∈ Y) (hyY : y ∈ Y) (h4 : x ^ 4 = 1) (hord : orderOf x = 4) (hy : y * y = 1)
    (hrel : y * x * y⁻¹ = x⁻¹) (hnot : y ∉ zpowers x) (hfac : (Nat.card Y).factorization 2 = 3) :
    ∃ P : Sylow 2 ↥Y, Nonempty ((P : Subgroup ↥Y) ≃* DihedralGroup (2 ^ (3 - 1))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := HSFLit.injective_dihedralLift 4 x y h4 hy hrel hord hnot
  have hrange := HSFLit.range_dihedralLift 4 x y h4 hy hrel
  set D := zpowers x ⊔ zpowers y with hD
  have hDY : D ≤ Y := sup_le (zpowers_le.mpr hxY) (zpowers_le.mpr hyY)
  have hDcard : Nat.card D = 8 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, DihedralGroup.nat_card]
  have hcard : Nat.card (D.subgroupOf Y) = 2 ^ (Nat.card Y).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv, hDcard, hfac]
    norm_num
  refine ⟨Sylow.ofCard _ hcard, ⟨?_⟩⟩
  exact (subgroupOfEquivOfLe hDY).trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm

theorem ordA_one_ne_2520 {q : ℕ} (hq : 1 ≤ q) : Open.ordA 1 q ≠ 2520 := by
  intro h
  by_cases h18 : 18 ≤ q
  · have hg : Nat.gcd (1 + 1) (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hpos : 0 < Nat.gcd (1 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hprod : q ^ (1 * (1 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (1 + 1), (q ^ i - 1) =
        q * (q ^ 2 - 1) := by
      simp
    have h1 : 5814 ≤ q * (q ^ 2 - 1) := by
      have : 323 ≤ q ^ 2 - 1 := by
        have : 324 ≤ q ^ 2 := by nlinarith
        omega
      nlinarith
    unfold Open.ordA at h
    rw [hprod] at h
    have h2 : q * (q ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / Nat.gcd (1 + 1) (q - 1) :=
      Nat.div_le_div_left hg hpos
    omega
  · push Not at h18
    interval_cases q <;> simp_all [Open.ordA]

@[expose] def heUA (j : ℕ) : Array ℕ := heUpsilon.getD j #[]

theorem tabRep_heUA {j : ℕ} (hj : j < 3) : TabRep (heUA j) (heUpsP j) := by
  refine ⟨?_, rep_heUps hj⟩
  interval_cases j <;> decide

@[expose] def heYy : Equiv.Perm (Fin 35) :=
  heUpsP 2 * heUpsP 2 * heUpsP 2 * heUpsP 1 * heUpsP 2 * heUpsP 2 * heUpsP 0 * heUpsP 2

@[expose] def heYyT : Tab :=
  comp 35 (comp 35 (comp 35 (comp 35 (comp 35 (comp 35 (comp 35 (heUA 2) (heUA 2)) (heUA 2))
    (heUA 1)) (heUA 2)) (heUA 2)) (heUA 0)) (heUA 2)

theorem tabRep_heYy : TabRep heYyT heYy := by
  have h0 := tabRep_heUA (j := 0) (by norm_num)
  have h1 := tabRep_heUA (j := 1) (by norm_num)
  have h2 := tabRep_heUA (j := 2) (by norm_num)
  exact ((((((h2.comp h2).comp h2).comp h1).comp h2).comp h2).comp h0).comp h2

theorem heY_facts :
    comp 35 (heUA 0) (comp 35 (heUA 0) (comp 35 (heUA 0) (heUA 0))) = idTab 35 ∧
      comp 35 (heUA 0) (heUA 0) ≠ idTab 35 ∧ comp 35 heYyT heYyT = idTab 35 ∧
      comp 35 (comp 35 heYyT (heUA 0)) heYyT = comp 35 (heUA 0) (comp 35 (heUA 0) (heUA 0)) ∧
      heYyT ≠ idTab 35 ∧ heYyT ≠ heUA 0 ∧ heYyT ≠ comp 35 (heUA 0) (heUA 0) ∧
      heYyT ≠ comp 35 (heUA 0) (comp 35 (heUA 0) (heUA 0)) := by
  decide

theorem heY_relations : heUpsP 0 ^ 4 = 1 ∧ orderOf (heUpsP 0) = 4 ∧ heYy * heYy = 1 ∧
    heYy * heUpsP 0 * heYy⁻¹ = (heUpsP 0)⁻¹ ∧ heYy ∉ zpowers (heUpsP 0) := by
  obtain ⟨h4, h2, hyy, hinv, hy0, hy1, hy2, hy3⟩ := heY_facts
  have hx := tabRep_heUA (j := 0) (by norm_num)
  have hx2 := hx.comp hx
  have hx3 := hx.comp hx2
  have hx4 := hx.comp hx3
  have hy := tabRep_heYy
  have hp4 : heUpsP 0 ^ 4 = 1 := by
    rw [show heUpsP 0 ^ 4 = heUpsP 0 * (heUpsP 0 * (heUpsP 0 * heUpsP 0)) by
      simp only [pow_succ', pow_zero, mul_one]]
    exact (hx4.eq_iff TabRep.idTab).mp h4
  have hp2 : heUpsP 0 ^ 2 ≠ 1 := by
    rw [pow_two]
    exact fun h => h2 ((hx2.eq_iff TabRep.idTab).mpr h)
  have hord : orderOf (heUpsP 0) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := heUpsP 0) (by simpa using hp2)
      (by simpa using hp4)
    simpa using this
  have hyy' : heYy * heYy = 1 := ((hy.comp hy).eq_iff TabRep.idTab).mp hyy
  have hyinv : heYy⁻¹ = heYy := inv_eq_of_mul_eq_one_right hyy'
  have hrel : heYy * heUpsP 0 * heYy⁻¹ = (heUpsP 0)⁻¹ := by
    rw [hyinv]
    have h1 : heYy * heUpsP 0 * heYy = heUpsP 0 * (heUpsP 0 * heUpsP 0) :=
      (((hy.comp hx).comp hy).eq_iff hx3).mp hinv
    rw [h1, eq_inv_iff_mul_eq_one]
    calc heUpsP 0 * (heUpsP 0 * heUpsP 0) * heUpsP 0 = heUpsP 0 ^ 4 := by
          simp only [pow_succ', pow_zero, mul_one, mul_assoc]
      _ = 1 := hp4
  refine ⟨hp4, hord, hyy', hrel, fun hmem => ?_⟩
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hkx⟩ := hmem
  interval_cases k
  · exact hy0 ((hy.eq_iff TabRep.idTab).mpr (by simpa using hkx.symm))
  · exact hy1 ((hy.eq_iff hx).mpr (by simpa using hkx.symm))
  · exact hy2 ((hy.eq_iff hx2).mpr (by rw [← hkx, pow_two]))
  · exact hy3 ((hy.eq_iff hx3).mpr (by rw [← hkx]; simp only [pow_succ', pow_zero, mul_one]))

theorem heUpsP_mem_heQY {j : ℕ} (hj : j < 3) : heUpsP j ∈ heQY.originalSubgroup := by
  rw [heQY_eq]
  apply Subgroup.subset_closure
  interval_cases j <;> simp

theorem heYy_mem_heQY : heYy ∈ heQY.originalSubgroup := by
  have h0 := heUpsP_mem_heQY (j := 0) (by norm_num)
  have h1 := heUpsP_mem_heQY (j := 1) (by norm_num)
  have h2 := heUpsP_mem_heQY (j := 2) (by norm_num)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h2 h2) h2) h1) h2) h2) h0) h2

theorem isSimpleGroup_heQY : IsSimpleGroup heQY.originalSubgroup :=
  @MulEquiv.isSimpleGroup _ _ _ _ heOuterQuot_simple heOuterQuotEquiv.symm

theorem exists_mul_ne_heQY : ∃ a b : heQY.originalSubgroup, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := heOuterQuot_nonabelian
  exact ⟨heOuterQuotEquiv a, heOuterQuotEquiv b,
    fun h => hab (heOuterQuotEquiv.injective (by rw [map_mul, map_mul, h]))⟩

theorem nonempty_heQY_equiv_alternatingGroup :
    Nonempty (heQY.originalSubgroup ≃* alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup heQY.originalSubgroup := isSimpleGroup_heQY
  have hfac : (Nat.card heQY.originalSubgroup).factorization 2 = 3 := by
    rw [card_heQY, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨h4, hord, hyy, hrel, hnot⟩ := heY_relations
  obtain ⟨P, ⟨e⟩⟩ := exists_sylow_dihedral_eight (heUpsP_mem_heQY (by norm_num)) heYy_mem_heQY
    h4 hord hyy hrel hnot hfac
  rcases Adapters.dihedral_simple_recognition _ exists_mul_ne_heQY P 3 (by norm_num) ⟨e⟩ with
    ⟨p, f, hp, hp2, -, hmodel⟩ | h7
  · exfalso
    have hcard := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hmodel).1 rfl
    rw [card_heQY] at hcard
    exact ordA_one_ne_2520 (Nat.one_le_pow _ _ hp.pos) hcard.symm
  · exact h7

theorem nonempty_heOuterQuot_equiv_alternatingGroup :
    Nonempty (heOuterD ⧸ center heOuterD ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := nonempty_heQY_equiv_alternatingGroup
  exact ⟨heOuterQuotEquiv.trans e⟩

end CFSG.ComponentClassification.GrSLit
