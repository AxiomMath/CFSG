module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusU3Model
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.CyclicCriterion

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.AGLEmbedding.UnitaryModel

theorem eq_of_mem_of_odd_normal_of_isCyclic_quotient {N : Type*} [Group N]
    {R : Subgroup N} [R.Normal] (hodd : Odd (Nat.card R)) (hcyc : IsCyclic (N ⧸ R))
    {a b : N} (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a * b = b * a) :
    a = 1 ∨ b = 1 ∨ a = b := by
  have hsq : ∀ x : N, x ^ 2 = 1 → x ∈ R → x = 1 := by
    intro x hx2 hxR
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hcard : orderOf x ∣ Nat.card R := by
      rw [← Subgroup.orderOf_mk x hxR]
      exact orderOf_dvd_natCard _
    have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hodd hcard
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  by_cases hqa1 : (a : N ⧸ R) = 1
  · exact Or.inl (hsq a ha2 ((QuotientGroup.eq_one_iff a).mp hqa1))
  by_cases hqb1 : (b : N ⧸ R) = 1
  · exact Or.inr (Or.inl (hsq b hb2 ((QuotientGroup.eq_one_iff b).mp hqb1)))
  · right; right
    have hq : (a : N ⧸ R) = (b : N ⧸ R) :=
      CFSG.RankTwoShapes.eq_of_sq_eq_one_of_isCyclic (G := N ⧸ R)
        (by rw [← QuotientGroup.mk_pow, ha2, QuotientGroup.mk_one]) hqa1
        (by rw [← QuotientGroup.mk_pow, hb2, QuotientGroup.mk_one]) hqb1
    have hinv : a⁻¹ * b ∈ R := (QuotientGroup.eq).mp hq
    have ha2' : a * a = 1 := by rwa [pow_two] at ha2
    have hb2' : b * b = 1 := by rwa [pow_two] at hb2
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2'
    have hmem : a * b ∈ R := by rwa [hainv] at hinv
    have hcomm : Commute a b := hab
    have hsq_ab : (a * b) ^ 2 = 1 := by rw [hcomm.mul_pow, ha2, hb2, mul_one]
    have hab1 : a * b = 1 := hsq (a * b) hsq_ab hmem
    calc a = a * (b * b) := by rw [hb2', mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = 1 * b := by rw [hab1]
      _ = b := one_mul b

private theorem isCyclic_normalizer_rootGroup_quotient {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hq : 2 < p ^ f) :
    IsCyclic (Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ⧸
      (rootGroup J hJ).subgroupOf
        (Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) := by
  classical
  set N : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Subgroup.normalizer (rootGroup J hJ : Set _) with hNdef
  have hsup : N = rootGroup J hJ ⊔ torusGroup J hJ :=
    (CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.normalizer_rootGroup_eq_sup
      J hJ hK hfix hq).1
  have hTN : torusGroup J hJ ≤ N := by rw [hsup]; exact le_sup_right
  let R' : Subgroup N := (rootGroup J hJ).subgroupOf N
  let T' : Subgroup N := (torusGroup J hJ).subgroupOf N
  have htop : R' ⊔ T' = ⊤ := by
    have h := (Subgroup.subgroupOf_sup (Subgroup.le_normalizer (H := rootGroup J hJ)) hTN).symm
    rw [show R' ⊔ T' = (rootGroup J hJ ⊔ torusGroup J hJ).subgroupOf N from h, ← hsup,
      Subgroup.subgroupOf_self]
  letI : R'.Normal := Subgroup.normal_in_normalizer
  haveI : IsCyclic ↥(torusGroup J hJ) :=
    (CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.normalizer_rootGroup_eq_sup
      J hJ hK hfix hq).2
  have hTcyc : IsCyclic T' := by
    have e := Subgroup.subgroupOfEquivOfLe hTN
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  haveI hcyc : IsCyclic (N ⧸ R') :=
    CFSG.quotient_isCyclic_of_sup_cyclic_right htop hTcyc
  exact hcyc

private theorem eq_of_mem_normalizer_rootGroup_of_commute {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 2 < p ^ f) {a b : ProjectiveSpecialUnitaryMatrixGroup J}
    (ha : a ∈ Subgroup.normalizer (rootGroup J hJ : Set _))
    (hb : b ∈ Subgroup.normalizer (rootGroup J hJ : Set _))
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a * b = b * a) :
    a = 1 ∨ b = 1 ∨ a = b := by
  classical
  set N : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Subgroup.normalizer (rootGroup J hJ : Set _) with hNdef
  let R' : Subgroup N := (rootGroup J hJ).subgroupOf N
  letI : R'.Normal := Subgroup.normal_in_normalizer
  have hR'card : Nat.card R' = p ^ (3 * f) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H :=
      rootGroup J hJ))).toEquiv, card_rootGroup_eq J hJ hK hfix]
  have hpodd : Odd p := (hp.eq_two_or_odd').resolve_left hp2
  have hodd : Odd (Nat.card R') := hR'card ▸ Odd.pow hpodd
  have hcyc := isCyclic_normalizer_rootGroup_quotient J hJ hK hfix hq
  have h := eq_of_mem_of_odd_normal_of_isCyclic_quotient (N := N) (R := R') hodd hcyc
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (Subtype.ext (by simpa using ha2)) (Subtype.ext (by simpa using hb2))
    (Subtype.ext (by simpa using hab))
  rcases h with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (congrArg Subtype.val h))

theorem eq_of_mem_normalizer_sylow_unitary {L : Type} [Group L] [Finite L] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (h : Nonempty (L ≃* CFSG.AGLEmbedding.CatGroup d)) (U : Sylow p L) {a b : L}
    (ha : a ∈ Subgroup.normalizer ((U : Subgroup L) : Set L))
    (hb : b ∈ Subgroup.normalizer ((U : Subgroup L) : Set L))
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a * b = b * a) : a = 1 ∨ b = 1 ∨ a = b := by
  obtain ⟨hp, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    exists_equiv_psu (statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have ha' : e' a ∈ Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [← hN]
    exact Subgroup.mem_map_of_mem e'.toMonoidHom ha
  have hb' : e' b ∈ Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [← hN]
    exact Subgroup.mem_map_of_mem e'.toMonoidHom hb
  have ha2' : (e' a) ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have hb2' : (e' b) ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have hab' : e' a * e' b = e' b * e' a := by rw [← map_mul, ← map_mul, hab]
  have hres := eq_of_mem_normalizer_rootGroup_of_commute J hJ hK hfix hp hp2 hq
    ha' hb' ha2' hb2' hab'
  rcases hres with h1 | h1 | h1
  · exact Or.inl (e'.injective (by rw [h1, map_one]))
  · exact Or.inr (Or.inl (e'.injective (by rw [h1, map_one])))
  · exact Or.inr (Or.inr (e'.injective h1))

theorem card_normalizer_sylow_unitary_dvd {L : Type} [Group L] [Finite L] {p : ℕ}
    [Fact p.Prime] {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (h : Nonempty (L ≃* CFSG.AGLEmbedding.CatGroup d)) (U : Sylow p L) :
    Nat.card (Subgroup.normalizer ((U : Subgroup L) : Set L)) ∣
      (p ^ d.1.fieldExponent) ^ 3 * ((p ^ d.1.fieldExponent) ^ 2 - 1) := by
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    exists_equiv_psu (statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have hsup : Subgroup.normalizer (rootGroup J hJ : Set _) =
      rootGroup J hJ ⊔ torusGroup J hJ :=
    (CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.normalizer_rootGroup_eq_sup
      J hJ hK hfix hq).1
  have hdisj : Disjoint (rootGroup J hJ) (torusGroup J hJ) := by
    have hD : Disjoint (rootGroup J hJ)
        (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pzero J hJ)) :=
      rootGroup_disjoint_stabilizer_pzero J hJ
    exact hD.mono_right (torusGroup_le_stabilizer_pzero J hJ)
  have hcs := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (A := rootGroup J hJ) (B := torusGroup J hJ)
    (torusGroup_le_normalizer_rootGroup J hJ) hdisj
  have hcard : Nat.card (Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) =
      (p ^ d.1.fieldExponent) ^ 3 *
        (((p ^ d.1.fieldExponent) ^ 2 - 1) / Nat.gcd (p ^ d.1.fieldExponent + 1) 3) := by
    rw [hsup, hcs, card_rootGroup J hJ (p ^ d.1.fieldExponent) hK hfix,
      card_torusGroup J hJ (p ^ d.1.fieldExponent) hK hfix]
  rw [← Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hN, hcard]
  refine Nat.mul_dvd_mul_left _ (Nat.div_dvd_of_dvd ?_)
  exact (Nat.gcd_dvd_left (p ^ d.1.fieldExponent + 1) 3).trans
    (succ_dvd_sq_sub_one (p ^ d.1.fieldExponent))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
