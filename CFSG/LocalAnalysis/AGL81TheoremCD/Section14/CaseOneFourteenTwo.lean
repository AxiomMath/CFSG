module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChainNine
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTwoSingle
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTwoDouble
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoSL34
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open scoped commutatorElement Pointwise
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

private theorem two_kComp_fac_le {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    {J' : Subgroup G} (hK' : IsKComp M H J')
    (hinfcard : Nat.card ↥((Q ⊓ J) ⊓ (Q ⊓ J')) = 3)
    (hcardT₁ : Nat.card ↥(Q ⊓ J) = 27) (hcardT₂ : Nat.card ↥(Q ⊓ J') = 27)
    (hT₁syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J) J)
    (hT₂syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J') J') :
    (Nat.card ↥(J ⊔ J')).factorization 3 ≤ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfacJ : (Nat.card ↥J).factorization 3 = 3 := by
    have h1 : 3 ^ (Nat.card ↥J).factorization 3 = 3 ^ 3 := by
      rw [← hT₁syl.card_eq, hcardT₁]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hfacJ' : (Nat.card ↥J').factorization 3 = 3 := by
    have h1 : 3 ^ (Nat.card ↥J').factorization 3 = 3 ^ 3 := by
      rw [← hT₂syl.card_eq, hcardT₂]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hcard_sup : Nat.card ↥(J ⊔ J') * Nat.card ↥(J ⊓ J') = Nat.card ↥J * Nat.card ↥J' :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := J) (K := J')
      (h.isKComp.1.trans (h.kSub_le_normalizer_of_isKComp hpre hU hK'))
  have hdvd : 3 ∣ Nat.card ↥(J ⊓ J') := by
    have hle : (Q ⊓ J) ⊓ (Q ⊓ J') ≤ J ⊓ J' :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have h := Subgroup.card_dvd_of_le hle
    rwa [hinfcard] at h
  have hfac_mul : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
      (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
    intro a b ha hb
    rw [Nat.factorization_mul ha hb]
    simp
  have hfac_eq : (Nat.card ↥(J ⊔ J')).factorization 3 +
      (Nat.card ↥(J ⊓ J')).factorization 3 = 6 := by
    rw [← hfac_mul (Nat.card ↥(J ⊔ J')) (Nat.card ↥(J ⊓ J')) (Nat.card_pos.ne')
        (Nat.card_pos.ne'),
      hcard_sup, hfac_mul (Nat.card ↥J) (Nat.card ↥J') (Nat.card_pos.ne') (Nat.card_pos.ne'),
      hfacJ, hfacJ']
  have hc1 : 1 ≤ (Nat.card ↥(J ⊓ J')).factorization 3 := by
    have h3 : 3 ^ 1 ∣ Nat.card ↥(J ⊓ J') := by
      rw [pow_one]
      exact hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos.ne')).mp h3
  omega

private theorem two_kComp_card_le {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    {J' : Subgroup G} (hK' : IsKComp M H J') (hsup : kSub 3 M H = J ⊔ J')
    (hEsub : E ≤ (Q ⊓ J) ⊔ (Q ⊓ J'))
    (hinfcard : Nat.card ↥((Q ⊓ J) ⊓ (Q ⊓ J')) = 3)
    (hcardT₁ : Nat.card ↥(Q ⊓ J) = 27) (hcardT₂ : Nat.card ↥(Q ⊓ J') = 27)
    (hT₁syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J) J)
    (hT₂syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J') J') :
    Nat.card ↥Q ≤ 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQle_sup : Q ≤ J ⊔ J' := by
    have h1 : Q ≤ kSub 3 M H ⊔ E := h.sylow.le
    rw [hsup] at h1
    have hE : E ≤ J ⊔ J' :=
      hEsub.trans (sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right))
    calc Q ≤ (J ⊔ J') ⊔ E := h1
      _ = J ⊔ J' := sup_eq_left.mpr hE
  obtain ⟨k, hk⟩ := h.sylow.isPGroup.exists_card_eq
  have hk5 : k ≤ 5 := by
    have h1 : 3 ^ k ∣ Nat.card ↥(J ⊔ J') := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hQle_sup
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos.ne')).mp h1
    have h3 := two_kComp_fac_le h hpre hU hK' hinfcard hcardT₁ hcardT₂ hT₁syl hT₂syl
    omega
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk5

private theorem two_kComp_sup_eq {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    {J' : Subgroup G} (hK' : IsKComp M H J') (hsup : kSub 3 M H = J ⊔ J')
    (hcard : Nat.card ↥((Q ⊓ J) ⊔ (Q ⊓ J')) = 3 ^ 5)
    (hEsub : E ≤ (Q ⊓ J) ⊔ (Q ⊓ J'))
    (hinfcard : Nat.card ↥((Q ⊓ J) ⊓ (Q ⊓ J')) = 3)
    (hcardT₁ : Nat.card ↥(Q ⊓ J) = 27) (hcardT₂ : Nat.card ↥(Q ⊓ J') = 27)
    (hT₁syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J) J)
    (hT₂syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J') J') :
    Q = (Q ⊓ J) ⊔ (Q ⊓ J') := by
  have hTsup_le : (Q ⊓ J) ⊔ (Q ⊓ J') ≤ Q := sup_le inf_le_left inf_le_left
  have hcardle : Nat.card ↥Q ≤ Nat.card ↥((Q ⊓ J) ⊔ (Q ⊓ J')) := by
    rw [hcard]
    exact two_kComp_card_le h hpre hU hK' hsup hEsub hinfcard hcardT₁ hcardT₂ hT₁syl hT₂syl
  exact (Subgroup.eq_of_le_of_card_ge hTsup_le hcardle).symm

private theorem two_kComp_Z {Q T₁ T₂ Z : Subgroup G} (hQeq : Q = T₁ ⊔ T₂)
    (hAB : ⁅T₁, T₂⁆ = ⊥) (hinf : T₁ ⊓ T₂ = Z)
    (hZdef : Z = (Subgroup.center ↥T₁).map T₁.subtype)
    (hZcard : Nat.card ↥Z = 3)
    (hZcard₂ : Nat.card ↥((Subgroup.center ↥T₂).map T₂.subtype) = 3) :
    (Subgroup.center ↥T₂).map T₂.subtype = Z ∧ ∀ z ∈ Z, ∀ q ∈ Q, Commute z q := by
  have hTcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, Commute a b := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB ha) b hb)).symm
  have hZeqT₂ : (Subgroup.center ↥T₂).map T₂.subtype = Z := by
    have hle : T₁ ⊓ T₂ ≤ (Subgroup.center ↥T₂).map T₂.subtype := by
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hx₂⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hTcomm x hx₁ (y : G) y.2).symm
    have h1 := Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard₂, hinf, hZcard])
    exact h1.symm.trans hinf
  have hZcentT₁ : ∀ z ∈ Z, ∀ a ∈ T₁, Commute z a := by
    intro z hz a ha
    rw [hZdef] at hz
    obtain ⟨z₀, hz₀, hz₀z⟩ := Subgroup.mem_map.mp hz
    rw [← hz₀z]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀ ⟨a, ha⟩)).symm
  have hZcentT₂ : ∀ z ∈ Z, ∀ b ∈ T₂, Commute z b := by
    intro z hz b hb
    have hzb : z ∈ (Subgroup.center ↥T₂).map T₂.subtype := by
      have h := hz
      rw [← hZeqT₂] at h
      exact h
    obtain ⟨z₀, hz₀, hz₀z⟩ := Subgroup.mem_map.mp hzb
    rw [← hz₀z]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀ ⟨b, hb⟩)).symm
  refine ⟨hZeqT₂, ?_⟩
  intro z hz q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hTcomm).mp (hQeq ▸ hq)
  exact (hZcentT₁ z hz a ha).mul_right (hZcentT₂ z hz b hb)

private theorem two_kComp_commutator {Q T₁ T₂ Z : Subgroup G} (hQeq : Q = T₁ ⊔ T₂)
    (hAB : ⁅T₁, T₂⁆ = ⊥) (hZdef : Z = (Subgroup.center ↥T₁).map T₁.subtype)
    (hZeqT₂ : (Subgroup.center ↥T₂).map T₂.subtype = Z)
    (hZcentral : ∀ z ∈ Z, ∀ q ∈ Q, Commute z q)
    (hcardT₁ : Nat.card ↥T₁ = 27) (hcardT₂ : Nat.card ↥T₂ = 27)
    (hZcard : Nat.card ↥Z = 3)
    (hZcard₂ : Nat.card ↥((Subgroup.center ↥T₂).map T₂.subtype) = 3) :
    ⁅Q, Q⁆ = Z := by
  have hTcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, Commute a b := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB ha) b hb)).symm
  have hT₁comm : ⁅T₁, T₁⁆ = Z :=
    (commutator_eq_center_map_of_card_27 hcardT₁
      (exists_mul_ne_of_card_center_lt hcardT₁ (by rw [← hZdef]; exact hZcard))).trans hZdef.symm
  have hT₂comm : ⁅T₂, T₂⁆ = Z :=
    (commutator_eq_center_map_of_card_27 hcardT₂
      (exists_mul_ne_of_card_center_lt hcardT₂ hZcard₂)).trans hZeqT₂
  have hZleQQ : Z ≤ ⁅Q, Q⁆ := by
    rw [← hT₁comm]
    have hT₁Q : T₁ ≤ Q := by rw [hQeq]; exact le_sup_left
    exact Subgroup.commutator_mono hT₁Q hT₁Q
  have hQQ_le : ⁅Q, Q⁆ ≤ Z := by
    rw [hQeq]
    refine commutator_sup_le_of_commute_le hTcomm (le_of_eq hT₁comm) (le_of_eq hT₂comm) ?_
    intro z hz q hq
    exact hZcentral z hz q (hQeq.symm ▸ hq)
  exact le_antisymm hQQ_le hZleQQ

private theorem two_kComp_center_le {Q T₁ T₂ Z : Subgroup G} (hQeq : Q = T₁ ⊔ T₂)
    (hAB : ⁅T₁, T₂⁆ = ⊥) (hinf : T₁ ⊓ T₂ = Z)
    (hZdef : Z = (Subgroup.center ↥T₁).map T₁.subtype)
    (hZeqT₂ : (Subgroup.center ↥T₂).map T₂.subtype = Z) :
    Subgroup.center ↥Q ≤ Z.subgroupOf Q := by
  have hTcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, Commute a b := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB ha) b hb)).symm
  have hZleT₁ : Z ≤ T₁ := hinf ▸ inf_le_left
  have hZleT₂ : Z ≤ T₂ := hinf ▸ inf_le_right
  have hT₁Q : T₁ ≤ Q := by rw [hQeq]; exact le_sup_left
  have hT₂Q : T₂ ≤ Q := by rw [hQeq]; exact le_sup_right
  intro z hz
  have hzc : ∀ y ∈ Q, (z : G) * y = y * (z : G) := by
    intro y hy
    have h := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
    exact congrArg Subtype.val h.symm
  have hzQ : (z : G) ∈ T₁ ⊔ T₂ := by
    rw [← hQeq]
    exact z.2
  obtain ⟨a, ha, b, hb, hzab⟩ := (CFSG.mem_sup_of_commute hTcomm).mp hzQ
  have hcommz : ∀ y ∈ Q, a * b * y = y * (a * b) := by
    intro y hy
    rw [hzab]
    exact hzc y hy
  have haZ : a ∈ Z := by
    rw [hZdef]
    refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro y
    have hby : (y : G) * b = b * (y : G) := hTcomm (y : G) y.2 b hb
    have h1 : (a * (y : G)) * b = ((y : G) * a) * b := by
      calc (a * (y : G)) * b = a * ((y : G) * b) := by rw [mul_assoc]
        _ = a * (b * (y : G)) := by rw [hby]
        _ = a * b * (y : G) := by rw [mul_assoc]
        _ = (y : G) * (a * b) := hcommz (y : G) (hT₁Q y.2)
        _ = ((y : G) * a) * b := by rw [mul_assoc]
    exact Subtype.ext (mul_right_cancel h1).symm
  have hbz : b ∈ Z := by
    have hbz' : b ∈ (Subgroup.center ↥T₂).map T₂.subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨b, hb⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
      intro y
      have hay : (y : G) * a = a * (y : G) := (hTcomm a ha (y : G) y.2).eq.symm
      have h1 : a * (b * (y : G)) = a * ((y : G) * b) := by
        calc a * (b * (y : G)) = a * b * (y : G) := by rw [mul_assoc]
          _ = (y : G) * (a * b) := hcommz (y : G) (hT₂Q y.2)
          _ = ((y : G) * a) * b := by rw [mul_assoc]
          _ = (a * (y : G)) * b := by rw [hay]
          _ = a * ((y : G) * b) := by rw [mul_assoc]
      exact Subtype.ext (mul_left_cancel h1).symm
    rwa [hZeqT₂] at hbz'
  have hzT₁ : (z : G) ∈ T₁ := by
    have hmem : a * b ∈ T₁ := T₁.mul_mem ha (hZleT₁ hbz)
    rwa [hzab] at hmem
  have hzT₂ : (z : G) ∈ T₂ := by
    have hmem : a * b ∈ T₂ := T₂.mul_mem (hZleT₂ haZ) hb
    rwa [hzab] at hmem
  exact Subgroup.mem_subgroupOf.mpr (hinf ▸ Subgroup.mem_inf.mpr ⟨hzT₁, hzT₂⟩)

private theorem two_kComp_center_eq {Q T₁ T₂ Z : Subgroup G} (hQeq : Q = T₁ ⊔ T₂)
    (hinf : T₁ ⊓ T₂ = Z) (hcenter_le : Subgroup.center ↥Q ≤ Z.subgroupOf Q)
    (hZcentral : ∀ z ∈ Z, ∀ q ∈ Q, Commute z q) :
    (Subgroup.center ↥Q).map Q.subtype = Z ∧ Z ≤ T₂ := by
  have hZleT₁ : Z ≤ T₁ := hinf ▸ inf_le_left
  have hT₁Q : T₁ ≤ Q := by rw [hQeq]; exact le_sup_left
  have hZleQ : Z ≤ Q := hZleT₁.trans hT₁Q
  refine ⟨le_antisymm ?_ ?_, hinf ▸ inf_le_right⟩
  · calc (Subgroup.center ↥Q).map Q.subtype ≤ (Z.subgroupOf Q).map Q.subtype :=
          Subgroup.map_mono hcenter_le
      _ = Z := Subgroup.map_subgroupOf_eq_of_le hZleQ
  · intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hZleQ hz⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro q
    exact Subtype.ext (hZcentral z hz (q : G) q.2).eq.symm

private theorem two_kComp_sup_E {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    {J' : Subgroup G} (hne : J ≠ J') (hK' : IsKComp M H J')
    (hQcard5 : Nat.card Q = 3 ^ 5) (hcardT₁ : Nat.card ↥(Q ⊓ J) = 27) :
    (Q ⊓ J) ⊔ E = Q := by
  have hLN : ¬ pLayerIn 3 H ≤ M := hL 3 E H h.hypCGen
  have hQJ' : Q ≤ Subgroup.normalizer (J' : Set G) :=
    h.Q_le_normalizer_of_isKComp hpre hU hK'
  have hQT₁ : Q ≤ Subgroup.normalizer ((Q ⊓ J : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (h.Q_le_normalizer_J hpre hU)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hEbot : E ⊓ (Q ⊓ J) = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heT⟩ := Subgroup.mem_inf.mp he
    have heJ : e ∈ J := heT.2
    have hcomm_le : ∀ g ∈ J', e * g * e⁻¹ * g⁻¹ ∈ (CFSG.pPrimeCore 3 ↥J').map J'.subtype := by
      intro g hg
      have hmem : ⁅e, g⁆ ∈ ⁅J, J'⁆ := Subgroup.commutator_mem_commutator heJ hg
      exact commutator_le_pPrimeCore_of_distinct hK' h.isKComp hne
        (by simpa [commutatorElement_def] using hmem)
    have heStar : e ∈ starCentralizer J' :=
      mem_starCentralizer_iff.mpr ⟨hQJ' heT.1, jStarAct_eq_one_of_commutator_le hcomm_le⟩
    exact h.hypCGen.eq_one_of_mem_starCentralizer hLN hK' heE heStar
  have hcardTE : Nat.card ↥((Q ⊓ J) ⊔ E) = 3 ^ 5 :=
    card_sup_eq_pow_of_inf_eq_bot (S := Q ⊓ J) (E := E) (Q := (Q ⊓ J) ⊔ E) rfl
      (by rw [inf_comm]; exact hEbot) (h.E_le_Q.trans hQT₁) hcardT₁ h.card
  have hle : (Q ⊓ J) ⊔ E ≤ Q := sup_le inf_le_left h.E_le_Q
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardTE, hQcard5])

private theorem two_kComp_pCore
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    {J' : Subgroup G} (hne : J ≠ J') (hK' : IsKComp M H J') :
    ⁅Q ⊓ J', J⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hpCore : CFSG.Open.pCoreOf 2 J = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    rw [CFSG.openPCoreOf_eq_map_pCore,
      pCore_two_eq_pPrimeCore_three_of_isL34Type h.J_comp.2.2.1 hSL.1]
  rw [hpCore]
  exact (Subgroup.commutator_mono inf_le_right le_rfl).trans
    (commutator_le_pPrimeCore_of_distinct h.isKComp hK' hne.symm)

private theorem aux_two_kComp
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    {J' : Subgroup G} (hne : J ≠ J') (hK' : IsKComp M H J') (hsup : kSub 3 M H = J ⊔ J')
    (ht' : IsSL34Star J' ∨ Is3A6Star J') :
    FourteenTwoConcl Q J ∧ (Q ⊓ J) ⊔ E = Q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLN : ¬ pLayerIn 3 H ≤ M := hL 3 E H h.hypCGen
  have hSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hT₁syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J) J := h.isSylowOf_inf_J hpre hU
  have hT₂syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J') J' :=
    h.isSylowOf_inf_of_isKComp hpre hU hK'
  have hQJ : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hQJ' : Q ≤ Subgroup.normalizer (J' : Set G) :=
    h.Q_le_normalizer_of_isKComp hpre hU hK'
  have hQT₁ : Q ≤ Subgroup.normalizer ((Q ⊓ J : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hQJ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQT₂ : Q ≤ Subgroup.normalizer ((Q ⊓ J' : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hQJ').trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQH : Q ≤ H := h.sylow.le.trans (sup_le (kSub_le 3 M H) h.E_le_H)
  obtain ⟨hEsub, hcard, hAB, hinf, hexp⟩ :=
    h.hypCGen.le_sup_of_two_kComp (J₁ := J) (J₂ := J') (T₁ := Q ⊓ J) (T₂ := Q ⊓ J')
      (R := Q) hLN hne h.isKComp hK' hSL ht' hT₁syl hT₂syl h.sylow.isPGroup hQH
      h.E_le_Q inf_le_left inf_le_left hQJ hQJ' hQT₁ hQT₂
  have hcardT₁ : Nat.card ↥(Q ⊓ J) = 27 :=
    (IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hT₁syl).1
  have hcardT₂ : Nat.card ↥(Q ⊓ J') = 27 :=
    (IsKComp.sylow_three_structure hK' ht' hT₂syl).1
  set Z : Subgroup G := (Subgroup.center ↥(Q ⊓ J)).map (Q ⊓ J).subtype with hZdef
  have hZcard : Nat.card ↥Z = 3 := by
    rw [hZdef]
    exact (IsKComp.sylow_three_structure h.isKComp (Or.inl hSL) hT₁syl).2.2.2
  have hZcard₂ : Nat.card ↥((Subgroup.center ↥(Q ⊓ J')).map (Q ⊓ J').subtype) = 3 :=
    (IsKComp.sylow_three_structure hK' ht' hT₂syl).2.2.2
  have hinfZ : (Q ⊓ J) ⊓ (Q ⊓ J') = Z := hinf.trans hZdef.symm
  have hinfcard : Nat.card ↥((Q ⊓ J) ⊓ (Q ⊓ J')) = 3 := by
    rw [hinfZ, hZcard]
  have hQeq : Q = (Q ⊓ J) ⊔ (Q ⊓ J') :=
    two_kComp_sup_eq h hpre hU hK' hsup hcard hEsub hinfcard hcardT₁ hcardT₂ hT₁syl hT₂syl
  obtain ⟨hZeqT₂, hZcentral⟩ := two_kComp_Z hQeq hAB hinfZ hZdef hZcard hZcard₂
  have hQQ : ⁅Q, Q⁆ = Z :=
    two_kComp_commutator hQeq hAB hZdef hZeqT₂ hZcentral hcardT₁ hcardT₂ hZcard hZcard₂
  have hcenter_le := two_kComp_center_le hQeq hAB hinfZ hZdef hZeqT₂
  obtain ⟨hcenter_eq, hZleT₂⟩ := two_kComp_center_eq hQeq hinfZ hcenter_le hZcentral
  have hQcard5 : Nat.card Q = 3 ^ 5 := by rw [hQeq, hcard]
  have hexpQ : ∀ x ∈ Q, x ^ 3 = 1 := fun x hx => hexp x (hQeq ▸ hx)
  have hQ₀comm : ⁅Q ⊓ J', J⁆ ≤ CFSG.Open.pCoreOf 2 J := two_kComp_pCore h hA hpre hU hne hK'
  have hconcl : FourteenTwoConcl Q J := by
    refine ⟨⟨hQcard5, hexpQ, ?_, ?_⟩, Q ⊓ J', inf_le_left, hcardT₂, hQ₀comm, ?_⟩
    · rw [hcenter_eq]
      exact hQQ
    · rw [hcenter_eq, hZcard]
    · rw [hcenter_eq]
      exact hZleT₂
  exact ⟨hconcl, two_kComp_sup_E h hpre hU hL hne hK' hQcard5 hcardT₁⟩

theorem S14Choice.inf_J_sup_E
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) :
    (Q ⊓ J) ⊔ E = Q := by
  classical
  have hfive := (hpre 3 Q (h.Q_mem_QSet hU) H h.mem_H2StarFam).2
  rcases hfive with ⟨hK, -⟩ | ⟨J₁, J₂, hne, hJ₁, hJ₂, hsup, honly, hSL₁, hSL₂⟩
  · exact (h.eq_inf_J_sup_E_of_kComp_self hpre hU hK).symm
  · rcases honly J h.isKComp with hJ | hJ
    · exact (aux_two_kComp h hA hpre hU hL (by rw [hJ]; exact hne) hJ₂
        (by rw [← hJ] at hsup; exact hsup) hSL₂).2
    · exact (aux_two_kComp (J' := J₁) h hA hpre hU hL (by rw [hJ]; exact hne.symm) hJ₁
        (by rw [← hJ] at hsup; rw [sup_comm] at hsup; exact hsup) (Or.inl hSL₁)).2

theorem fourteenTwoCaseOneAt_of
    {M : Subgroup G} (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) :
    FourteenTwoCaseOneAt M := by
  classical
  intro H E Q J h hA
  have hfive := (hpre 3 Q (h.Q_mem_QSet hU) H h.mem_H2StarFam).2
  rcases hfive with ⟨hK, -⟩ | ⟨J₁, J₂, hne, hJ₁, hJ₂, hsup, honly, hSL₁, hSL₂⟩
  · exact h.fourteenTwo_of_kComp_self hA hpre hU hL hK
  · rcases honly J h.isKComp with hJ | hJ
    · exact (aux_two_kComp h hA hpre hU hL (by rw [hJ]; exact hne) hJ₂
        (by rw [← hJ] at hsup; exact hsup) hSL₂).1
    · exact (aux_two_kComp (J' := J₁) h hA hpre hU hL (by rw [hJ]; exact hne.symm) hJ₁
        (by rw [← hJ] at hsup; rw [sup_comm] at hsup; exact hsup) (Or.inl hSL₁)).1

theorem fourteenTwoCaseOneGen_of
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen) (h96 : NineSixMoreoverGen)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen) : FourteenTwoCaseOneGen := by
  intro G _ _ M H E Q J h hA
  have hU : NineNineOneAt M := nineNineOneAt_of_twelveEleven h991 h1211
  have hpre : PreambleTypes M :=
    preambleTypes_of h1211 h.cstar h.maxLocal h.sigma_nonempty
      (preambleFiveTypes_of h1210 h97 h96 h.cstar h.maxLocal h.sigma_nonempty hU)
  have hL : PLayerNotLeAt M := pLayerNotLeAt_of h1211 h1210 h97 hU
  exact fourteenTwoCaseOneAt_of (M := M) hpre hU hL H E Q J h hA

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
