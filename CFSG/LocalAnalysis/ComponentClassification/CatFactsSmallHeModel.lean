module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallHeGen
public import CFSG.Sporadic.HeldB.AllFixed
public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.Sporadic.HeldB.InnerRestrict
public meta import CFSG.Sporadic.HeldB.OuterCentRestrict
public meta import CFSG.GH74.KGroups.PermCheck
public import Certificates.Certificate2110
public import Certificates.Certificate2111
public import Certificates.Certificate2112
public import Certificates.Certificate2114
public import Certificates.Certificate2116
public import Certificates.Certificate2223
public import Certificates.Certificate2224
public import Certificates.Certificate2225
public import Certificates.Certificate2115
public import Certificates.Certificate2117
public import Certificates.Certificate2118
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallHeModelInputs
public import Certificates.Certificate2010
public import Certificates.Certificate3168

public section

namespace CFSG.ComponentClassification.CatFactsSmall.He

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct

theorem QY0_valid : QY0.check = true ∧ QY0.orderCertificate = 40320 :=
  Certificates.certificate2010.1

theorem y0_orders : orderIs y00 5 = true ∧ orderIs y01 5 = true :=
  Certificates.certificate2010.2.1

theorem QY0_eq : QY0.originalSubgroup = closure {y00, y01} := by
  rw [QY0, certificate_originalSubgroup]
  congr 1
  ext g
  simp [tab_eq]

theorem sigma0_mem (j : ℕ) (hj : j < 9) : heInnerSigmaP0 j ∈ heX0.originalSubgroup := by
  rw [heX0_eq]
  exact subset_closure ⟨j, hj, rfl⟩

theorem y00_mem : y00 ∈ heX0.originalSubgroup :=
  mul_mem (mul_mem (mul_mem (sigma0_mem 3 (by norm_num)) (sigma0_mem 8 (by norm_num)))
    (sigma0_mem 4 (by norm_num))) (sigma0_mem 1 (by norm_num))

theorem y01_mem : y01 ∈ heX0.originalSubgroup :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (sigma0_mem 6 (by norm_num))
    (sigma0_mem 4 (by norm_num))) (sigma0_mem 1 (by norm_num))) (sigma0_mem 7 (by norm_num)))
    (sigma0_mem 4 (by norm_num))) (sigma0_mem 5 (by norm_num))

theorem card_closure_pair {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) :
    Nat.card (closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set H)) = Nat.card (closure ({a, b} : Set G)) := by
  rw [← card_map_of_injective H.subtype_injective, MonoidHom.map_closure]
  congr 2
  ext g
  simp

theorem heX0_good5 : Good5 heX0.originalSubgroup := by
  refine good5_of_witness (by rw [card_heX0]; norm_num) ⟨y00, y00_mem⟩ ⟨y01, y01_mem⟩ ?_ ?_ ?_
  · rw [Subgroup.orderOf_mk]; exact (orderIs_iff _ (by norm_num)).1 y0_orders.1
  · rw [Subgroup.orderOf_mk]; exact (orderIs_iff _ (by norm_num)).1 y0_orders.2
  · rw [card_closure_pair, ← QY0_eq, ← QY0.orderCertificate_eq_card QY0_valid.1, QY0_valid.2]
    norm_num

theorem heInnerGrp0_eq : heInnerGrp0 = centralizerIn heP (heGenPerm 0) :=
  (oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one
    heDelta0_injective heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8)
    (by rw [card_heX0]; norm_num) oddWitness_heX0 (by rw [card_heP_cent0, card_heX0])).1

theorem good5_C0 : Good5 (centralizerIn heP (heGenPerm 0)) := by
  rw [← heInnerGrp0_eq]
  set ρ := restrictHom heDelta0_injective heInnerGrp0 heInnerGrp0_stab
  let f : heInnerGrp0 →* heX0.originalSubgroup :=
    (MulEquiv.subgroupCongr heInnerRes0_range).toMonoidHom.comp ρ.rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr heInnerRes0_range).surjective.comp ρ.rangeRestrict_surjective
  refine good5_of_surjective f hf ?_ heX0_good5
  have hc : Nat.card heInnerGrp0 = 161280 := by rw [heInnerGrp0_eq, card_heP_cent0]
  have h := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, card_heX0,
    hc] at h
  have : Nat.card f.ker = 2 := by omega
  rw [this]

theorem good5_C1 : Good5 (centralizerIn heP heT1P) :=
  good5_of_not_dvd (by rw [card_heP_cent1]; norm_num)

theorem QYu_valid : QYu.check = true ∧ QYu.orderCertificate = 1080 :=
  Certificates.certificate2010.2.2.1

theorem yu_orders : orderIs yu0 5 = true ∧ orderIs yu1 5 = true :=
  Certificates.certificate2010.2.2.2

theorem QYu_eq : QYu.originalSubgroup = closure {yu0, yu1} := by
  rw [QYu, certificate_originalSubgroup]
  congr 1
  ext g
  simp [tab_eq]

theorem sigma1_mem : heSigma1P ∈ heQC.originalSubgroup := by
  rw [← heResF_range, ← heResF_c1]
  exact ⟨_, rfl⟩

theorem sigma2_mem : heSigma2P ∈ heQC.originalSubgroup := by
  rw [← heResF_range, ← heResF_c2]
  exact ⟨_, rfl⟩

theorem yu0_mem : yu0 ∈ heQC.originalSubgroup := by
  have h1 := sigma1_mem
  have h2 := sigma2_mem
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h2 h1) h2) h1) h1) h2) h1

theorem yu1_mem : yu1 ∈ heQC.originalSubgroup := by
  have h1 := sigma1_mem
  have h2 := sigma2_mem
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h2 h1) h1) h2) h1) h2) h1

theorem heQC_good5 : Good5 heQC.originalSubgroup := by
  refine good5_of_witness (by rw [card_heQC]; norm_num) ⟨yu0, yu0_mem⟩ ⟨yu1, yu1_mem⟩ ?_ ?_ ?_
  · rw [Subgroup.orderOf_mk]; exact (orderIs_iff _ (by norm_num)).1 yu_orders.1
  · rw [Subgroup.orderOf_mk]; exact (orderIs_iff _ (by norm_num)).1 yu_orders.2
  · rw [card_closure_pair, ← QYu_eq, ← QYu.orderCertificate_eq_card QYu_valid.1, QYu_valid.2]
    norm_num

theorem good5_Cu : Good5 (heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))) := by
  rw [← heOuterC_eq]
  exact good5_of_mulEquiv ((MonoidHom.ofInjective heResF_injective).trans
    (MulEquiv.subgroupCongr heResF_range)) heQC_good5

theorem good5_fixedSubgroup {S : Type*} [Group S] (θ : S ≃* heP) (α : MulAut S)
    (hα : orderOf α = 2) : Good5 (fixedSubgroup α) := by
  have : Finite S := Finite.of_equiv _ θ.symm.toEquiv
  have hβ : orderOf (MulAut.congr θ α) = 2 := by rw [orderOf_congr, hα]
  by_cases hinn : MulAut.congr θ α ∈ (MulAut.conj : heP →* MulAut heP).range
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center heP_center_eq_bot) t, ht, hβ]
    let f : fixedSubgroup α ≃* centralizer ({t} : Set heP) :=
      (fixedSubgroupCongr θ α).trans (MulEquiv.subgroupCongr (by rw [← ht, fixedSubgroup_conj]))
    refine good5_of_mulEquiv (f.trans (heCentralizerEquiv t)) ?_
    rcases involution_conj_cases t.2 (by rw [Subgroup.orderOf_coe]; exact ht2) with
      ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
    · exact good5_of_mulEquiv ((MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans
        (infCentralizerConjEquiv hc (heGenPerm 0))) good5_C0
    · exact good5_of_mulEquiv ((MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans
        (infCentralizerConjEquiv hc heT1P)) good5_C1
  · obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
      (MulAut.congr θ α) hβ hinn
    obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
    exact good5_of_mulEquiv (((fixedSubgroupCongr θ α).trans
      (MulEquiv.subgroupCongr (by rw [hx]))).trans (fixedSubgroupEquivOfConj x hg heAutU hxg))
      good5_Cu

end CFSG.ComponentClassification.CatFactsSmall.He
