module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayPerfect
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma39

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup CFSG.ComponentClassification.AschbacherKnownGroup

private theorem isCyclic_of_card_le_three {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ≤ 3) : IsCyclic H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcases : Nat.card H = 1 ∨ Nat.card H = 2 ∨ Nat.card H = 3 := by
    have hpos : 0 < Nat.card H := Nat.card_pos_iff.mpr ⟨⟨(1 : H)⟩, inferInstance⟩
    omega
  rcases hcases with h1 | h2 | h3
  · haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (p := 2) h2
  · exact isCyclic_of_prime_card (p := 3) h3

@[expose] def DihedralOuterInvolutionFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (a : G),
    IsSimpleGroup L → HasDihedralSylowTwo L → a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
    HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) →
    a ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
    (∀ K : Subgroup G, Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K →
      K ≤ Subgroup.zpowers a ⊔ L →
      K = Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)) ∨
        K = Subgroup.zpowers a ⊔ L) ∧
    (∀ y ∈ Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)),
      (∀ m ∈ Subgroup.zpowers a ⊔ (L ⊓ Subgroup.centralizer ({a} : Set G)), y * m = m * y) →
      y ∈ Subgroup.zpowers a) ∧
    (∀ b ∈ Subgroup.normalizer (L : Set G), b ^ 2 = 1 →
      HasCyclicSylowTwo (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) →
      a * b ∈ L ⊔ Subgroup.centralizer (L : Set G))

theorem false_of_dihedral_small_centralizer (hF : DihedralOuterInvolutionFact) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hL : IsSimpleGroup ↥L)
    (hnab : ∃ x y : L, x * y ≠ y * x) (heven : 2 ∣ Nat.card L)
    (hdih : HasDihedralSylowTwo ↥L) {a : G} (ha : a ^ 2 = 1)
    (haN : a ∈ normalizer (L : Set G)) (haL : a ∉ L)
    (hC : Nat.card ↥(L ⊓ centralizer ({a} : Set G)) ≤ 3) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Csub : Subgroup G := L ⊓ centralizer ({a} : Set G)
  let K : Subgroup G := zpowers a ⊔ Csub
  let M : Subgroup G := zpowers a ⊔ L
  have hCsmall : Nat.card Csub ≤ 3 := hC
  have hCcyc : IsCyclic Csub := isCyclic_of_card_le_three hCsmall
  have hca : HasCyclicSylowTwo Csub := by
    refine ⟨Classical.choice Sylow.nonempty, ?_⟩
    haveI : IsCyclic (⊤ : Subgroup Csub) :=
      (Subgroup.topEquiv : (⊤ : Subgroup Csub) ≃* Csub).isCyclic.mpr hCcyc
    exact Subgroup.isCyclic_of_le le_top
  obtain ⟨hout, hmax, hcen, _⟩ := hF G L a hL hdih haN ha hca
  have hCle : Csub ≤ zpowers a := by
    intro y hy
    refine hcen y (mem_sup_right hy) ?_
    intro m hm
    have hyC : y ∈ centralizer ({a} : Set G) := (mem_inf.mp hy).2
    have hay : a * y = y * a := (mem_centralizer_singleton_iff.mp hyC).symm
    haveI : IsCyclic Csub := hCcyc
    haveI : IsMulCommutative Csub := IsCyclic.isMulCommutative
    have hcommC : ∀ z ∈ Csub, ∀ w ∈ Csub, z * w = w * z := by
      intro z hz w hw
      exact congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : Csub) (⟨w, hw⟩ : Csub))
    have hCsuby : Csub ≤ centralizer ({y} : Set G) := by
      intro z hz
      exact mem_centralizer_singleton_iff.mpr (hcommC z hz y hy)
    have hzpa : zpowers a ≤ centralizer ({y} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hay)
    have hzK : K ≤ centralizer ({y} : Set G) := sup_le hzpa hCsuby
    exact (mem_centralizer_singleton_iff.mp (hzK hm)).symm
  have hCbot : Csub = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hCle hy)
    rcases CFSG.ComponentClassification.AschbacherKnownGroup.Lemma39.zpow_eq_one_or_self ha k
      with h | h
    · rw [mem_bot, ← hk, h]
    · exfalso
      apply haL
      have hy' : y = a := by rw [hk.symm, h]
      rw [← hy']
      exact (mem_inf.mp hy).1
  have hKsup : zpowers a ⊔ Csub = zpowers a := by rw [hCbot, sup_bot_eq]
  have horder : orderOf a = 2 :=
    orderOf_eq_prime ha (fun h => haL (by rw [h]; exact L.one_mem))
  have hcardM : Nat.card M = 2 * Nat.card L := by
    have h := card_sup_zpowers_eq_two_mul (X := G) (J := L) (t := a) ha haN haL
    rw [sup_comm] at h
    exact h
  have h4dvdM : 4 ∣ Nat.card M := by
    rw [hcardM]
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    exact ⟨k, by ring⟩
  have hfacM : 2 ≤ (Nat.card M).factorization 2 := by
    have hne : Nat.card M ≠ 0 :=
      (Nat.card_pos_iff.mpr ⟨⟨(1 : M)⟩, inferInstance⟩).ne'
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp h4dvdM
  have hzp2 : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_iff_pow_eq_one.mpr ha)
  have hsub2 : IsPGroup 2 ((zpowers a).subgroupOf M) := by
    rw [← Subgroup.comap_subtype]
    exact hzp2.comap_subtype (K := M)
  obtain ⟨P, hPle⟩ := hsub2.exists_le_sylow
  let K' : Subgroup G := (P : Subgroup ↥M).map M.subtype
  have hK'2 : IsPGroup 2 K' := P.isPGroup'.map M.subtype
  have hzpK' : zpowers a ≤ K' := by
    have h := Subgroup.map_mono (f := M.subtype) hPle
    rwa [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show zpowers a ≤ M from le_sup_left)] at h
  have hK'M : K' ≤ M := Subgroup.map_subtype_le (P : Subgroup ↥M)
  have hlower : zpowers a ⊔ Csub ≤ K' := by rw [hKsup]; exact hzpK'
  rcases hmax K' hlower hK'M with hK'eq | hK'eq
  · have hK'card : Nat.card K' = 2 := by
      calc Nat.card K' = Nat.card ↥(zpowers a ⊔ Csub) := by rw [hK'eq]
        _ = Nat.card ↥(zpowers a) := by rw [hCbot, sup_bot_eq]
        _ = orderOf a := Nat.card_zpowers a
        _ = 2 := horder
    have hK'ge : 4 ≤ Nat.card K' := by
      have hcardP : Nat.card K' = Nat.card (P : Subgroup ↥M) :=
        Subgroup.card_subtype M (P : Subgroup ↥M)
      rw [hcardP, Sylow.card_eq_multiplicity P]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (Nat.card ↥M).factorization 2 :=
            Nat.pow_le_pow_right (by norm_num) hfacM
    omega
  · have hMK : M = K' :=
      (show M = Subgroup.zpowers a ⊔ L from rfl).trans hK'eq.symm
    have hM2 : IsPGroup 2 M := by
      rw [hMK]
      exact hK'2
    have hL2 : IsPGroup 2 L := hM2.to_le (show L ≤ M from le_sup_right)
    haveI : Nontrivial ↥L := by
      obtain ⟨x, y, hxy⟩ := hnab
      exact ⟨x, y, fun h => hxy (by rw [h])⟩
    haveI : Nontrivial (Subgroup.center ↥L) := IsPGroup.center_nontrivial hL2
    rcases hL.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hbot | htop
    · haveI : Subsingleton (Subgroup.center ↥L) := by rw [hbot]; infer_instance
      obtain ⟨u, v, huv⟩ := (inferInstance : Nontrivial (Subgroup.center ↥L))
      exact huv (Subsingleton.elim u v)
    · have hcomm : IsMulCommutative ↥L := Subgroup.center_eq_top_iff.mp htop
      haveI : IsMulCommutative ↥L := hcomm
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (mul_comm' x y)

end CFSG.OddStandard.AltStdSec.SwapPartner
