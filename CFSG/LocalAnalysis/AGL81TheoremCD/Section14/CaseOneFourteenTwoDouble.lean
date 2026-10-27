module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneInnerAction
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34SylowStructure
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L4Aux

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M E N : Subgroup G}

private theorem exists_mem_pow_three_not_mem_center_of_sylow
    {J T : Subgroup G}
    (hJ : IsKComp M N J) (htype : IsSL34Star J ∨ Is3A6Star J)
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T J) :
    ∃ v ∈ T, v ∉ (Subgroup.center ↥T).map T.subtype ∧ v ^ 3 = 1 := by
  have hZle : (Subgroup.center ↥T).map T.subtype ≤ T := Subgroup.map_subtype_le _
  have hcard := (hJ.sylow_three_structure htype hT).1
  have hne : (Subgroup.center ↥T).map T.subtype ≠ T := by
    intro heq
    have hZ := (hJ.sylow_three_structure htype hT).2.2.2
    rw [heq, hcard] at hZ
    norm_num at hZ
  have hnot : ¬ T ≤ (Subgroup.center ↥T).map T.subtype :=
    fun hle => hne (le_antisymm hZle hle)
  obtain ⟨v, hvT, hvZ⟩ := Set.not_subset.mp hnot
  exact ⟨v, hvT, hvZ, (hJ.sylow_three_structure htype hT).2.1 v hvT⟩

private theorem exists_elemAbelian_card_nine_of_sylow
    {J T : Subgroup G}
    (hJ : IsKComp M N J) (htype : IsSL34Star J ∨ Is3A6Star J)
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T J) :
    ∃ A : Subgroup G, A ≤ T ∧ IsElemAbelian 3 A ∧ Nat.card ↥A = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Z : Subgroup G := (Subgroup.center ↥T).map T.subtype
  have hZcard : Nat.card ↥Z = 3 := (hJ.sylow_three_structure htype hT).2.2.2
  have hZT : Z ≤ T := Subgroup.map_subtype_le _
  have hnt : Nontrivial ↥Z :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hZcard]; norm_num)
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥Z)
  have hzT : (z : G) ∈ T := hZT z.2
  have hzpow : (z : G) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Z) (x := z)
    rw [hZcard] at h
    exact congrArg Subtype.val h
  have hzord : orderOf (z : G) = 3 := by
    have hdvd : orderOf (z : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hzpow
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) fun h => hz1 (Subtype.ext h)
    · exact h3
  obtain ⟨v, hvT, hvZ, hvpow⟩ := exists_mem_pow_three_not_mem_center_of_sylow hJ htype hT
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Z.one_mem)
  have hvord : orderOf v = 3 := by
    have hdvd : orderOf v ∣ 3 := orderOf_dvd_of_pow_eq_one hvpow
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hv1
    · exact h3
  have hcomm : ∀ a ∈ Z, a * v = v * a := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp ha' ⟨v, hvT⟩).symm
  refine ⟨Z ⊔ Subgroup.zpowers v, sup_le hZT (Subgroup.zpowers_le.mpr hvT),
    (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hZcard hvord hvZ hcomm).1,
    ?_⟩
  simpa using (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    hZcard hvord hvZ hcomm).2

private theorem mem_starCentralizer_of_commutator_le {J : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (J : Set G))
    (hx : ∀ g ∈ J, x * g * x⁻¹ * g⁻¹ ∈
      (CFSG.pPrimeCore 3 ↥J).map J.subtype) :
    x ∈ starCentralizer J :=
  (mem_starCentralizer_iff).mpr ⟨hxN, jStarAct_eq_one_of_commutator_le hx⟩

private theorem commute_of_mem_starCentralizer {J T : Subgroup G} {x : G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T J)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hx : x ∈ starCentralizer J) :
    ∀ t ∈ T, x * t = t * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  have hO : ¬ 3 ∣ Nat.card ↥O := by
    rw [show Nat.card ↥O = Nat.card ↥(CFSG.pPrimeCore 3 ↥J) from
      Subgroup.card_map_of_injective J.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := hT.isPGroup.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥T) (Nat.card ↥O) := by
    rw [hk]
    exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hO))
  have hinf : T ⊓ O = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  intro t ht
  have hmemO : x * t * x⁻¹ * t⁻¹ ∈ O :=
    commutator_mem_map_of_mem_quotientCentralizer (CFSG.pPrimeCore 3 ↥J)
      Subgroup.le_normalizer le_rfl hx (hT.le ht)
  have hmemT : x * t * x⁻¹ * t⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.mp hxT t).mp ht) (T.inv_mem ht)
  have h1 : x * t * x⁻¹ * t⁻¹ = 1 := by
    have hmem : x * t * x⁻¹ * t⁻¹ ∈ T ⊓ O := ⟨hmemT, hmemO⟩
    rw [hinf] at hmem
    simpa using hmem
  have h2 : x * t * x⁻¹ = t := by
    simpa [mul_assoc] using congrArg (fun z => z * t) h1
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [h2]

private theorem pow_three_eq_one_of_decomp {x₁ x₂ e : G}
    (hx : x₁ * x₂ = x₂ * x₁) (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1)
    (he : e ^ 3 = 1) (he₁ : e * x₁ = x₁ * e) (he₂ : e * x₂ = x₂ * e) :
    ((x₁ * x₂)⁻¹ * e) ^ 3 = 1 := by
  have hxpow : (x₁ * x₂) ^ 3 = 1 := by
    rw [Commute.mul_pow (show Commute x₁ x₂ from hx) 3, hx₁, hx₂, one_mul]
  have hcomm : Commute ((x₁ * x₂)⁻¹) e :=
    (Commute.mul_right (show Commute e x₁ from he₁)
      (show Commute e x₂ from he₂)).symm.inv_left
  rw [Commute.mul_pow hcomm, inv_pow, hxpow, inv_one, he, one_mul]

private theorem not_isElemAbelian_card_81 {N' F : Subgroup G}
    (hrank : CFSG.Open.pRank 3 N' ≤ 3) (hF : IsElemAbelian 3 F)
    (hcard : Nat.card ↥F = 3 ^ 4) (hFN : F ≤ N') : False := by
  have h4 : 4 ≤ CFSG.Open.pRank 3 N' :=
    CFSG.SectionRank.le_pRank (by norm_num) hFN hF hcard
  omega

private theorem commutator_eq_bot_of_two_kComp {J₁ J₂ T₁ T₂ R : Subgroup G}
    (h₁ : IsKComp M N J₁) (h₂ : IsKComp M N J₂) (hne : J₁ ≠ J₂)
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J₁)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂)
    (hR : IsPGroup 3 R) (hT₁R : T₁ ≤ R) (hT₂R : T₂ ≤ R) : ⁅T₁, T₂⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR' : IsPGroup 3 ↥⁅T₁, T₂⁆ := hR.to_le (Subgroup.commutator_le_of_le hT₁R hT₂R)
  have hJ₂J₁ : ⁅J₂, J₁⁆ ≤ (CFSG.pPrimeCore 3 ↥J₁).map J₁.subtype :=
    commutator_le_pPrimeCore_of_distinct h₁ h₂ hne.symm
  have hle : ⁅T₁, T₂⁆ ≤ (CFSG.pPrimeCore 3 ↥J₁).map J₁.subtype :=
    (Subgroup.commutator_mono hT₁.le hT₂.le).trans
      (by rw [Subgroup.commutator_comm J₁ J₂]; exact hJ₂J₁)
  refine CFSG.ABGTheoremB.TotallyInverted.DataConstruction.eq_bot_of_isPGroup_of_le
    Nat.prime_three hR' hle ?_
  rw [Subgroup.card_map_of_injective J₁.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card

private theorem inf_eq_center_of_two_kComp
    {J₁ J₂ T₁ T₂ R N' : Subgroup G}
    (h₁ : IsKComp M N J₁) (h₂ : IsKComp M N J₂) (ht₁ : IsSL34Star J₁)
    (ht₂ : IsSL34Star J₂ ∨ Is3A6Star J₂)
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J₁)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂)
    (hT₁R : T₁ ≤ R) (hT₂R : T₂ ≤ R) (hRN : R ≤ N')
    (hcomm : ⁅T₁, T₂⁆ = ⊥) (hrank : CFSG.Open.pRank 3 N' ≤ 3) :
    T₁ ⊓ T₂ = (Subgroup.center ↥T₁).map T₁.subtype := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs₁ := h₁.sylow_three_structure (Or.inl ht₁) hT₁
  have hs₂ := h₂.sylow_three_structure ht₂ hT₂
  have hcent₂ : T₂ ≤ Subgroup.centralizer (T₁ : Set G) := by
    have h := Subgroup.commutator_comm T₁ T₂
    rw [h] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hleZ : T₁ ⊓ T₂ ≤ (Subgroup.center ↥T₁).map T₁.subtype := by
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hx₁⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hyx : (y : G) * x = x * (y : G) :=
      Subgroup.mem_centralizer_iff.mp (hcent₂ hx₂) (y : G) y.2
    exact Subtype.ext hyx
  by_cases hbot : T₁ ⊓ T₂ = ⊥
  · obtain ⟨A₁, hA₁T, hA₁, hA₁card⟩ :=
      exists_elemAbelian_card_nine_of_sylow h₁ (Or.inl ht₁) hT₁
    obtain ⟨A₂, hA₂T, hA₂, hA₂card⟩ := exists_elemAbelian_card_nine_of_sylow h₂ ht₂ hT₂
    have hcA : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm (hA₁T ha))
        b (hA₂T hb)).symm
    have hinfA : A₁ ⊓ A₂ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
      have hmem : x ∈ T₁ ⊓ T₂ := ⟨hA₁T hx₁, hA₂T hx₂⟩
      rw [hbot] at hmem
      simpa using hmem
    have hcardA : Nat.card ↥(A₁ ⊔ A₂) = 3 ^ 4 := by
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hcA).1
      rw [hinfA, Subgroup.card_bot, hA₁card, hA₂card] at h
      norm_num at h
      rw [h]
      norm_num
    exact (not_isElemAbelian_card_81 hrank (IsElemAbelian.sup_of_commute hA₁ hA₂ hcA)
      hcardA ((sup_le (hA₁T.trans hT₁R) (hA₂T.trans hT₂R)).trans hRN)).elim
  · have hdvd : Nat.card ↥(T₁ ⊓ T₂) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hleZ
      rwa [hs₁.2.2.2] at h
    have hne1 : Nat.card ↥(T₁ ⊓ T₂) ≠ 1 :=
      fun h1 => hbot (Subgroup.card_eq_one.mp h1)
    have hcardinf : Nat.card ↥(T₁ ⊓ T₂) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd h1 hne1
      · exact h3
    exact Subgroup.eq_of_le_of_card_ge hleZ (by rw [hcardinf, hs₁.2.2.2])

private theorem exists_pair_of_mem_two_kComp
    (h : HypCGen G M 3 E N)
    (hLN : ¬ pLayerIn 3 N ≤ M) {J₁ J₂ T₁ T₂ R : Subgroup G}
    (hne : J₁ ≠ J₂) (h₁ : IsKComp M N J₁) (h₂ : IsKComp M N J₂)
    (ht₁ : IsSL34Star J₁) (ht₂ : IsSL34Star J₂ ∨ Is3A6Star J₂)
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J₁)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂)
    (hER : E ≤ R) (hT₁R : T₁ ≤ R) (hT₂R : T₂ ≤ R)
    (hRJ₁ : R ≤ Subgroup.normalizer (J₁ : Set G))
    (hRJ₂ : R ≤ Subgroup.normalizer (J₂ : Set G))
    (hRT₁ : R ≤ Subgroup.normalizer (T₁ : Set G))
    (hRT₂ : R ≤ Subgroup.normalizer (T₂ : Set G))
    (hcomm : ⁅T₁, T₂⁆ = ⊥) {e : G} (he : e ∈ E) :
    ∃ x₁ ∈ T₁, ∃ x₂ ∈ T₂,
      x₂ ∈ starCentralizer J₁ ∧ x₁ ∈ starCentralizer J₂ ∧
        (x₁⁻¹ * e) ∈ starCentralizer J₁ ∧ (x₂⁻¹ * e) ∈ starCentralizer J₂ ∧
        (x₁⁻¹ * e) ∈ Subgroup.normalizer (T₁ : Set G) ∧
        (x₂⁻¹ * e) ∈ Subgroup.normalizer (T₂ : Set G) ∧
        (∀ t ∈ T₁, (x₁⁻¹ * e) * t = t * (x₁⁻¹ * e)) ∧
        (∀ t ∈ T₂, (x₂⁻¹ * e) * t = t * (x₂⁻¹ * e)) ∧
        e * x₁ = x₁ * e ∧ e * x₂ = x₂ * e ∧
        x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧ x₁ * x₂ = x₂ * x₁ := by
  have hE₁ : E ≤ Subgroup.normalizer (J₁ : Set G) := hER.trans hRJ₁
  have hE₂ : E ≤ Subgroup.normalizer (J₂ : Set G) := hER.trans hRJ₂
  have hET₁ : E ≤ Subgroup.normalizer (T₁ : Set G) := hER.trans hRT₁
  have hET₂ : E ≤ Subgroup.normalizer (T₂ : Set G) := hER.trans hRT₂
  obtain ⟨x₁, hx₁T, hw₁⟩ :=
    h.exists_inner_mul_mem_starCentralizer hLN h₁ (Or.inl ht₁) hE₁ hT₁ hET₁ he
  obtain ⟨x₂, hx₂T, hw₂⟩ :=
    h.exists_inner_mul_mem_starCentralizer hLN h₂ ht₂ hE₂ hT₂ hET₂ he
  have hx₁R : x₁ ∈ R := hT₁R hx₁T
  have hx₂R : x₂ ∈ R := hT₂R hx₂T
  have hcT : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
  have hx₂star : x₂ ∈ starCentralizer J₁ := by
    refine mem_starCentralizer_of_commutator_le (hRJ₁ hx₂R) ?_
    intro g hg
    have hmem := Subgroup.commutator_mem_commutator (H₁ := J₂) (H₂ := J₁)
      (hT₂.le hx₂T) hg
    exact commutator_le_pPrimeCore_of_distinct h₁ h₂ hne.symm
      (by simpa [commutatorElement_def] using hmem)
  have hx₁star : x₁ ∈ starCentralizer J₂ := by
    refine mem_starCentralizer_of_commutator_le (hRJ₂ hx₁R) ?_
    intro g hg
    have hmem := Subgroup.commutator_mem_commutator (H₁ := J₁) (H₂ := J₂)
      (hT₁.le hx₁T) hg
    exact commutator_le_pPrimeCore_of_distinct h₂ h₁ hne
      (by simpa [commutatorElement_def] using hmem)
  have hw₁N : x₁⁻¹ * e ∈ Subgroup.normalizer (T₁ : Set G) :=
    (Subgroup.normalizer (T₁ : Set G)).mul_mem
      ((Subgroup.normalizer (T₁ : Set G)).inv_mem (hRT₁ hx₁R)) (hET₁ he)
  have hw₂N : x₂⁻¹ * e ∈ Subgroup.normalizer (T₂ : Set G) :=
    (Subgroup.normalizer (T₂ : Set G)).mul_mem
      ((Subgroup.normalizer (T₂ : Set G)).inv_mem (hRT₂ hx₂R)) (hET₂ he)
  have hw₁comm : ∀ t ∈ T₁, (x₁⁻¹ * e) * t = t * (x₁⁻¹ * e) :=
    commute_of_mem_starCentralizer hT₁ hw₁N hw₁
  have hw₂comm : ∀ t ∈ T₂, (x₂⁻¹ * e) * t = t * (x₂⁻¹ * e) :=
    commute_of_mem_starCentralizer hT₂ hw₂N hw₂
  have he₁ : e * x₁ = x₁ * e := by
    calc e * x₁ = (x₁ * (x₁⁻¹ * e)) * x₁ := by rw [mul_inv_cancel_left]
      _ = x₁ * ((x₁⁻¹ * e) * x₁) := by group
      _ = x₁ * (x₁ * (x₁⁻¹ * e)) := by rw [hw₁comm x₁ hx₁T]
      _ = x₁ * e := by rw [mul_inv_cancel_left]
  have he₂ : e * x₂ = x₂ * e := by
    calc e * x₂ = (x₂ * (x₂⁻¹ * e)) * x₂ := by rw [mul_inv_cancel_left]
      _ = x₂ * ((x₂⁻¹ * e) * x₂) := by group
      _ = x₂ * (x₂ * (x₂⁻¹ * e)) := by rw [hw₂comm x₂ hx₂T]
      _ = x₂ * e := by rw [mul_inv_cancel_left]
  have hexp₁ : x₁ ^ 3 = 1 := (h₁.sylow_three_structure (Or.inl ht₁) hT₁).2.1 x₁ hx₁T
  have hexp₂ : x₂ ^ 3 = 1 := (h₂.sylow_three_structure ht₂ hT₂).2.1 x₂ hx₂T
  exact ⟨x₁, hx₁T, x₂, hx₂T, hx₂star, hx₁star, hw₁, hw₂, hw₁N, hw₂N, hw₁comm, hw₂comm,
    he₁, he₂, hexp₁, hexp₂, hcT x₁ hx₁T x₂ hx₂T⟩

private theorem exists_factor_of_mem_two_kComp
    (h : HypCGen G M 3 E N)
    (hLN : ¬ pLayerIn 3 N ≤ M) {J₁ J₂ T₁ T₂ R : Subgroup G}
    (hne : J₁ ≠ J₂) (h₁ : IsKComp M N J₁) (h₂ : IsKComp M N J₂)
    (ht₁ : IsSL34Star J₁) (ht₂ : IsSL34Star J₂ ∨ Is3A6Star J₂)
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J₁)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂)
    (hER : E ≤ R) (hT₁R : T₁ ≤ R) (hT₂R : T₂ ≤ R)
    (hRJ₁ : R ≤ Subgroup.normalizer (J₁ : Set G))
    (hRJ₂ : R ≤ Subgroup.normalizer (J₂ : Set G))
    (hRT₁ : R ≤ Subgroup.normalizer (T₁ : Set G))
    (hRT₂ : R ≤ Subgroup.normalizer (T₂ : Set G))
    (hcomm : ⁅T₁, T₂⁆ = ⊥) {e : G} (he : e ∈ E) :
    ∃ x₁ ∈ T₁, ∃ x₂ ∈ T₂, ∃ f : G,
      e = x₁ * x₂ * f ∧ f ∈ starCentralizer J₁ ∧ f ∈ starCentralizer J₂ ∧
        f ∈ Subgroup.normalizer (T₁ : Set G) ∧
        f ∈ Subgroup.normalizer (T₂ : Set G) ∧ f ^ 3 = 1 := by
  obtain ⟨x₁, hx₁T, x₂, hx₂T, hx₂star, hx₁star, hw₁, hw₂, hw₁N, hw₂N, hw₁comm,
    hw₂comm, he₁, he₂, hexp₁, hexp₂, hx₁x₂⟩ :=
    exists_pair_of_mem_two_kComp h hLN hne h₁ h₂ ht₁ ht₂ hT₁ hT₂ hER hT₁R hT₂R
      hRJ₁ hRJ₂ hRT₁ hRT₂ hcomm he
  have hx₁R : x₁ ∈ R := hT₁R hx₁T
  have hx₂R : x₂ ∈ R := hT₂R hx₂T
  have hfeq₁ : (x₁ * x₂)⁻¹ * e = x₂⁻¹ * (x₁⁻¹ * e) := by
    rw [mul_inv_rev]
    group
  have hfeq₂ : (x₁ * x₂)⁻¹ * e = x₁⁻¹ * (x₂⁻¹ * e) := by
    rw [show (x₁ * x₂)⁻¹ = (x₂ * x₁)⁻¹ from by rw [hx₁x₂], mul_inv_rev]
    group
  have hfN₁ : (x₁ * x₂)⁻¹ * e ∈ Subgroup.normalizer (T₁ : Set G) := by
    rw [hfeq₁]
    exact (Subgroup.normalizer (T₁ : Set G)).mul_mem
      ((Subgroup.normalizer (T₁ : Set G)).inv_mem (hRT₁ hx₂R)) hw₁N
  have hfN₂ : (x₁ * x₂)⁻¹ * e ∈ Subgroup.normalizer (T₂ : Set G) := by
    rw [hfeq₂]
    exact (Subgroup.normalizer (T₂ : Set G)).mul_mem
      ((Subgroup.normalizer (T₂ : Set G)).inv_mem (hRT₂ hx₁R)) hw₂N
  have hf3 : ((x₁ * x₂)⁻¹ * e) ^ 3 = 1 :=
    pow_three_eq_one_of_decomp hx₁x₂ hexp₁ hexp₂ (h.elem.2 e he) he₁ he₂
  refine ⟨x₁, hx₁T, x₂, hx₂T, (x₁ * x₂)⁻¹ * e, ?_, ?_, ?_, hfN₁, hfN₂, hf3⟩
  · group
  · rw [hfeq₁]
    exact (starCentralizer J₁).mul_mem ((starCentralizer J₁).inv_mem hx₂star) hw₁
  · rw [hfeq₂]
    exact (starCentralizer J₂).mul_mem ((starCentralizer J₂).inv_mem hx₁star) hw₂

private theorem commute_sup_of_commute_two_kComp {J₁ J₂ T₁ T₂ : Subgroup G} {f : G}
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J₁)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂)
    (hfT₁ : f ∈ Subgroup.normalizer (T₁ : Set G))
    (hfT₂ : f ∈ Subgroup.normalizer (T₂ : Set G))
    (hf₁ : f ∈ starCentralizer J₁) (hf₂ : f ∈ starCentralizer J₂) :
    ∀ t ∈ T₁ ⊔ T₂, f * t = t * f := by
  have hf₁' : ∀ t ∈ T₁, f * t = t * f :=
    commute_of_mem_starCentralizer hT₁ hfT₁ hf₁
  have hf₂' : ∀ t ∈ T₂, f * t = t * f :=
    commute_of_mem_starCentralizer hT₂ hfT₂ hf₂
  have hcen₁ : T₁ ≤ Subgroup.centralizer ({f} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hf₁' t ht
  have hcen₂ : T₂ ≤ Subgroup.centralizer ({f} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hf₂' t ht
  intro t ht
  exact Subgroup.mem_centralizer_iff.mp (sup_le hcen₁ hcen₂ ht) f (Set.mem_singleton f)

private theorem false_of_factor_not_mem_sup
    {J₂ T₁ T₂ R N' : Subgroup G}
    (h₂ : IsKComp M N J₂) (ht₂ : IsSL34Star J₂ ∨ Is3A6Star J₂)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂)
    (hT₁R : T₁ ≤ R) (hT₂R : T₂ ≤ R) (hRN : R ≤ N')
    (hcomm : ⁅T₁, T₂⁆ = ⊥) (hinf : T₁ ⊓ T₂ = (Subgroup.center ↥T₁).map T₁.subtype)
    (hrank : CFSG.Open.pRank 3 N' ≤ 3)
    (hZcard₁ : Nat.card ↥((Subgroup.center ↥T₁).map T₁.subtype) = 3)
    {A : Subgroup G} (hAT : A ≤ T₁)
    (hAea : IsElemAbelian 3 A) (hAcard : Nat.card ↥A = 9) {f : G} (hf3 : f ^ 3 = 1)
    (hfcent : ∀ t ∈ T₁ ⊔ T₂, f * t = t * f) (hfV : f ∉ T₁ ⊔ T₂)
    (hfR : f ∈ R) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hvT, hvZ, hvpow⟩ :=
    exists_mem_pow_three_not_mem_center_of_sylow h₂ ht₂ hT₂
  have hcent₂ : T₂ ≤ Subgroup.centralizer (T₁ : Set G) := by
    have h := Subgroup.commutator_comm T₁ T₂
    rw [h] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hZ₁leZ₂ : (Subgroup.center ↥T₁).map T₁.subtype ≤
      (Subgroup.center ↥T₂).map T₂.subtype := by
    intro z hz
    have hzT₁ : z ∈ T₁ := Subgroup.map_subtype_le _ hz
    have hzT₂ : z ∈ T₂ := by
      have hmem : z ∈ T₁ ⊓ T₂ := by
        rw [hinf]
        exact hz
      exact (Subgroup.mem_inf.mp hmem).2
    refine Subgroup.mem_map.mpr ⟨⟨z, hzT₂⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : (y : G) * z = z * (y : G) :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hzT₁) (y : G) y.2
    exact Subtype.ext hy
  have hZeq : (Subgroup.center ↥T₂).map T₂.subtype =
      (Subgroup.center ↥T₁).map T₁.subtype := by
    refine (Subgroup.eq_of_le_of_card_ge hZ₁leZ₂ ?_).symm
    rw [(h₂.sylow_three_structure ht₂ hT₂).2.2.2, hZcard₁]
  have hvA : v ∉ A := by
    intro hvA
    have hmem : v ∈ T₁ ⊓ T₂ := ⟨hAT hvA, hvT⟩
    rw [hinf] at hmem
    exact hvZ (hZeq.symm ▸ hmem)
  have hAcomm : ∀ a ∈ A, a * v = v * a := by
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm (hAT ha)) v hvT).symm
  have hB := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hAea hvA hvpow hAcomm
  have hBleV : A ⊔ Subgroup.zpowers v ≤ T₁ ⊔ T₂ :=
    sup_le (hAT.trans le_sup_left)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hvT))
  have hfB : f ∉ A ⊔ Subgroup.zpowers v := fun hfB => hfV (hBleV hfB)
  have hfcommB : ∀ b ∈ A ⊔ Subgroup.zpowers v, b * f = f * b := by
    intro b hb
    exact (hfcent b (hBleV hb)).symm
  have hF := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hB.1 hfB hf3 hfcommB
  have hFR : A ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers f ≤ R := by
    refine sup_le (sup_le (hAT.trans hT₁R) (Subgroup.zpowers_le.mpr (hT₂R hvT))) ?_
    exact Subgroup.zpowers_le.mpr hfR
  have hcardF : Nat.card ↥(A ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers f) = 3 ^ 4 := by
    rw [hF.2, hB.2, hAcard]
    norm_num
  exact not_isElemAbelian_card_81 hrank hF.1 hcardF (hFR.trans hRN)

private theorem mem_sup_of_two_kComp
    (h : HypCGen G M 3 E N)
    (hLN : ¬ pLayerIn 3 N ≤ M) {J₁ J₂ T₁ T₂ R N' : Subgroup G}
    (hne : J₁ ≠ J₂) (h₁ : IsKComp M N J₁) (h₂ : IsKComp M N J₂)
    (ht₁ : IsSL34Star J₁) (ht₂ : IsSL34Star J₂ ∨ Is3A6Star J₂)
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J₁)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂)
    (hER : E ≤ R) (hT₁R : T₁ ≤ R) (hT₂R : T₂ ≤ R) (hRN : R ≤ N')
    (hRJ₁ : R ≤ Subgroup.normalizer (J₁ : Set G))
    (hRJ₂ : R ≤ Subgroup.normalizer (J₂ : Set G))
    (hRT₁ : R ≤ Subgroup.normalizer (T₁ : Set G))
    (hRT₂ : R ≤ Subgroup.normalizer (T₂ : Set G))
    (hcomm : ⁅T₁, T₂⁆ = ⊥) (hinf : T₁ ⊓ T₂ = (Subgroup.center ↥T₁).map T₁.subtype)
    (hrank : CFSG.Open.pRank 3 N' ≤ 3) {e : G} (he : e ∈ E) : e ∈ T₁ ⊔ T₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, hx₁T, x₂, hx₂T, f, heq, hf₁, hf₂, hfT₁, hfT₂, hf3⟩ :=
    exists_factor_of_mem_two_kComp h hLN hne h₁ h₂ ht₁ ht₂ hT₁ hT₂ hER hT₁R hT₂R
      hRJ₁ hRJ₂ hRT₁ hRT₂ hcomm he
  have hfcent : ∀ t ∈ T₁ ⊔ T₂, f * t = t * f :=
    commute_sup_of_commute_two_kComp hT₁ hT₂ hfT₁ hfT₂ hf₁ hf₂
  by_cases hfV : f ∈ T₁ ⊔ T₂
  · rw [heq]
    exact (T₁ ⊔ T₂).mul_mem ((T₁ ⊔ T₂).mul_mem (Subgroup.mem_sup_left hx₁T)
      (Subgroup.mem_sup_right hx₂T)) hfV
  · obtain ⟨A, hAT, hAea, hAcard⟩ :=
      exists_elemAbelian_card_nine_of_sylow h₁ (Or.inl ht₁) hT₁
    have hfR : f ∈ R := by
      have hx₁R : x₁ ∈ R := hT₁R hx₁T
      have hx₂R : x₂ ∈ R := hT₂R hx₂T
      have hfeq : f = (x₁ * x₂)⁻¹ * e := by
        rw [heq]
        group
      rw [hfeq]
      exact R.mul_mem (R.inv_mem (R.mul_mem hx₁R hx₂R)) (hER he)
    have hZcard₁ : Nat.card ↥((Subgroup.center ↥T₁).map T₁.subtype) = 3 :=
      (h₁.sylow_three_structure (Or.inl ht₁) hT₁).2.2.2
    exact (false_of_factor_not_mem_sup h₂ ht₂ hT₂ hT₁R hT₂R hRN hcomm hinf hrank
      hZcard₁ hAT hAea hAcard hf3 hfcent hfV hfR).elim

theorem HypCGen.le_sup_of_two_kComp
    (h : HypCGen G M 3 E N)
    (hLN : ¬ pLayerIn 3 N ≤ M)
    {J₁ J₂ T₁ T₂ R : Subgroup G} (hne : J₁ ≠ J₂) (h₁ : IsKComp M N J₁) (h₂ : IsKComp M N J₂)
    (ht₁ : IsSL34Star J₁) (ht₂ : IsSL34Star J₂ ∨ Is3A6Star J₂)
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J₁)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J₂) (hR : IsPGroup 3 R) (hRN : R ≤ N)
    (hER : E ≤ R) (hT₁R : T₁ ≤ R) (hT₂R : T₂ ≤ R)
    (hRJ₁ : R ≤ Subgroup.normalizer (J₁ : Set G))
    (hRJ₂ : R ≤ Subgroup.normalizer (J₂ : Set G))
    (hRT₁ : R ≤ Subgroup.normalizer (T₁ : Set G))
    (hRT₂ : R ≤ Subgroup.normalizer (T₂ : Set G)) :
    E ≤ T₁ ⊔ T₂ ∧ Nat.card ↥(T₁ ⊔ T₂) = 3 ^ 5 ∧ ⁅T₁, T₂⁆ = ⊥ ∧
      T₁ ⊓ T₂ = (Subgroup.center ↥T₁).map T₁.subtype ∧ ∀ x ∈ T₁ ⊔ T₂, x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : CFSG.Open.pRank 3 N ≤ 3 :=
    h.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num) h.not_mem_sigmaA
      h.isTwoLocal
  have hcomm : ⁅T₁, T₂⁆ = ⊥ :=
    commutator_eq_bot_of_two_kComp h₁ h₂ hne hT₁ hT₂ hR hT₁R hT₂R
  have hinf : T₁ ⊓ T₂ = (Subgroup.center ↥T₁).map T₁.subtype :=
    inf_eq_center_of_two_kComp h₁ h₂ ht₁ ht₂ hT₁ hT₂ hT₁R hT₂R hRN hcomm hrank
  have hcT : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
  obtain ⟨hcard₁, hexp₁, -, hZ₁⟩ := h₁.sylow_three_structure (Or.inl ht₁) hT₁
  obtain ⟨hcard₂, hexp₂, -, -⟩ := h₂.sylow_three_structure ht₂ hT₂
  refine ⟨?_, ?_, hcomm, hinf, fun x hx =>
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4.pow_eq_one_of_mem_sup hcT hexp₁ hexp₂ hx⟩
  · intro e he
    exact mem_sup_of_two_kComp h hLN hne h₁ h₂ ht₁ ht₂ hT₁ hT₂ hER hT₁R hT₂R hRN
      hRJ₁ hRJ₂ hRT₁ hRT₂ hcomm hinf hrank he
  · have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute T₁ T₂ hcT).1
    rw [hinf, hZ₁, hcard₁, hcard₂] at hcard
    omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
