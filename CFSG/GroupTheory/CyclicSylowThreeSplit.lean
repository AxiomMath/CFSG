module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.CyclicSylow
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {A : Type*} [Group A]

theorem mul_inv_mem_or_sq_mul_inv_mem_of_sup_zpowers {S P : Subgroup A} {a : A}
    (hP : P = S ⊔ Subgroup.zpowers a) (hSP : P ≤ Subgroup.normalizer (S : Set A))
    (ha3 : a ^ 3 ∈ S) (haP : a ∈ P) (haS : a ∉ S) {y : A} (hyP : y ∈ P) (hyS : y ∉ S) :
    y * a⁻¹ ∈ S ∨ y ^ 2 * a⁻¹ ∈ S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hSleP : S ≤ P := by rw [hP]; exact le_sup_left
  have hzpleP : Subgroup.zpowers a ≤ P := by rw [hP]; exact le_sup_right
  let K : Subgroup P := S.subgroupOf P
  haveI hKn : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSleP).mpr hSP
  have hzps : (Subgroup.zpowers a).subgroupOf P = Subgroup.zpowers (⟨a, haP⟩ : P) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hKtop : K ⊔ Subgroup.zpowers (⟨a, haP⟩ : P) = ⊤ := by
    have h1 : (S ⊔ Subgroup.zpowers a).subgroupOf P = ⊤ :=
      Subgroup.subgroupOf_eq_top.mpr (by rw [hP])
    rw [Subgroup.subgroupOf_sup hSleP hzpleP, hzps] at h1
    exact h1
  have hgen : Subgroup.zpowers (QuotientGroup.mk' K ⟨a, haP⟩) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' K)) hKtop
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top,
      QuotientGroup.range_mk'] at h
    rw [← h, (Subgroup.map_eq_bot_iff K).mpr (by rw [QuotientGroup.ker_mk']), bot_sup_eq]
  have ha3' : (QuotientGroup.mk' K ⟨a, haP⟩) ^ 3 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using ha3
  have hbne : QuotientGroup.mk' K ⟨y, hyP⟩ ≠ 1 := by
    rw [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hyS
  have hb : QuotientGroup.mk' K ⟨y, hyP⟩ ∈
      Subgroup.zpowers (QuotientGroup.mk' K ⟨a, haP⟩) := by
    rw [hgen]
    exact Subgroup.mem_top _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hred : (QuotientGroup.mk' K ⟨a, haP⟩) ^ i =
      (QuotientGroup.mk' K ⟨a, haP⟩) ^ (i % 3) := zpow_eq_zpow_emod i (by simpa using ha3')
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by
    have h0 : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
    have h1 : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
    omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero] at hred
    exact absurd (hi ▸ hred) hbne
  · left
    have hxy : QuotientGroup.mk' K ⟨y, hyP⟩ = QuotientGroup.mk' K ⟨a, haP⟩ := by
      rw [← hi, hred, h, zpow_one]
    have hmem : (⟨y, hyP⟩ : P) * (⟨a, haP⟩ : P)⁻¹ ∈ K := by
      have h1 : QuotientGroup.mk' K ((⟨y, hyP⟩ : P) * (⟨a, haP⟩ : P)⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : y * a⁻¹ ∈ S := by
      have := (Subgroup.mem_subgroupOf (H := S) (K := P)).mp hmem
      simpa using this
    exact h2
  · right
    have hxy : QuotientGroup.mk' K ⟨y, hyP⟩ = (QuotientGroup.mk' K ⟨a, haP⟩) ^ 2 := by
      rw [← hi, hred, h]
      exact zpow_natCast _ 2
    have hEq : (QuotientGroup.mk' K ⟨y, hyP⟩) ^ 2 = QuotientGroup.mk' K ⟨a, haP⟩ := by
      rw [hxy, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, ha3', one_mul, pow_one]
    have hmem : (⟨y, hyP⟩ : P) ^ 2 * (⟨a, haP⟩ : P)⁻¹ ∈ K := by
      have h1 : QuotientGroup.mk' K ((⟨y, hyP⟩ : P) ^ 2 * (⟨a, haP⟩ : P)⁻¹) = 1 := by
        rw [map_mul, map_pow, map_inv, hEq, mul_inv_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : y ^ 2 * a⁻¹ ∈ S := by
      have := (Subgroup.mem_subgroupOf (H := S) (K := P)).mp hmem
      simpa using this
    exact h2

theorem exists_mul_pow_three_eq_one_of_isCyclic {A : Type*} [Group A] [Finite A]
    {I : Subgroup A} (hIn : I.Normal) (hIp : ⁅I, I⁆ = I) {R S : Subgroup A}
    (hR : IsPGroup 3 R) (hS : CFSG.ABGLocalTools.IsSylowOf 3 S I) (hSc : IsCyclic S)
    (hSR : S ≤ R) {α : A} (hα : α ∈ R) (hα3 : α ^ 3 ∈ S) :
    ∃ s ∈ S, (s * α) ^ 3 = 1 := by
  classical
  haveI h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI hScyc : IsCyclic ↥S := hSc
  have hSeq : R ⊓ I = S :=
    hS.eq_of_le (le_inf hSR hS.le) inf_le_right hR.to_inf_left
  have hRnorm : R ≤ Subgroup.normalizer (S : Set A) := by
    rw [← hSeq]
    exact Subgroup.le_normalizer_iff.mpr fun r hr x hx =>
      ⟨R.mul_mem (R.mul_mem hr hx.1) (R.inv_mem hr), hIn.conj_mem x hx.2 r⟩
  by_cases hαI : α ∈ I
  · refine ⟨α⁻¹, ?_, ?_⟩
    · rw [← hSeq]
      exact ⟨R.inv_mem hα, I.inv_mem hαI⟩
    · rw [inv_mul_cancel, one_pow]
  ·
    set P : Subgroup A := S ⊔ Subgroup.zpowers α with hPdef
    have hSleP : S ≤ P := by rw [hPdef]; exact le_sup_left
    have hαP : α ∈ P := by
      rw [hPdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers α)
    have hαS : α ∉ S := fun h => hαI (hS.le h)
    have hPleR : P ≤ R := by
      rw [hPdef]; exact sup_le hSR (Subgroup.zpowers_le.mpr hα)
    have hPnorm : P ≤ Subgroup.normalizer (S : Set A) := hPleR.trans hRnorm
    have hHdef : I ⊔ P = I ⊔ Subgroup.zpowers α := by
      rw [hPdef, ← sup_assoc, sup_eq_left.mpr hS.le]
    have hIP : P ⊓ I = S :=
      hS.eq_of_le (le_inf hSleP hS.le) inf_le_right (hR.to_le hPleR).to_inf_left
    have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P (I ⊔ P) := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_sup_right, hR.to_le hPleR, ?_⟩
      rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal I P]
      have hPeq : P.subgroupOf I = S.subgroupOf I := by
        ext x
        simp only [Subgroup.mem_subgroupOf]
        rw [← hIP]
        exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
      have hrel : P.relIndex I = S.relIndex I := by
        rw [show P.relIndex I = (P.subgroupOf I).index from rfl,
          show S.relIndex I = (S.subgroupOf I).index from rfl, hPeq]
      rw [hrel]
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
    have hHcomm : ⁅I ⊔ Subgroup.zpowers α, I ⊔ Subgroup.zpowers α⁆ = I := by
      refine le_antisymm ?_ ?_
      · rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [Subgroup.mem_sup_of_normal_left] at hx hy
        obtain ⟨i₁, hi₁, a₁, ha₁, rfl⟩ := hx
        obtain ⟨i₂, hi₂, a₂, ha₂, rfl⟩ := hy
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₁
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₂
        have hcomm : α ^ m * α ^ n = α ^ n * α ^ m := zpow_mul_comm α m n
        have h1 : α ^ m * i₂ * (α ^ m)⁻¹ ∈ I := hIn.conj_mem i₂ hi₂ (α ^ m)
        have h2 : α ^ n * i₁⁻¹ * (α ^ n)⁻¹ ∈ I := hIn.conj_mem i₁⁻¹ (I.inv_mem hi₁) (α ^ n)
        have heq : ⁅i₁ * α ^ m, i₂ * α ^ n⁆ =
            i₁ * (α ^ m * i₂ * (α ^ m)⁻¹) *
              (α ^ m * α ^ n * (α ^ m)⁻¹ * (α ^ n)⁻¹) *
              (α ^ n * i₁⁻¹ * (α ^ n)⁻¹) * i₂⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [heq, show α ^ m * α ^ n * (α ^ m)⁻¹ * (α ^ n)⁻¹ = 1 from by rw [hcomm]; group,
          mul_one]
        exact I.mul_mem (I.mul_mem (I.mul_mem hi₁ h1) h2) (I.inv_mem hi₂)
      · calc I = ⁅I, I⁆ := hIp.symm
          _ ≤ ⁅I ⊔ Subgroup.zpowers α, I ⊔ Subgroup.zpowers α⁆ :=
              Subgroup.commutator_mono le_sup_left le_sup_left
    have hmap : Subgroup.map (I ⊔ P).subtype (commutator ↥(I ⊔ P)) = I := by
      have h1 : Subgroup.map (I ⊔ P).subtype ⁅(⊤ : Subgroup ↥(I ⊔ P)), ⊤⁆ = I := by
        rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hHdef]
        exact hHcomm
      exact h1
    by_cases hPcyc : IsCyclic ↥P
    ·
      haveI hPc : IsCyclic ↥P := hPcyc
      obtain ⟨Q, hQeq⟩ := hPsyl.exists_sylow_eq_subgroupOf
      have hPH : P ≤ I ⊔ P := le_sup_right
      have hQcyc : IsCyclic ↥(Q : Subgroup ↥(I ⊔ P)) := by
        rw [hQeq]
        exact isCyclic_of_surjective
          (Subgroup.subgroupOfEquivOfLe hPH).symm.toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hPH).symm.surjective
      rcases CFSG.sylow_inf_commutator_eq_bot_or_le_commutator 3 Q hQcyc with hbot | hle
      ·
        have hPbot : P ⊓ I = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨hxP, hxI⟩ := hx
          have hxH : x ∈ I ⊔ P := hPH hxP
          have hxQ : (⟨x, hxH⟩ : ↥(I ⊔ P)) ∈ (Q : Subgroup ↥(I ⊔ P)) := by
            rw [hQeq]; exact hxP
          have hxc : (⟨x, hxH⟩ : ↥(I ⊔ P)) ∈ commutator ↥(I ⊔ P) := by
            have hx' : x ∈ Subgroup.map (I ⊔ P).subtype (commutator ↥(I ⊔ P)) := by
              rw [hmap]; exact hxI
            obtain ⟨c, hc, hcx⟩ := hx'
            have hceq : c = ⟨x, hxH⟩ := by
              apply (I ⊔ P).subtype_injective
              simpa using hcx
            rwa [← hceq]
          have hmem : (⟨x, hxH⟩ : ↥(I ⊔ P)) ∈
              ((Q : Subgroup ↥(I ⊔ P)) ⊓ commutator ↥(I ⊔ P)) := ⟨hxQ, hxc⟩
          rw [hbot] at hmem
          simpa using hmem
        have hSbot : S = ⊥ := by rw [← hIP]; exact hPbot
        refine ⟨1, ?_, ?_⟩
        · rw [hSbot]; exact Subgroup.mem_bot.mpr rfl
        · rw [one_mul]
          rw [hSbot] at hα3
          simpa using hα3
      ·
        exact absurd (show α ∈ I from (show P ≤ I from
          calc P = Subgroup.map (I ⊔ P).subtype (Q : Subgroup ↥(I ⊔ P)) := by
                rw [hQeq, Subgroup.map_subgroupOf_eq_of_le hPH]
            _ ≤ Subgroup.map (I ⊔ P).subtype (commutator ↥(I ⊔ P)) := Subgroup.map_mono hle
            _ = I := hmap) hαP) hαI
    ·
      obtain ⟨B, hBelem, hBcard⟩ :=
        CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two (p := 3)
          (show Odd 3 from ⟨1, by norm_num⟩) (hR.to_le hPleR) hPcyc
      let E : Subgroup A := B.map P.subtype
      have hEP : E ≤ P := Subgroup.map_subtype_le B
      have hEcard : Nat.card E = 9 := by
        rw [show (9 : ℕ) = 3 ^ 2 from rfl, ← hBcard,
          Subgroup.card_map_of_injective P.subtype_injective]
      have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
        rintro x ⟨b, hb, rfl⟩
        haveI : CFSG.IsElementaryAbelian 3 ↥B := hBelem
        have hb3 : b ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := B) b hb
        simpa using congrArg (⇑P.subtype) hb3
      have hEnotS : ¬ E ≤ S := by
        intro hES
        haveI : IsCyclic ↥E := Subgroup.isCyclic_of_le hES
        have hdvd : Nat.card ↥E ∣ 3 := by
          rw [← IsCyclic.exponent_eq_card]
          exact Monoid.exponent_dvd_of_forall_pow_eq_one
            fun g => Subtype.ext (hEexp (g : A) g.2)
        have hle : Nat.card ↥E ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
        rw [hEcard] at hle
        norm_num at hle
      obtain ⟨x, hxE, hxS⟩ := SetLike.not_le_iff_exists.mp hEnotS
      have hxP : x ∈ P := hEP hxE
      have hx3 : x ^ 3 = 1 := hEexp x hxE
      rcases mul_inv_mem_or_sq_mul_inv_mem_of_sup_zpowers hPdef hPnorm hα3 hαP hαS
        hxP hxS with h | h
      · refine ⟨x * α⁻¹, h, ?_⟩
        have hxα : x * α⁻¹ * α = x := by rw [mul_assoc, inv_mul_cancel, mul_one]
        rw [hxα, hx3]
      · refine ⟨x ^ 2 * α⁻¹, h, ?_⟩
        have hx23 : (x ^ 2) ^ 3 = 1 := by
          rw [← pow_mul]
          rw [show 2 * 3 = 3 * 2 from rfl, pow_mul, hx3, one_pow]
        have hxα : x ^ 2 * α⁻¹ * α = x ^ 2 := by rw [mul_assoc, inv_mul_cancel, mul_one]
        rw [hxα, hx23]

end CFSG.GroupTheory
