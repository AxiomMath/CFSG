module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalEightExclusion
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSeven

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix SectionSix.BarTools SectionSix.Exclusion DeltaLocal DeltaLocal.Eight

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem lemma_6_8 (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hsize : 2 ^ (Nat.card (aschbacherThm5Preimage D (Abar a) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) :
        Subgroup G)).factorization 2 ≤ Nat.card d.T) :
    ∃ x ∈ aschbacherThm5Preimage D (Abar a),
      x ∉ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ∧
      Even (Nat.card (d.T ⊓ rightConjugate d.T x : Subgroup G)) ∧
      rightConjugate (factorZStar D Abar a) d.g ⊓
        rightConjugate (factorZStar D Abar a) (d.g * x) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  have hgH : d.g ∉ Subgroup.normalizer (D : Set G) :=
    fun h => d.ne ((rightConjugate_eq_self_iff _ d.g).mpr (Subgroup.le_normalizer h))
  have hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) d.g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) := ⟨d.g, rfl, d.ne, d.U, d.four⟩
  have hT2 : IsPGroup 2 d.T := d.sylowT.isPGroup
  have hTL : d.T ≤ rightConjugate A d.g := d.sylowT.le.trans inf_le_left
  obtain ⟨-, -, U', hU', hU'L⟩ := lemma_6_7 h3 hin hC hΔ a
  have hU'N := lemma_6_5_one hC d.ne hU' a
  have hTcyc : ¬ IsCyclic d.T := by
    intro hcyc
    have hU'2 : IsPGroup 2 U' := IsPGroup.of_card (n := 2) (by rw [hU'.2.2.1]; norm_num)
    obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf d.sylowT hU'2
      (le_inf hU'L hU'N)
    have hcyc' : IsCyclic (rightConjugate U' c) := Strong.isCyclic_of_le hc hcyc
    have hsq : ∀ y ∈ rightConjugate U' c, y ^ 2 = 1 :=
      (CFSG.SectionRank.isElemAbelian_map hU'.2.1 (MulAut.conj c⁻¹).toMonoidHom).2
    have h2 := card_le_two_of_isCyclic hcyc' hsq
    rw [rightConjugate_card, hU'.2.2.1] at h2
    omega
  have hex : ∃ x ∈ A, x ∉ Subgroup.normalizer (rightConjugate A d.g : Set G) ∧
      Even (Nat.card (d.T ⊓ rightConjugate d.T x : Subgroup G)) := by
    by_contra hno
    push Not at hno
    have hstar : ∀ y ∈ A, y ∉ Subgroup.normalizer (rightConjugate A d.g : Set G) →
        d.T ⊓ rightConjugate d.T y = ⊥ := fun y hy hyL =>
      two_subgroup_of_odd_eq_bot _ _ (hT2.to_le inf_le_left)
        (Nat.not_even_iff_odd.mp (hno y hy hyL)) le_rfl
    have hidx : ∀ Q : Subgroup G,
        Q ≤ A ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) →
        IsPGroup 2 Q → Nat.card Q ≤ Nat.card d.T := fun Q hQ hQ2 => by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
      have hdvd : 2 ^ k ∣ Nat.card (A ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) :
          Subgroup G) := hk ▸ Subgroup.card_dvd_of_le hQ
      have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
      calc Nat.card Q = 2 ^ k := hk
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hle
        _ ≤ Nat.card d.T := hsize
    exact not_altThree_eight h3 hC hgH d.sylowT hstar hidx
      (altThree_of_tight h3 hC hgH d.sylowT hTcyc hstar hidx)
  obtain ⟨x, hxA, hxL, hev⟩ := hex
  refine ⟨x, hxA, hxL, hev, ?_⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  have hw' : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hwT : (w : G) ∈ d.T := w.2.1
  have hxw : x * w * x⁻¹ ∈ d.T := (mem_rightConjugate_iff d.T x w).mp w.2.2
  have hw1 : (w : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hw'; omega
  have hw2 : (w : G) ^ 2 = 1 := by rw [← hw']; exact pow_orderOf_eq_one _
  obtain ⟨b, hba⟩ := Strong.exists_ne_index (two_le hC) a
  have hC' := hC.conj d.g
  have hA'eq : aschbacherThm5Preimage (rightConjugate D d.g) (conjFactors D Abar d.g a) =
      rightConjugate A d.g := preimage_conjFactors D Abar d.g a
  have hTA' : d.T ≤ aschbacherThm5Preimage (rightConjugate D d.g) (conjFactors D Abar d.g a) := by
    rw [hA'eq]
    exact hTL
  have hA'b := factor_le_centralizing hC'.hyp.hcomm hba (D := rightConjugate D d.g)
    (Abar := conjFactors D Abar d.g)
  have hxH' : x ∈ Subgroup.normalizer ((rightConjugate D d.g : Subgroup G) : Set G) := by
    refine mem_normalizer_of_fusion hC' b b (t := x * w * x⁻¹) (g := x) ⟨1, ?_⟩ ?_
      (centralizes_of_mem_centralizing (hA'b (hTA' hxw))) ?_
    · rw [pow_one, conj_pow, hw2]
      group
    · intro h
      apply hw1
      calc (w : G) = x⁻¹ * (x * w * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · rw [show x⁻¹ * (x * w * x⁻¹) * x = w by group]
      exact centralizes_of_mem_centralizing (hA'b (hTA' hwT))
  have hxA' : x ∉ Subgroup.normalizer ((aschbacherThm5Preimage (rightConjugate D d.g)
      (conjFactors D Abar d.g a) : Subgroup G) : Set G) := by
    rw [hA'eq]
    exact hxL
  obtain ⟨j, hj⟩ := hC'.hyp.hperm x hxH' a
  have hja : j ≠ a := by
    rintro rfl
    exact hxA' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hj)
  obtain ⟨j', hj'⟩ := hC'.hyp.hperm x⁻¹ (Subgroup.inv_mem _ hxH') a
  have hj'a : j' ≠ a := by
    rintro rfl
    exact hxA' ((Subgroup.inv_mem_iff _).mp (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hj'))
  have hwj' : (w : G) ∈ aschbacherThm5Preimage (rightConjugate D d.g)
      (conjFactors D Abar d.g j') := by
    rw [← hj']
    exact ⟨x * w * x⁻¹, hTA' hxw, by simp [mul_assoc]⟩
  have hsj : x * w * x⁻¹ ∈ aschbacherThm5Preimage (rightConjugate D d.g)
      (conjFactors D Abar d.g j) := by
    rw [← hj]
    exact ⟨w, hTA' hwT, by simp⟩
  have hAD : A ≤ D := preimage_le D _
  have hwZ : (w : G) ∈ rightConjugate (factorZStar D Abar a) d.g := by
    rw [mem_rightConjugate_iff]
    have hgw : d.g * w * d.g⁻¹ ∈ A := (mem_rightConjugate_iff A d.g w).mp (hTL hwT)
    refine ⟨hgw, (mem_centralizing_iff _ _).mpr ⟨hAD hgw, ?_⟩⟩
    exact (centralizes_conj_iff D Abar d.g a w).mp (centralizes_of_mem_centralizing
      (factor_le_centralizing hC'.hyp.hcomm (Ne.symm hj'a) hwj'))
  have hwZx : (w : G) ∈ rightConjugate (factorZStar D Abar a) (d.g * x) := by
    rw [mem_rightConjugate_iff, show d.g * x * w * (d.g * x)⁻¹ = d.g * (x * w * x⁻¹) * d.g⁻¹ by
      group]
    have hgs : d.g * (x * w * x⁻¹) * d.g⁻¹ ∈ A := (mem_rightConjugate_iff A d.g _).mp (hTL hxw)
    refine ⟨hgs, (mem_centralizing_iff _ _).mpr ⟨hAD hgs, ?_⟩⟩
    exact (centralizes_conj_iff D Abar d.g a _).mp (centralizes_of_mem_centralizing
      (factor_le_centralizing hC'.hyp.hcomm (Ne.symm hja) hsj))
  intro hbot
  have hmem : (w : G) ∈ rightConjugate (factorZStar D Abar a) d.g ⊓
      rightConjugate (factorZStar D Abar a) (d.g * x) := ⟨hwZ, hwZx⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hw1 hmem

end CFSG.ComponentClassification.AschbacherTheorem5
