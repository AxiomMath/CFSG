module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainFactors

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace FieldHyps

variable {t g : G}

theorem exists_orderOf_four (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) :
    ∃ e ∈ aschbacherThm5Preimage D (Abar i), e * t = t * e ∧ orderOf e = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ē, hfix, hord⟩ := hF.exists_fixed_orderOf_four hin hC hii' hnd
  set H := Subgroup.normalizer (D : Set G)
  set t' : H := ⟨t, hF.mem⟩
  have ht' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe]; exact hF.two
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D)
    (ē : D ⧸ aschbacherThm5OddCore D)
  have hdA : (d : G) ∈ aschbacherThm5Preimage D (Abar i) := by
    rw [mem_preimage_iff, hd]
    exact ē.2
  set h₀ : H := Subgroup.inclusion Subgroup.le_normalizer d
  have hqE : quotientEmbedding D (ē : D ⧸ aschbacherThm5OddCore D) = toBar D h₀ := by
    rw [← hd, quotientEmbedding_mk]
    rfl
  have hcomm : toBar D h₀ ∈ Subgroup.centralizer ({toBar D t'} : Set (Bar D)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hqE]
    have h1 := quotientEmbedding_onQuotient (D := D) t' (ē : D ⧸ aschbacherThm5OddCore D)
    rw [← hF.alpha_apply i ē, hfix] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm
  rw [centralizer_toBar_eq t' ht'] at hcomm
  obtain ⟨h, hh, hhe⟩ := hcomm
  have hhA : (h : G) ∈ aschbacherThm5Preimage D (Abar i) := by
    have hker : h₀⁻¹ * h ∈ coreIn D := by
      rw [← ker_toBar, MonoidHom.mem_ker, map_mul, map_inv, hhe, inv_mul_cancel]
    have hmem := Subgroup.mem_subgroupOf.mp hker
    have hcore := core_le_preimage D (Abar i) hmem
    have h2 : (h : G) = (h₀ : G) * ((h₀⁻¹ * h : H) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h2]
    exact Subgroup.mul_mem _ hdA hcore
  set C : Subgroup H := Subgroup.centralizer ({t'} : Set H) ⊓
    (aschbacherThm5Preimage D (Abar i)).subgroupOf H
  have hhC : h ∈ C := ⟨hh, Subgroup.mem_subgroupOf.mpr hhA⟩
  set V := Subgroup.zpowers (toBar D h)
  have hVord : orderOf (toBar D h) = 4 := by
    rw [hhe, ← hqE, orderOf_injective _ (quotientEmbedding_injective D), Subgroup.orderOf_coe,
      hord]
  have hV2 : IsPGroup 2 V :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hVord]; norm_num)
  have hVC : V ≤ C.map (QuotientGroup.mk' (coreIn D)) :=
    Subgroup.zpowers_le.mpr ⟨h, hhC, rfl⟩
  obtain ⟨W, hWC, hW2, hWcard, hWmap⟩ := exists_isPGroup_lift (coreIn D) (coreIn_odd D) hV2 hVC
  have hmemV : toBar D h ∈ W.map (QuotientGroup.mk' (coreIn D)) := by
    rw [hWmap]
    exact Subgroup.mem_zpowers _
  obtain ⟨w, hwW, hwh⟩ := hmemV
  have hwo : orderOf w = 4 := by
    have h1 : orderOf (toBar D w) ∣ orderOf w := orderOf_map_dvd _ _
    have h2 : orderOf w ∣ 4 := by
      have := Subgroup.orderOf_dvd_natCard W hwW
      rwa [hWcard, Nat.card_zpowers, hVord] at this
    have h3 : toBar D w = toBar D h := hwh
    rw [h3, hVord] at h1
    exact Nat.dvd_antisymm h2 h1
  obtain ⟨hwt, hwA⟩ := hWC hwW
  refine ⟨w, Subgroup.mem_subgroupOf.mp hwA, ?_, by rw [Subgroup.orderOf_coe]; exact hwo⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hwt)

theorem exists_config (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) {j m : Fin 2} (hjm : j ≠ m)
    (hj : aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
      (g * t * g⁻¹)) :
    ∃ e ∈ aschbacherThm5Preimage D (Abar i), e * t = t * e ∧ orderOf e = 4 ∧
      orderOf (e * e) = 2 ∧
      (∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k)).map
        (MulAut.conj (e * e)).toMonoidHom =
          aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k)) ∧
      t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) := by
  have hC' := hC.conj g
  have hN' := normalizer_rightConjugate D g
  obtain ⟨e, heA, het, he4⟩ := hF.exists_orderOf_four hin hC hii' hnd
  have hcK : ∀ x : G, x * t = t * x →
      x ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := fun x hx =>
    hN' ▸ (hF.hyp71 hC).centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr hx)
  have heN : e ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := hcK e het
  have hr2 : orderOf (e * e) = 2 := by
    rw [← sq, orderOf_pow' e two_ne_zero, he4]
    rfl
  have hnorm := fun k => sq_map_factor hC'.hyp heN k
  refine ⟨e, heA, het, he4, hr2, hnorm, ?_⟩
  have htj : aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j)) t :=
    (centralizes_conj_iff D Abar g j t).mpr hj
  have htN : t ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    hcK t rfl
  have htLj := mem_normalizer_of_centralizes (core_le_preimage _ _) htj
  have htLm := map_other_of_map hC'.hyp htN hjm
    ((Subgroup.mem_normalizer_iff_map_conj_eq).mp htLj)
  have hrt : e * e * t = t * (e * e) := by
    rw [mul_assoc, het, ← mul_assoc, het, mul_assoc]
  exact mem_factor_of_centralizes hin hC (hF.hyp71 hC) hjm htj hr2 hrt
    (centralizer_le_of_mem_factor hC (Subgroup.mul_mem _ heA heA)
      (two_power_of_orderOf hr2) (by rintro h; rw [h, orderOf_one] at hr2; omega))
    ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr (hnorm m))
    ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr htLm)

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
