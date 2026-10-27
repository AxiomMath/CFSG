module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16d
public import CFSG.Goldschmidt.Final

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup ThmC GL42 CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

namespace E16

variable {X : Type} [Group X] [Finite X] {D : ThmC.UTSylow X}

namespace CaseB

theorem normalizer_le (hB : CaseB D) {K : Subgroup X} (hK : gComp D.E K)
    (hEK : D.E ≤ K) {g : X} (hg : g ∈ normalizer (D.E : Set X)) {k : X} (hk : k ∈ K) :
    g * k * g⁻¹ ∈ K := by
  have hEKg : D.E ≤ K.map (MulAut.conj g).toMonoidHom := fun e he => by
    rw [mem_conj_iff]
    have h := (mem_normalizer_iff.mp (inv_mem hg) e).mp he
    rw [inv_inv] at h
    exact hEK h
  by_cases hKK : K.map (MulAut.conj g).toMonoidHom = K
  · rw [← hKK]
    exact ⟨k, hk, rfl⟩
  · have he : D.toX ⟨1, 0, 0⟩ ∈ D.E := D.toX_mem_E_iff.mpr rfl
    exact absurd (hB.eq_one_of_mem hK (gComp_conj hK g) (Ne.symm hKK) (hEK he) (hEKg he))
      (toX_ne_one (by decide))


theorem psi_eq_one (hB : CaseB D) {K : Subgroup X} (hK : gComp D.E K) (hEK : D.E ≤ K)
    (m : normalizer (D.E : Set X)) (hm : (m : X) ∈ K) (hm2 : D.psi m ^ 2 = 1) :
    D.psi m = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  have hpsi : D.psi (m ^ r) = D.psi m := by
    obtain ⟨j, rfl⟩ := hr
    rw [map_pow, pow_succ, pow_mul, hm2, one_pow, one_mul]
  have hm'2 : (m ^ r) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hkr, pow_orderOf_eq_one]
  have hp : IsPGroup 2 (zpowers ((m ^ r : normalizer (D.E : Set X)) : X)) := by
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hm'2
  have hmK : ((m ^ r : normalizer (D.E : Set X)) : X) ∈ K := by
    rw [SubgroupClass.coe_pow]
    exact pow_mem hm r
  have hR : IsPGroup 2 (D.E ⊔ zpowers ((m ^ r : normalizer (D.E : Set X)) : X) : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' (D.T.isPGroup'.to_le D.E_le_T) hp
      (zpowers_le.mpr (m ^ r).2)
  have hEq := ((hB.comp_facts hK).2 hEK).2 _ hR le_sup_left (sup_le hEK (zpowers_le.mpr hmK))
  have hmE : ((m ^ r : normalizer (D.E : Set X)) : X) ∈ D.E :=
    hEq.le (mem_sup_right (mem_zpowers _))
  rw [← hpsi]
  exact (D.psi_eq_one_iff _).mpr (D.E_le_centralizer hmE)


theorem psi_comm (hB : CaseB D) {K : Subgroup X} (hK : gComp D.E K) (hEK : D.E ≤ K)
    (hn : ∃ n ∈ normalizer (D.E : Set X), ∃ t ∈ (D.T : Subgroup X),
      n * t * n⁻¹ ∉ (D.T : Subgroup X) ⊔ centralizer (D.E : Set X))
    (m : normalizer (D.E : Set X)) (hm : (m : X) ∈ K) (g : D.psi.range) :
    D.psi.rangeRestrict m * g = g * D.psi.rangeRestrict m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup D.psi.range := (K.subgroupOf (normalizer (D.E : Set X))).map
    D.psi.rangeRestrict
  have hmA : D.psi.rangeRestrict m ∈ A := ⟨m, mem_subgroupOf.mpr hm, rfl⟩
  have hAn : A.Normal := by
    have hKN : (K.subgroupOf (normalizer (D.E : Set X))).Normal :=
      ⟨fun n hn g => mem_subgroupOf.mpr (hB.normalizer_le hK hEK g.2 (mem_subgroupOf.mp hn))⟩
    exact hKN.map _ D.psi.rangeRestrict_surjective
  have hAodd : ¬ 2 ∣ Nat.card A := by
    intro h2
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨m₀, hm₀, hm₀a⟩ := a.2
    have h1 : orderOf (D.psi.rangeRestrict m₀) = orderOf a := by
      rw [hm₀a, Subgroup.orderOf_coe]
    have hord : orderOf (D.psi m₀) = 2 := by
      rw [← MonoidHom.coe_rangeRestrict D.psi m₀, Subgroup.orderOf_coe, h1, ha]
    have h3 := hB.psi_eq_one hK hEK m₀ (mem_subgroupOf.mp hm₀) (by
      have h4 := pow_orderOf_eq_one (D.psi m₀)
      rwa [hord] at h4)
    rw [h3, orderOf_one] at hord
    omega
  rcases (D.sylE0).iso_a5 (D.sylE0_not_normal hn) with he | he
  ·
    obtain ⟨e⟩ := he
    have := hAn.map e.toMonoidHom e.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map e.toMonoidHom) with h | h
    · have hA1 : A = ⊥ := (map_eq_bot_iff_of_injective _ e.injective).mp h
      rw [hA1, mem_bot] at hmA
      rw [hmA, one_mul, mul_one]
    · exfalso
      apply hAodd
      rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, h, card_top, card_A5]
      norm_num
  ·
    obtain ⟨e⟩ := he
    have hS : ((A.map e.toMonoidHom).map (MonoidHom.snd _ _)).Normal :=
      (hAn.map e.toMonoidHom e.surjective).map _ fun x => ⟨(1, x), rfl⟩
    have hS' : (A.map e.toMonoidHom).map (MonoidHom.snd _ _) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((A.map e.toMonoidHom).map (MonoidHom.snd _ _)) with h | h
      · exact h
      · exfalso
        apply hAodd
        have h1 := card_map_dvd (A.map e.toMonoidHom) (MonoidHom.snd _ _)
        rw [card_map_of_injective (f := e.toMonoidHom) e.injective, h, card_top, card_A5] at h1
        exact dvd_trans (by norm_num) h1
    have h2 : (e (D.psi.rangeRestrict m)).2 = 1 := by
      have h := mem_map_of_mem (MonoidHom.snd _ _) (mem_map_of_mem e.toMonoidHom hmA)
      rw [hS', mem_bot] at h
      exact h
    apply e.injective
    rw [map_mul, map_mul]
    refine Prod.ext (mul_comm _ _) ?_
    rw [Prod.snd_mul, Prod.snd_mul, h2, one_mul, mul_one]

theorem conj_mem_T_sup (hB : CaseB D) {K : Subgroup X} (hK : gComp D.E K) (hEK : D.E ≤ K)
    {n : X} (hnN : n ∈ normalizer (D.E : Set X)) (hnK : n ∈ K) {t : X}
    (ht : t ∈ (D.T : Subgroup X)) :
    n * t * n⁻¹ ∈ (D.T : Subgroup X) ⊔ centralizer (D.E : Set X) := by
  by_cases hn : ∃ n ∈ normalizer (D.E : Set X), ∃ t ∈ (D.T : Subgroup X),
      n * t * n⁻¹ ∉ (D.T : Subgroup X) ⊔ centralizer (D.E : Set X)
  · have hc := hB.psi_comm hK hEK hn ⟨n, hnN⟩ hnK
      (D.psi.rangeRestrict ⟨t, D.T_le_normalizer ht⟩)
    have hc' : D.psi (⟨n, hnN⟩ * ⟨t, D.T_le_normalizer ht⟩ * ⟨n, hnN⟩⁻¹ *
        ⟨t, D.T_le_normalizer ht⟩⁻¹) = 1 := by
      have h := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict] at h
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
      group
    have hcen : n * t * n⁻¹ * t⁻¹ ∈ centralizer (D.E : Set X) := (D.psi_eq_one_iff _).mp hc'
    rw [show n * t * n⁻¹ = (n * t * n⁻¹ * t⁻¹) * t by group]
    exact mul_mem (mem_sup_right hcen) (mem_sup_left ht)
  · push Not at hn
    exact hn n hnN t ht

theorem false_of_caseB (hB : CaseB D) : False := by
  obtain ⟨K, hK, hTK⟩ := hB.exists_normalized
  have hEK := hB.E_le_of_normalized hK hTK
  have hz₀E : D.toX ⟨0, 0, 1⟩ ∈ D.E := D.toX_mem_E_iff.mpr rfl
  have hz₀Z : D.toX ⟨0, 0, 1⟩ ∈ D.Z := D.toX_mem_Z_iff.mpr ⟨rfl, rfl⟩
  have he₁E : D.toX ⟨1, 0, 0⟩ ∈ D.E := D.toX_mem_E_iff.mpr rfl
  obtain ⟨n, hnK, hnN, hn⟩ := ((hB.comp_facts hK).2 hEK).1 _ hz₀E _ he₁E
    (toX_ne_one (by decide)) (toX_ne_one (by decide))
  have hle : (D.T : Subgroup X) ⊔ centralizer (D.E : Set X) ≤
      centralizer ({D.toX ⟨0, 0, 1⟩} : Set X) :=
    sup_le (fun s hs => mem_centralizer_singleton_iff.mpr (D.Z_comm hz₀Z hs).symm)
      (fun c hc => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc _ hz₀E).symm)
  have htT : D.toX ⟨0, 1, 0⟩ ∈ (D.T : Subgroup X) := D.toX_mem _
  have htE : D.toX ⟨0, 1, 0⟩ ∉ D.E := toX_not_mem_E (by decide)
  have h1 := mem_centralizer_singleton_iff.mp (hle (hB.conj_mem_T_sup hK hEK hnN hnK htT))
  have h2 : D.toX ⟨1, 0, 0⟩ * D.toX ⟨0, 1, 0⟩ = D.toX ⟨0, 1, 0⟩ * D.toX ⟨1, 0, 0⟩ := by
    rw [← hn]
    calc n⁻¹ * D.toX ⟨0, 0, 1⟩ * n * D.toX ⟨0, 1, 0⟩ =
        n⁻¹ * (D.toX ⟨0, 0, 1⟩ * (n * D.toX ⟨0, 1, 0⟩ * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * D.toX ⟨0, 1, 0⟩ * n⁻¹) * D.toX ⟨0, 0, 1⟩) * n := by rw [← h1]
      _ = D.toX ⟨0, 1, 0⟩ * (n⁻¹ * D.toX ⟨0, 0, 1⟩ * n) := by group
  have h3 := D.mem_Z_of_comm_of_not_mem he₁E htT htE h2
  exact absurd (D.toX_mem_Z_iff.mp h3).1 (by decide)

end CaseB

end E16

section Main


theorem E16.E_normal {X : Type} [Group X] [Finite X] (D : ThmC.UTSylow X)
    (hO : pPrimeCore 2 X = ⊥)
    (hcl : ∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E) :
    D.E.Normal := by
  rcases E16.normal_or_Z_le D CFSG.Goldschmidt.topStatement hO hcl with h | hZ
  · exact h
  · exact (E16.CaseB.false_of_caseB
      (E16.caseB_of D CFSG.Goldschmidt.topStatement hO hcl hZ)).elim

theorem stronglyClosedE16Input : StronglyClosedE16Input := by
  intro X _ _ hO T hT A hAT h16 hA2 hAc hcl
  obtain ⟨φ⟩ := hT
  let D : UTSylow X := ⟨T, (φ.trans sylLCongr).symm⟩
  rcases D.eq_E_or_F hAT hA2 hAc h16 with rfl | rfl
  · exact E16.E_normal D hO hcl
  · have hcl' : ∀ a ∈ D.swap.E, ∀ g : X, g⁻¹ * a * g ∈ (D.swap.T : Subgroup X) →
        g⁻¹ * a * g ∈ D.swap.E := by
      rw [UTSylow.swap_E]
      exact hcl
    have h := E16.E_normal D.swap hO hcl'
    rwa [UTSylow.swap_E] at h

theorem gorensteinHaradaThmCInput_holds : GorensteinHaradaThmCInput :=
  gorensteinHaradaThmCInput_of_E16 stronglyClosedE16Input

end Main

end CFSG.ComponentClassification.GHarris
