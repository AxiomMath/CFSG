module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisMb2

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.ut_ab_cases : ∀ u : UT3 F4c, u.a = 0 → u.b = 0 →
    u = 1 ∨ u = toUT (invRep 1) ∨ u = toUT (invRep 2) ∨ u = toUT (invRep 1) * toUT (invRep 2) := by
  decide +kernel

theorem SCert.SE.ut_t_a1l : (toUT (invRep 1)).a = 0 ∧ (toUT (invRep 1)).b = 0 ∧
    (toUT (invRep 2)).a = 0 ∧ (toUT (invRep 2)).b = 0 ∧ toUT (invRep 1) ≠ toUT (invRep 2) := by
  decide

theorem exists_conj_of_pow_three {X : Type*} [Group X] {w k₁ k₂ : X} (hw : w ^ 3 = 1)
    (h1 : k₁ * k₁ = 1) (h2 : k₂ * k₂ = 1) (hk₁ : k₁ ≠ 1) (hk₂ : k₂ ≠ 1) (h12 : k₁ ≠ k₂)
    (hK : ∀ c, c = 1 ∨ c = k₁ ∨ c = k₂ ∨ c = k₁ * k₂ → w⁻¹ * c * w = 1 ∨ w⁻¹ * c * w = k₁ ∨
      w⁻¹ * c * w = k₂ ∨ w⁻¹ * c * w = k₁ * k₂)
    (hfix : w⁻¹ * k₁ * w = k₁ → w⁻¹ * k₂ * w = k₂ → False) : ∃ g : X, g⁻¹ * k₁ * g = k₂ := by
  have hmul : ∀ c d : X, w⁻¹ * (c * d) * w = w⁻¹ * c * w * (w⁻¹ * d * w) := fun c d => by group
  have hw' : w * w * w = 1 := by rw [← pow_three']; exact hw
  have h3 : ∀ c : X, w⁻¹ * (w⁻¹ * (w⁻¹ * c * w) * w) * w = c := fun c => by
    calc w⁻¹ * (w⁻¹ * (w⁻¹ * c * w) * w) * w = (w * w * w)⁻¹ * c * (w * w * w) := by group
      _ = c := by rw [hw']; group
  have hinj : ∀ c d : X, w⁻¹ * c * w = w⁻¹ * d * w → c = d := fun c d h => by
    simpa using congrArg (fun e => w * e * w⁻¹) h
  have hne1 : ∀ c : X, c ≠ 1 → w⁻¹ * c * w ≠ 1 := fun c hc h => hc (hinj c 1 (by rw [h]; group))
  have hk12 : k₁ * k₂ ≠ k₂ := fun h => hk₁ (by simpa using h)
  rcases hK k₁ (Or.inr (Or.inl rfl)) with e1 | e1 | e1 | e1
  · exact absurd e1 (hne1 k₁ hk₁)
  · rcases hK k₂ (Or.inr (Or.inr (Or.inl rfl))) with e2 | e2 | e2 | e2
    · exact absurd e2 (hne1 k₂ hk₂)
    · exact absurd (hinj _ _ (e1.trans e2.symm)) h12
    · exact (hfix e1 e2).elim
    · exfalso
      have e3 : w⁻¹ * (k₁ * k₂) * w = k₂ := by rw [hmul, e1, e2, ← mul_assoc, h1, one_mul]
      have h := h3 k₂
      rw [e2, e3, e2] at h
      exact hk12 h
  · exact ⟨w, e1⟩
  · rcases hK k₂ (Or.inr (Or.inr (Or.inl rfl))) with e2 | e2 | e2 | e2
    · exact absurd e2 (hne1 k₂ hk₂)
    · refine ⟨w⁻¹, ?_⟩
      rw [inv_inv, ← e2]
      group
    · exfalso
      have e3 : w⁻¹ * (k₁ * k₂) * w = k₁ := by rw [hmul, e1, e2, mul_assoc, h2, mul_one]
      have h := h3 k₁
      rw [e1, e3, e1] at h
      exact hk₂ (by simpa using h)
    · exact absurd (hinj _ _ (e1.trans e2.symm)) h12

section Ybar

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

abbrev a1lX : D.Xt := D.piX ⟨D.a1l, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩

theorem tUT_tX (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (h : D.tX ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    D.tUT hO hz ⟨D.tX, h⟩ = SE.toUT (SE.invRep 1) := by
  have e := D.tUT_apply hO hz ⟨⟨D.t, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩,
    mem_subgroupOf.mpr (D.toG_mem_S1 (by decide))⟩
  rw [D.preS1_eq rfl] at e
  exact e

theorem tUT_a1lX (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (h : D.a1lX ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    D.tUT hO hz ⟨D.a1lX, h⟩ = SE.toUT (SE.invRep 2) := by
  have e := D.tUT_apply hO hz ⟨⟨D.a1l, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩,
    mem_subgroupOf.mpr (D.toG_mem_S1 (by decide))⟩
  rw [D.preS1_eq rfl] at e
  exact e

theorem tX_a1lX_mem_ZT (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.tX ∈ D.Et ⊓ D.Ft ∧ D.a1lX ∈ D.Et ⊓ D.Ft := by
  have ht : D.tX ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) :=
    D.mem_sylowXt hO hz ⟨_, mem_subgroupOf.mpr (D.toG_mem_S1 (by decide))⟩
  have ha : D.a1lX ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) :=
    D.mem_sylowXt hO hz ⟨_, mem_subgroupOf.mpr (D.toG_mem_S1 (by decide))⟩
  refine ⟨mem_inf.mpr ⟨?_, ?_⟩, mem_inf.mpr ⟨?_, ?_⟩⟩
  · rw [D.mem_Et_iff_tUT hO hz ht, D.tUT_tX hO hz ht]; exact SE.ut_t_a1l.2.1
  · rw [D.mem_Ft_iff_tUT hO hz ht, D.tUT_tX hO hz ht]; exact SE.ut_t_a1l.1
  · rw [D.mem_Et_iff_tUT hO hz ha, D.tUT_a1lX hO hz ha]; exact SE.ut_t_a1l.2.2.2.1
  · rw [D.mem_Ft_iff_tUT hO hz ha, D.tUT_a1lX hO hz ha]; exact SE.ut_t_a1l.2.2.1

theorem mem_ZT_cases (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) {c : D.Xt}
    (hc : c ∈ D.Et ⊓ D.Ft) : c = 1 ∨ c = D.tX ∨ c = D.a1lX ∨ c = D.tX * D.a1lX := by
  obtain ⟨⟨htE, -⟩, ⟨haE, -⟩⟩ := D.tX_a1lX_mem_ZT hO hz
  have hT := D.Et_le hO hz (mem_inf.mp hc).1
  have htT := D.Et_le hO hz htE
  have haT := D.Et_le hO hz haE
  have hinj := (D.tUT hO hz).injective
  rcases SE.ut_ab_cases _ ((D.mem_Ft_iff_tUT hO hz hT).mp (mem_inf.mp hc).2)
      ((D.mem_Et_iff_tUT hO hz hT).mp (mem_inf.mp hc).1) with h | h | h | h
  · exact Or.inl (congrArg Subtype.val (hinj (h.trans (map_one _).symm)))
  · exact Or.inr (Or.inl (congrArg Subtype.val (hinj (h.trans (D.tUT_tX hO hz htT).symm))))
  · exact Or.inr (Or.inr (Or.inl
      (congrArg Subtype.val (hinj (h.trans (D.tUT_a1lX hO hz haT).symm)))))
  · have e : D.tUT hO hz ⟨c, hT⟩ = D.tUT hO hz (⟨D.tX, htT⟩ * ⟨D.a1lX, haT⟩) := by
      rw [map_mul, D.tUT_tX hO hz htT, D.tUT_a1lX hO hz haT]
      exact h
    exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val (hinj e))))

theorem tX_a1lX_facts (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.tX * D.tX = 1 ∧ D.a1lX * D.a1lX = 1 ∧ D.a1lX ≠ 1 ∧ D.tX ≠ D.a1lX := by
  obtain ⟨⟨-, htF⟩, ⟨haE, haF⟩⟩ := D.tX_a1lX_mem_ZT hO hz
  have haT := D.Et_le hO hz haE
  have htT := D.Ft_le hO hz htF
  refine ⟨D.Ft_sq hO hz _ htF, D.Ft_sq hO hz _ haF, fun h => ?_, fun h => ?_⟩
  · have e := D.tUT_a1lX hO hz haT
    rw [show (⟨D.a1lX, haT⟩ : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) = 1 from
      Subtype.ext h, map_one] at e
    exact absurd e (by decide)
  · have e := D.tUT_a1lX hO hz haT
    rw [show (⟨D.a1lX, haT⟩ : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) =
      ⟨D.tX, htT⟩ from Subtype.ext h.symm, D.tUT_tX hO hz htT] at e
    exact SE.ut_t_a1l.2.2.2.2 e

theorem mem_S_of_index_one (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (h1 : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index = 1) (g : Y) :
    g ∈ (D.S : Subgroup Y) := by
  have hY : D.Y1 ≤ D.S1 := by
    have h := D.relIndex_S1_Y1 hO hz
    rw [h1] at h
    exact Subgroup.relIndex_eq_one.mp h
  by_cases hg : g ∈ D.Y1
  · exact (mem_inf.mp (hY hg)).1
  · have hga : g * D.a⁻¹ ∈ D.Y1 := by
      rw [mul_mem_iff_of_index_two (D.index_centralizer_l hO hz), inv_mem_iff]
      exact iff_of_false hg (D.a_not_mem_Y1 hO hz)
    simpa using mul_mem (mem_inf.mp (hY hga)).1 (D.toG_mem (SE.invRep 7))


theorem exists_conj_tX_a1lX (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    (hB : pCore 2 D.Xt = ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt))
    (h3 : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index = 3) :
    ∃ g : D.Xt, g⁻¹ * D.tX * g = D.a1lX := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hEn, hFn, hCT⟩ := D.prop38B_of hC hO hz hB
  have hdvd : 3 ∣ Nat.card D.Xt := by
    rw [← ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).card_mul_index, h3]
    exact dvd_mul_left 3 _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hodd : Odd (orderOf w) := by rw [hw]; decide
  obtain ⟨hts, has, ha1, hta⟩ := D.tX_a1lX_facts hO hz
  obtain ⟨htZ, haZ⟩ := D.tX_a1lX_mem_ZT hO hz
  have hZ : ∀ c ∈ D.Et ⊓ D.Ft, w⁻¹ * c * w ∈ D.Et ⊓ D.Ft := fun c hc => by
    have h1 := hEn.conj_mem c (mem_inf.mp hc).1 w⁻¹
    have h2 := hFn.conj_mem c (mem_inf.mp hc).2 w⁻¹
    rw [inv_inv] at h1 h2
    exact mem_inf.mpr ⟨h1, h2⟩
  refine exists_conj_of_pow_three hw3 hts has D.tX_ne_one ha1 hta (fun c hc => ?_) ?_
  · refine D.mem_ZT_cases hO hz (hZ c ?_)
    rcases hc with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact htZ
    · exact haZ
    · exact mul_mem htZ haZ
  · intro e1 e2
    have hw1 : w = 1 := D.eq_one_of_centralizes_ZT hO hz hEn hFn hCT hodd fun c hc => by
      have hfix : w⁻¹ * c * w = c := by
        rcases D.mem_ZT_cases hO hz hc with rfl | rfl | rfl | rfl
        · group
        · exact e1
        · exact e2
        · rw [show w⁻¹ * (D.tX * D.a1lX) * w = w⁻¹ * D.tX * w * (w⁻¹ * D.a1lX * w) by group, e1,
            e2]
      calc w * c = w * (w⁻¹ * c * w) := by rw [hfix]
        _ = c * w := by group
    rw [hw1, orderOf_one] at hw
    exact absurd hw (by decide)

theorem exists_conj_t_a1l_Y (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    (hB : pCore 2 D.Xt = ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt))
    (h3 : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index = 3) :
    ∃ h : D.Y1, h⁻¹ * ⟨D.t, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩ * h =
      ⟨D.a1l, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩ := by
  obtain ⟨g, hg⟩ := D.exists_conj_tX_a1lX hC hO hz hB h3
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (zpowers D.lY) g
  refine D.exists_conj_Y1_of_conj_Xt (D.toG_mem_S1 (by decide)) (Subtype.ext D.t_mul_t)
    (Subtype.ext ?_) (fun h => ?_) (fun h => ?_) (by rw [map_mul, map_mul, map_inv]; exact hg)
  · change D.toG (SE.invRep 2) * D.toG (SE.invRep 2) = 1
    rw [← map_mul, SE.invRep_mul_self', map_one]
  · exact absurd (D.toG_eq_one_iff.mp (congrArg Subtype.val h)) (by decide)
  · exact absurd (D.toG_injective h) (by decide)

end GHSylow

end Ybar

end CFSG.ComponentClassification.GHarris
