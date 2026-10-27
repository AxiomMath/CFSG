module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.GH74.GLS.Stage12.McLRec

open Subgroup Equiv Equiv.Perm

theorem card_alternatingGroup_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

@[expose] def permA : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
@[expose] def permB : Perm (Fin 8) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7
@[expose] def permC : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

theorem sign_permA : sign permA = 1 := by simp [permA, Perm.sign_mul]
theorem sign_permB : sign permB = 1 := by simp [permB, Perm.sign_mul]
theorem sign_permC : sign permC = 1 := by simp [permC, Perm.sign_mul]

theorem permABC_facts : (permA * permB = permB * permA) ∧ (permA * permC = permC * permA) ∧
    (permB * permC = permC * permB) ∧
    permA * permA = 1 ∧ permB * permB = 1 ∧ permC * permC = 1 ∧ permA ≠ 1 ∧ permB ≠ 1 ∧
    permC ≠ 1 ∧ permA * permB ≠ 1 ∧ permA * permC ≠ 1 ∧ permB * permC ≠ 1 ∧
    permA * permB * permC ≠ 1 ∧ (permA * permB) * (permA * permB) = 1 ∧
    (permA * permC) * (permA * permC) = 1 ∧ (permB * permC) * (permB * permC) = 1 ∧
    (permA * permB * permC) * (permA * permB * permC) = 1 := by
  unfold permA permB permC
  decide

theorem exists_noncentral_involution_of_map {K : Type*} [Group K] (ρ : K →* Perm (Fin 8))
    (hρ : ∀ p : Perm (Fin 8), sign p = 1 → ∃ x, ρ x = p)
    (hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center K) (hc : Nat.card (Subgroup.center K) = 2) :
    ∃ u : K, u ^ 2 = 1 ∧ u ∉ Subgroup.center K := by
  by_contra H
  push Not at H
  obtain ⟨⟨z0, hz0⟩, hz01, hz0uniq'⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).mp hc
  have hz01' : z0 ≠ 1 := fun h => hz01 (Subtype.ext h)
  have hz0uniq : ∀ c ∈ Subgroup.center K, c = 1 ∨ c = z0 := by
    intro c hc'
    by_cases h1 : c = 1
    · exact Or.inl h1
    · right
      have e1 : (⟨c, hc'⟩ : Subgroup.center K) = ⟨z0, hz0⟩ :=
        (hz0uniq' ⟨c, hc'⟩ (fun h => h1 (congrArg Subtype.val h))).trans
          (hz0uniq' ⟨z0, hz0⟩ hz01).symm
      exact congrArg Subtype.val e1
  have hsqc : ∀ c ∈ Subgroup.center K, c * c = 1 := by
    intro c hc'
    rcases hz0uniq c hc' with h | h
    · rw [h, mul_one]
    · have := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨c, hc'⟩)
      rw [hc] at this
      have h2 := congrArg Subtype.val this
      simpa [pow_two] using h2
  have hsq : ∀ v : K, ρ v ≠ 1 → ρ v * ρ v = 1 → v * v = z0 := by
    intro v hv1 hv2
    have hvc : v * v ∈ Subgroup.center K := (hker (v * v)).mp (by rw [map_mul]; exact hv2)
    rcases hz0uniq _ hvc with h | h
    · exfalso
      have : v ^ 2 = 1 := by rw [pow_two]; exact h
      exact hv1 ((hker v).mpr (H v this))
    · exact h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    permABC_facts
  obtain ⟨x, hx⟩ := hρ permA sign_permA
  obtain ⟨y, hy⟩ := hρ permB sign_permB
  obtain ⟨w, hw⟩ := hρ permC sign_permC
  have cen : ∀ u v : K, ρ u * ρ v = ρ v * ρ u → v⁻¹ * u⁻¹ * v * u ∈ Subgroup.center K := by
    intro u v huv
    rw [← hker]
    simp only [map_mul, map_inv]
    calc (ρ v)⁻¹ * (ρ u)⁻¹ * ρ v * ρ u = (ρ v)⁻¹ * (ρ u)⁻¹ * (ρ v * ρ u) := by group
      _ = (ρ v)⁻¹ * (ρ u)⁻¹ * (ρ u * ρ v) := by rw [huv]
      _ = 1 := by group
  have hcxy := cen x y (by rw [hx, hy]; exact h1)
  have hcxw := cen x w (by rw [hx, hw]; exact h2)
  have hcyw := cen y w (by rw [hy, hw]; exact h3)
  have sqid : ∀ u v : K, v⁻¹ * u⁻¹ * v * u ∈ Subgroup.center K →
      (u * v) * (u * v) = (u * u) * (v * v) * (v⁻¹ * u⁻¹ * v * u) := by
    intro u v hk
    have hkc := Subgroup.mem_center_iff.mp hk
    have e : (u * v) * (u * v) = (u * u) * (v * v) * (v⁻¹ * (v⁻¹ * u⁻¹ * v * u) * v) := by group
    have hk' : v⁻¹ * (v⁻¹ * u⁻¹ * v * u) * v = v⁻¹ * u⁻¹ * v * u := by
      rw [hkc v⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, hk']
  have sxx : x * x = z0 := hsq x (by rw [hx]; exact h7) (by rw [hx]; exact h4)
  have syy : y * y = z0 := hsq y (by rw [hy]; exact h8) (by rw [hy]; exact h5)
  have sww : w * w = z0 := hsq w (by rw [hw]; exact h9) (by rw [hw]; exact h6)
  have sxy : (x * y) * (x * y) = z0 :=
    hsq (x * y) (by rw [map_mul, hx, hy]; exact h10) (by rw [map_mul, hx, hy]; exact h14)
  have sxw : (x * w) * (x * w) = z0 :=
    hsq (x * w) (by rw [map_mul, hx, hw]; exact h11) (by rw [map_mul, hx, hw]; exact h15)
  have syw : (y * w) * (y * w) = z0 :=
    hsq (y * w) (by rw [map_mul, hy, hw]; exact h12) (by rw [map_mul, hy, hw]; exact h16)
  have hz2 : z0 * z0 = 1 := hsqc z0 hz0
  have kxw : w⁻¹ * x⁻¹ * w * x = z0 := by
    have := sqid x w hcxw
    rw [sxw, sxx, sww, hz2, one_mul] at this
    exact this.symm
  have kyw : w⁻¹ * y⁻¹ * w * y = z0 := by
    have := sqid y w hcyw
    rw [syw, syy, sww, hz2, one_mul] at this
    exact this.symm
  have kxyw : w⁻¹ * (x * y)⁻¹ * w * (x * y) = 1 := by
    have e : w⁻¹ * (x * y)⁻¹ * w * (x * y) =
        (w⁻¹ * y⁻¹ * w * y) * (y⁻¹ * (w⁻¹ * x⁻¹ * w * x) * y) := by group
    have hkc := Subgroup.mem_center_iff.mp hz0
    have hcc : y⁻¹ * z0 * y = z0 := by rw [hkc y⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, kyw, kxw, hcc, hz2]
  have hcen : w⁻¹ * (x * y)⁻¹ * w * (x * y) ∈ Subgroup.center K := by
    rw [kxyw]; exact Subgroup.one_mem _
  have sall : (x * y * w) * (x * y * w) = 1 := by
    have := sqid (x * y) w hcen
    rw [sxy, sww, kxyw, hz2, mul_one] at this
    exact this
  have := hsq (x * y * w) (by rw [map_mul, map_mul, hx, hy, hw]; exact h13)
    (by rw [map_mul, map_mul, hx, hy, hw]; exact h17)
  rw [sall] at this
  exact hz01' this.symm

section Cover

variable {K : Type} [Group K]

theorem card_eq_of_doubleCover (h : IsDoubleCoverOfAlt K 8) : Nat.card K = 40320 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [Nat.card_congr e.toEquiv, hc, card_alternatingGroup_eight] at h1
  omega

theorem finite_of_doubleCover (h : IsDoubleCoverOfAlt K 8) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [card_eq_of_doubleCover h]; norm_num)

theorem card_le_two_of_normal_of_doubleCover (h : IsDoubleCoverOfAlt K 8) (T : Subgroup K)
    [T.Normal] (hT : IsPGroup 2 T) : Nat.card T ≤ 2 := by
  have hfin : Finite K := finite_of_doubleCover h
  obtain ⟨hq, hc, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  set Q := K ⧸ Subgroup.center K
  have hQ : Nat.card Q = 20160 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_eight]
  have hQfin : Finite Q := inferInstance
  set T' : Subgroup Q := T.map (QuotientGroup.mk' (Subgroup.center K)) with hT'
  have : T'.Normal := Subgroup.Normal.map (inferInstance) (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _)
  have hT'2 : IsPGroup 2 T' := by
    have := hT.map (QuotientGroup.mk' (Subgroup.center K))
    simpa [hT'] using this
  rcases hs.eq_bot_or_eq_top_of_normal T' with h | h
  · have hle : T ≤ Subgroup.center K := by
      intro t ht
      have : QuotientGroup.mk' (Subgroup.center K) t ∈ T' := Subgroup.mem_map_of_mem _ ht
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff t).mp this
    calc Nat.card T ≤ Nat.card (Subgroup.center K) := Subgroup.card_le_of_le hle
      _ = 2 := hc
  · exfalso
    have hQ2 : IsPGroup 2 Q := by
      have := hT'2
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ2
    rw [hQ] at hk
    have h3 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk]; norm_num
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega

theorem exists_noncentral_involution_of_doubleCover (h : IsDoubleCoverOfAlt K 8) :
    ∃ u : K, u ^ 2 = 1 ∧ u ∉ Subgroup.center K := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  let ρ : K →* Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  refine exists_noncentral_involution_of_map ρ ?_ ?_ hc
  · intro p hp
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center K)
      (e.symm ⟨p, Perm.mem_alternatingGroup.mpr hp⟩)
    refine ⟨x, ?_⟩
    have := congrArg e hx
    simp only [MulEquiv.apply_symm_apply] at this
    simpa [ρ] using congrArg Subtype.val this
  · intro x
    simp only [ρ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom]
    constructor
    · intro hx
      have : e (QuotientGroup.mk' (center K) x) = 1 := Subtype.ext hx
      rw [MulEquiv.map_eq_one_iff] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    · intro hx
      have : QuotientGroup.mk' (center K) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [this, map_one]
      rfl

end Cover

theorem isDoubleCoverOfAlt_congr {K L : Type} [Group K] [Group L] (e : K ≃* L) {n : ℕ}
    (h : IsDoubleCoverOfAlt K n) : IsDoubleCoverOfAlt L n := by
  obtain ⟨hq, hc, ⟨φ⟩⟩ := h
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]; exact hc
  · have hmap : (center K).map e.toMonoidHom = center L := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro g
        have := hx (e.symm g)
        have h2 := congrArg e this
        simpa using h2
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        rw [Subgroup.mem_center_iff] at hy ⊢
        intro g
        have := hy (e g)
        have h2 := congrArg e.symm this
        simpa using h2
    exact ⟨(QuotientGroup.congr (center K) (center L) e hmap).symm.trans φ⟩

section Conj

variable {G : Type*} [Group G]

theorem map_conj_centralizer (c z : G) :
    (centralizer ({z} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * z * c⁻¹} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hy
    calc c * z * c⁻¹ * (c * y * c⁻¹) = c * (z * y) * c⁻¹ := by group
      _ = c * (y * z) * c⁻¹ := by rw [this]
      _ = _ := by group
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · calc z * (c⁻¹ * x * c) = c⁻¹ * (c * z * c⁻¹ * x) * c := by group
        _ = c⁻¹ * (x * (c * z * c⁻¹)) * c := by rw [hx]
        _ = _ := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

noncomputable def centralizerConjEquiv (c z : G) :
    ↥(centralizer ({z} : Set G)) ≃* ↥(centralizer ({c * z * c⁻¹} : Set G)) :=
  ((centralizer ({z} : Set G)).equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr (map_conj_centralizer c z))

end Conj

section ConjCard

variable {G : Type*} [Group G]

theorem card_centralizer_conj (c z : G) :
    Nat.card (centralizer ({c * z * c⁻¹} : Set G)) = Nat.card (centralizer ({z} : Set G)) := by
  rw [← map_conj_centralizer c z]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective

end ConjCard

end CFSG.GH74.GLS.Stage12.McLRec
