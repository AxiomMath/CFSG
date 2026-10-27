module

public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.LieType.SteinbergBR.SmallAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def finSubgroup {m : ℕ} (f : Fin 8 → Perm (Fin m)) (hmul : ∀ i j, ∃ k, f i * f j = f k)
    (hinv : ∀ i, ∃ k, (f i)⁻¹ = f k) (h1 : ∃ i, f i = 1) : Subgroup (alternatingGroup (Fin m)) where
  carrier := {x | ∃ i, f i = x.1}
  mul_mem' := by
    rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hmul i j
    exact ⟨k, by rw [← hk, hi, hj]; rfl⟩
  one_mem' := by
    obtain ⟨i, hi⟩ := h1
    exact ⟨i, hi⟩
  inv_mem' := by
    rintro x ⟨i, hi⟩
    obtain ⟨k, hk⟩ := hinv i
    exact ⟨k, by rw [← hk, hi]; rfl⟩

theorem card_finSubgroup {m : ℕ} (f : Fin 8 → Perm (Fin m)) (hmul : ∀ i j, ∃ k, f i * f j = f k)
    (hinv : ∀ i, ∃ k, (f i)⁻¹ = f k) (h1 : ∃ i, f i = 1) (hinj : Function.Injective f)
    (hsign : ∀ i, f i ∈ alternatingGroup (Fin m)) :
    Nat.card (finSubgroup f hmul hinv h1) = 8 := by
  let e : Fin 8 ≃ finSubgroup f hmul hinv h1 := Equiv.ofBijective
    (fun i => ⟨⟨f i, hsign i⟩, i, rfl⟩) ⟨fun i j h => hinj (congrArg (fun x => x.1.1) h),
      fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext (Subtype.ext hi)⟩⟩
  rw [← Nat.card_congr e, Nat.card_fin]

theorem card_alternating {m : ℕ} (hm : 2 ≤ m) :
    2 * Nat.card (alternatingGroup (Fin m)) = m.factorial := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]

theorem isPGroup_of_pow_four {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ x ∈ H, x ^ 4 = 1) : IsPGroup 2 H :=
  fun x => ⟨2, Subtype.ext (h x.1 x.2)⟩

theorem normalizer_eq_of_isPGroup {G : Type*} [Group G] (P : Sylow 2 G)
    (h : IsPGroup 2 (normalizer ((P : Subgroup G) : Set G))) :
    normalizer ((P : Subgroup G) : Set G) = P :=
  P.is_maximal' h le_normalizer

@[expose] def a6P : Fin 8 → Perm (Fin 6) :=
  ![1, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5,
    swap 0 2 * swap 4 5, swap 1 3 * swap 4 5]

@[expose] def a6Q : Fin 16 → Perm (Fin 6) :=
  ![1, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5,
    swap 0 2 * swap 4 5, swap 1 3 * swap 4 5, swap 4 5, swap 0 2 * swap 1 3 * swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5, swap 0 3 * swap 1 2 * swap 4 5,
    swap 0 1 * swap 1 2 * swap 2 3, swap 0 3 * swap 3 2 * swap 2 1, swap 0 2, swap 1 3]

theorem a6P_mul : ∀ i j : Fin 8, ∃ k : Fin 8, a6P i * a6P j = a6P k := by
  decide +kernel

theorem a6P_inv : ∀ i : Fin 8, ∃ k : Fin 8, (a6P i)⁻¹ = a6P k := by
  decide +kernel

theorem a6P_one : ∃ i : Fin 8, a6P i = 1 := ⟨0, rfl⟩

theorem a6P_sign : ∀ i : Fin 8, sign (a6P i) = 1 := by
  decide +kernel

theorem a6P_injective : Function.Injective a6P := by
  decide +kernel

theorem a6Q_pow_four : ∀ j : Fin 16, a6Q j ^ 4 = 1 := by
  decide +kernel

theorem a6_normalizer_check : ∀ σ : Perm (Fin 6), (∃ i, σ * a6P 4 * σ⁻¹ = a6P i) →
    (∃ i, σ * a6P 6 * σ⁻¹ = a6P i) → ∃ j, σ = a6Q j := by
  decide +kernel

theorem exists_selfNormalizing_six :
    ∃ P : Sylow 2 (alternatingGroup (Fin 6)),
      normalizer (P : Set (alternatingGroup (Fin 6))) = P := by
  set P := finSubgroup a6P a6P_mul a6P_inv a6P_one
  have hcard : Nat.card P = 8 := card_finSubgroup _ _ _ _ a6P_injective
    fun i => (mem_alternatingGroup).2 (a6P_sign i)
  have hA : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    have := card_alternating (m := 6) (by norm_num)
    rw [show Nat.factorial 6 = 720 by decide] at this
    omega
  let S : Sylow 2 (alternatingGroup (Fin 6)) := Sylow.ofCard P (by
    rw [hcard, hA, ordProj_prime_pow_mul Nat.prime_two 3 (by norm_num)]; norm_num)
  refine ⟨S, normalizer_eq_of_isPGroup S (isPGroup_of_pow_four fun x hx => ?_)⟩
  have hg (i : Fin 8) : (⟨a6P i, (mem_alternatingGroup).2 (a6P_sign i)⟩ :
      alternatingGroup (Fin 6)) ∈ P := ⟨i, rfl⟩
  obtain ⟨i, hi⟩ := (mem_normalizer_iff.1 hx _).1 (hg 4)
  obtain ⟨k, hk⟩ := (mem_normalizer_iff.1 hx _).1 (hg 6)
  obtain ⟨j, hj⟩ := a6_normalizer_check x.1 ⟨i, hi.symm⟩ ⟨k, hk.symm⟩
  apply Subtype.ext
  change x.1 ^ 4 = 1
  rw [hj, a6Q_pow_four]

theorem isPGroup_outer_six : IsPGroup 2 (Outer (alternatingGroup (Fin 6))) := by
  have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have hf1 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (swap 0 1)) ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← CFSG.Quasithin.SteinbergCB.map_conjPerm_alternatingGroup] at h
    obtain ⟨a, ha, hae⟩ := h
    have := CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num) hae
    rw [this, SetLike.mem_coe, mem_alternatingGroup, sign_swap (by decide)] at ha
    exact absurd ha (by decide)
  have hf2 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (swap 0 1)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, sq, swap_mul_self, map_one, map_one]
  have hord := orderOf_eq_prime hf2 hf1
  have hdvd : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := hord ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  have hcases : Nat.card (Outer (alternatingGroup (Fin 6))) = 2 ^ 1 ∨
      Nat.card (Outer (alternatingGroup (Fin 6))) = 2 ^ 2 := by
    obtain ⟨c, hc⟩ := hdvd
    rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
    · exact Or.inl (by rw [hc]; norm_num)
    · exact Or.inr (by rw [hc]; norm_num)
  rcases hcases with h | h
  · exact IsPGroup.of_card h
  · exact IsPGroup.of_card h

@[expose] def a7P : Fin 8 → Perm (Fin 7) :=
  ![1, swap 1 3 * swap 2 4, swap 1 2 * swap 3 4, swap 1 4 * swap 2 3,
    swap 1 2 * swap 2 3 * swap 3 4 * swap 5 6, swap 1 4 * swap 4 3 * swap 3 2 * swap 5 6,
    swap 1 3 * swap 5 6, swap 2 4 * swap 5 6]

@[expose] def a7Q : Fin 16 → Perm (Fin 7) :=
  ![1, swap 1 3 * swap 2 4, swap 1 2 * swap 3 4, swap 1 4 * swap 2 3,
    swap 1 2 * swap 2 3 * swap 3 4 * swap 5 6, swap 1 4 * swap 4 3 * swap 3 2 * swap 5 6,
    swap 1 3 * swap 5 6, swap 2 4 * swap 5 6, swap 5 6, swap 1 3 * swap 2 4 * swap 5 6,
    swap 1 2 * swap 3 4 * swap 5 6, swap 1 4 * swap 2 3 * swap 5 6,
    swap 1 2 * swap 2 3 * swap 3 4, swap 1 4 * swap 4 3 * swap 3 2, swap 1 3, swap 2 4]

theorem a7P_mul : ∀ i j : Fin 8, ∃ k : Fin 8, a7P i * a7P j = a7P k := by
  decide +kernel

theorem a7P_inv : ∀ i : Fin 8, ∃ k : Fin 8, (a7P i)⁻¹ = a7P k := by
  decide +kernel

theorem a7P_one : ∃ i : Fin 8, a7P i = 1 := ⟨0, rfl⟩

theorem a7P_sign : ∀ i : Fin 8, sign (a7P i) = 1 := by
  decide +kernel

theorem a7P_injective : Function.Injective a7P := by
  decide +kernel

theorem a7Q_pow_four : ∀ j : Fin 16, a7Q j ^ 4 = 1 := by
  decide +kernel

theorem a7P_fix_zero : ∀ i : Fin 8, a7P i 0 = 0 := by
  decide +kernel

theorem a7P_four_fix : ∀ y : Fin 7, a7P 4 y = y → y = 0 := by
  decide +kernel

theorem a7_normalizer_check : ∀ e : Perm (Fin 6),
    (∃ i, decomposeFin.symm (0, e) * a7P 4 * (decomposeFin.symm (0, e))⁻¹ = a7P i) →
    (∃ i, decomposeFin.symm (0, e) * a7P 6 * (decomposeFin.symm (0, e))⁻¹ = a7P i) →
    ∃ j, decomposeFin.symm (0, e) = a7Q j := by
  decide +kernel

theorem exists_selfNormalizing_seven :
    ∃ P : Sylow 2 (alternatingGroup (Fin 7)),
      normalizer (P : Set (alternatingGroup (Fin 7))) = P := by
  set P := finSubgroup a7P a7P_mul a7P_inv a7P_one
  have hcard : Nat.card P = 8 := card_finSubgroup _ _ _ _ a7P_injective
    fun i => (mem_alternatingGroup).2 (a7P_sign i)
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
    have := card_alternating (m := 7) (by norm_num)
    rw [show Nat.factorial 7 = 5040 by decide] at this
    omega
  let S : Sylow 2 (alternatingGroup (Fin 7)) := Sylow.ofCard P (by
    rw [hcard, hA, ordProj_prime_pow_mul Nat.prime_two 3 (by norm_num)]; norm_num)
  refine ⟨S, normalizer_eq_of_isPGroup S (isPGroup_of_pow_four fun x hx => ?_)⟩
  have hg (i : Fin 8) : (⟨a7P i, (mem_alternatingGroup).2 (a7P_sign i)⟩ :
      alternatingGroup (Fin 7)) ∈ P := ⟨i, rfl⟩
  have hx0 : x.1 0 = 0 := by
    have hxinv := Subgroup.inv_mem _ hx
    obtain ⟨i, hi⟩ := (mem_normalizer_iff.1 hxinv _).1 (hg 4)
    have h1 : (x⁻¹ * ⟨a7P 4, (mem_alternatingGroup).2 (a7P_sign 4)⟩ * x⁻¹⁻¹ :
        alternatingGroup (Fin 7)).1 0 = 0 := by
      rw [← hi, a7P_fix_zero]
    change x.1⁻¹ (a7P 4 (x.1 0)) = 0 at h1
    refine a7P_four_fix _ ?_
    have h2 := congrArg x.1 h1
    rwa [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at h2
  set d := decomposeFin x.1 with hd
  have hd1 : d.1 = 0 := by
    have : decomposeFin.symm d 0 = d.1 := by
      rw [show d = (d.1, d.2) from rfl, decomposeFin_symm_apply_zero]
    rw [← this, hd, Equiv.symm_apply_apply, hx0]
  have hxd : x.1 = decomposeFin.symm (0, d.2) := by
    rw [← hd1, show (d.1, d.2) = d from rfl, hd, Equiv.symm_apply_apply]
  obtain ⟨i, hi⟩ := (mem_normalizer_iff.1 hx _).1 (hg 4)
  obtain ⟨k, hk⟩ := (mem_normalizer_iff.1 hx _).1 (hg 6)
  have hi' : x.1 * a7P 4 * x.1⁻¹ = a7P i := hi.symm
  have hk' : x.1 * a7P 6 * x.1⁻¹ = a7P k := hk.symm
  rw [hxd] at hi' hk'
  obtain ⟨j, hj⟩ := a7_normalizer_check d.2 ⟨i, hi'⟩ ⟨k, hk'⟩
  apply Subtype.ext
  change x.1 ^ 4 = 1
  rw [hxd, hj, a7Q_pow_four]

theorem isPGroup_outer_seven : IsPGroup 2 (Outer (alternatingGroup (Fin 7))) := by
  have h := CFSG.Quasithin.SteinbergCB.index_inner_dvd_two (n := 7) (Or.inr (by norm_num))
  change Nat.card (Outer (alternatingGroup (Fin 7))) ∣ 2 at h
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [h2, pow_one])

end CFSG.LieType.SteinbergBR.SmallAlt
