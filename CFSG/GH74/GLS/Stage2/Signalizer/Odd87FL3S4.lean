module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3S4Pgrp

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section AutZ

variable {F : Type} [Field F] [Finite F]

theorem ringEquiv_apply_eq_or_nine (hF : Nat.card F = 9) (τ : F ≃+* F) (x : F) : τ x = x ∨ τ x = x ^ 3 := by
  have hchar := s4_charP_three hF
  have hfix : ∀ c : F, c ^ 3 = c → τ c = c := by
    intro c hc
    have h : c * ((c - 1) * (c + 1)) = 0 := by linear_combination hc
    rcases mul_eq_zero.1 h with h | h
    · rw [h, map_zero]
    · rcases mul_eq_zero.1 h with h | h
      · rw [show c = 1 by linear_combination h, map_one]
      · rw [show c = -1 by linear_combination h, map_neg, map_one]
  have h9 := pow_nine_eq_self hF x
  have hc1 : (x + x ^ 3) ^ 3 = x + x ^ 3 := by
    rw [add_pow_char, ← pow_mul, show 3 * 3 = 9 by norm_num, h9, add_comm]
  have hc0 : (x ^ 4) ^ 3 = x ^ 4 := by
    calc (x ^ 4) ^ 3 = x ^ 9 * x ^ 3 := by ring
      _ = x ^ 4 := by rw [h9]; ring
  obtain ⟨c1, hc1def⟩ : ∃ c1 : F, c1 = x + x ^ 3 := ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c0 : F, c0 = x ^ 4 := ⟨_, rfl⟩
  have key : τ x ^ 2 - c1 * τ x + c0 = 0 := by
    have h : x ^ 2 - c1 * x + c0 = 0 := by rw [hc1def, hc0def]; ring
    have := congrArg τ h
    rw [map_add, map_sub, map_mul, map_pow, hfix c1 (by rw [hc1def]; exact hc1),
      hfix c0 (by rw [hc0def]; exact hc0), map_zero] at this
    exact this
  have hprod : (τ x - x) * (τ x - x ^ 3) = 0 := by
    rw [hc1def, hc0def] at key
    linear_combination key
  rcases mul_eq_zero.1 hprod with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

theorem ringEquiv_mul_self_eq_one (hF : Nat.card F = 9) (τ : F ≃+* F) : τ * τ = 1 := by
  ext x
  have h9 := pow_nine_eq_self hF x
  rcases ringEquiv_apply_eq_or_nine hF τ x with h | h
  · change τ (τ x) = x
    rw [h, h]
  · change τ (τ x) = x
    rw [h, map_pow, h, ← pow_mul, show 3 * 3 = 9 by norm_num, h9]

end AutZ


section AutZ2

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem fieldAut_dualAut_pow_proj_of {τ : F ≃+* F} {g : SL(3, F)} (h1 : (g⁻¹).transpose = g)
    (h2 : SpecialLinearGroup.map τ.toRingHom g = g) {ε : ℕ} (hε : ε ≤ 1) :
    (fieldAut 3 F τ * dualAut 3 F ^ ε) (proj 3 F g) = proj 3 F g := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one]
    exact fieldAut_proj_of h2
  · rw [pow_one, MulAut.mul_apply, dualAut_proj_of h1, fieldAut_proj_of h2]

theorem aut_eq_one_of_fixes (hF : Nat.card F = 9) (φ : MulAut (projectiveSL 3 F))
    (ha : φ (proj 3 F s4Da) = proj 3 F s4Da) (hb : φ (proj 3 F s4Db) = proj 3 F s4Db)
    (hp : φ (proj 3 F s4P) = proj 3 F s4P) {m : ℕ} (hm : Odd m) (hφ : φ ^ m = 1) : φ = 1 := by
  have h2 := two_ne_zero_of_card_nine hF
  have inj := proj_injective_of_card_nine hF
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  obtain ⟨B, τ, ε, hε, hφeq⟩ := (automorphism_generation (K := F) (n := 3) (by norm_num)).2 φ
  have hτ := ringEquiv_mul_self_eq_one hF τ
  have hcomm : ∀ g : SL(3, F), (fieldAut 3 F τ * dualAut 3 F ^ ε) (proj 3 F g) = proj 3 F g →
      φ (proj 3 F g) = proj 3 F g →
      (B : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
        (g : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) := by
    intro g h1 h2'
    have h3 : conjAut 3 F B (proj 3 F g) = proj 3 F g := by
      have : φ (proj 3 F g) = conjAut 3 F B ((fieldAut 3 F τ * dualAut 3 F ^ ε) (proj 3 F g)) := by
        rw [hφeq, mul_assoc, MulAut.mul_apply]
      rw [h1] at this
      exact this.symm.trans h2'
    rw [conjAut_proj] at h3
    have h4 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (inj h3)
    simp only [coe_slConjugation] at h4
    have h5 := congrArg (fun x => x * (B : Matrix (Fin 3) (Fin 3) F)) h4
    simp only [Matrix.mul_assoc] at h5
    rwa [Units.inv_mul, Matrix.mul_one] at h5
  obtain ⟨c, hc⟩ := s4_eq_scalar_of_commute_gens h2 (M := (B : Matrix (Fin 3) (Fin 3) F))
    (hcomm s4Da (fieldAut_dualAut_pow_proj_of s4Da_inv_transpose (map_s4Da τ) hε) ha)
    (hcomm s4Db (fieldAut_dualAut_pow_proj_of s4Db_inv_transpose (map_s4Db τ) hε) hb)
    (hcomm s4P (fieldAut_dualAut_pow_proj_of s4P_inv_transpose (map_s4P τ) hε) hp)
  have hB1 : conjAut 3 F B = 1 := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [MulAut.one_apply, conjAut_proj]
    congr 1
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have hcg : (B : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
        (g : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) := by
      rw [hc]
      exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    rw [coe_slConjugation, hcg, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hφ' : φ = fieldAut 3 F τ * dualAut 3 F ^ ε := by rw [hφeq, hB1, one_mul]
  have hsq : φ * φ = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · rw [hφ', pow_zero, mul_one, htrans.2.1 τ τ, hτ, map_one]
    · rw [hφ', pow_one]
      calc fieldAut 3 F τ * dualAut 3 F * (fieldAut 3 F τ * dualAut 3 F)
          = fieldAut 3 F τ * (dualAut 3 F * fieldAut 3 F τ * dualAut 3 F) := by simp only [mul_assoc]
        _ = fieldAut 3 F τ * fieldAut 3 F τ := by rw [htrans.2.2.2.2.2.1 τ]
        _ = 1 := by rw [htrans.2.1 τ τ, hτ, map_one]
  have h1 : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hsq])
  have h3 : orderOf φ ∣ m := orderOf_dvd_of_pow_eq_one hφ
  have h4 : orderOf φ ∣ Nat.gcd 2 m := Nat.dvd_gcd h1 h3
  rw [(Nat.coprime_two_left.2 hm : Nat.Coprime 2 m)] at h4
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

end AutZ2

section Main

theorem fl3_s4_false {A : Type} [Group A] [Finite A] (K : Subgroup A) [K.Normal] {F : Type} [Field F]
    [Finite F] (hF9 : Nat.card F = 9) (e : ↥K ≃* projectiveSL 3 F) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, e j ∈ S4img F → (j : A) ∈ normalizer (X : Set A)) : False := by
  let Y : Subgroup (projectiveSL 3 F) := (X.subgroupOf K).map e.toMonoidHom
  have hY : IsPGroup p Y := by
    rintro ⟨y, k, hk, rfl⟩
    obtain ⟨n, hn⟩ := hX ⟨(k : A), hk⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hk' : k ^ p ^ n = 1 := by
      have := congrArg (fun z : X => (z : A)) hn
      exact Subtype.ext (by simpa using this)
    simp [← map_pow, hk']
  have hnormY : ∀ g ∈ S4img F, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hjg : e (e.symm g) = g := e.apply_symm_apply g
    have hjn : ((e.symm g : K) : A) ∈ normalizer (X : Set A) := hJ _ (by rw [hjg]; exact hg)
    have hk' : k ∈ X.subgroupOf K := hk
    refine ⟨e.symm g * k * (e.symm g)⁻¹, ?_, ?_⟩
    · change e.symm g * k * (e.symm g)⁻¹ ∈ X.subgroupOf K
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.1 hjn (k : A)).1 hk'
      simpa using this
    · simp [hjg]
  have hY1 : Y = ⊥ := pgroup_trivial_of_s4_normal hF9 hp2 Y hY hnormY
  have hXK : ∀ x ∈ X, x ∈ K → x = 1 := by
    intro x hx hxK
    have hmem : (⟨x, hxK⟩ : K) ∈ X.subgroupOf K := hx
    have h1 : e ⟨x, hxK⟩ ∈ Y := ⟨_, hmem, rfl⟩
    rw [hY1, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
  have hcomm : ∀ x ∈ X, ∀ j : K, e j ∈ S4img F → (j : A) * x = x * j := by
    intro x hx j hj
    have hjn : (j : A) ∈ normalizer (X : Set A) := hJ j hj
    have h1 : (j : A) * x * (j : A)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hjn x).1 hx
    have h2 : (j : A) * x * (j : A)⁻¹ * x⁻¹ ∈ X := mul_mem h1 (inv_mem hx)
    have h3 : (j : A) * x * (j : A)⁻¹ * x⁻¹ ∈ K := by
      have h4 : x * (j : A)⁻¹ * x⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance _ (inv_mem j.2) x
      simpa [mul_assoc] using mul_mem j.2 h4
    have h5 := hXK _ h2 h3
    rw [mul_inv_eq_one] at h5
    exact mul_inv_eq_iff_eq_mul.1 h5
  have hX0 : ∀ x ∈ X, x = 1 := by
    intro x hx
    let Φ : A →* MulAut (projectiveSL 3 F) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
    have hΦ : ∀ g : projectiveSL 3 F, Φ x g = e (MulAut.conjNormal x (e.symm g)) := fun g => rfl
    have hfixg : ∀ g : projectiveSL 3 F, g ∈ S4img F → Φ x g = g := by
      intro g hg
      rw [hΦ]
      have h1 := hcomm x hx (e.symm g) (by rw [e.apply_symm_apply]; exact hg)
      have h2 : MulAut.conjNormal x (e.symm g) = e.symm g := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        rw [mul_inv_eq_iff_eq_mul]
        exact h1.symm
      rw [h2, e.apply_symm_apply]
    obtain ⟨n, hn⟩ := hX ⟨x, hx⟩
    have hxn : x ^ p ^ n = 1 := by
      have := congrArg (fun z : X => (z : A)) hn
      simpa using this
    have hodd : Odd (p ^ n) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    have hΦ1 : Φ x = 1 :=
      aut_eq_one_of_fixes hF9 (Φ x) (hfixg _ proj_s4Da_mem) (hfixg _ proj_s4Db_mem) (hfixg _ proj_s4P_mem)
        hodd (by rw [← map_pow, hxn, map_one])
    have hcent : x ∈ centralizer (K : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : Φ x (e ⟨k, hk⟩) = e ⟨k, hk⟩ := by rw [hΦ1, MulAut.one_apply]
      rw [hΦ, e.symm_apply_apply] at h1
      have h2 := Subtype.ext_iff.1 (e.injective h1)
      rw [MulAut.conjNormal_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    have : x ∈ X ⊓ centralizer (K : Set A) := ⟨hx, hcent⟩
    rw [hfaith, Subgroup.mem_bot] at this
    exact this
  exact hX1 ((Subgroup.eq_bot_iff_forall X).2 hX0)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
