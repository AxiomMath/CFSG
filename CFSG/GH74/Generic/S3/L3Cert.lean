module

public import CFSG.GH74.Generic.ClassicalCerts

public section

namespace CFSG.GH74.Generic.S3

open CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.Generic CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.L5U5 Matrix Subgroup
open scoped MatrixGroups

section Three
variable {F : Type} [Field F]

@[expose] def alpha3 (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 4) →* Fˣ) :
    Q8 × Multiplicative (ZMod 4) →* Matrix (Fin (2 + 1)) (Fin (2 + 1)) F where
  toFun g := diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1)
    ((((χ g.2 : Fˣ) : F) ^ 2) • (1 : Matrix (Fin 1) (Fin 1) F))
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one, Units.val_one, one_pow, one_smul]
    rw [diagBlock_one]
  map_mul' g h := by
    rw [diagBlock_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul, mul_pow, smul_mul_smul_comm,
      mul_one]

theorem alpha3_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (g : Q8 × Multiplicative (ZMod 4)) :
    alpha3 ρ χ g = diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1)
      ((((χ g.2 : Fˣ) : F) ^ 2) • (1 : Matrix (Fin 1) (Fin 1) F)) :=
  rfl

theorem det_alpha3 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, (ρ g).det = 1)
    (χ : Multiplicative (ZMod 4) →* Fˣ) (hχ : ∀ k, ((χ k : Fˣ) : F) ^ 4 = 1)
    (g : Q8 × Multiplicative (ZMod 4)) : (alpha3 ρ χ g).det = 1 := by
  rw [alpha3_apply, det_diagBlock, det_smul, det_smul, hρ, det_one]
  simp only [Fintype.card_fin, mul_one, pow_one]
  linear_combination hχ g.2

theorem alpha3_scalar (Q : QuatRep F) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (hχ : ∀ k, ((χ k : Fˣ) : F) ^ 2 = 1 → zRed 4 (by decide) k = 1)
    (g : Q8 × Multiplicative (ZMod 4)) (c : F)
    (h : alpha3 Q.ρ χ g = scalar (Fin (2 + 1)) c) :
    q8Frattini g.1 = 1 ∧ zRed 4 (by decide) g.2 = 1 := by
  rw [alpha3_apply] at h
  obtain ⟨h1, h3⟩ := eq_scalar_of_diagBlock_eq h
  have ht0 : ((χ g.2 : Fˣ) : F) ≠ 0 := Units.ne_zero _
  set t : F := ((χ g.2 : Fˣ) : F) with ht
  have hc : t ^ 2 = c := by
    have := congrFun (congrFun h3 0) 0
    simpa [scalar_apply] using this
  have hx : Q.ρ g.1 = scalar (Fin 2) (t⁻¹ * c) := by
    rw [← smul_scalar_fin_two, ← h1, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  obtain ⟨hx1, hx2⟩ := Q.scalar_eq _ _ hx
  refine ⟨hx1, hχ _ ?_⟩
  have e : t⁻¹ * c = t := by rw [← hc, sq, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  rw [e] at hx2
  have h1 : t ^ 2 = 1 := by
    rcases hx2 with h' | h' <;> rw [h'] <;> norm_num
  exact h1

theorem isUni_alpha3 {σ : F →+* F} {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F}
    (hρ : ∀ g, IsUni σ (ρ g)) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (hχ : ∀ k, σ ((χ k : Fˣ) : F) * ((χ k : Fˣ) : F) = 1)
    (g : Q8 × Multiplicative (ZMod 4)) : IsUni σ (alpha3 ρ χ g) := by
  rw [alpha3_apply]
  refine IsUni.diagBlock ((hρ _).smul (hχ _)) (IsUni.one.smul ?_)
  rw [map_pow, ← mul_pow, hχ, one_pow]

end Three

theorem card_V4_V2 : Nat.card (V4 × Multiplicative (ZMod 2)) = 8 := by
  simp [Nat.card_eq_fintype_card]

theorem rankCertified_L3_lin {F : Type} [Field F] [Finite F] (h4 : 4 ∣ Nat.card F - 1) :
    RankCertified (StatedProj (StatedSL 3 F)) 2 := by
  have hF : ringChar F ≠ 2 := ringChar_ne_two_of_dvd_four h4
  obtain ⟨Q⟩ := exists_quatRep hF
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := F) (d := 4) h4
  have hu4 : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have hχ4 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 4 = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val]
    change (((u ^ (Multiplicative.toAdd k).val) ^ 4 : Fˣ) : F) = 1
    rw [← pow_mul, mul_comm, pow_mul, hu4, one_pow, Units.val_one]
  have hχ2 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 2 = 1 → zRed 4 (by decide) k = 1 :=
    fun k hk => (zRed_eq_one_iff 4 _ k).2
      (zChar_pow_imp (m := 2) rfl (by norm_num) hu hu4 k hk)
  refine rankCertified_statedProj (A := V4 × Multiplicative (ZMod 2))
    (alpha3 Q.ρ (zChar u 4 hu4)).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap (zRed 4 (by decide)))
    (q8Frattini_surjective.prodMap (zRed_surjective 4 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_V2]; norm_num) ?_
  · exact Subgroup.subset_closure (det_alpha3 Q.det_eq _ hχ4 k)
  · intro k c h
    obtain ⟨h1, h3⟩ := alpha3_scalar Q (zChar u 4 hu4) hχ2 k c h
    exact Prod.ext h1 h3

theorem rankCertified_U3 {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 3) : RankCertified (StatedProj (StatedSU 3 q F)) 2 := by
  obtain ⟨p, f, _, _, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]; exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card hodd
  obtain ⟨Q, hQ⟩ := exists_unitary_quatRep hp2 hF
  have hσ : ∀ x, iterateFrobenius F p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have h4 : 4 ∣ Nat.card F - 1 := by
    have : (p ^ f) ^ 2 % 4 = 1 := by rw [Nat.pow_mod, hq]
    omega
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := F) (d := 4) h4
  have hun : iterateFrobenius F p f (u : F) * u = 1 := by
    have h1 : u ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hu]; omega)
    rw [hσ, ← pow_succ]
    simpa using congrArg Units.val h1
  have hu4 : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have hχ4 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 4 = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val]
    change (((u ^ (Multiplicative.toAdd k).val) ^ 4 : Fˣ) : F) = 1
    rw [← pow_mul, mul_comm, pow_mul, hu4, one_pow, Units.val_one]
  have hχσ : ∀ k, iterateFrobenius F p f (((zChar u 4 hu4) k : Fˣ) : F) *
      (((zChar u 4 hu4) k : Fˣ) : F) = 1 := fun k => by
    change iterateFrobenius F p f ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) *
      ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]
  have hχ2 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 2 = 1 → zRed 4 (by decide) k = 1 :=
    fun k hk => (zRed_eq_one_iff 4 _ k).2
      (zChar_pow_imp (m := 2) rfl (by norm_num) hu hu4 k hk)
  refine rankCertified_statedProj (A := V4 × Multiplicative (ZMod 2))
    (alpha3 Q.ρ (zChar u 4 hu4)).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap (zRed 4 (by decide)))
    (q8Frattini_surjective.prodMap (zRed_surjective 4 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_V2]; norm_num) ?_
  · exact mem_statedSU_of_isUni hσ _ (det_alpha3 Q.det_eq _ hχ4 k) (isUni_alpha3 hQ _ hχσ k)
  · intro k c h
    obtain ⟨h1, h3⟩ := alpha3_scalar Q (zChar u 4 hu4) hχ2 k c h
    exact Prod.ext h1 h3

end CFSG.GH74.Generic.S3
