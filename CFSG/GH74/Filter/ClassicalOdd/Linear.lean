module

public import CFSG.GH74.Filter.ClassicalOdd.Basic
public import CFSG.GH74.Filter.Statements
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.GH74.Filter.ClassicalOdd

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section Alpha

variable {F : Type*} [Field F]

@[expose] def alpha6 (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (m : ℕ) :
    Q8 × Q8 × Q8 →* Matrix (Fin (2 + (2 + (2 + m)))) (Fin (2 + (2 + (2 + m)))) F where
  toFun g := diagBlock (ρ g.1) (diagBlock (ρ g.2.1) (diagBlock (ρ g.2.2)
    (1 : Matrix (Fin m) (Fin m) F)))
  map_one' := by simp [diagBlock_one]
  map_mul' g h := by simp [diagBlock_mul]

theorem alpha6_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (m : ℕ) (g : Q8 × Q8 × Q8) :
    alpha6 ρ m g = diagBlock (ρ g.1) (diagBlock (ρ g.2.1) (diagBlock (ρ g.2.2)
      (1 : Matrix (Fin m) (Fin m) F))) := rfl

theorem det_alpha6 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, (ρ g).det = 1) (m : ℕ)
    (g : Q8 × Q8 × Q8) : (alpha6 ρ m g).det = 1 := by
  simp only [alpha6_apply, det_diagBlock, hρ, det_one, mul_one]

theorem alpha6_scalar (Q : QuatRep F) (m : ℕ) (g : Q8 × Q8 × Q8) (c : F)
    (h : alpha6 Q.ρ m g = scalar (Fin (2 + (2 + (2 + m)))) c) :
    q8Frattini g.1 = 1 ∧ q8Frattini g.2.1 = 1 ∧ q8Frattini g.2.2 = 1 := by
  rw [alpha6_apply] at h
  obtain ⟨h1, h23⟩ := eq_scalar_of_diagBlock_eq h
  obtain ⟨h2, h3m⟩ := eq_scalar_of_diagBlock_eq h23
  obtain ⟨h3, -⟩ := eq_scalar_of_diagBlock_eq h3m
  exact ⟨(Q.scalar_eq _ _ h1).1, (Q.scalar_eq _ _ h2).1, (Q.scalar_eq _ _ h3).1⟩

@[expose] def alpha4 (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 8) →* Fˣ) :
    (Q8 × Q8) × Multiplicative (ZMod 8) →* Matrix (Fin (2 + 2)) (Fin (2 + 2)) F where
  toFun g := diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1.1) ((((χ g.2)⁻¹ : Fˣ) : F) • ρ g.1.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one, Units.val_one, inv_one, one_smul]
    exact diagBlock_one
  map_mul' g h := by
    rw [diagBlock_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul, mul_inv, smul_mul_smul_comm]

theorem alpha4_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 8) →* Fˣ)
    (g : (Q8 × Q8) × Multiplicative (ZMod 8)) :
    alpha4 ρ χ g = diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1.1) ((((χ g.2)⁻¹ : Fˣ) : F) • ρ g.1.2) :=
  rfl

theorem det_alpha4 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, (ρ g).det = 1)
    (χ : Multiplicative (ZMod 8) →* Fˣ) (g : (Q8 × Q8) × Multiplicative (ZMod 8)) :
    (alpha4 ρ χ g).det = 1 := by
  rw [alpha4_apply, det_diagBlock, det_smul, det_smul, hρ, hρ, Units.val_inv_eq_inv_val]
  have ht : ((χ g.2 : Fˣ) : F) ≠ 0 := Units.ne_zero _
  simp only [Fintype.card_fin, mul_one]
  rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 ht)]

theorem alpha4_scalar (Q : QuatRep F) (χ : Multiplicative (ZMod 8) →* Fˣ)
    (hχ : ∀ k, ((χ k : Fˣ) : F) ^ 4 = 1 → zRed 8 (by decide) k = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 8)) (c : F)
    (h : alpha4 Q.ρ χ g = scalar (Fin (2 + 2)) c) :
    q8Frattini g.1.1 = 1 ∧ q8Frattini g.1.2 = 1 ∧ zRed 8 (by decide) g.2 = 1 := by
  rw [alpha4_apply] at h
  obtain ⟨h1, h2⟩ := eq_scalar_of_diagBlock_eq h
  have ht0 : ((χ g.2 : Fˣ) : F) ≠ 0 := Units.ne_zero _
  set t : F := ((χ g.2 : Fˣ) : F) with ht
  have hinv : (((χ g.2)⁻¹ : Fˣ) : F) = t⁻¹ := by simp [ht]
  rw [hinv] at h2
  have hx : Q.ρ g.1.1 = scalar (Fin 2) (t⁻¹ * c) := by
    rw [← smul_scalar_fin_two, ← h1, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hy : Q.ρ g.1.2 = scalar (Fin 2) (t * c) := by
    rw [← smul_scalar_fin_two, ← h2, smul_smul, mul_inv_cancel₀ ht0, one_smul]
  obtain ⟨hx1, hx2⟩ := Q.scalar_eq _ _ hx
  obtain ⟨hy1, hy2⟩ := Q.scalar_eq _ _ hy
  refine ⟨hx1, hy1, hχ _ ?_⟩
  have e : t ^ 2 * (t⁻¹ * c) = t * c := by field_simp
  rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;> rw [hx2, hy2] at e
  · linear_combination (t ^ 2 + 1) * e
  · linear_combination (t ^ 2 - 1) * e
  · linear_combination (1 - t ^ 2) * e
  · linear_combination (-(t ^ 2 + 1)) * e

@[expose] def alpha5 (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 4) →* Fˣ) :
    (Q8 × Q8) × Multiplicative (ZMod 4) →* Matrix (Fin (2 + 2 + 1)) (Fin (2 + 2 + 1)) F where
  toFun g := diagBlock (diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1.1) (ρ g.1.2))
    ((((χ g.2 : Fˣ) : F) ^ 2) • (1 : Matrix (Fin 1) (Fin 1) F))
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one, Units.val_one, one_pow, one_smul]
    rw [diagBlock_one, diagBlock_one]
  map_mul' g h := by
    rw [diagBlock_mul, diagBlock_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul, mul_pow, smul_mul_smul_comm,
      mul_one]

theorem alpha5_apply (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) :
    alpha5 ρ χ g = diagBlock (diagBlock (((χ g.2 : Fˣ) : F) • ρ g.1.1) (ρ g.1.2))
      ((((χ g.2 : Fˣ) : F) ^ 2) • (1 : Matrix (Fin 1) (Fin 1) F)) :=
  rfl

theorem det_alpha5 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, (ρ g).det = 1)
    (χ : Multiplicative (ZMod 4) →* Fˣ) (hχ : ∀ k, ((χ k : Fˣ) : F) ^ 4 = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) : (alpha5 ρ χ g).det = 1 := by
  rw [alpha5_apply, det_diagBlock, det_diagBlock, det_smul, det_smul, hρ, hρ, det_one]
  simp only [Fintype.card_fin, mul_one, pow_one]
  linear_combination hχ g.2

theorem alpha5_scalar (Q : QuatRep F) (χ : Multiplicative (ZMod 4) →* Fˣ)
    (hχ : ∀ k, ((χ k : Fˣ) : F) ^ 2 = 1 → zRed 4 (by decide) k = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) (c : F)
    (h : alpha5 Q.ρ χ g = scalar (Fin (2 + 2 + 1)) c) :
    q8Frattini g.1.1 = 1 ∧ q8Frattini g.1.2 = 1 ∧ zRed 4 (by decide) g.2 = 1 := by
  rw [alpha5_apply] at h
  obtain ⟨h12, h3⟩ := eq_scalar_of_diagBlock_eq h
  obtain ⟨h1, h2⟩ := eq_scalar_of_diagBlock_eq h12
  have ht0 : ((χ g.2 : Fˣ) : F) ≠ 0 := Units.ne_zero _
  set t : F := ((χ g.2 : Fˣ) : F) with ht
  have hc : t ^ 2 = c := by
    have := congrFun (congrFun h3 0) 0
    simpa [scalar_apply] using this
  have hx : Q.ρ g.1.1 = scalar (Fin 2) (t⁻¹ * c) := by
    rw [← smul_scalar_fin_two, ← h1, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  obtain ⟨hx1, hx2⟩ := Q.scalar_eq _ _ hx
  obtain ⟨hy1, hy2⟩ := Q.scalar_eq _ _ h2
  refine ⟨hx1, hy1, hχ _ ?_⟩
  have e : t⁻¹ * c = t := by rw [← hc, sq, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  rw [e] at hx2
  have h1 : t ^ 2 = 1 := by
    rcases hx2 with h | h <;> rw [h] <;> norm_num
  exact h1

end Alpha

theorem not_gen4_SL_ge_six {F : Type} [Field F] (Q : QuatRep F) (m : ℕ) :
    ¬ Gen4 (StatedProj (StatedSL (2 + (2 + (2 + m))) F)) := by
  refine not_gen4_statedProj (A := V4 × V4 × V4) (alpha6 Q.ρ m).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap (q8Frattini.prodMap q8Frattini))
    (q8Frattini_surjective.prodMap (q8Frattini_surjective.prodMap q8Frattini_surjective))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_cube]; norm_num) ?_
  · exact Subgroup.subset_closure (det_alpha6 Q.det_eq m k)
  · intro k c h
    obtain ⟨h1, h2, h3⟩ := alpha6_scalar Q m k c h
    exact Prod.ext h1 (Prod.ext h2 h3)

theorem not_gen4_SL_four {F : Type} [Field F] (Q : QuatRep F) (u : Fˣ) (hu : orderOf u = 8) :
    ¬ Gen4 (StatedProj (StatedSL (2 + 2) F)) := by
  have hu8 : u ^ 8 = 1 := hu ▸ pow_orderOf_eq_one u
  refine not_gen4_statedProj (A := (V4 × V4) × Multiplicative (ZMod 2))
    (alpha4 Q.ρ (zChar u 8 hu8)).toHomUnits (fun k => ?_)
    ((q8Frattini.prodMap q8Frattini).prodMap (zRed 8 (by decide)))
    ((q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap (zRed_surjective 8 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_
  · exact Subgroup.subset_closure (det_alpha4 Q.det_eq _ k)
  · intro k c h
    obtain ⟨h1, h2, h3⟩ := alpha4_scalar Q (zChar u 8 hu8)
      (fun k hk => (zRed_eq_one_iff 8 _ k).2 (zChar_pow_imp (m := 4) rfl (by norm_num) hu hu8 k hk))
      k c h
    exact Prod.ext (Prod.ext h1 h2) h3

theorem not_gen4_SL_five {F : Type} [Field F] (Q : QuatRep F) (u : Fˣ) (hu : orderOf u = 4) :
    ¬ Gen4 (StatedProj (StatedSL (2 + 2 + 1) F)) := by
  have hu4 : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have hχ4 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 4 = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val]
    change (((u ^ (Multiplicative.toAdd k).val) ^ 4 : Fˣ) : F) = 1
    rw [← pow_mul, mul_comm, pow_mul, hu4, one_pow, Units.val_one]
  refine not_gen4_statedProj (A := (V4 × V4) × Multiplicative (ZMod 2))
    (alpha5 Q.ρ (zChar u 4 hu4)).toHomUnits (fun k => ?_)
    ((q8Frattini.prodMap q8Frattini).prodMap (zRed 4 (by decide)))
    ((q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap (zRed_surjective 4 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_
  · exact Subgroup.subset_closure (det_alpha5 Q.det_eq _ hχ4 k)
  · intro k c h
    obtain ⟨h1, h2, h3⟩ := alpha5_scalar Q (zChar u 4 hu4)
      (fun k hk => (zRed_eq_one_iff 4 _ k).2 (zChar_pow_imp (m := 2) rfl (by norm_num) hu hu4 k hk))
      k c h
    exact Prod.ext (Prod.ext h1 h2) h3

end CFSG.GH74.Filter.ClassicalOdd

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.ClassicalOdd

theorem t_PSL_six_odd : S_PSL_six_odd := by
  intro G _ _ p f hp2 hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨Q⟩ := exists_quatRep hK2
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SL_ge_six Q 0)

theorem t_PSL_ge_seven_odd : S_PSL_ge_seven_odd := by
  intro G _ _ n p f hp2 hn hm
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + (2 + (2 + m)) := ⟨n - 6, by omega⟩
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨Q⟩ := exists_quatRep hK2
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SL_ge_six Q m)

theorem t_PSL_four_odd : S_PSL_four_odd := by
  intro G _ _ p f hp2 hmod hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨Q⟩ := exists_quatRep hK2
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := K) (d := 8) (by omega)
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SL_four Q u hu)

theorem t_PSL_five_odd : S_PSL_five_odd := by
  intro G _ _ p f hp2 hmod hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨Q⟩ := exists_quatRep hK2
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := K) (d := 4) (by omega)
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SL_five Q u hu)

end CFSG.GH74.Filter
