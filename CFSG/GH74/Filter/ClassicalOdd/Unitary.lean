module

public import CFSG.GH74.Filter.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Unitary
public import CFSG.LocalAnalysis.SectionRank.OddCover.AltForm

public section

namespace CFSG.GH74.Filter.ClassicalOdd

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section Unitary

open CFSG.SectionRank.ClassicalOdd

variable {F : Type} [Field F] {σ : F →+* F}

@[expose] def IsUni (σ : F →+* F) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) :
    Prop :=
  hstar σ A * A = 1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem IsUni.one : IsUni σ (1 : Matrix ι ι F) := by
  rw [IsUni, hstar_one, Matrix.mul_one]

theorem IsUni.mul {A B : Matrix ι ι F} (hA : IsUni σ A) (hB : IsUni σ B) : IsUni σ (A * B) := by
  have hA' : hstar σ A * A = 1 := hA
  have hB' : hstar σ B * B = 1 := hB
  rw [IsUni, hstar_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (hstar σ A), hA', Matrix.one_mul, hB']

theorem IsUni.pow {A : Matrix ι ι F} (hA : IsUni σ A) (n : ℕ) : IsUni σ (A ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IsUni.one
  | succ n ih => rw [pow_succ]; exact ih.mul hA

theorem IsUni.smul {t : F} (ht : σ t * t = 1) {A : Matrix ι ι F} (hA : IsUni σ A) :
    IsUni σ (t • A) := by
  have hA' : hstar σ A * A = 1 := hA
  rw [IsUni, hstar_smul, smul_mul_smul_comm, ht, one_smul, hA']

theorem hstar_diagBlock {k m : ℕ} (X : Matrix (Fin k) (Fin k) F) (Y : Matrix (Fin m) (Fin m) F) :
    hstar σ (diagBlock X Y) = diagBlock (hstar σ X) (hstar σ Y) := by
  rw [hstar, hstar, hstar, diagBlock_map, diagBlock_transpose]

theorem IsUni.diagBlock {k m : ℕ} {X : Matrix (Fin k) (Fin k) F} {Y : Matrix (Fin m) (Fin m) F}
    (hX : IsUni σ X) (hY : IsUni σ Y) : IsUni σ (diagBlock X Y) := by
  have hX' : hstar σ X * X = 1 := hX
  have hY' : hstar σ Y * Y = 1 := hY
  rw [IsUni, hstar_diagBlock, diagBlock_mul, hX', hY', diagBlock_one]

theorem isUni_quatI : IsUni σ (quatI F) := by
  unfold IsUni
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, quatI, Matrix.mul_apply, Fin.sum_univ_two]

theorem isUni_quatJ {a b : F} (h : a ^ 2 + b ^ 2 = -1) (ha : σ a = -a) (hb : σ b = -b) :
    IsUni σ (quatJ a b) := by
  unfold IsUni
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hstar, quatJ, Matrix.mul_apply, Fin.sum_univ_two, ha, hb] <;>
    first | ring1 | linear_combination (-1 : F) * h

theorem isUni_quatHom {a b : F} (h : a ^ 2 + b ^ 2 = -1) (ha : σ a = -a) (hb : σ b = -b)
    (g : Q8) :
    IsUni σ ((quatHom h g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rcases g with k | k
  · rw [coe_quatHom_a]
    exact isUni_quatI.pow _
  · rw [coe_quatHom_xa]
    exact (isUni_quatJ h ha hb).mul (isUni_quatI.pow _)

theorem isUni_alpha6 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, IsUni σ (ρ g)) (m : ℕ)
    (g : Q8 × Q8 × Q8) : IsUni σ (alpha6 ρ m g) := by
  rw [alpha6_apply]
  exact (hρ _).diagBlock ((hρ _).diagBlock ((hρ _).diagBlock IsUni.one))

theorem isUni_alpha4 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, IsUni σ (ρ g))
    (χ : Multiplicative (ZMod 8) →* Fˣ) (hχ : ∀ k, σ ((χ k : Fˣ) : F) * ((χ k : Fˣ) : F) = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 8)) : IsUni σ (alpha4 ρ χ g) := by
  rw [alpha4_apply]
  refine IsUni.diagBlock ((hρ _).smul (hχ _)) ((hρ _).smul ?_)
  rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hχ, inv_one]

theorem isUni_alpha5 {ρ : Q8 →* Matrix (Fin 2) (Fin 2) F} (hρ : ∀ g, IsUni σ (ρ g))
    (χ : Multiplicative (ZMod 4) →* Fˣ) (hχ : ∀ k, σ ((χ k : Fˣ) : F) * ((χ k : Fˣ) : F) = 1)
    (g : (Q8 × Q8) × Multiplicative (ZMod 4)) : IsUni σ (alpha5 ρ χ g) := by
  rw [alpha5_apply]
  refine IsUni.diagBlock (IsUni.diagBlock ((hρ _).smul (hχ _)) (hρ _)) (IsUni.one.smul ?_)
  rw [map_pow, ← mul_pow, hχ, one_pow]

end Unitary

theorem exists_quat_unitary {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (hK : Nat.card F = (p ^ f) ^ 2) :
    ∃ a b : F, a ^ (p ^ f) = -a ∧ b ^ (p ^ f) = -b ∧ a ^ 2 + b ^ 2 = -1 := by
  obtain ⟨-, η, -, hη0, hη⟩ := CFSG.SectionRank.ClassicalOdd.exists_unitary_elems hp2 hK
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  set σ := iterateFrobenius F p f with hσdef
  have hσ : ∀ x, σ x = x ^ (p ^ f) := CFSG.SectionRank.ClassicalOdd.frob_apply
  let L : Subfield F := σ.eqLocusField (RingHom.id F)
  have : Finite L := inferInstance
  have : Fintype L := Fintype.ofFinite L
  have h2L : (2 : L) ≠ 0 := fun h => h2F (by
    have := congrArg (Subfield.subtype L) h
    simp only [map_ofNat, map_zero] at this
    exact this)
  have hLchar : ringChar L ≠ 2 := fun h => h2L (by
    have := ringChar.Nat.cast_ringChar (R := L)
    rw [h] at this
    exact_mod_cast this)
  have hodd : Fintype.card L % 2 = 1 := FiniteField.odd_card_of_char_ne_two hLchar
  have hη' : σ η = -η := by rw [hσ]; exact hη
  have hc : σ (-(η ^ 2)⁻¹) = (RingHom.id F) (-(η ^ 2)⁻¹) := by
    simp only [RingHom.id_apply, map_neg, map_inv₀, map_pow, hη', neg_sq]
  obtain ⟨s, t, hst⟩ := CFSG.SectionRank.OddCover.exists_sq_add_sq hodd (⟨-(η ^ 2)⁻¹, hc⟩ : L)
  have hs : σ (s : F) = s := s.2
  have ht : σ (t : F) = t := t.2
  have hst' : (s : F) ^ 2 + (t : F) ^ 2 = -(η ^ 2)⁻¹ := by
    simpa using congrArg Subtype.val hst
  refine ⟨η * s, η * t, ?_, ?_, ?_⟩
  · rw [← hσ, map_mul, hη', hs]
    ring
  · rw [← hσ, map_mul, hη', ht]
    ring
  · have : η ^ 2 ≠ 0 := pow_ne_zero 2 hη0
    calc (η * s) ^ 2 + (η * t) ^ 2 = η ^ 2 * ((s : F) ^ 2 + (t : F) ^ 2) := by ring
      _ = -1 := by rw [hst', mul_neg, mul_inv_cancel₀ this]

theorem not_gen4_SU_ge_six {F : Type} [Field F] {q : ℕ} {σ : F →+* F} (hσ : ∀ x, σ x = x ^ q)
    (Q : QuatRep F) (hQ : ∀ g, IsUni σ (Q.ρ g)) (m : ℕ) :
    ¬ Gen4 (StatedProj (StatedSU (2 + (2 + (2 + m))) q F)) := by
  have hfun : (fun x : F => x ^ q) = σ := funext fun x => (hσ x).symm
  refine not_gen4_statedProj (A := V4 × V4 × V4) (alpha6 Q.ρ m).toHomUnits (fun k => ?_)
    (q8Frattini.prodMap (q8Frattini.prodMap q8Frattini))
    (q8Frattini_surjective.prodMap (q8Frattini_surjective.prodMap q8Frattini_surjective))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_cube]; norm_num) ?_
  · refine Subgroup.subset_closure ⟨det_alpha6 Q.det_eq m k, ?_⟩
    change ((alpha6 Q.ρ m k).map (fun x => x ^ q))ᵀ * alpha6 Q.ρ m k = 1
    rw [hfun]
    exact isUni_alpha6 hQ m k
  · intro k c h
    obtain ⟨h1, h2, h3⟩ := alpha6_scalar Q m k c h
    exact Prod.ext h1 (Prod.ext h2 h3)

theorem not_gen4_SU_four {F : Type} [Field F] {q : ℕ} {σ : F →+* F} (hσ : ∀ x, σ x = x ^ q)
    (Q : QuatRep F) (hQ : ∀ g, IsUni σ (Q.ρ g)) (u : Fˣ) (hu : orderOf u = 8)
    (hun : σ (u : F) * u = 1) :
    ¬ Gen4 (StatedProj (StatedSU (2 + 2) q F)) := by
  have hfun : (fun x : F => x ^ q) = σ := funext fun x => (hσ x).symm
  have hu8 : u ^ 8 = 1 := hu ▸ pow_orderOf_eq_one u
  have hχσ : ∀ k, σ (((zChar u 8 hu8) k : Fˣ) : F) * (((zChar u 8 hu8) k : Fˣ) : F) = 1 :=
    fun k => by
      change σ ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) *
        ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]
  refine not_gen4_statedProj (A := (V4 × V4) × Multiplicative (ZMod 2))
    (alpha4 Q.ρ (zChar u 8 hu8)).toHomUnits (fun k => ?_)
    ((q8Frattini.prodMap q8Frattini).prodMap (zRed 8 (by decide)))
    ((q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap (zRed_surjective 8 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_
  · refine Subgroup.subset_closure ⟨det_alpha4 Q.det_eq _ k, ?_⟩
    change ((alpha4 Q.ρ (zChar u 8 hu8) k).map (fun x => x ^ q))ᵀ *
      alpha4 Q.ρ (zChar u 8 hu8) k = 1
    rw [hfun]
    exact isUni_alpha4 hQ _ hχσ k
  · intro k c h
    obtain ⟨h1, h2, h3⟩ := alpha4_scalar Q (zChar u 8 hu8)
      (fun k hk => (zRed_eq_one_iff 8 _ k).2 (zChar_pow_imp (m := 4) rfl (by norm_num) hu hu8 k hk))
      k c h
    exact Prod.ext (Prod.ext h1 h2) h3

theorem not_gen4_SU_five {F : Type} [Field F] {q : ℕ} {σ : F →+* F} (hσ : ∀ x, σ x = x ^ q)
    (Q : QuatRep F) (hQ : ∀ g, IsUni σ (Q.ρ g)) (u : Fˣ) (hu : orderOf u = 4)
    (hun : σ (u : F) * u = 1) :
    ¬ Gen4 (StatedProj (StatedSU (2 + 2 + 1) q F)) := by
  have hfun : (fun x : F => x ^ q) = σ := funext fun x => (hσ x).symm
  have hu4 : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have hχ4 : ∀ k, (((zChar u 4 hu4) k : Fˣ) : F) ^ 4 = 1 := fun k => by
    rw [← Units.val_pow_eq_pow_val]
    change (((u ^ (Multiplicative.toAdd k).val) ^ 4 : Fˣ) : F) = 1
    rw [← pow_mul, mul_comm, pow_mul, hu4, one_pow, Units.val_one]
  have hχσ : ∀ k, σ (((zChar u 4 hu4) k : Fˣ) : F) * (((zChar u 4 hu4) k : Fˣ) : F) = 1 :=
    fun k => by
      change σ ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) *
        ((u ^ (Multiplicative.toAdd k).val : Fˣ) : F) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]
  refine not_gen4_statedProj (A := (V4 × V4) × Multiplicative (ZMod 2))
    (alpha5 Q.ρ (zChar u 4 hu4)).toHomUnits (fun k => ?_)
    ((q8Frattini.prodMap q8Frattini).prodMap (zRed 4 (by decide)))
    ((q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap (zRed_surjective 4 (by decide)))
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_
  · refine Subgroup.subset_closure ⟨det_alpha5 Q.det_eq _ hχ4 k, ?_⟩
    change ((alpha5 Q.ρ (zChar u 4 hu4) k).map (fun x => x ^ q))ᵀ *
      alpha5 Q.ρ (zChar u 4 hu4) k = 1
    rw [hfun]
    exact isUni_alpha5 hQ _ hχσ k
  · intro k c h
    obtain ⟨h1, h2, h3⟩ := alpha5_scalar Q (zChar u 4 hu4)
      (fun k hk => (zRed_eq_one_iff 4 _ k).2 (zChar_pow_imp (m := 2) rfl (by norm_num) hu hu4 k hk))
      k c h
    exact Prod.ext (Prod.ext h1 h2) h3

end CFSG.GH74.Filter.ClassicalOdd

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.ClassicalOdd

theorem t_PSU_six_odd : S_PSU_six_odd := by
  intro G _ _ p f hp2 hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hK
  have hσ : ∀ x, iterateFrobenius K p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have hQ : ∀ g, IsUni (iterateFrobenius K p f) ((QuatRep.ofSq hK2 hab).ρ g) := fun g =>
    isUni_quatHom hab (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SU_ge_six hσ _ hQ 0)

theorem t_PSU_ge_seven_odd : S_PSU_ge_seven_odd := by
  intro G _ _ n p f hp2 hn hm
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + (2 + (2 + m)) := ⟨n - 6, by omega⟩
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hK
  have hσ : ∀ x, iterateFrobenius K p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have hQ : ∀ g, IsUni (iterateFrobenius K p f) ((QuatRep.ofSq hK2 hab).ρ g) := fun g =>
    isUni_quatHom hab (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SU_ge_six hσ _ hQ m)

theorem t_PSU_four_odd : S_PSU_four_odd := by
  intro G _ _ p f hp2 hmod hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hK
  have hσ : ∀ x, iterateFrobenius K p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have hQ : ∀ g, IsUni (iterateFrobenius K p f) ((QuatRep.ofSq hK2 hab).ρ g) := fun g =>
    isUni_quatHom hab (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g
  have h8 : 8 ∣ Nat.card K - 1 := by
    have : (p ^ f) ^ 2 % 8 = 1 := by rw [Nat.pow_mod, hmod]
    omega
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := K) (d := 8) h8
  have hun : iterateFrobenius K p f (u : K) * u = 1 := by
    have h1 : u ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hu]; omega)
    rw [hσ, ← pow_succ]
    simpa using congrArg Units.val h1
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SU_four hσ _ hQ u hu hun)

theorem t_PSU_five_odd : S_PSU_five_odd := by
  intro G _ _ p f hp2 hmod hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hK
  have hσ : ∀ x, iterateFrobenius K p f x = x ^ (p ^ f) :=
    CFSG.SectionRank.ClassicalOdd.frob_apply
  have hQ : ∀ g, IsUni (iterateFrobenius K p f) ((QuatRep.ofSq hK2 hab).ρ g) := fun g =>
    isUni_quatHom hab (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g
  have h4 : 4 ∣ Nat.card K - 1 := by
    have : (p ^ f) ^ 2 % 4 = 1 := by rw [Nat.pow_mod, hmod]
    omega
  obtain ⟨u, hu⟩ := exists_units_orderOf (F := K) (d := 4) h4
  have hun : iterateFrobenius K p f (u : K) * u = 1 := by
    have h1 : u ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hu]; omega)
    rw [hσ, ← pow_succ]
    simpa using congrArg Units.val h1
  exact not_gen4_of_mulEquiv e.symm (not_gen4_SU_five hσ _ hQ u hu hun)


end CFSG.GH74.Filter
