module

public import CFSG.CGT.T75N.PpdCyclic
public import CFSG.GH74.Bender.Suzuki
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

namespace CFSG.CGT.T75N

open Equiv Matrix MatrixGroups CFSG.BenderSuzuki

section L2

variable {F : Type} [Field F] [CharP F 2]

theorem center_sl2_eq_bot : Subgroup.center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
    subst hr1
    ext i j
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) hA
    simp at this
    simpa using this.symm
  · rintro rfl
    exact ⟨1, by simp, by simp⟩


noncomputable def pslEquivSL :
    ProjectiveSpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot (F := F))).trans
    QuotientGroup.quotientBot

@[expose] def diag2 (x : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(x : F), 0; 0, ((x⁻¹ : Fˣ) : F)], by rw [Matrix.det_fin_two_of]; simp⟩

omit [CharP F 2] in
theorem coe_diag2 (x : Fˣ) : ((diag2 x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![(x : F), 0; 0, ((x⁻¹ : Fˣ) : F)] := rfl

def torus2 : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun := diag2
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diag2]
  map_mul' x y := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [coe_diag2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

omit [CharP F 2] in
theorem torus2_injective : Function.Injective (torus2 (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hx
  simp [torus2, coe_diag2] at this
  exact this


omit [CharP F 2] in
theorem card_sl2 [Fintype F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) =
      Fintype.card F * (Fintype.card F - 1) * (Fintype.card F + 1) := by
  rw [Matrix.card_SL_field (𝔽 := F) 2]
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 2 := ⟨Fintype.card F - 2, by omega⟩
  rw [hr, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have h1 : (r + 2) ^ 2 - 1 = (r + 1) * (r + 3) := by
    apply Nat.sub_eq_of_eq_add; ring
  have h2 : (r + 2) ^ 2 - (r + 2) = (r + 2) * (r + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [h1, h2, show r + 2 - 1 = r + 1 by omega]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  ring

end L2

section SL2Cyc

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {p : ℕ} [hp : Fact p.Prime]

theorem isCyclic_of_isPGroup_sl2 (hp2 : p ≠ 2) (P : Subgroup (SpecialLinearGroup (Fin 2) F))
    (hP : IsPGroup p P) : IsCyclic P := by
  classical
  by_cases hbot : P = ⊥
  · subst hbot; infer_instance
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hbot
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
  have hpP : p ∣ Nat.card P := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hm
      have := Nat.card_eq_one_iff_unique.1 hm
      obtain ⟨a, b, hab⟩ := exists_pair_ne P
      exact hab (this.1.elim a b)
    · rw [hm]; exact dvd_pow_self p hpos.ne'
  set q := Fintype.card F with hq
  have hcard := card_sl2 (F := F)
  have hpSL : p ∣ q * (q - 1) * (q + 1) :=
    hcard ▸ hpP.trans (Subgroup.card_subgroup_dvd_card P)
  have hq2 : ∃ k : ℕ, q = 2 ^ k := by
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    exact ⟨k, hk⟩
  have hpq : ¬ p ∣ q := by
    intro h
    obtain ⟨k, hk⟩ := hq2
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hdiff : p ∣ q - 1 → p ∣ q + 1 → False := by
    intro h1 h2
    have h3 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h2 h1
    have : (q + 1) - (q - 1) = 2 := by omega
    rw [this] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h3)
  rcases (hp.out.dvd_mul.1 hpSL) with h | h
  · rcases hp.out.dvd_mul.1 h with h' | h'
    · exact absurd h' hpq
    ·
      have hTc : IsCyclic (torus2 (F := F)).range :=
        isCyclic_of_surjective (torus2 (F := F)).rangeRestrict
          (MonoidHom.rangeRestrict_surjective _)
      have hTcard : Nat.card (torus2 (F := F)).range = q - 1 := by
        rw [← Nat.card_congr (MonoidHom.ofInjective (torus2_injective (F := F))).toEquiv,
          Nat.card_units, Nat.card_eq_fintype_card]
      refine isCyclic_of_isPGroup_of_cyclic_hall (torus2 (F := F)).range (M := q * (q + 1))
        (by rw [hcard, hTcard]; ring) ?_ P hP
      intro hM
      rcases hp.out.dvd_mul.1 hM with h1 | h1
      · exact hpq h1
      · exact hdiff h' h1
  ·
    have hn1 : ¬ p ∣ q - 1 := fun h1 => hdiff h1 h
    refine isCyclic_of_isPGroup_of_embed (n := 2) (F := F) Matrix.SpecialLinearGroup.toGL
      (fun a b hab => ?_) (by norm_num) ?_ ?_ P hP
    · exact Matrix.SpecialLinearGroup.toGL_injective hab
    · have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        rw [hr]; simp only [Nat.add_sub_cancel]; apply Nat.sub_eq_of_eq_add; ring
      rw [this]
      exact Dvd.dvd.mul_left h _
    · intro k hk0 hk2
      have : k = 1 := by omega
      subst this
      simpa using hn1

end SL2Cyc

section Sz


noncomputable def szTorus (a : ℕ) :
    (GaloisField 2 (2 * a + 1))ˣ →* GL (Fin 4) (GaloisField 2 (2 * a + 1)) :=
  (Units.map (Matrix.diagonalRingHom (Fin 4) (GaloisField 2 (2 * a + 1))).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin 4 => GaloisField 2 (2 * a + 1))).symm.toMonoidHom.comp
      (MonoidHom.pi fun i : Fin 4 =>
        match i with
        | 0 => powMonoidHom (1 + 2 ^ a)
        | 1 => powMonoidHom (2 ^ a)
        | 2 => (powMonoidHom (2 ^ a))⁻¹
        | 3 => (powMonoidHom (1 + 2 ^ a))⁻¹))

theorem szTorus_coe (a : ℕ) (x : (GaloisField 2 (2 * a + 1))ˣ) :
    ((szTorus a x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) =
      !![(x : GaloisField 2 (2 * a + 1)) ^ (1 + 2 ^ a), 0, 0, 0;
         0, (x : GaloisField 2 (2 * a + 1)) ^ (2 ^ a), 0, 0;
         0, 0, ((x : GaloisField 2 (2 * a + 1)) ^ (2 ^ a))⁻¹, 0;
         0, 0, 0, ((x : GaloisField 2 (2 * a + 1)) ^ (1 + 2 ^ a))⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szTorus, MonoidHom.pi_apply, powMonoidHom_apply, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]


theorem szTorus_mem (a : ℕ) (x : (GaloisField 2 (2 * a + 1))ˣ) : szTorus a x ∈ SzModel a := by
  apply Subgroup.subset_closure
  show ((szTorus a x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) ∈ SzGenerators a
  rw [szTorus_coe]
  exact Or.inr (Or.inl ⟨x, rfl⟩)

theorem szTorus_injective (a : ℕ) : Function.Injective (szTorus a) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := congrArg (fun A : GL (Fin 4) (GaloisField 2 (2 * a + 1)) =>
    (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) 1 1) hx
  rw [szTorus_coe] at h
  simp at h
  have h' : ((x : GaloisField 2 (2 * a + 1))) ^ 2 ^ a = 1 := h
  have : ((x : GaloisField 2 (2 * a + 1)) - 1) ^ 2 ^ a = 0 := by
    rw [sub_pow_char_pow, h', one_pow, sub_self]
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by positivity) |>.1 this))


theorem isCyclic_of_isPGroup_sz {a : ℕ} (ha : 1 ≤ a) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (P : Subgroup (SzModel a)) (hP : IsPGroup p P) :
    IsCyclic P := by
  classical
  by_cases hbot : P = ⊥
  · subst hbot; infer_instance
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hbot
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
  have hpP : p ∣ Nat.card P := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hm
      have := Nat.card_eq_one_iff_unique.1 hm
      obtain ⟨x, y, hxy⟩ := exists_pair_ne P
      exact hxy (this.1.elim x y)
    · rw [hm]; exact dvd_pow_self p hpos.ne'
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : Nat.card (SzModel a) = q ^ 2 * (q ^ 2 + 1) * (q - 1) :=
    (Nat.card_congr (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz a)).toEquiv).trans
      (CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a)
  have hpX : p ∣ q ^ 2 * (q ^ 2 + 1) * (q - 1) :=
    hX ▸ hpP.trans (Subgroup.card_subgroup_dvd_card P)
  have hpq : ¬ p ∣ q := by
    intro h
    rw [hq] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)
  have hidA : q ^ 2 + 1 = (q - 1) * (q + 1) + 2 := by
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [hr]; simp only [Nat.add_sub_cancel]; ring
  have hidB : q ^ 2 - 1 + 2 = q ^ 2 + 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hd1 : p ∣ q - 1 → p ∣ q ^ 2 + 1 → False := by
    intro h1 h2
    rw [hidA] at h2
    exact hp2' ((Nat.dvd_add_right (Dvd.dvd.mul_right h1 (q + 1))).1 h2)
  have hd2 : p ∣ q ^ 2 - 1 → p ∣ q ^ 2 + 1 → False := by
    intro h1 h2
    rw [← hidB] at h2
    exact hp2' ((Nat.dvd_add_right h1).1 h2)
  have hd3 : p ∣ q ^ 3 - 1 → p ∣ q ^ 2 + 1 → False := by
    intro h1 h2
    have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h3 : p ∣ q * (q ^ 2 + 1) - (q ^ 3 - 1) := Nat.dvd_sub (Dvd.dvd.mul_left h2 q) h1
    have e : q * (q ^ 2 + 1) - (q ^ 3 - 1) = q + 1 := by
      have : q * (q ^ 2 + 1) = q ^ 3 + q := by ring
      omega
    rw [e] at h3
    rw [hidA] at h2
    exact hp2' ((Nat.dvd_add_right (Dvd.dvd.mul_left h3 (q - 1))).1 h2)
  rcases hp.out.dvd_mul.1 hpX with h | h
  · rcases hp.out.dvd_mul.1 h with h' | h'
    · exact absurd (hp.out.dvd_of_dvd_pow h') hpq
    ·
      have : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
      have hcardF : Fintype.card (GaloisField 2 (2 * a + 1)) = q := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * a + 1) (by omega)]
      refine isCyclic_of_isPGroup_of_embed (n := 4) (F := GaloisField 2 (2 * a + 1))
        (SzModel a).subtype Subtype.val_injective (by norm_num) ?_ ?_ P hP
      · rw [hcardF]
        have : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
          obtain ⟨s, hs⟩ : ∃ s, q ^ 2 = s + 1 :=
            ⟨q ^ 2 - 1, by have := Nat.one_le_pow 2 q (by omega); omega⟩
          have h4 : q ^ 4 = (q ^ 2) ^ 2 := by ring
          rw [h4, hs, Nat.add_sub_cancel]
          apply Nat.sub_eq_of_eq_add; ring
        rw [this]
        exact Dvd.dvd.mul_left h' _
      · intro k hk0 hk4
        rw [hcardF]
        interval_cases k
        · exact fun h1 => hd1 (by simpa using h1) h'
        · exact fun h1 => hd2 h1 h'
        · exact fun h1 => hd3 h1 h'
  ·
    have : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
    let τ : (GaloisField 2 (2 * a + 1))ˣ →* SzModel a :=
      (szTorus a).codRestrict (SzModel a) (szTorus_mem a)
    have hτinj : Function.Injective τ := fun x y h => szTorus_injective a (congrArg Subtype.val h)
    have hTc : IsCyclic τ.range :=
      isCyclic_of_surjective τ.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    have hTcard : Nat.card τ.range = q - 1 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, Nat.card_units,
        GaloisField.card 2 (2 * a + 1) (by omega)]
    refine isCyclic_of_isPGroup_of_cyclic_hall τ.range (M := q ^ 2 * (q ^ 2 + 1))
      (by rw [hX, hTcard]; ring) ?_ P hP
    intro hM
    rcases hp.out.dvd_mul.1 hM with h1 | h1
    · exact hpq (hp.out.dvd_of_dvd_pow h1)
    · exact hd1 h h1

end Sz

section Final

theorem isCyclic_of_isPGroup_benderModel {X : Type}
    [Group X]
    (hmodel : (∃ f : ℕ, 2 ≤ f ∧ Nonempty (X ≃* PSL2Model f)) ∨
      (∃ a : ℕ, 1 ≤ a ∧ Nonempty (X ≃* SzModel a)))
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (P : Subgroup X) (hP : IsPGroup p P) :
    IsCyclic P := by
  rcases hmodel with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  ·
    have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    let e' : X ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 f) := e.trans pslEquivSL
    have hc : IsCyclic (P.map e'.toMonoidHom) :=
      isCyclic_of_isPGroup_sl2 hp2 _ (hP.map e'.toMonoidHom)
    exact isCyclic_of_injective
      (Subgroup.equivMapOfInjective P e'.toMonoidHom e'.injective).toMonoidHom
      (Subgroup.equivMapOfInjective P e'.toMonoidHom e'.injective).injective
  · have hc : IsCyclic (P.map e.toMonoidHom) :=
      isCyclic_of_isPGroup_sz ha hp2 _ (hP.map e.toMonoidHom)
    exact isCyclic_of_injective
      (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective).toMonoidHom
      (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective).injective

end Final

end CFSG.CGT.T75N
