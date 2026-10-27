module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section SL

variable {L : Type} [Field L] {ν : ℕ}

theorem slMap_transvection (σ : L →+* L) {a b : Fin ν} (hab : a ≠ b) (t : L) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.transvection hab t) =
      Matrix.SpecialLinearGroup.transvection hab (σ t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

@[expose] def stdUnitary (σ : L →+* L) : SL(ν, L) →* SL(ν, L) :=
  invTransposeSL.comp (Matrix.SpecialLinearGroup.map σ)

theorem stdUnitary_transvection (σ : L →+* L) {a b : Fin ν} (hab : a ≠ b) (t : L) :
    stdUnitary σ (Matrix.SpecialLinearGroup.transvection hab t) =
      Matrix.SpecialLinearGroup.transvection hab.symm (-(σ t)) := by
  rw [stdUnitary, MonoidHom.comp_apply, slMap_transvection]
  exact invTransposeSL_transvection hab.symm (σ t)

theorem coe_stdUnitary (σ : L →+* L) (X : SL(ν, L)) :
    ((stdUnitary σ X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      (((X : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹)ᵀ := by
  rw [stdUnitary, MonoidHom.comp_apply, coe_invTransposeSL, coe_inv_eq_nonsing_inv,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem slMap_invTransposeSL (σ : L →+* L) (Y : SL(ν, L)) :
    Matrix.SpecialLinearGroup.map σ (invTransposeSL Y) =
      invTransposeSL (Matrix.SpecialLinearGroup.map σ Y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_invTransposeSL, coe_invTransposeSL, ← map_inv,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    Matrix.transpose_map]

@[expose] noncomputable def stdUnitaryEquiv (σ : L ≃+* L) : SL(ν, L) ≃* SL(ν, L) :=
  MulEquiv.ofBijective (stdUnitary σ.toRingHom) (by
    refine ⟨fun X Y h => ?_, fun Y => ?_⟩
    · have h1 : Matrix.SpecialLinearGroup.map σ.toRingHom X =
          Matrix.SpecialLinearGroup.map σ.toRingHom Y := by
        have := congrArg invTransposeSL h
        simpa [stdUnitary, invTransposeSL_invTransposeSL] using this
      apply Subtype.ext
      ext i j
      have h2 := congrArg (fun Z : SL(ν, L) => (Z : Matrix (Fin ν) (Fin ν) L) i j) h1
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] at h2
      exact σ.injective h2
    · refine ⟨Matrix.SpecialLinearGroup.map σ.symm.toRingHom (invTransposeSL Y), ?_⟩
      rw [stdUnitary, MonoidHom.comp_apply]
      have : Matrix.SpecialLinearGroup.map σ.toRingHom
          (Matrix.SpecialLinearGroup.map σ.symm.toRingHom (invTransposeSL Y)) =
            invTransposeSL Y := by
        apply Subtype.ext
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]
      rw [this, invTransposeSL_invTransposeSL])

theorem stdUnitaryEquiv_apply (σ : L ≃+* L) (X : SL(ν, L)) :
    stdUnitaryEquiv σ X = stdUnitary σ.toRingHom X := rfl

theorem mem_fixSubgroup_stdUnitaryEquiv_iff {ℓ f : ℕ} (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (X : SL(ν, L)) :
    X ∈ fixSubgroup (stdUnitaryEquiv (ν := ν) σ) ↔
      Matrix.SpecialLinearGroup.toGL X ∈ unitarySet (ℓ ^ f) ν := by
  classical
  have hσmap : ∀ M : Matrix (Fin ν) (Fin ν) L, M.map σ.toRingHom = M.map (· ^ ℓ ^ f) := by
    intro M
    ext i j
    simp [hσ]
  have hdetX : IsUnit ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)).det := by
    rw [← hσmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, X.2, map_one]
    exact isUnit_one
  rw [mem_fixSubgroup, stdUnitaryEquiv_apply]
  constructor
  · intro h
    have hstd : stdUnitary σ.toRingHom X = X := h
    have h1 : (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ =
        (X : Matrix (Fin ν) (Fin ν) L) := by
      rw [← hσmap, ← coe_stdUnitary, hstd]
    have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
        (X : Matrix (Fin ν) (Fin ν) L) = 1 := by
      have e1 : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
            (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ := by rw [h1]
      rw [e1, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdetX, Matrix.transpose_one]
    refine ⟨fun i j => ?_, X.2, hu⟩
    have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom X = invTransposeSL X := by
      have := congrArg invTransposeSL hstd
      rwa [stdUnitary, MonoidHom.comp_apply, invTransposeSL_invTransposeSL] at this
    have h2 : Matrix.SpecialLinearGroup.map σ.toRingHom
        (Matrix.SpecialLinearGroup.map σ.toRingHom X) = X := by
      rw [hmap, slMap_invTransposeSL, ← MonoidHom.comp_apply invTransposeSL, ← stdUnitary, hstd]
    have h3 := congrArg (fun Y : SL(ν, L) => (Y : Matrix (Fin ν) (Fin ν) L) i j) h2
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ] at h3
    rw [← pow_mul, ← sq] at h3
    exact h3
  · rintro ⟨-, -, hu'⟩
    have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
        (X : Matrix (Fin ν) (Fin ν) L) = 1 := hu'
    apply Subtype.ext
    rw [coe_stdUnitary, hσmap]
    have : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹ =
        (X : Matrix (Fin ν) (Fin ν) L)ᵀ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.transpose_transpose ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)),
        ← Matrix.transpose_mul, hu, Matrix.transpose_one]
    rw [this, Matrix.transpose_transpose]

theorem commutator_transvection_rev {A B C : Fin ν} (hBA : B ≠ A) (hCB : C ≠ B) (hCA : C ≠ A)
    (u w : L) :
    ⁅Matrix.SpecialLinearGroup.transvection hBA u, Matrix.SpecialLinearGroup.transvection hCB w⁆ =
      Matrix.SpecialLinearGroup.transvection hCA (-(u * w)) := by
  rw [← commutatorElement_inv, Matrix.SpecialLinearGroup.commutatorElement_transvection hCB hBA hCA,
    transvection_inv', mul_comm]

theorem exists_units_of_cocycle (hν : 3 ≤ ν) (β : Fin ν → Fin ν → Lˣ)
    (hβ : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c)) :
    ∃ e : Fin ν → Lˣ, ∀ a b, a ≠ b → β a b = -(e a * (e b)⁻¹) := by
  classical
  have third : ∀ a b : Fin ν, ∃ c, c ≠ a ∧ c ≠ b := by
    intro a b
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin ν)) ⊆ {a, b} := fun e _ => by
      by_cases hea : e = a
      · simp [hea]
      · simp [h e hea]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_insert_le a ({b} : Finset (Fin ν))
    rw [Finset.card_singleton] at h2
    omega
  set γ : Fin ν → Fin ν → Lˣ := fun a b => -β a b with hγ
  have hγc : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → γ a c = γ a b * γ b c := by
    intro a b c hab hbc hac
    simp only [hγ, hβ a b c hab hbc hac, neg_neg, neg_mul_neg]
  have hinv : ∀ a b, a ≠ b → γ a b * γ b a = 1 := by
    intro a b hab
    obtain ⟨c, hca, hcb⟩ := third a b
    have h1 := hγc a b c hab (Ne.symm hcb) (Ne.symm hca)
    have h2 := hγc b a c (Ne.symm hab) (Ne.symm hca) (Ne.symm hcb)
    rw [h2, ← mul_assoc] at h1
    exact mul_right_cancel (h1.symm.trans (one_mul _).symm)
  set z : Fin ν := ⟨0, by omega⟩
  set e : Fin ν → Lˣ := fun a => if a = z then 1 else γ a z with he
  refine ⟨e, fun a b hab => ?_⟩
  have hγab : γ a b = e a * (e b)⁻¹ := by
    by_cases ha : a = z
    · subst ha
      have hb : b ≠ z := Ne.symm hab
      simp only [he, ite_true, hb, ite_false, one_mul]
      exact eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (hinv b z hb))
    · by_cases hb : b = z
      · subst hb
        simp only [he, ha, ite_false, ite_true, inv_one, mul_one]
      · simp only [he, ha, hb, ite_false]
        rw [hγc a z b ha (Ne.symm hb) hab]
        congr 1
        exact eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (hinv b z hb))
  rw [← hγab]
  simp [hγ]

theorem mem_center_SL_of_commute (hν : 3 ≤ ν) {G : Type*} [Group G] (ψ : SL(ν, L) →* G)
    (hψ : ψ.ker ≠ ⊤) {B : SL(ν, L)} (hB : ∀ X, ψ B * ψ X = ψ X * ψ B) :
    B ∈ Subgroup.center SL(ν, L) := by
  have hQ : CFSG.IsQuasisimple SL(ν, L) := isQuasisimple_specialLinearGroup hν
  have hker : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ ψ.ker with h | h
    · exact h
    · exact absurd h hψ
  have hcm : ∀ X, ⁅B, X⁆ ∈ Subgroup.center SL(ν, L) := by
    intro X
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hB X]
    group
  let f : SL(ν, L) →* Subgroup.center SL(ν, L) :=
    { toFun := fun X => ⟨⁅B, X⁆, hcm X⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun X Y => by
        apply Subtype.ext
        change ⁅B, X * Y⁆ = ⁅B, X⁆ * ⁅B, Y⁆
        have hY : X * ⁅B, Y⁆ = ⁅B, Y⁆ * X := Subgroup.mem_center_iff.1 (hcm Y) X
        calc ⁅B, X * Y⁆ = ⁅B, X⁆ * (X * ⁅B, Y⁆ * X⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅B, X⁆ * ⁅B, Y⁆ := by rw [hY, mul_inv_cancel_right] }
  have hf : ∀ X, f X = 1 := by
    intro X
    have hX : X ∈ commutator SL(ν, L) := by
      rw [Group.isPerfect_def.1 hQ.1]
      exact Subgroup.mem_top X
    exact Abelianization.commutator_subset_ker f hX
  rw [Subgroup.mem_center_iff]
  intro X
  have h1 := congrArg Subtype.val (hf X)
  change ⁅B, X⁆ = 1 at h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end SL

section Fixed

variable {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ}

theorem stdUnitary_fixSubgroup {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hν : 3 ≤ ν) :
    Finite (fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) ∧
      ((ν, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple (fixSubgroup (stdUnitaryEquiv (ν := ν) σ))) ∧
      ((ν, ℓ ^ f) = (3, 2) → Nat.card (fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) = 216) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set Φ := stdUnitaryEquiv (ν := ν) σ with hΦ
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hfix : ∀ X : SL(ν, L), X ∈ fixSubgroup Φ ↔
      Matrix.SpecialLinearGroup.toGL X ∈ unitarySet (ℓ ^ f) ν := by
    intro X
    rw [hΦ]
    exact mem_fixSubgroup_stdUnitaryEquiv_iff σ hσ X
  let Ψ : StatedSU ν (ℓ ^ f) F →* SL(ν, L) := statedSUToSL F ν (ℓ ^ f)
  have hΨmem : ∀ Y, Ψ Y ∈ fixSubgroup Φ := fun Y =>
    (hfix _).2 ((mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩)
  let e : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup Φ := MulEquiv.ofBijective (Ψ.codRestrict _ hΨmem)
    ⟨fun Y Z h => statedSUToSL_injective F ν (ℓ ^ f) (congrArg Subtype.val h), fun X => by
      obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) X).mpr
        ((hfix X).1 X.2)
      exact ⟨Y, Subtype.ext hY⟩⟩
  refine ⟨Finite.of_equiv _ e.toEquiv, fun hnq => ?_, fun h32 => ?_⟩
  · obtain ⟨hQ, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
      (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard hν hnq)
      (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F ℓ f hFcard ν hν hnq)
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e hQ
  · have hν3 : ν = 3 := congrArg Prod.fst h32
    have hq : ℓ ^ f = 2 := congrArg Prod.snd h32
    subst hν3
    have := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (K := F) (p := ℓ) (f := f) hFcard
    rw [← Nat.card_congr e.toEquiv, card_statedSU_three hFcard, hq]
    norm_num

end Fixed

end CFSG.HardMathSupport.Timmesfeld.CrossChar
