module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModDefs
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix Subgroup CFSG.SL2MinimalFaithful

abbrev SL2 (F : Type) [Field F] := SpecialLinearGroup (Fin 2) F

section Grp

variable {F : Type} [Field F]

theorem unipotent_eq_upperSL (t : F) : (unipotent t : SL2 F) = upperSL t := rfl

@[expose] def lowerHom : Multiplicative F →* SL2 F where
  toFun t := lowerSL t.toAdd
  map_one' := lowerSL_zero
  map_mul' s t := (lowerSL_add s.toAdd t.toAdd).symm

@[expose] def Qup (F : Type) [Field F] : Subgroup (SL2 F) := (unipotentHom (F := F)).range

@[expose] def Qlow (F : Type) [Field F] : Subgroup (SL2 F) := (lowerHom (F := F)).range

theorem mem_Qup {g : SL2 F} : g ∈ Qup F ↔ ∃ t : F, g = upperSL t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem mem_Qlow {g : SL2 F} : g ∈ Qlow F ↔ ∃ t : F, g = lowerSL t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem upperSL_mem_Qup (t : F) : upperSL t ∈ Qup F := mem_Qup.2 ⟨t, rfl⟩

theorem lowerSL_mem_Qlow (t : F) : lowerSL t ∈ Qlow F := mem_Qlow.2 ⟨t, rfl⟩

theorem upperSL_injective : Function.Injective (upperSL : F → SL2 F) :=
  unipotent_injective

theorem lowerSL_injective : Function.Injective (lowerSL : F → SL2 F) := by
  intro s t h
  simpa [coe_lowerSL] using
    congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h

theorem card_Qup : Nat.card (Qup F) = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective (unipotentHom_injective (F := F))).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem card_Qlow : Nat.card (Qlow F) = Nat.card F := by
  have hinj : Function.Injective (lowerHom (F := F)) := fun s t h => lowerSL_injective (F := F) h
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem Qup_inf_Qlow : Qup F ⊓ Qlow F = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hu, hl⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨s, rfl⟩ := mem_Qup.1 hu
  obtain ⟨t, ht⟩ := mem_Qlow.1 hl
  rw [Subgroup.mem_bot]
  have h1 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) ht
  simp [coe_upperSL, coe_lowerSL] at h1
  rw [h1, upperSL_zero]

theorem Qup_sup_Qlow : Qup F ⊔ Qlow F = ⊤ := by
  have hU : ∀ t, upperSL t ∈ Qup F ⊔ Qlow F := fun t => Subgroup.mem_sup_left (upperSL_mem_Qup t)
  have hL : ∀ t, lowerSL t ∈ Qup F ⊔ Qlow F := fun t => Subgroup.mem_sup_right (lowerSL_mem_Qlow t)
  have hne : ∀ M : SL2 F, (M : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → M ∈ Qup F ⊔ Qlow F := by
    intro M hc
    have hdet := M.2
    rw [det_fin_two] at hdet
    have hM : M = upperSL (((M : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) /
        (M : Matrix (Fin 2) (Fin 2) F) 1 0) * lowerSL ((M : Matrix (Fin 2) (Fin 2) F) 1 0) *
        upperSL (((M : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (M : Matrix (Fin 2) (Fin 2) F) 1 0) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coe_upperSL, coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> first | ring1 | linear_combination hdet | linear_combination -hdet
    rw [hM]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  refine eq_top_iff.2 fun M _ => ?_
  by_cases hc : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := M.2
    rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
    have ha : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have h1 : lowerSL 1 * M ∈ Qup F ⊔ Qlow F := hne _ (by
      simpa [coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha)
    have h2 : M = (lowerSL 1)⁻¹ * (lowerSL 1 * M) := by group
    rw [h2]
    exact mul_mem (inv_mem (hL 1)) h1
  · exact hne M hc

@[expose] def Bor (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] at ha hb ⊢
    rw [ha, hb]
    ring
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
    simp [ha]

theorem mem_Bor {g : SL2 F} : g ∈ Bor F ↔ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

theorem entry_conj_upperSL (g : SL2 F) (t : F) :
    ((g * upperSL t * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      -((g : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 * t := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  simp [coe_upperSL, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem conj_upperSL_of_mem_Bor {g : SL2 F} (hg : g ∈ Bor F) (t : F) :
    g * upperSL t * g⁻¹ = upperSL (((g : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * t) := by
  have hdet := g.2
  rw [det_fin_two, mem_Bor.1 hg, mul_zero, sub_zero] at hdet
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_upperSL, Matrix.mul_apply, Fin.sum_univ_two, mem_Bor.1 hg] <;>
    first | ring1 | linear_combination (t * ((g : Matrix (Fin 2) (Fin 2) F) 0 0)) * hdet |
      linear_combination hdet

theorem Bor_le_normalizer : Bor F ≤ normalizer (Qup F : Set (SL2 F)) := by
  have key : ∀ g ∈ Bor F, ∀ h ∈ Qup F, g * h * g⁻¹ ∈ Qup F := by
    intro g hg h hh
    obtain ⟨t, rfl⟩ := mem_Qup.1 hh
    rw [conj_upperSL_of_mem_Bor hg]
    exact upperSL_mem_Qup _
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem mem_Bor_of_conj_mem {g : SL2 F} {t : F} (ht : t ≠ 0)
    (h : g * upperSL t * g⁻¹ ∈ Qup F) : g ∈ Bor F := by
  obtain ⟨s, hs⟩ := mem_Qup.1 h
  have := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 1 0) hs
  simp only [entry_conj_upperSL, coe_upperSL] at this
  simp at this
  rcases this with h1 | h1
  · exact mem_Bor.2 h1
  · exact absurd h1 ht

theorem normalizer_Qup_le_Bor : normalizer (Qup F : Set (SL2 F)) ≤ Bor F := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  exact mem_Bor_of_conj_mem one_ne_zero ((hg _).1 (upperSL_mem_Qup 1))

theorem normalizer_Qup : normalizer (Qup F : Set (SL2 F)) = Bor F :=
  le_antisymm normalizer_Qup_le_Bor Bor_le_normalizer

theorem eq_one_of_conj_mem {g : SL2 F} (hg : g ∉ Bor F) {h : SL2 F} (hh : h ∈ Qup F)
    (hgh : g * h * g⁻¹ ∈ Qup F) : h = 1 := by
  obtain ⟨t, rfl⟩ := mem_Qup.1 hh
  by_cases ht : t = 0
  · rw [ht, upperSL_zero]
  · exact absurd (mem_Bor_of_conj_mem ht hgh) hg

theorem card_Bor [Finite F] : Nat.card (Bor F) = (Nat.card F - 1) * Nat.card F := by
  have hdet : ∀ g : Bor F, ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 *
      ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    intro g
    have h := g.1.2
    rw [det_fin_two, mem_Bor.1 g.2, mul_zero, sub_zero] at h
    exact h
  let e : Bor F ≃ Fˣ × F :=
    { toFun := fun g => (Units.mk0 _ (left_ne_zero_of_mul_eq_one (hdet g)),
        ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1)
      invFun := fun x => ⟨⟨!![(x.1 : F), x.2; 0, ((x.1⁻¹ : Fˣ) : F)], by
        simp [det_fin_two]⟩, by
        show (!![(x.1 : F), x.2; 0, ((x.1⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        simp⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Subtype.ext
        have h1 : ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
            (((Units.mk0 _ (left_ne_zero_of_mul_eq_one (hdet g)))⁻¹ : Fˣ) : F) := by
          rw [Units.val_inv_eq_inv_val, Units.val_mk0]
          exact eq_inv_of_mul_eq_one_right (hdet g)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h1, mem_Bor.1 g.2]
      right_inv := fun x => by
        ext <;> simp }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_units]

end Grp

section Syl

variable {F : Type} [Field F] [Finite F] {p n : ℕ}

theorem isPGroup_and_index_of_card_eq (hp : p.Prime) (hF : Nat.card F = p ^ n)
    {U : Subgroup (SL2 F)} (hU : Nat.card U = Nat.card F) : IsPGroup p U ∧ ¬ p ∣ U.index := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hF
    omega
  have hpq : p ∣ Nat.card F := hF ▸ dvd_pow_self p hn
  refine ⟨IsPGroup.of_card (hU.trans hF), fun hdvd => ?_⟩
  have hind : U.index = Nat.card F ^ 2 - 1 := by
    have := U.card_mul_index
    rw [hU, card_specialLinearGroup_fin_two] at this
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : p ∣ Nat.card F ^ 2 - 1 + 1 := by
    rw [Nat.sub_add_cancel h1]
    exact dvd_pow hpq two_ne_zero
  rw [hind] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp h2))

theorem exists_conj_of_card_eq (hp : p.Prime) (hF : Nat.card F = p ^ n)
    {U : Subgroup (SL2 F)} (hU : Nat.card U = Nat.card F) :
    ∃ g : SL2 F, ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ Qup F := by
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem hp hF hU
  let C : Subgroup (SL2 F) := (Qup F).map (MulAut.conj g).toMonoidHom
  have hCU : C ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := mem_Qup.1 hy
    exact hg t
  have hC : Nat.card C = Nat.card U := by
    show Nat.card ((Qup F).map (MulAut.conj g).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_Qup, hU]
  have hCeq : C = U := Subgroup.eq_of_le_of_card_ge hCU (le_of_eq hC.symm)
  refine ⟨g, fun x => ?_⟩
  rw [← hCeq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g⁻¹ * (g * y * g⁻¹) * g ∈ Qup F
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this]
    exact hy
  · intro hx
    refine ⟨_, hx, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem card_subgroups_card_eq_le (hp : p.Prime) (hF : Nat.card F = p ^ n) :
    Nat.card {U : Subgroup (SL2 F) // Nat.card U = Nat.card F} ≤ Nat.card F + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsyl := fun (U : Subgroup (SL2 F)) (hU : Nat.card U = Nat.card F) =>
    isPGroup_and_index_of_card_eq hp hF hU
  let ι : {U : Subgroup (SL2 F) // Nat.card U = Nat.card F} → Sylow p (SL2 F) :=
    fun U => (hsyl U.1 U.2).1.toSylow (hsyl U.1 U.2).2
  have hι : Function.Injective ι := by
    intro U V h
    apply Subtype.ext
    have := congrArg (fun P : Sylow p (SL2 F) => (P : Subgroup (SL2 F))) h
    simpa [ι] using this
  have hQ : Nat.card (Qup F) = Nat.card F := card_Qup
  let P₀ : Sylow p (SL2 F) := (hsyl _ hQ).1.toSylow (hsyl _ hQ).2
  have hP₀ : (P₀ : Subgroup (SL2 F)) = Qup F := rfl
  have h1 : Nat.card {U : Subgroup (SL2 F) // Nat.card U = Nat.card F} ≤
      Nat.card (Sylow p (SL2 F)) := Nat.card_le_card_of_injective ι hι
  have h2 : Nat.card (Sylow p (SL2 F)) = (normalizer ((P₀ : Subgroup (SL2 F)) : Set (SL2 F))).index :=
    Sylow.card_eq_index_normalizer P₀
  rw [hP₀, normalizer_Qup] at h2
  have h3 := (Bor F).index_mul_card
  rw [card_Bor, card_specialLinearGroup_fin_two] at h3
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h4 : (Bor F).index = Nat.card F + 1 := by
    have h5 : (Nat.card F + 1) * ((Nat.card F - 1) * Nat.card F) =
        Nat.card F * (Nat.card F ^ 2 - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      have : (m + 1) ^ 2 - 1 = m * (m + 2) := by
        have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
        omega
      rw [this]
      ring
    have : 0 < (Nat.card F - 1) * Nat.card F := Nat.mul_pos (by omega) (by omega)
    exact Nat.eq_of_mul_eq_mul_right this (h3.trans h5.symm)
  omega

theorem sq_eq_one_aux {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (a b c d : F)
    (h00 : a * a + b * c = 1) (h01 : a * b + b * d = 0) (h10 : c * a + d * c = 0)
    (hdet : a * d - b * c = 1) : b = 0 ∧ c = 0 ∧ d = a ∧ (a = 1 ∨ a = -1) := by
  by_cases had : a + d = 0
  · exfalso
    apply h2
    have hd : d = -a := by linear_combination had
    rw [hd] at hdet
    linear_combination (-1 : F) * h00 + (-1 : F) * hdet
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right had
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right had
    subst hb hc
    have ha : a * a = 1 := by linear_combination h00
    have hda : a * d = 1 := by linear_combination hdet
    have hd : d = a := by
      have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one ha
      apply mul_left_cancel₀ ha0
      rw [hda, ha]
    exact ⟨rfl, rfl, hd, mul_self_eq_one_iff.1 ha⟩

theorem eq_one_or_neg_one_of_sq_eq_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {g : SL2 F}
    (hg : g ^ 2 = 1) : g = 1 ∨ g = -1 := by
  have hm := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) hg
  simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  have hdet := g.2
  rw [det_fin_two] at hdet
  obtain ⟨hb, hc, hd, h1⟩ := sq_eq_one_aux h2 _ _ _ _ h00 h01 h10 hdet
  rcases h1 with h1 | h1
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hd, hb, hc]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hd, hb, hc]

end Syl

end CFSG.GH74.GLS.IVK.Proofs2
