module

public import CFSG.CGT.Timmesfeld75.L2AutStmt

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section FieldAut

variable {F : Type} [Field F]

@[expose] def sl2FieldAut (σ : F ≃+* F) : SL(2, F) ≃* SL(2, F) where
  toFun g := Matrix.SpecialLinearGroup.map (σ : F →+* F) g
  invFun g := Matrix.SpecialLinearGroup.map (σ.symm : F →+* F) g
  left_inv g := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv g := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' g h := map_mul (Matrix.SpecialLinearGroup.map (σ : F →+* F)) g h

theorem sl2FieldAut_eq_map (σ : F ≃+* F) (g : SL(2, F)) :
    sl2FieldAut σ g = Matrix.SpecialLinearGroup.map (σ : F →+* F) g := rfl

theorem sl2FieldAut_apply_00 (σ : F ≃+* F) (g : SL(2, F)) :
    sl2FieldAut σ g 0 0 = σ (g 0 0) := rfl

theorem sl2FieldAut_apply_01 (σ : F ≃+* F) (g : SL(2, F)) :
    sl2FieldAut σ g 0 1 = σ (g 0 1) := rfl

theorem sl2FieldAut_apply_10 (σ : F ≃+* F) (g : SL(2, F)) :
    sl2FieldAut σ g 1 0 = σ (g 1 0) := rfl

theorem sl2FieldAut_apply_11 (σ : F ≃+* F) (g : SL(2, F)) :
    sl2FieldAut σ g 1 1 = σ (g 1 1) := rfl

theorem sl2FieldAut_refl : sl2FieldAut (RingEquiv.refl F) = MulEquiv.refl SL(2, F) :=
  MulEquiv.ext fun _ => Matrix.SpecialLinearGroup.ext _ _ fun _ _ => rfl

theorem sl2FieldAut_trans (σ τ : F ≃+* F) :
    sl2FieldAut (σ.trans τ) = (sl2FieldAut σ).trans (sl2FieldAut τ) :=
  MulEquiv.ext fun _ => Matrix.SpecialLinearGroup.ext _ _ fun _ _ => rfl

theorem sl2FieldAut_utriElt (σ : F ≃+* F) (s : F) :
    sl2FieldAut σ (utriElt s) = utriElt (σ s) := by
  apply sl2_ext
  · rw [sl2FieldAut_apply_00, utriElt_apply_00, utriElt_apply_00, map_one]
  · rw [sl2FieldAut_apply_01, utriElt_apply_01, utriElt_apply_01]
  · rw [sl2FieldAut_apply_10, utriElt_apply_10, utriElt_apply_10, map_zero]
  · rw [sl2FieldAut_apply_11, utriElt_apply_11, utriElt_apply_11, map_one]

theorem sl2FieldAut_ltriElt (σ : F ≃+* F) (t : F) :
    sl2FieldAut σ (ltriElt t) = ltriElt (σ t) := by
  apply sl2_ext
  · rw [sl2FieldAut_apply_00, ltriElt_apply_00, ltriElt_apply_00, map_one]
  · rw [sl2FieldAut_apply_01, ltriElt_apply_01, ltriElt_apply_01, map_zero]
  · rw [sl2FieldAut_apply_10, ltriElt_apply_10, ltriElt_apply_10]
  · rw [sl2FieldAut_apply_11, ltriElt_apply_11, ltriElt_apply_11, map_one]

theorem sl2FieldAut_torusElt (σ : F ≃+* F) (a : Fˣ) :
    sl2FieldAut σ (torusElt a) = torusElt (Units.map (σ : F →* F) a) := by
  apply sl2_ext
  · rw [sl2FieldAut_apply_00, torusElt_apply_00, torusElt_apply_00]
    rfl
  · rw [sl2FieldAut_apply_01, torusElt_apply_01, torusElt_apply_01, map_zero]
  · rw [sl2FieldAut_apply_10, torusElt_apply_10, torusElt_apply_10, map_zero]
  · rw [sl2FieldAut_apply_11, torusElt_apply_11, torusElt_apply_11]
    simp

end FieldAut

section Elementary

variable {F : Type} [Field F]

theorem ltriElt_zero : (ltriElt 0 : SL(2, F)) = 1 := by
  apply sl2_ext <;> sl2_simp

theorem torusElt_mul_ltriElt_mul_inv (a : Fˣ) (t : F) :
    torusElt a * ltriElt t * (torusElt a)⁻¹ = ltriElt (((a : F) ^ 2)⁻¹ * t) := by
  apply sl2_ext
  all_goals sl2_simp
  all_goals (try simp only [Units.val_inv_eq_inv_val])
  all_goals field_simp
  all_goals ring

theorem conj_ltriElt_apply_01 (g : SL(2, F)) (t : F) :
    (g * ltriElt t * g⁻¹) 0 1 = - g 0 1 ^ 2 * t := by
  sl2_simp
  ring

theorem mul_eq_one_of_braid [CharP F 2] {a b : F} (ha : a ≠ 0)
    (h : utriElt a * ltriElt b * utriElt a = ltriElt b * utriElt a * ltriElt b) : a * b = 1 := by
  have h01 := congrArg (fun g : SL(2, F) => g 0 1) h
  sl2_simp at h01
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h3 : a * (a * b - 1) = 0 := by linear_combination h01 - a * h2
  have h4 := (mul_eq_zero.1 h3).resolve_left ha
  exact sub_eq_zero.1 h4

theorem mem_iff_of_map_mulEquiv_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {S : Subgroup X} {T : Subgroup Y} (h : S.map e.toMonoidHom = T) (x : X) :
    e x ∈ T ↔ x ∈ S := by
  rw [← h]
  exact mem_map_mulEquiv_iff e

theorem eq_of_conjSubgroup_utriElt_ltri_eq {r r' : F}
    (h : conjSubgroup (utriElt r) (ltri F) = conjSubgroup (utriElt r') (ltri F)) : r = r' := by
  rw [conjSubgroup_eq_conjSubgroup_iff, mem_normalizer_iff_conjSubgroup_eq] at h
  have hx : (utriElt r)⁻¹ * utriElt r' = utriElt (r' - r) := by
    rw [utriElt_inv, ← utriElt_add]
    congr 1
    ring
  have hmem := conj_mem_conjSubgroup ((utriElt r)⁻¹ * utriElt r') (ltriElt_mem_ltri (1 : F))
  rw [h, hx] at hmem
  have h01 : (utriElt (r' - r) * ltriElt 1 * (utriElt (r' - r))⁻¹ : SL(2, F)) 0 1 = 0 :=
    hmem.1
  rw [conj_ltriElt_apply_01, utriElt_apply_01] at h01
  have h2 : (r' - r) ^ 2 = 0 := by linear_combination (-1) * h01
  have h3 : r' - r = 0 := (pow_eq_zero_iff two_ne_zero).1 h2
  exact (sub_eq_zero.1 h3).symm

end Elementary

section Opposite

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_eq_torusElt_conj_sl2FieldAut (φ : SL(2, F) ≃* SL(2, F))
    (hU : ∀ x, φ x ∈ utri F ↔ x ∈ utri F) (hL : ∀ x, φ x ∈ ltri F ↔ x ∈ ltri F) :
    ∃ (a : Fˣ) (σ : F ≃+* F), ∀ x, φ x = torusElt a * sl2FieldAut σ x * (torusElt a)⁻¹ := by
  obtain ⟨f, hf⟩ : ∃ f : F → F, ∀ s, φ (utriElt s) = utriElt (f s) :=
    ⟨fun s => (φ (utriElt s)) 0 1, fun s =>
      eq_utriElt_of_mem_utri ((hU _).2 (utriElt_mem_utri s))⟩
  have hfadd : ∀ s t, f (s + t) = f s + f t := fun s t => by
    apply utriElt_injective
    rw [← hf (s + t), utriElt_add, map_mul, hf s, hf t, ← utriElt_add]
  have hfinj : Function.Injective f := fun s t h =>
    utriElt_injective (φ.injective (by rw [hf s, hf t, h]))
  have hf0 : f 0 = 0 := by
    apply utriElt_injective
    rw [← hf 0, utriElt_zero, map_one]
  have hc0 : f 1 ≠ 0 := fun h => one_ne_zero (hfinj (h.trans hf0.symm))
  have hrel : ∀ (a : Fˣ) (s : F),
      f ((a : F) ^ 2 * s) = (φ (torusElt a) 0 0) ^ 2 * f s := fun a s => by
    have h1 := congrArg (fun g : SL(2, F) => g 0 1)
      (congrArg φ (torusElt_mul_utriElt_mul_inv a s))
    simp only [map_mul, map_inv, hf] at h1
    rw [conj_utriElt_apply_01, utriElt_apply_01] at h1
    exact h1.symm
  have hmulf : ∀ s t, f (s * t) * f 1 = f s * f t := by
    intro s t
    by_cases hs : s = 0
    · rw [hs, zero_mul, hf0, zero_mul, zero_mul]
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) s
      have hr0 : r ≠ 0 := fun h => hs (by rw [hr, h, zero_mul])
      have hsa : s = ((Units.mk0 r hr0 : Fˣ) : F) ^ 2 := by rw [hr, sq]; rfl
      have h1 := hrel (Units.mk0 r hr0) t
      have h2 := hrel (Units.mk0 r hr0) 1
      rw [mul_one, ← hsa] at h2
      rw [← hsa] at h1
      rw [h1, h2]
      ring
  have hinj' : Function.Injective (fun s => f s / f 1) := fun s t h =>
    hfinj ((div_left_inj' hc0).1 h)
  let σ0 : F →+* F :=
    { toFun := fun s => f s / f 1
      map_one' := div_self hc0
      map_mul' := fun s t => by
        have h := hmulf s t
        field_simp
        linear_combination h
      map_zero' := by simp [hf0]
      map_add' := fun s t => by simp [hfadd, add_div] }
  let σ : F ≃+* F := RingEquiv.ofBijective σ0 ⟨hinj', Finite.surjective_of_injective hinj'⟩
  have hσ : ∀ s, σ s = f s / f 1 := fun s => rfl
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (f 1)
  have hr0 : r ≠ 0 := fun h => hc0 (by rw [hr, h, zero_mul])
  have hrc : ((Units.mk0 r hr0 : Fˣ) : F) ^ 2 = f 1 := by rw [sq, hr]; rfl
  refine ⟨Units.mk0 r hr0, σ, ?_⟩
  have hU' : ∀ s, φ (utriElt s) =
      torusElt (Units.mk0 r hr0) * sl2FieldAut σ (utriElt s) *
        (torusElt (Units.mk0 r hr0))⁻¹ := by
    intro s
    rw [sl2FieldAut_utriElt, torusElt_mul_utriElt_mul_inv, hf, hrc, hσ]
    congr 1
    field_simp
  have hL' : ∀ t, φ (ltriElt t) =
      torusElt (Units.mk0 r hr0) * sl2FieldAut σ (ltriElt t) *
        (torusElt (Units.mk0 r hr0))⁻¹ := by
    intro t
    rw [sl2FieldAut_ltriElt, torusElt_mul_ltriElt_mul_inv, hrc]
    by_cases ht : t = 0
    · rw [ht, ltriElt_zero, map_one, map_zero, mul_zero, ltriElt_zero]
    · obtain ⟨t', ht'⟩ : ∃ t', φ (ltriElt t) = ltriElt t' :=
        ⟨_, eq_ltriElt_of_mem_ltri ((hL _).2 (ltriElt_mem_ltri t))⟩
      have hbr := braid_utriElt_ltriElt (s := t⁻¹) (t := t) (inv_mul_cancel₀ ht)
      have hbr' := congrArg φ hbr
      simp only [map_mul, hf, ht'] at hbr'
      have hfs : f t⁻¹ ≠ 0 := fun h => inv_ne_zero ht (hfinj (h.trans hf0.symm))
      have h1 := mul_eq_one_of_braid hfs hbr'
      rw [ht']
      congr 1
      have hσt : σ t ≠ 0 := fun h => ht (σ.injective (h.trans (map_zero σ).symm))
      have h2' : (σ t)⁻¹ = f t⁻¹ / f 1 := by rw [← map_inv₀, hσ]
      have h2 : f t⁻¹ = f 1 * (σ t)⁻¹ := by rw [h2']; field_simp
      have h4 : f 1 * (σ t)⁻¹ * t' = 1 := by rw [← h2]; exact h1
      calc t' = (f 1)⁻¹ * σ t * (f 1 * (σ t)⁻¹ * t') := by field_simp
        _ = (f 1)⁻¹ * σ t := by rw [h4, mul_one]
  intro x
  have hle : utri F ⊔ ltri F ≤ MonoidHom.eqLocus φ.toMonoidHom
      ((sl2FieldAut σ).trans (MulAut.conj (torusElt (Units.mk0 r hr0)))).toMonoidHom := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨s, rfl⟩ := mem_utri_iff.1 hg
      exact hU' s
    · obtain ⟨t, rfl⟩ := mem_ltri_iff.1 hg
      exact hL' t
  rw [utri_sup_ltri] at hle
  exact hle (Subgroup.mem_top x)

theorem exists_eq_torusElt_conj_sl2FieldAut_of_map_eq (φ : SL(2, F) ≃* SL(2, F))
    (hU : (utri F).map φ.toMonoidHom = utri F) (hL : (ltri F).map φ.toMonoidHom = ltri F) :
    ∃ (a : Fˣ) (σ : F ≃+* F), ∀ x, φ x = torusElt a * sl2FieldAut σ x * (torusElt a)⁻¹ :=
  exists_eq_torusElt_conj_sl2FieldAut φ (mem_iff_of_map_mulEquiv_eq φ hU)
    (mem_iff_of_map_mulEquiv_eq φ hL)

theorem exists_eq_conj_sl2FieldAut (φ : SL(2, F) ≃* SL(2, F)) :
    ∃ (g : SL(2, F)) (σ : F ≃+* F), ∀ x, φ x = g * sl2FieldAut σ x * g⁻¹ := by
  obtain ⟨h, hh⟩ := exists_conjSubgroup_utri_eq_of_sylow
    (Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective (utriSylow F))
  have hh' : conjSubgroup h (utri F) = (utri F).map φ.toMonoidHom := hh
  have hU₁ : (utri F).map (φ.trans (MulAut.conj h⁻¹)).toMonoidHom = utri F := by
    rw [map_trans_conj_eq, ← hh', conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hne : conjSubgroup 1 (utri F) ≠
      conjSubgroup ((φ.trans (MulAut.conj h⁻¹)) wElt) (utri F) := by
    intro heq
    rw [conjSubgroup_one] at heq
    have hw : (φ.trans (MulAut.conj h⁻¹)) wElt ∈ Subgroup.normalizer (utri F : Set SL(2, F)) :=
      mem_normalizer_iff_conjSubgroup_eq.2 heq.symm
    have hw' : (wElt : SL(2, F)) ∈ Subgroup.normalizer (utri F : Set SL(2, F)) := by
      rw [mem_normalizer_iff_mulEquiv (φ.trans (MulAut.conj h⁻¹)), hU₁]
      exact hw
    rw [normalizer_utri] at hw'
    exact wElt_not_mem_borel hw'
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_normal_form hne
  rw [mul_one] at hg1
  have hU₂ : (utri F).map ((φ.trans (MulAut.conj h⁻¹)).trans (MulAut.conj g)).toMonoidHom =
      utri F := by
    rw [map_trans_conj_eq, hU₁]
    exact hg1
  have hL₂ : (ltri F).map ((φ.trans (MulAut.conj h⁻¹)).trans (MulAut.conj g)).toMonoidHom =
      ltri F := by
    have hL₁ : (ltri F).map (φ.trans (MulAut.conj h⁻¹)).toMonoidHom =
        conjSubgroup ((φ.trans (MulAut.conj h⁻¹)) wElt) (utri F) := by
      rw [← conjSubgroup_wElt_utri, map_conjSubgroup_mulEquiv, hU₁]
    rw [map_trans_conj_eq, hL₁, conjSubgroup_conjSubgroup]
    exact hg2
  obtain ⟨a, σ, ha⟩ := exists_eq_torusElt_conj_sl2FieldAut
    ((φ.trans (MulAut.conj h⁻¹)).trans (MulAut.conj g)) (mem_iff_of_map_mulEquiv_eq _ hU₂)
    (mem_iff_of_map_mulEquiv_eq _ hL₂)
  refine ⟨h * g⁻¹ * torusElt a, σ, fun x => ?_⟩
  have key : g * (h⁻¹ * φ x * h⁻¹⁻¹) * g⁻¹ = torusElt a * sl2FieldAut σ x * (torusElt a)⁻¹ :=
    ha x
  calc φ x = h * g⁻¹ * (g * (h⁻¹ * φ x * h⁻¹⁻¹) * g⁻¹) * g * h⁻¹ := by group
    _ = h * g⁻¹ * (torusElt a * sl2FieldAut σ x * (torusElt a)⁻¹) * g * h⁻¹ := by rw [key]
    _ = (h * g⁻¹ * torusElt a) * sl2FieldAut σ x * (h * g⁻¹ * torusElt a)⁻¹ := by group

end Opposite

section Fixed

variable {F : Type} [Field F]

@[expose] def autFixedSubfield (σ : F ≃+* F) : Subfield F :=
  RingHom.eqLocusField (σ : F →+* F) (RingHom.id F)

theorem mem_autFixedSubfield {σ : F ≃+* F} {x : F} : x ∈ autFixedSubfield σ ↔ σ x = x :=
  Iff.rfl

theorem sl2FieldAut_eq_self_iff (σ : F ≃+* F) (x : SL(2, F)) :
    sl2FieldAut σ x = x ↔ ∀ i j, x i j ∈ autFixedSubfield σ := by
  constructor
  · intro h i j
    exact congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) i j) h
  · intro h
    ext i j
    exact h i j

theorem natCard_fixed_utri (σ : F ≃+* F) :
    Nat.card {u : utri F // sl2FieldAut σ u = u} = Nat.card (autFixedSubfield σ) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨(u.1 : SL(2, F)) 0 1, ?_⟩
      invFun := fun s => ⟨⟨utriElt (s : F), utriElt_mem_utri (s : F)⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact congrArg (fun g : SL(2, F) => g 0 1) u.2
  · show sl2FieldAut σ (utriElt (s : F)) = utriElt (s : F)
    rw [sl2FieldAut_utriElt, (mem_autFixedSubfield.1 s.2)]
  · rintro ⟨⟨g, hg⟩, hfix⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (eq_utriElt_of_mem_utri hg).symm
  · rintro ⟨s, hs⟩
    apply Subtype.ext
    exact utriElt_apply_01 s

@[expose] def autAddMap (σ : F ≃+* F) : F →+ F where
  toFun s := s + σ s
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; abel

theorem autAddMap_apply (σ : F ≃+* F) (s : F) : autAddMap σ s = s + σ s := rfl

theorem ker_autAddMap [CharP F 2] (σ : F ≃+* F) :
    (autAddMap σ).ker = (autFixedSubfield σ).toAddSubgroup := by
  ext s
  rw [AddMonoidHom.mem_ker, autAddMap_apply, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
  exact eq_comm

theorem natCard_eq_sq_of_orderOf_eq_two [Finite F] {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    Nat.card F = Nat.card (autFixedSubfield σ) ^ 2 := by
  have : Finite (RingAut F) :=
    Finite.of_injective (fun τ : RingAut F => (τ : F → F)) DFunLike.coe_injective
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  have hG : FixedPoints.subfield (Subgroup.zpowers σ) F = autFixedSubfield σ := by
    ext x
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      have hst : σ ∈ MulAction.stabilizer (RingAut F) x := hx
      exact Subgroup.zpowers_le.2 hst g.2
  have h1 := FixedPoints.finrank_eq_card (Subgroup.zpowers σ) F
  rw [hG, Fintype.card_eq_nat_card, Nat.card_zpowers, hσ] at h1
  rw [Module.natCard_eq_pow_finrank (K := autFixedSubfield σ) (V := F), h1]

theorem natCard_range_autAddMap [Finite F] [CharP F 2] {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    Nat.card (autAddMap σ).range = Nat.card (autFixedSubfield σ) := by
  have h1 := AddSubgroup.card_mul_index (autAddMap σ).ker
  rw [AddSubgroup.index_ker, ker_autAddMap, natCard_eq_sq_of_orderOf_eq_two hσ] at h1
  have h2 : Nat.card (autFixedSubfield σ).toAddSubgroup = Nat.card (autFixedSubfield σ) := rfl
  rw [h2, sq] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

@[expose] def utriCommutator (σ : F ≃+* F) : Subgroup SL(2, F) where
  carrier := {x | ∃ s : F, x = utriElt (s - σ s)}
  one_mem' := ⟨0, by rw [map_zero, sub_zero, utriElt_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    rw [← utriElt_add, map_add]
    congr 1
    ring
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    refine ⟨-s, ?_⟩
    rw [utriElt_inv, map_neg]
    congr 1
    ring

theorem mem_utriCommutator_iff {σ : F ≃+* F} {x : SL(2, F)} :
    x ∈ utriCommutator σ ↔ ∃ u ∈ utri F, x = u * (sl2FieldAut σ u)⁻¹ := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨utriElt s, utriElt_mem_utri s, ?_⟩
    rw [sl2FieldAut_utriElt, utriElt_inv, ← utriElt_add, sub_eq_add_neg]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨s, rfl⟩ := mem_utri_iff.1 hu
    refine ⟨s, ?_⟩
    rw [sl2FieldAut_utriElt, utriElt_inv, ← utriElt_add, sub_eq_add_neg]

theorem utriElt_mem_utriCommutator_of_mem_range [CharP F 2] {σ : F ≃+* F} {y : F}
    (hy : y ∈ (autAddMap σ).range) : utriElt y ∈ utriCommutator σ := by
  obtain ⟨s, rfl⟩ := hy
  exact ⟨s, by rw [autAddMap_apply, CharTwo.sub_eq_add]⟩

theorem natCard_utriCommutator [Finite F] [CharP F 2] {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    Nat.card (utriCommutator σ) = Nat.card (autFixedSubfield σ) := by
  rw [← natCard_range_autAddMap hσ]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun y : (autAddMap σ).range => (⟨utriElt (y : F), ?_⟩ : utriCommutator σ)) ⟨?_, ?_⟩)
  · exact utriElt_mem_utriCommutator_of_mem_range y.2
  · intro y z h
    exact Subtype.ext (utriElt_injective (congrArg Subtype.val h))
  · rintro ⟨x, s, rfl⟩
    refine ⟨⟨s + σ s, s, rfl⟩, ?_⟩
    apply Subtype.ext
    simp only [CharTwo.sub_eq_add]

end Fixed

section Rigidity

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sl2_eq_refl_of_map_conjSubgroup_eq (φ : SL(2, F) ≃* SL(2, F))
    (h : ∀ k, (conjSubgroup k (utri F)).map φ.toMonoidHom = conjSubgroup k (utri F)) :
    φ = MulEquiv.refl SL(2, F) := by
  have hU' : (utri F).map φ.toMonoidHom = utri F := by
    simpa only [conjSubgroup_one] using h 1
  have hL' : (ltri F).map φ.toMonoidHom = ltri F := by
    rw [← conjSubgroup_wElt_utri]
    exact h wElt
  obtain ⟨a, σ, ha⟩ := exists_eq_torusElt_conj_sl2FieldAut φ
    (mem_iff_of_map_mulEquiv_eq φ hU') (mem_iff_of_map_mulEquiv_eq φ hL')
  have key : ∀ r : F, (a : F) ^ 2 * σ r = r := by
    intro r
    have hφr : φ (utriElt r) = utriElt ((a : F) ^ 2 * σ r) := by
      rw [ha, sl2FieldAut_utriElt, torusElt_mul_utriElt_mul_inv]
    have h1 : (conjSubgroup (utriElt r) (ltri F)).map φ.toMonoidHom =
        conjSubgroup (utriElt r) (ltri F) := by
      rw [← conjSubgroup_wElt_utri, conjSubgroup_conjSubgroup]
      exact h _
    have h2 : conjSubgroup (φ (utriElt r)) (ltri F) = conjSubgroup (utriElt r) (ltri F) := by
      rwa [map_conjSubgroup_mulEquiv, hL'] at h1
    rw [hφr] at h2
    exact eq_of_conjSubgroup_utriElt_ltri_eq h2
  have h1 : (a : F) ^ 2 = 1 := by simpa using key 1
  have ha1 : a = 1 := Units.ext (CharTwo.sq_injective (by simpa using h1))
  have hσ : σ = RingEquiv.refl F := RingEquiv.ext fun r => by
    have := key r
    rw [ha1] at this
    simpa using this
  ext x
  rw [ha x, ha1, hσ, torusElt_one, sl2FieldAut_refl]
  simp

theorem sl2_eq_refl_of_map_sylow_eq (φ : SL(2, F) ≃* SL(2, F))
    (h : ∀ P : Sylow 2 SL(2, F), (P : Subgroup SL(2, F)).map φ.toMonoidHom = P) :
    φ = MulEquiv.refl SL(2, F) :=
  sl2_eq_refl_of_map_conjSubgroup_eq φ fun k =>
    h (Sylow.mapSurjective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).surjective
      (utriSylow F))

end Rigidity

theorem IsL2Pair.eq_refl_of_map_conjSubgroup_eq {X : Type} [Group X] {S : Subgroup X} {q : ℕ}
    (hX : IsL2Pair X S q) (φ : X ≃* X)
    (h : ∀ g, (conjSubgroup g S).map φ.toMonoidHom = conjSubgroup g S) :
    φ = MulEquiv.refl X := by
  obtain ⟨F, i1, i2, i3, e, hq, hS⟩ := hX
  have key := sl2_eq_refl_of_map_conjSubgroup_eq (F := F) (e.symm.trans (φ.trans e))
    (fun k => by
      have hk : conjSubgroup k (utri F) = (conjSubgroup (e.symm k) S).map e.toMonoidHom := by
        rw [map_conjSubgroup_mulEquiv, e.apply_symm_apply, hS]
      have hcomp : (e.symm.trans (φ.trans e)).toMonoidHom.comp e.toMonoidHom =
          e.toMonoidHom.comp φ.toMonoidHom := MonoidHom.ext fun x => by simp
      rw [hk, Subgroup.map_map, hcomp, ← Subgroup.map_map, h (e.symm k)])
  ext x
  have := congrArg (fun ψ : SL(2, F) ≃* SL(2, F) => e.symm (ψ (e x))) key
  simpa using this

section Dichotomy

variable {F : Type} [Field F]

theorem inv_torusElt (a : Fˣ) : (torusElt a : SL(2, F))⁻¹ = torusElt a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← torusElt_mul, mul_inv_cancel, torusElt_one]

theorem conjSubgroup_torusElt_utri (a : Fˣ) :
    conjSubgroup (torusElt a) (utri F) = utri F :=
  mem_normalizer_iff_conjSubgroup_eq.1 (by rw [normalizer_utri]; exact torusElt_mem_borel a)

theorem conj_torusElt_mem_ltri {a : Fˣ} {y : SL(2, F)} (hy : y ∈ ltri F) :
    torusElt a * y * (torusElt a)⁻¹ ∈ ltri F := by
  obtain ⟨t, rfl⟩ := mem_ltri_iff.1 hy
  rw [torusElt_mul_ltriElt_mul_inv]
  exact ltriElt_mem_ltri _

theorem conjSubgroup_torusElt_ltri (a : Fˣ) :
    conjSubgroup (torusElt a) (ltri F) = ltri F := by
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro hx
    have h := conj_torusElt_mem_ltri (a := a) hx
    have e : torusElt a * ((torusElt a)⁻¹ * x * torusElt a) * (torusElt a)⁻¹ = x := by group
    rwa [e] at h
  · intro hx
    have h := conj_torusElt_mem_ltri (a := a⁻¹) hx
    rwa [inv_torusElt, inv_inv, ← inv_torusElt] at h

end Dichotomy

theorem autInvolDichotomy : AutInvolDichotomy := by
  intro Q _ S S' q hQ hg hne φ hφφ hSφ hS'φ
  obtain ⟨g, hg⟩ := hg
  obtain ⟨F, i1, i2, i3, e0, hq, hS0⟩ := hQ
  have hne' : conjSubgroup 1 (utri F) ≠ conjSubgroup (e0 g) (utri F) := by
    intro h
    apply hne
    have hinj : Function.Injective e0.toMonoidHom := e0.injective
    apply Subgroup.map_injective hinj
    rw [hg, map_conjSubgroup_mulEquiv, hS0]
    rw [conjSubgroup_one] at h
    exact h.symm
  obtain ⟨k, hk1, hk2⟩ := exists_conj_pair_normal_form hne'
  rw [mul_one] at hk1
  obtain ⟨e, hSe, hS'e⟩ : ∃ e : Q ≃* SL(2, F),
      S.map e.toMonoidHom = utri F ∧ S'.map e.toMonoidHom = ltri F :=
    ⟨e0.trans (MulAut.conj k), by rw [map_trans_conj_eq, hS0]; exact hk1,
      by rw [map_trans_conj_eq, hg, map_conjSubgroup_mulEquiv, hS0, conjSubgroup_conjSubgroup]
         exact hk2⟩
  have hψU : ∀ y, e (φ (e.symm y)) ∈ utri F ↔ y ∈ utri F := fun y => by
    rw [mem_iff_of_map_mulEquiv_eq e hSe, mem_iff_of_map_mulEquiv_eq φ hSφ,
      ← mem_iff_of_map_mulEquiv_eq e hSe, e.apply_symm_apply]
  have hψL : ∀ y, e (φ (e.symm y)) ∈ ltri F ↔ y ∈ ltri F := fun y => by
    rw [mem_iff_of_map_mulEquiv_eq e hS'e, mem_iff_of_map_mulEquiv_eq φ hS'φ,
      ← mem_iff_of_map_mulEquiv_eq e hS'e, e.apply_symm_apply]
  obtain ⟨c, σ, hc⟩ := exists_eq_torusElt_conj_sl2FieldAut (e.symm.trans (φ.trans e)) hψU hψL
  have hφe : ∀ x, e (φ x) = torusElt c * sl2FieldAut σ (e x) * (torusElt c)⁻¹ := fun x => by
    have h := hc (e x)
    rwa [MulEquiv.trans_apply, MulEquiv.trans_apply, e.symm_apply_apply] at h
  have hψu : ∀ s : F, e (φ (e.symm (utriElt s))) = utriElt ((c : F) ^ 2 * σ s) := fun s => by
    have h3 := hφe (e.symm (utriElt s))
    rwa [e.apply_symm_apply, sl2FieldAut_utriElt, torusElt_mul_utriElt_mul_inv] at h3
  have hψψ : ∀ s : F, utriElt ((c : F) ^ 2 * σ ((c : F) ^ 2 * σ s)) = utriElt s := fun s => by
    have h2 : e (φ (e.symm (e (φ (e.symm (utriElt s)))))) = utriElt s := by
      rw [e.symm_apply_apply, hφφ, e.apply_symm_apply]
    rw [← hψu ((c : F) ^ 2 * σ s), ← hψu s]
    exact h2
  have hnorm2 : ((c : F) * σ c) ^ 2 = 1 := by
    have h := utriElt_injective (hψψ 1)
    simpa [mul_pow] using h
  have hn : (c : F) * σ c = 1 := CharTwo.sq_injective (by simpa using hnorm2)
  by_cases hσ : σ = RingEquiv.refl F
  · left
    have hc2 : (c : F) ^ 2 = 1 := by
      rw [sq]
      simpa [hσ] using hn
    have hc1 : c = 1 := Units.ext (CharTwo.sq_injective (by simpa using hc2))
    intro x
    apply e.injective
    rw [hφe x, hc1, hσ, torusElt_one, sl2FieldAut_refl]
    simp
  · right
    have hσc : σ (c : F) = (c : F)⁻¹ := eq_inv_of_mul_eq_one_right hn
    obtain ⟨d, hd⟩ : ∃ d : Fˣ, σ (d : F) = (c : F) * d := by
      by_cases hc1 : (c : F) = 1
      · exact ⟨1, by rw [hc1]; simp⟩
      · have hd0 : (1 : F) + (c : F)⁻¹ ≠ 0 := by
          intro h
          apply hc1
          have h1 : (c : F)⁻¹ = -1 := eq_neg_of_add_eq_zero_right h
          rw [CharTwo.neg_eq] at h1
          exact inv_eq_one.1 h1
        refine ⟨Units.mk0 _ hd0, ?_⟩
        have hc0 : (c : F) ≠ 0 := c.ne_zero
        simp only [Units.val_mk0, map_add, map_one, map_inv₀, hσc, inv_inv]
        field_simp
        ring
    have htd : torusElt d * torusElt c = torusElt (Units.map (σ : F →* F) d) := by
      rw [← torusElt_mul]
      congr 1
      apply Units.ext
      simp [hd, mul_comm]
    refine ⟨F, i1, i2, i3, e.trans (MulAut.conj (torusElt d)), σ, hσ, ?_, ?_, ?_⟩
    · rw [map_trans_conj_eq, hSe, conjSubgroup_torusElt_utri]
    · rw [map_trans_conj_eq, hS'e, conjSubgroup_torusElt_ltri]
    · intro x
      show torusElt d * e (φ x) * (torusElt d)⁻¹ =
        sl2FieldAut σ (torusElt d * e x * (torusElt d)⁻¹)
      rw [hφe x, map_mul, map_mul, map_inv, sl2FieldAut_torusElt, ← htd]
      group

end CFSG.CGT.Timmesfeld75
