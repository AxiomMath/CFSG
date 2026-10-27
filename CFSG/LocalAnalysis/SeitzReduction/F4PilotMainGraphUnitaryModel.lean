module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusEmbed
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer
public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite map_subtype_map_bar map_subtype_injective descendMatrix
    descendMatrix_map)

section Gram

variable (K : Type) [Field K]

theorem isPrimeFormGram_graphGram6 : IsPrimeFormGram (graphGram6 K) where
  symm := transpose_blockSwapJ_six K
  prime i j := by
    simp only [coe_graphGram6, blockSwapJ, of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem isPrimeFormGram_graphGram7 : IsPrimeFormGram (graphGram7 K) where
  symm := transpose_gram7 K
  prime i j := by
    simp only [coe_graphGram7, gram7, of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end Gram

section Groups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

abbrev uGroup6 : Subgroup (GL (Fin 6) K) :=
  gramSU h ((graphGram6 K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)

abbrev uGroup7 : Subgroup (GL (Fin 7) K) :=
  gramSU h ((graphGram7 K : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)

variable {n : ℕ}

@[expose] def gramSUToSL (C : Matrix (Fin n) (Fin n) K) :
    gramSU h C →* SpecialLinearGroup (Fin n) K where
  toFun g := ⟨((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), g.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_gramSUToSL (C : Matrix (Fin n) (Fin n) K) (g : gramSU h C) :
    ((gramSUToSL h C g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem gramSUToSL_injective (C : Matrix (Fin n) (Fin n) K) :
    Function.Injective (gramSUToSL h C) := fun _ _ hgg' =>
  Subtype.ext (Units.ext (congrArg
    (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hgg'))

theorem center_gramSU_le_normOneScalars {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    center (gramSU h (C : Matrix (Fin n) (Fin n) K)) ≤
      normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n := by
  intro z hz
  have hc : (z : primeFormP h (C : Matrix (Fin n) (Fin n) K)) ∈
      center (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
    rw [mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hz y]
  rw [CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot h hC hn hq, mem_bot,
    QuotientGroup.eq_one_iff] at hc
  exact hc

theorem center_gramSU_eq_normOneScalars {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    center (gramSU h (C : Matrix (Fin n) (Fin n) K)) =
      normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n :=
  le_antisymm (center_gramSU_le_normOneScalars h hC hn hq) (normOneScalars_le_center h _ n)

theorem gramSUToSL_mem_center {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) {z : gramSU h (C : Matrix (Fin n) (Fin n) K)}
    (hz : z ∈ center (gramSU h (C : Matrix (Fin n) (Fin n) K))) :
    gramSUToSL h _ z ∈ center (SpecialLinearGroup (Fin n) K) := by
  obtain ⟨c, -, -, hcz⟩ := center_gramSU_le_normOneScalars h hC hn hq hz
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : Matrix (Fin n) (Fin n) K) * ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)
  rw [hcz, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : K) (fun _ => Commute.all _ _) _).eq.symm

end Groups

section Fixed

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem toGL_map_mem_gramSU {C : Matrix (Fin n) (Fin n) h.fixedField}
    {g : SpecialLinearGroup (Fin n) h.fixedField}
    (hg : (g : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * C * g = C) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map h.fixedField.subtype g) ∈
      gramSU h (C.map h.fixedField.subtype) := by
  refine ⟨?_, ?_⟩
  · change (((g : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype).map h.bar)ᵀ *
        C.map h.fixedField.subtype * (g : Matrix (Fin n) (Fin n) h.fixedField).map
          h.fixedField.subtype = C.map h.fixedField.subtype
    rw [map_subtype_map_bar, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  · exact (SpecialLinearGroup.map h.fixedField.subtype g).2

theorem exists_eq_map_of_map_bar_eq {C : Matrix (Fin n) (Fin n) h.fixedField}
    {x : GL (Fin n) K} (hx : x ∈ gramSU h (C.map h.fixedField.subtype))
    (hbar : (x : Matrix (Fin n) (Fin n) K).map h.bar = x) :
    ∃ g : SpecialLinearGroup (Fin n) h.fixedField,
      (g : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * C * g = C ∧
        SpecialLinearGroup.toGL (SpecialLinearGroup.map h.fixedField.subtype g) = x := by
  set M := descendMatrix h (x : Matrix (Fin n) (Fin n) K) hbar
  have hM : M.map h.fixedField.subtype = x := descendMatrix_map h _ hbar
  have hdet : M.det = 1 := by
    apply Subtype.val_injective
    change h.fixedField.subtype M.det = h.fixedField.subtype 1
    rw [RingHom.map_det, map_one]
    change (M.map h.fixedField.subtype).det = 1
    rw [hM]
    exact hx.2
  refine ⟨⟨M, hdet⟩, ?_, Units.ext ?_⟩
  · apply map_subtype_injective h
    change (Mᵀ * C * M).map h.fixedField.subtype = C.map h.fixedField.subtype
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, hM]
    have h1 := hx.1
    rwa [hbar] at h1
  · exact hM

end Fixed

section ToriMap

variable {F F' : Type} [Field F] [Field F'] (φ : F →+* F')

theorem lin6Weights_map (t : Fin 3 → Fˣ) :
    lin6Weights F' (fun i => Units.map (φ : F →* F') (t i)) =
      fun i => Units.map (φ : F →* F') (lin6Weights F t i) := by
  funext i
  fin_cases i <;> simp [lin6Weights]

theorem lin7Weights_map (t : Fin 3 → Fˣ) :
    lin7Weights F' (fun i => Units.map (φ : F →* F') (t i)) =
      fun i => Units.map (φ : F →* F') (lin7Weights F t i) := by
  funext i
  fin_cases i <;> simp [lin7Weights]

theorem map_lin6Torus (t : Fin 3 → Fˣ) :
    SpecialLinearGroup.map φ (lin6Torus F t) =
      lin6Torus F' (fun i => Units.map (φ : F →* F') (t i)) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, lin6Torus, lin6Torus, coe_diagTorusSL, coe_diagTorusSL,
    lin6Weights_map, RingHom.mapMatrix_apply, diagonal_map (map_zero φ)]
  rfl

theorem map_lin7Torus (t : Fin 3 → Fˣ) :
    SpecialLinearGroup.map φ (lin7Torus F t) =
      lin7Torus F' (fun i => Units.map (φ : F →* F') (t i)) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, lin7Torus, lin7Torus, coe_diagTorusSL, coe_diagTorusSL,
    lin7Weights_map, RingHom.mapMatrix_apply, diagonal_map (map_zero φ)]
  rfl

end ToriMap

section Embed

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem map_blockSwapJ_six :
    (blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) h.fixedField).map h.fixedField.subtype =
      blockSwapJ 6 3 := by
  ext i j
  simp only [Matrix.map_apply, blockSwapJ, of_apply]
  split_ifs <;> simp

theorem map_gram7_fixedField :
    (gram7 h.fixedField).map h.fixedField.subtype = gram7 K := by
  ext i j
  simp only [Matrix.map_apply, gram7, of_apply]
  split_ifs <;> simp

@[expose] noncomputable def uEmbedGL6 : StatedSp 3 h.fixedField →* GL (Fin 6) K :=
  SpecialLinearGroup.toGL.comp ((SpecialLinearGroup.map h.fixedField.subtype).comp sp6ToSL6)

@[expose] noncomputable def uEmbedGL7 : StatedSp 3 h.fixedField →* GL (Fin 7) K :=
  SpecialLinearGroup.toGL.comp ((SpecialLinearGroup.map h.fixedField.subtype).comp sp6ToSL7)

theorem uEmbedGL6_mem (A : StatedSp 3 h.fixedField) : uEmbedGL6 h A ∈ uGroup6 h := by
  have := fixedField_charP h
  have h1 := toGL_map_mem_gramSU h ((sp6ToSL6_mem_range_iff (sp6ToSL6 A)).1 ⟨A, rfl⟩)
  rw [map_blockSwapJ_six] at h1
  exact h1

theorem uEmbedGL7_mem (A : StatedSp 3 h.fixedField) : uEmbedGL7 h A ∈ uGroup7 h := by
  have := fixedField_charP h
  have h1 := toGL_map_mem_gramSU h ((sp6ToSL7_mem_range_iff (sp6ToSL7 A)).1 ⟨A, rfl⟩)
  rw [map_gram7_fixedField] at h1
  exact h1

@[expose] noncomputable def uEmbed6 : StatedSp 3 h.fixedField →* uGroup6 h :=
  (uEmbedGL6 h).codRestrict _ (uEmbedGL6_mem h)

@[expose] noncomputable def uEmbed7 : StatedSp 3 h.fixedField →* uGroup7 h :=
  (uEmbedGL7 h).codRestrict _ (uEmbedGL7_mem h)

theorem coe_uEmbed6 (A : StatedSp 3 h.fixedField) :
    ((uEmbed6 h A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (sp6ToSL6 A : Matrix (Fin 6) (Fin 6) h.fixedField).map h.fixedField.subtype :=
  rfl

theorem coe_uEmbed7 (A : StatedSp 3 h.fixedField) :
    ((uEmbed7 h A : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
      (sp6ToSL7 A : Matrix (Fin 7) (Fin 7) h.fixedField).map h.fixedField.subtype :=
  rfl

theorem uEmbed6_injective : Function.Injective (uEmbed6 h) := fun A B hAB => by
  apply sp6ToSL6_injective
  apply Subtype.ext
  apply map_subtype_injective h
  have e := congrArg (fun x : uGroup6 h => ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hAB
  simp only [coe_uEmbed6] at e
  exact e

theorem uEmbed7_injective : Function.Injective (uEmbed7 h) := fun A B hAB => by
  apply sp6ToSL7_injective
  apply Subtype.ext
  apply map_subtype_injective h
  have e := congrArg (fun x : uGroup7 h => ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) hAB
  simp only [coe_uEmbed7] at e
  exact e

theorem gramSUToSL_uEmbed6_sp6Diag (t : Fin 3 → h.fixedFieldˣ) :
    gramSUToSL h _ (uEmbed6 h (sp6Diag _ t)) =
      lin6Torus K (fun i => Units.map (h.fixedField.subtype : h.fixedField →* K) (t i)) := by
  rw [← map_lin6Torus, ← sp6ToSL6_sp6Diag]
  rfl

theorem gramSUToSL_uEmbed7_sp6Diag (t : Fin 3 → h.fixedFieldˣ) :
    gramSUToSL h _ (uEmbed7 h (sp6Diag _ t)) =
      lin7Torus K (fun i => Units.map (h.fixedField.subtype : h.fixedField →* K) (t i)) := by
  rw [← map_lin7Torus, ← sp6ToSL7_sp6Diag]
  rfl

end Embed

section FixedPoints

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem coe_primeFormFieldSU {n : ℕ} {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (φ : K ≃+* K)
    (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
    ((primeFormFieldSU h hC φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ :=
  coe_glAut φ (g : GL (Fin n) K)

theorem fixedSubgroup_barSU6 :
    fixedSubgroup (primeFormFieldSU h (isPrimeFormGram_graphGram6 K) h.barEquiv) =
      (uEmbed6 h).range := by
  have := fixedField_charP h
  ext x
  constructor
  · intro hx
    have hbar : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar =
        ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      have e : ((primeFormFieldSU h _ h.barEquiv x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
        congrArg (fun y : uGroup6 h => ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hx
      rw [coe_primeFormFieldSU] at e
      exact e
    have hx' : (x : GL (Fin 6) K) ∈
        gramSU h ((blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) h.fixedField).map
          h.fixedField.subtype) := by
      rw [map_blockSwapJ_six]
      exact x.2
    obtain ⟨g, hg, hgx⟩ := exists_eq_map_of_map_bar_eq h hx' hbar
    obtain ⟨A, hA⟩ := (sp6ToSL6_mem_range_iff g).2 hg
    refine ⟨A, Subtype.ext (Units.ext ?_)⟩
    rw [coe_uEmbed6, hA, ← hgx]
    rfl
  · rintro ⟨A, rfl⟩
    apply Subtype.ext
    apply Units.ext
    change ((primeFormFieldSU h _ h.barEquiv (uEmbed6 h A) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = ((uEmbed6 h A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    rw [coe_primeFormFieldSU, coe_uEmbed6]
    exact map_subtype_map_bar h _

theorem fixedSubgroup_barSU7 :
    fixedSubgroup (primeFormFieldSU h (isPrimeFormGram_graphGram7 K) h.barEquiv) =
      (uEmbed7 h).range := by
  have := fixedField_charP h
  ext x
  constructor
  · intro hx
    have hbar : ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K).map h.bar =
        ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := by
      have e : ((primeFormFieldSU h _ h.barEquiv x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
          ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) :=
        congrArg (fun y : uGroup7 h => ((y : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) hx
      rw [coe_primeFormFieldSU] at e
      exact e
    have hx' : (x : GL (Fin 7) K) ∈
        gramSU h ((gram7 h.fixedField).map h.fixedField.subtype) := by
      rw [map_gram7_fixedField]
      exact x.2
    obtain ⟨g, hg, hgx⟩ := exists_eq_map_of_map_bar_eq h hx' hbar
    obtain ⟨A, hA⟩ := (sp6ToSL7_mem_range_iff g).2 hg
    refine ⟨A, Subtype.ext (Units.ext ?_)⟩
    rw [coe_uEmbed7, hA, ← hgx]
    rfl
  · rintro ⟨A, rfl⟩
    apply Subtype.ext
    apply Units.ext
    change ((primeFormFieldSU h _ h.barEquiv (uEmbed7 h A) : GL (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K) = ((uEmbed7 h A : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
    rw [coe_primeFormFieldSU, coe_uEmbed7]
    exact map_subtype_map_bar h _

theorem exists_ringEquiv_extend (ρ : h.fixedField ≃+* h.fixedField) :
    ∃ ρ' : K ≃+* K, ∀ x : h.fixedField, ρ' (x : K) = (ρ x : K) := by
  have := fixedField_finite h
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨s, -, hs, -⟩ := exists_frobenius_pow_eq h.one_le h.card_fixedField ρ
  refine ⟨iterateFrobeniusEquiv K 2 s, fun x => ?_⟩
  rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def, hs]
  simp

theorem primeFormFieldSU_uEmbed6 {ρ : h.fixedField ≃+* h.fixedField} {ρ' : K ≃+* K}
    (hρ : ∀ x : h.fixedField, ρ' (x : K) = (ρ x : K)) (A : StatedSp 3 h.fixedField) :
    primeFormFieldSU h (isPrimeFormGram_graphGram6 K) ρ' (uEmbed6 h A) =
      uEmbed6 h (statedSpMap (ρ : h.fixedField →+* h.fixedField) 3 A) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_primeFormFieldSU, coe_uEmbed6, coe_uEmbed6, sp6ToSL6_statedSpMap,
    SpecialLinearGroup.map_apply_coe]
  ext i j
  exact hρ _

theorem primeFormFieldSU_uEmbed7 {ρ : h.fixedField ≃+* h.fixedField} {ρ' : K ≃+* K}
    (hρ : ∀ x : h.fixedField, ρ' (x : K) = (ρ x : K)) (A : StatedSp 3 h.fixedField) :
    primeFormFieldSU h (isPrimeFormGram_graphGram7 K) ρ' (uEmbed7 h A) =
      uEmbed7 h (statedSpMap (ρ : h.fixedField →+* h.fixedField) 3 A) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_primeFormFieldSU, coe_uEmbed7, coe_uEmbed7, sp6ToSL7_statedSpMap,
    SpecialLinearGroup.map_apply_coe]
  ext i j
  exact hρ _

end FixedPoints

end CFSG.SeitzReduction.F4Pilot
