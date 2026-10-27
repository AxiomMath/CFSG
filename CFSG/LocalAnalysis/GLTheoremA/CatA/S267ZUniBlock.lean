module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniModel
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Phan

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

abbrev SG : Subgroup (GL (Fin 3) K) := gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

noncomputable abbrev projU : ↥(SG h) →* PU h := QuotientGroup.mk' _

@[expose] def toSLU : ↥(SG h) →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), (mem_gramSU.1 g.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def blockU (I : Finset (Fin 3)) : Subgroup ↥(SG h) :=
  (coordBlockSL K I).comap (toSLU h)

@[expose] noncomputable def diagU (d : Fin 3 → K) (hn : ∀ i, h.bar (d i) * d i = 1)
    (hd : ∏ i, d i = 1) : ↥(SG h) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal d)
      (by rw [det_diagonal, hd]; exact one_ne_zero), mem_gramSU.2 ⟨by
    change ((diagonal d).map h.bar)ᵀ * ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      diagonal d = ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Units.val_one, diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hn i, by
    change (diagonal d).det = 1
    rw [det_diagonal, hd]⟩⟩

variable {h}

variable (h) in
theorem toSLU_injective : Function.Injective (toSLU h) := fun a b hab =>
  Subtype.ext (Units.ext (congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
    (x : Matrix (Fin 3) (Fin 3) K)) hab))

theorem mem_blockU_iff {I : Finset (Fin 3)} {g : ↥(SG h)} :
    g ∈ blockU h I ↔ ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = if i = j then 1 else 0 :=
  mem_coordBlockSL_iff

theorem coe_diagU (d : Fin 3 → K) (hn : ∀ i, h.bar (d i) * d i = 1) (hd : ∏ i, d i = 1) :
    (((diagU h d hn hd : ↥(SG h)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d :=
  rfl

theorem ker_projU : (projU h).ker = normOneScalars h (SG h) 3 :=
  QuotientGroup.ker_mk' _

theorem projU_eq_one_iff {g : ↥(SG h)} :
    projU h g = 1 ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ 3 = 1 ∧
      (g : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  rw [← MonoidHom.mem_ker, ker_projU, mem_normOneScalars]

theorem eq_one_of_mem_blockU_of_projU_eq_one {I : Finset (Fin 3)} {i : Fin 3} (hi : i ∉ I)
    {g : ↥(SG h)} (hg : g ∈ blockU h I) (h1 : projU h g = 1) : g = 1 := by
  obtain ⟨c, -, -, hc⟩ := projU_eq_one_iff.1 h1
  have hii := mem_blockU_iff.1 hg i i (Or.inl hi)
  rw [hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, if_pos rfl] at hii
  apply Subtype.ext
  rw [hc, show c = 1 from Units.ext hii, map_one]
  rfl

noncomputable def mapProjUEquiv {I : Finset (Fin 3)} {i : Fin 3} (hi : i ∉ I) (L : Subgroup ↥(SG h))
    (hL : L ≤ blockU h I) : ↥L ≃* ↥(L.map (projU h)) :=
  MulEquiv.ofBijective ((projU h).subgroupMap L)
    ⟨fun a b hab => by
      have h1 : projU h ((a : ↥(SG h))⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val hab
      have h2 := eq_one_of_mem_blockU_of_projU_eq_one hi (hL (mul_mem (inv_mem a.2) b.2)) h1
      exact Subtype.ext (inv_mul_eq_one.1 h2),
     (projU h).subgroupMap_surjective L⟩

section Su

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

variable (h) in
theorem suid_eq_gramSU : SUid (unitaryInvolution K ℓ f) 3 = SG h := by
  ext B
  rw [CFSG.LieType.Universal.Unitary.mem_SUid, mem_gramSU, Units.val_one, Matrix.mul_one, conjTr]
  have hmap : (B : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K ℓ f) =
      (B : Matrix (Fin 3) (Fin 3) K).map h.bar := by
    ext i j
    rw [map_apply, map_apply, unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  rw [hmap]
  exact And.comm

variable (h) in
@[expose] noncomputable def suEquiv : Su K ℓ f 3 ≃* ↥(SG h) :=
  MulEquiv.subgroupCongr (suid_eq_gramSU h)

theorem blockU_eq_map (I : Finset (Fin 3)) :
    blockU h I = (coordBlockSU K ℓ f I).map (suEquiv h).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_blockU_iff, mem_coordBlockSU_iff]
  rfl

theorem isQuasisimple_blockU (hK : Nat.card K = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f)
    {I : Finset (Fin 3)} (hI : 2 ≤ I.card) : CFSG.Open.IsQuasisimple ↥(blockU h I) := by
  rw [blockU_eq_map]
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective _ _ (suEquiv h).injective).symm
    (isQuasisimple_coordBlockSU hK hq hI)

end Su

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
