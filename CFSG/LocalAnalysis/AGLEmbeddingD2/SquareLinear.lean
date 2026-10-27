module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareGeneric
public import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabRealThreeModels
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.AGLEmbeddingD2.SquareLinear

open CFSG.Open CFSG.SectionRank CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbeddingD2.SquareGeneric Matrix

section SL2

variable {F : Type} [Field F]

theorem isCyclic_of_isPGroup_three_sl2 [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (P : Subgroup (SpecialLinearGroup (Fin 2) F)) (hP : IsPGroup 3 P) : IsCyclic P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  set φ := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact sl2_center_eq_bot
  obtain ⟨Q, hQ⟩ := (hP.map φ).exists_le_sylow
  have hQc := CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_psl2 h3 h4 Q
  have hPc : IsCyclic (P.map φ) := Subgroup.isCyclic_of_le hQ
  exact isCyclic_of_surjective (P.equivMapOfInjective φ hinj).symm.toMonoidHom
    (P.equivMapOfInjective φ hinj).symm.surjective

@[expose] noncomputable def sl2Diag (t : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp⟩

@[expose] noncomputable def sl2Swap [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem coe_sl2Diag (t : Fˣ) :
    (sl2Diag t : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)] := rfl

theorem sl2Diag_pow (t : Fˣ) (k : ℕ) : sl2Diag t ^ k = sl2Diag (t ^ k) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Diag, coe_sl2Diag, Matrix.diagonal_pow]
  fin_cases i <;> fin_cases j <;> simp [inv_pow]

theorem sl2Swap_mul_self [CharP F 2] : (sl2Swap : SpecialLinearGroup (Fin 2) F) * sl2Swap = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [sl2Swap, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Diag_mul (s t : Fˣ) : sl2Diag s * sl2Diag t = sl2Diag (s * t) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag, coe_sl2Diag, coe_sl2Diag,
    Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem sl2Diag_inv (t : Fˣ) : (sl2Diag t)⁻¹ = sl2Diag t⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [sl2Diag_mul, mul_inv_cancel]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2Diag, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Swap_conj_sl2Diag [CharP F 2] (t : Fˣ) :
    sl2Swap * sl2Diag t * sl2Swap⁻¹ = (sl2Diag t)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right sl2Swap_mul_self, sl2Diag_inv]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag,
    coe_sl2Diag]
  fin_cases i <;> fin_cases j <;>
    simp [sl2Swap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.diagonal_apply]

end SL2

section Coord

variable {N : ℕ} {F : Type} [Field F] (S : Finset (Fin N))

@[expose] def coordEquiv : ↥S ⊕ {a : Fin N // a ∉ S} ≃ Fin N :=
  Equiv.sumCompl fun a => a ∈ S

theorem coordEquiv_inl (x : ↥S) : coordEquiv S (Sum.inl x) = x := rfl

theorem coordEquiv_inr (x : {a : Fin N // a ∉ S}) : coordEquiv S (Sum.inr x) = x := rfl

@[expose] def coordMat (A : Matrix ↥S ↥S F) : Matrix (Fin N) (Fin N) F :=
  Matrix.reindexAlgEquiv F F (coordEquiv S) (Matrix.fromBlocks A 0 0 1)

theorem coordMat_apply (A : Matrix ↥S ↥S F) (p q) :
    coordMat S A (coordEquiv S p) (coordEquiv S q) = Matrix.fromBlocks A 0 0 1 p q := by
  simp [coordMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem det_coordMat (A : Matrix ↥S ↥S F) : (coordMat S A).det = A.det := by
  rw [coordMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

@[expose] def coordHom : SpecialLinearGroup ↥S F →* SpecialLinearGroup (Fin N) F where
  toFun A := ⟨coordMat S (A : Matrix ↥S ↥S F), by rw [det_coordMat]; exact A.2⟩
  map_one' := Subtype.ext (by
    change coordMat S ((1 : SpecialLinearGroup ↥S F) : Matrix ↥S ↥S F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, coordMat, Matrix.fromBlocks_one, map_one])
  map_mul' A B := Subtype.ext (by
    change coordMat S ((A * B : SpecialLinearGroup ↥S F) : Matrix ↥S ↥S F) =
      coordMat S (A : Matrix ↥S ↥S F) * coordMat S (B : Matrix ↥S ↥S F)
    rw [Matrix.SpecialLinearGroup.coe_mul, coordMat, coordMat, coordMat, ← map_mul,
      Matrix.fromBlocks_multiply]
    simp)

theorem coordHom_injective : Function.Injective (coordHom (F := F) S) := fun A B h => by
  have h1 := congrArg Subtype.val h
  change coordMat S (A : Matrix ↥S ↥S F) = coordMat S (B : Matrix ↥S ↥S F) at h1
  have h2 := (Matrix.reindexAlgEquiv F F (coordEquiv S)).injective h1
  exact Subtype.ext (Matrix.fromBlocks_inj.1 h2).1

theorem mem_range_coordHom {g : SpecialLinearGroup (Fin N) F}
    (hg : ∀ a b, (a ∉ S ∨ b ∉ S) →
      (g : Matrix (Fin N) (Fin N) F) a b = (1 : Matrix (Fin N) (Fin N) F) a b) :
    g ∈ (coordHom (F := F) S).range := by
  set B : Matrix ↥S ↥S F := fun x y => (g : Matrix (Fin N) (Fin N) F) x y with hB
  have hgB : coordMat S B = (g : Matrix (Fin N) (Fin N) F) := by
    ext a b
    obtain ⟨p, rfl⟩ := (coordEquiv S).surjective a
    obtain ⟨q, rfl⟩ := (coordEquiv S).surjective b
    rw [coordMat_apply]
    rcases p with x | x <;> rcases q with y | y
    · rfl
    · have := hg x y (Or.inr y.2)
      have hne : (x : Fin N) ≠ (y : Fin N) := fun h => y.2 (h ▸ x.2)
      rw [Matrix.fromBlocks_apply₁₂, coordEquiv_inl, coordEquiv_inr, this,
        Matrix.one_apply_ne hne]
      rfl
    · have := hg x y (Or.inl x.2)
      have hne : (x : Fin N) ≠ (y : Fin N) := fun h => x.2 (h ▸ y.2)
      rw [Matrix.fromBlocks_apply₂₁, coordEquiv_inl, coordEquiv_inr, this,
        Matrix.one_apply_ne hne]
      rfl
    · have := hg x y (Or.inl x.2)
      rw [Matrix.fromBlocks_apply₂₂, coordEquiv_inr, coordEquiv_inr, this]
      by_cases hxy : x = y
      · subst hxy
        simp
      · rw [Matrix.one_apply_ne hxy, Matrix.one_apply_ne (fun h => hxy (Subtype.ext h))]
  have hdet : B.det = 1 := by
    rw [← det_coordMat S B, hgB]
    exact g.2
  exact ⟨⟨B, hdet⟩, Subtype.ext hgB⟩

theorem exists_injective_GL_coord :
    ∃ φ : ↥(coordHom (F := F) S).range →* GL (Fin S.card) F, Function.Injective φ := by
  classical
  let e₁ : ↥(coordHom (F := F) S).range ≃* SpecialLinearGroup ↥S F :=
    (MonoidHom.ofInjective (coordHom_injective S)).symm
  let e₂ : ↥S ≃ Fin S.card := (Finset.equivFin S)
  let ι : SpecialLinearGroup ↥S F →* GL ↥S F := Matrix.SpecialLinearGroup.toGL
  let r : GL ↥S F →* GL (Fin S.card) F :=
    Units.map (Matrix.reindexAlgEquiv F F e₂).toMonoidHom
  refine ⟨r.comp (ι.comp e₁.toMonoidHom), ?_⟩
  intro a b h
  apply e₁.injective
  apply Matrix.SpecialLinearGroup.toGL_injective
  apply Units.ext
  have h' := congrArg (fun u : GL (Fin S.card) F => (u : Matrix (Fin S.card) (Fin S.card) F)) h
  exact (Matrix.reindexAlgEquiv F F e₂).injective h'

end Coord

section Datum

variable {m : ℕ} {F : Type} [Field F]

theorem blockHom_upper (i : Fin m) (c : F) :
    SL.blockHom F i (sl2Upper c) = SL.x m F (Pi.single i 1) c := by
  rw [SL.x_eq (SL.castSucc_ne_succ i) (toStd_single m i)]
  exact Subtype.ext (SL.blockMat_transvection_upper i c)

theorem blockHom_lower (i : Fin m) (c : F) :
    SL.blockHom F i (sl2Lower c) = SL.x m F (-Pi.single i 1) c := by
  rw [SL.x_eq (SL.castSucc_ne_succ i).symm (SL.toStd_neg_single i)]
  exact Subtype.ext (SL.blockMat_transvection_lower i c)

theorem rankOne_eq_range_blockHom (i : Fin m) :
    rankOne (rootDatum m F).rootGroup i = (SL.blockHom F i).range :=
  rankOne_eq_range_of_sl2 SL.isParametrization (blockHom_upper i) (blockHom_lower i)

theorem blockHom_sl2Diag_mem_torus (i : Fin m) (t : Fˣ) :
    SL.blockHom F i (sl2Diag t) ∈ torus m F i := by
  refine Subgroup.subset_closure ⟨t, ?_⟩
  change SL.blockMat i (Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)]) = _
  have hne := SL.castSucc_ne_succ i
  refine SL.ext_blockEquiv i fun p q => ?_
  rw [SL.blockMat_apply]
  rcases p with p | ⟨a, ha⟩ <;> rcases q with q | ⟨b, hb⟩
  · fin_cases p <;> fin_cases q <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, hne, Ne.symm hne, Function.update_of_ne]
  · push Not at hb
    fin_cases p <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, Ne.symm hb.1,
        Ne.symm hb.2]
  · push Not at ha
    fin_cases q <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, ha.1, ha.2]
  · push Not at ha
    rw [Matrix.fromBlocks_apply₂₂, SL.blockEquiv_inr, SL.blockEquiv_inr]
    simp [Matrix.one_apply, Matrix.diagonal_apply, Function.update_of_ne ha.2,
      Function.update_of_ne ha.1]

theorem rankOne_le_range_coordHom (i : Fin m) {S : Finset (Fin (m + 1))}
    (hi : i.castSucc ∈ S) (hi' : i.succ ∈ S) :
    rankOne (rootDatum m F).rootGroup i ≤ (coordHom (F := F) S).range := by
  rw [rankOne_eq_range_blockHom]
  rintro _ ⟨A, rfl⟩
  refine mem_range_coordHom S fun a b hab => ?_
  change SL.blockMat i (A : Matrix (Fin 2) (Fin 2) F) a b = _
  obtain ⟨p, rfl⟩ := (SL.blockEquiv i).surjective a
  obtain ⟨q, rfl⟩ := (SL.blockEquiv i).surjective b
  rw [SL.blockMat_apply]
  rcases p with p | ⟨a, ha⟩ <;> rcases q with q | ⟨b, hb⟩
  · exfalso
    fin_cases p <;> fin_cases q <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, hi, hi'] at hab
  · push Not at hb
    fin_cases p <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, Ne.symm hb.1,
        Ne.symm hb.2]
  · push Not at ha
    fin_cases q <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, ha.1, ha.2]
  · rw [Matrix.fromBlocks_apply₂₂, SL.blockEquiv_inr, SL.blockEquiv_inr]
    simp [Matrix.one_apply]

end Datum

section Facts

variable {m : ℕ} {F : Type} [Field F]

theorem sl2Diag_one : sl2Diag (1 : Fˣ) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2Diag, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Diag_mul_sl2Upper_ne {ω : Fˣ} (hω : ω ≠ ω⁻¹) :
    sl2Diag ω * sl2Upper 1 ≠ sl2Upper 1 * sl2Diag ω := by
  intro h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1)
    h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag] at h1
  simp [sl2Upper, Matrix.mul_apply, Matrix.diagonal_apply] at h1
  exact hω (Units.ext (by simpa using h1))

theorem realThreeOver_torus_sl [CharP F 2] [Finite F] (h4 : 4 ≤ Nat.card F) {Y : Type*}
    [Group Y] {π : SpecialLinearGroup (Fin (m + 1)) F →* Y} {J : Subgroup Y}
    (hBJ : borel (rootDatum m F) (torus m F) ≤ J.comap π) (i : Fin m) {ω : Fˣ}
    (hω : orderOf ω = 3) : RealThreeOver π (rankOne (rootDatum m F).rootGroup i) J := by
  have hrange := rankOne_eq_range_blockHom (F := F) i
  set g := SL.blockHom F i (sl2Diag ω) with hg
  have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
  have hωne : ω ≠ ω⁻¹ := by
    intro h
    have h2 : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel ω
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hω] at this
    omega
  refine ⟨g, ?_, ?_, ?_, ?_, SL.blockHom F i sl2Swap, hrange ▸ ⟨_, rfl⟩, ?_⟩
  · rw [hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      (sl2_isPerfect h4).commutator_eq_top]
    exact ⟨_, Subgroup.mem_top _, rfl⟩
  · exact hBJ (le_sup_left (a := ⨆ k, torus m F k)
      (le_iSup (torus m F) i (blockHom_sl2Diag_mem_torus i ω)))
  · rw [hg, ← map_pow, sl2Diag_pow, hω3, sl2Diag_one, map_one]
  · intro hz
    have h1 := Subgroup.mem_center_iff.mp hz (SL.blockHom F i (sl2Upper 1))
    rw [← map_mul, ← map_mul] at h1
    exact sl2Diag_mul_sl2Upper_ne hωne (SL.blockHom_injective i h1).symm
  · rw [hg, ← map_inv, ← map_mul, ← map_mul, sl2Swap_conj_sl2Diag, map_inv]

theorem exists_orderOf_eq_three [Finite F] (h3 : 3 ∣ Nat.card F - 1) :
    ∃ ω : Fˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact h3
  exact exists_prime_orderOf_dvd_card' 3 h

theorem coprime_three_card_center_sl [Finite F] (h3 : ¬ 3 ∣ m + 1) :
    Nat.Coprime 3 (Nat.card (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp z.2
  have hz3 : (z : SpecialLinearGroup (Fin (m + 1)) F) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hr3 : r ^ 3 = 1 := by
    have h := congrArg (fun A : SpecialLinearGroup (Fin (m + 1)) F =>
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) 0 0) hz3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hrz,
      Matrix.scalar_apply, Matrix.diagonal_pow] at h
    simpa using h
  have hr1 : r = 1 := by
    have hcop : Nat.Coprime 3 (m + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [Fintype.card_fin] at hr
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hr3)
      (orderOf_dvd_of_pow_eq_one hr))
  have hz1 : (z : SpecialLinearGroup (Fin (m + 1)) F) = 1 := by
    apply Subtype.ext
    rw [← hrz, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  omega

end Facts

section Coords

variable {m : ℕ}

@[expose] noncomputable def coords (I : Set (Fin m)) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter fun a => ∃ i ∈ I, a = i.castSucc ∨ a = i.succ

theorem castSucc_mem_coords {I : Set (Fin m)} {i : Fin m} (hi : i ∈ I) :
    i.castSucc ∈ coords I := by
  classical
  simp only [coords, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, hi, Or.inl rfl⟩

theorem succ_mem_coords {I : Set (Fin m)} {i : Fin m} (hi : i ∈ I) : i.succ ∈ coords I := by
  classical
  simp only [coords, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, hi, Or.inr rfl⟩

theorem card_coords_le_six (I : Set (Fin m))
    (hI : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val) :
    (coords I).card ≤ 6 := by
  classical
  by_cases hne : I.Nonempty
  ·
    obtain ⟨a, ha, hamin⟩ : ∃ a ∈ I, ∀ x ∈ I, a.val ≤ x.val := by
      obtain ⟨x, hx⟩ := hne
      let s := (Set.toFinset I)
      have hs : s.Nonempty := ⟨x, by simpa [s] using hx⟩
      refine ⟨s.min' hs, by simpa [s] using s.min'_mem hs, fun y hy => ?_⟩
      exact Fin.le_def.1 (s.min'_le y (by simpa [s] using hy))
    by_cases hne2 : ∃ x ∈ I, a.val + 2 ≤ x.val
    · obtain ⟨b, hb, hab2, hbmin⟩ : ∃ b ∈ I, a.val + 2 ≤ b.val ∧
          ∀ x ∈ I, a.val + 2 ≤ x.val → b.val ≤ x.val := by
        let s := (Set.toFinset I).filter fun x => a.val + 2 ≤ x.val
        obtain ⟨x, hx, hax⟩ := hne2
        have hs : s.Nonempty := ⟨x, by simpa [s] using ⟨hx, hax⟩⟩
        have hmem := s.min'_mem hs
        simp only [s, Finset.mem_filter, Set.mem_toFinset] at hmem
        refine ⟨s.min' hs, hmem.1, hmem.2, fun y hy hay => ?_⟩
        exact Fin.le_def.1 (s.min'_le y (by simpa [s] using ⟨hy, hay⟩))
      have hall : ∀ x ∈ I, x.val ≤ a.val + 1 ∨ (b.val ≤ x.val ∧ x.val ≤ b.val + 1) := by
        intro x hx
        by_contra hc
        push Not at hc
        obtain ⟨h1, h2⟩ := hc
        have hax : a.val + 2 ≤ x.val := by omega
        have hbx : b.val + 2 ≤ x.val := by
          have := hbmin x hx hax
          have := h2 this
          omega
        exact hI ⟨a, ha, b, hb, x, hx, hab2, hbx⟩
      set t : Finset ℕ := [a.val, a.val + 1, a.val + 2, b.val, b.val + 1, b.val + 2].toFinset
      have ht : t.card ≤ 6 := List.toFinset_card_le _
      refine le_trans (Finset.card_le_card_of_injOn (fun y => y.val) ?_ ?_) ht
      · intro y hy
        simp only [coords, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨i, hi, rfl | rfl⟩ := hy
        · have := hamin i hi
          rcases hall i hi with h | h <;> simp [t] <;> omega
        · have := hamin i hi
          rcases hall i hi with h | h <;> simp [t] <;> omega
      · intro y _ z _ h
        exact Fin.ext h
    · push Not at hne2
      set t : Finset ℕ := [a.val, a.val + 1, a.val + 2].toFinset
      have ht : t.card ≤ 3 := List.toFinset_card_le _
      refine le_trans (Finset.card_le_card_of_injOn (fun y => y.val) ?_ ?_) (ht.trans (by norm_num))
      · intro y hy
        simp only [coords, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨i, hi, rfl | rfl⟩ := hy
        · have := hne2 i hi
          have := hamin i hi
          simp [t]
          omega
        · have := hne2 i hi
          have := hamin i hi
          simp [t]
          omega
      · intro y _ z _ h
        exact Fin.ext h
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [coords]

end Coords

section Main

variable {m : ℕ} {F : Type} [Field F]

local notation "A₅" => alternatingGroup (Fin 5)

theorem isCyclic_of_le_range {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {P : Subgroup G'} (hP : P ≤ f.range)
    (h : IsCyclic (P.comap f)) : IsCyclic P := by
  have hmap : (P.comap f).map f = P := Subgroup.map_comap_eq_self hP
  have hc : IsCyclic ((P.comap f).map f) :=
    isCyclic_of_surjective ((P.comap f).equivMapOfInjective f hf).toMonoidHom
      ((P.comap f).equivMapOfInjective f hf).surjective
  rw [hmap] at hc
  exact hc

theorem ker_comp_mk' {Y : Type*} [Group Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center
      (SpecialLinearGroup (Fin (m + 1)) F)))).ker =
      Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
  ext z
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

theorem three_le_pRank_sl [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) {X : Type} [Group X]
    [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (h3 : 3 ∣ Nat.card ρ.ker → 3 ∣ m + 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (hQ : LeviSection.HasSubquotient J (A₅ × A₅)) : 3 ≤ Open.pRank 3 (J.comap ρ) := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_sl e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have hM := hasSubquotient_leviM_of_parab hb' hBJ hQ
  have hBJ' : (borel (rootDatum m F) (torus m F)).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr hBJ
  obtain ⟨j, hj⟩ := LieOut.exists_node_not_mem_negIndices hb' hBJ' hJ
  have hr : ∀ i, ParabRealThree.HasRealOrderThree (rootDatum m F) i := fun i =>
    ParabRealThree.HasSL2Node.hasRealOrderThree (hasSL2Node_sl i)
  have hcart : ∀ a b : Fin m, a.val + 2 ≤ b.val → (rootDatum m F).cartan a b = 0 := by
    intro a b hab
    change CartanMatrix.A m a b = 0
    have h1 : a ≠ b := fun h => by rw [h] at hab; omega
    have h2 : ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by omega
    simp only [CartanMatrix.A, Matrix.of_apply, h1, h2, ite_false]
  rcases Nat.even_or_odd (f : ℕ) with hfe | hfo
  ·
    obtain ⟨k, hk⟩ := hfe
    have hk1 : 1 ≤ k := by have := f.pos; omega
    have hq : Nat.card F = 4 ^ k := by rw [hfc, hk, ← two_mul, pow_mul]; norm_num
    have hq3 : 3 ∣ Nat.card F - 1 := by
      rw [hq]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
    have hq4 : 4 ≤ Nat.card F := by
      rw [hq]
      exact le_self_pow₀ (by norm_num) (by omega)
    obtain ⟨ω, hω⟩ := exists_orderOf_eq_three hq3
    by_cases hm5 : 5 ≤ m
    ·
      let a : Fin m := ⟨0, by omega⟩
      let b : Fin m := ⟨2, by omega⟩
      let c : Fin m := ⟨4, by omega⟩
      exact three_le_pRank_of_triple hb'.ker_central ρ hρ hρker
        (commutes_rankOne_of_cartan_eq_zero hb'.extras
          (fun h => absurd (congrArg Fin.val h) (by simp [a, b])) (hcart a b (by simp [a, b])))
        (commutes_rankOne_of_cartan_eq_zero hb'.extras
          (fun h => absurd (congrArg Fin.val h) (by simp [a, c])) (hcart a c (by simp [a, c])))
        (commutes_rankOne_of_cartan_eq_zero hb'.extras
          (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) (hcart b c (by simp [b, c])))
        (realThreeOver_torus_sl hq4 hBJ a hω) (realThreeOver_torus_sl hq4 hBJ b hω)
        (realThreeOver_torus_sl hq4 hBJ c hω)
    · by_cases hm3 : 3 ≤ m
      ·
        have h3m : ¬ 3 ∣ m + 1 := by omega
        have hρ3 : Nat.Coprime 3 (Nat.card ρ.ker) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => h3m (h3 h)
        have hπ3 : Nat.Coprime 3 (Nat.card π'.ker) := by
          rw [hker', ker_comp_mk' e]
          exact coprime_three_card_center_sl h3m
        have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
        have hω1 : ω ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hω
          omega
        have hg3 : ∀ i : Fin m, (SL.blockHom F i (sl2Diag ω)) ^ 3 = 1 := fun i => by
          rw [← map_pow, sl2Diag_pow, hω3, sl2Diag_one, map_one]
        have hg1 : ∀ i : Fin m, SL.blockHom F i (sl2Diag ω) ≠ 1 := fun i h => by
          have h' := SL.blockHom_injective i (h.trans (map_one _).symm)
          have h'' := congrArg (fun A : SpecialLinearGroup (Fin 2) F =>
            (A : Matrix (Fin 2) (Fin 2) F) 0 0) h'
          simp [coe_sl2Diag] at h''
          exact hω1 h''
        let a : Fin m := ⟨0, by omega⟩
        let b : Fin m := ⟨1, by omega⟩
        let c : Fin m := ⟨2, by omega⟩
        refine (three_le_pRank_of_torus hb'.extras hπ3 hBJ (a := a) (b := b) (c := c)
          (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
          (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
          (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) (blockHom_sl2Diag_mem_torus a ω)
          (blockHom_sl2Diag_mem_torus b ω) (blockHom_sl2Diag_mem_torus c ω) (hg3 a) (hg3 b)
          (hg3 c) (hg1 a) (hg1 b) (hg1 c)).trans (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
      ·
        exfalso
        have hsub : (negIndices (rootDatum m F) (J.comap π')).Subsingleton := by
          intro x hx y hy
          have hxj : x.val ≠ j.val := fun h => hj (Fin.ext h ▸ hx)
          have hyj : y.val ≠ j.val := fun h => hj (Fin.ext h ▸ hy)
          have h1 : x.val < m := x.isLt
          have h2 : y.val < m := y.isLt
          have h3 : j.val < m := j.isLt
          exact Fin.ext (by omega)
        rcases hsub.eq_empty_or_singleton with hI | ⟨i, hI⟩
        · rw [hI, leviM_empty] at hM
          exact false_of_hasSubquotient_bot hM
        · rw [hI, leviM_singleton, rankOne_eq_range_blockHom (m := m) (F := F) i] at hM
          refine false_of_hasSubquotient_of_isCyclic (fun P hP h3P => ?_) hM
          exact isCyclic_of_le_range (SL.blockHom_injective i) hP
            (isCyclic_of_isPGroup_three_sl2 hq4 _
            (h3P.comap_of_injective _ (SL.blockHom_injective i)))
  ·
    by_cases ho : ∃ a ∈ negIndices (rootDatum m F) (J.comap π'),
        ∃ b ∈ negIndices (rootDatum m F) (J.comap π'),
        ∃ c ∈ negIndices (rootDatum m F) (J.comap π'), a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val
    · obtain ⟨a, ha, b, hb2, c, hc, hab, hbc⟩ := ho
      exact three_le_pRank_of_orth hb'.extras hb'.ker_central ρ hρ hρker hBJ hr
        (fun h => by rw [h] at hab; omega) (fun h => by rw [h] at hab; omega)
        (fun h => by rw [h] at hbc; omega) (hcart a b hab) (hcart a c (by omega))
        (hcart b c hbc) ha hb2 hc
    · exfalso
      set S := coords (negIndices (rootDatum m F) (J.comap π'))
      have hS : S.card ≤ 6 := card_coords_le_six _ ho
      have hle : leviM (rootDatum m F) (negIndices (rootDatum m F) (J.comap π')) ≤
          (coordHom (F := F) S).range :=
        iSup₂_le fun i hi => rankOne_le_range_coordHom i (castSucc_mem_coords hi)
          (succ_mem_coords hi)
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨φ, hφ⟩ := exists_injective_GL_coord (F := F) S
      refine (hM.mono hle).false_of_isCyclic (fun P hP h5 => ?_)
        LeviSection.exists_not_isCyclic_five
      have hc := CyclicSylowGL.isCyclic_of_isPGroup_five_of_injective_GL_two_pow hfo hf
        (by omega) φ hφ (P.subgroupOf (coordHom (F := F) S).range)
        (h5.comap_of_injective _ (Subgroup.subtype_injective _))
      exact (Subgroup.subgroupOfEquivOfLe hP).isCyclic.mp hc

end Main

end CFSG.AGLEmbeddingD2.SquareLinear
