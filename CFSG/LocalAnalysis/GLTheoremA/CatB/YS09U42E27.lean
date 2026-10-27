module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.Fischer.Classification.Unitary.Basic
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open
open CFSG.LieType.Universal.Unitary (SUid conjTr mem_SUid)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

section LiftOf

variable {H M : Type*} [Group H] [Finite H] [Group M]

theorem exists_pSubgroup_lift_of_le {p : ℕ} (hp : p.Prime) (π : H →* M)
    (hker : ¬ p ∣ Nat.card π.ker) {F : Subgroup M} (hF : IsPGroup p F) (hFπ : F ≤ π.range)
    {E₀ : Subgroup H} (hE₀ : IsPGroup p E₀) (hE₀F : E₀.map π ≤ F) :
    ∃ W : Subgroup H, IsPGroup p W ∧ E₀ ≤ W ∧ W.map π = F ∧
      Function.Injective (π.comp W.subtype) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Subgroup H := F.comap π
  let f : ↥P →* ↥F := π.subgroupComap F
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨h, hh⟩ := hFπ e.2
    exact ⟨⟨h, by simp [P, Subgroup.mem_comap, hh]⟩, Subtype.ext hh⟩
  haveI : Finite F := Finite.of_surjective f hf
  have hE₀P : E₀ ≤ P := fun x hx => hE₀F (Subgroup.mem_map_of_mem π hx)
  have htop : IsPGroup p (⊤ : Subgroup F) := hF.of_equiv Subgroup.topEquiv.symm
  have hQmap : ∀ Q : Sylow p P, (Q : Subgroup P).map f = ⊤ := by
    intro Q
    have h1 : ((Q.mapSurjective hf : Sylow p F) : Subgroup F) = (Q : Subgroup P).map f := rfl
    have h2 : (⊤ : Subgroup F) = ((Q.mapSurjective hf : Sylow p F) : Subgroup F) :=
      (Q.mapSurjective hf).3 htop le_top
    exact h1.symm.trans h2.symm
  have hE₀' : IsPGroup p (E₀.subgroupOf P) :=
    hE₀.of_equiv (Subgroup.subgroupOfEquivOfLe hE₀P).symm
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hE₀'
  have hW : IsPGroup p ((Q : Subgroup P).map P.subtype) := Q.2.map P.subtype
  have hmap : ((Q : Subgroup P).map P.subtype).map π = F := by
    rw [Subgroup.map_map]
    have h1 : π.comp P.subtype = F.subtype.comp f := rfl
    rw [h1, ← Subgroup.map_map, hQmap Q, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨(Q : Subgroup P).map P.subtype, hW, ?_, hmap, injective_comp_subtype hp π hker hW⟩
  intro x hx
  exact ⟨⟨x, hE₀P hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩

end LiftOf

section FourTwo

abbrev F4 : Type := CFSG.Blueprint.Fischer.K

noncomputable abbrev frob4 : F4 ≃+* F4 := CFSG.Fischer.Classification.Unitary.frob

theorem frob4_apply (c : F4) : frob4 c = c ^ 2 :=
  CFSG.Fischer.Classification.Unitary.frob_apply c

theorem card_F4 : Nat.card F4 = (2 ^ 1) ^ 2 :=
  CFSG.Fischer.Classification.Unitary.card_K

theorem unitaryFieldData_F4 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F4 :=
  ⟨Nat.prime_two, le_rfl, by rw [card_F4]; norm_num⟩

theorem bar_F4 : ⇑unitaryFieldData_F4.bar = ⇑frob4 := by
  funext c
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, frob4_apply]
  norm_num

theorem card_units_F4 : Nat.card F4ˣ = 3 :=
  (CFSG.ClassicalGroups.Unitary.card_units_of_card card_F4).trans (by norm_num)

theorem cube_units_F4 (c : F4ˣ) : c ^ 3 = 1 := by
  have h : c ^ Nat.card F4ˣ = 1 := pow_card_eq_one'
  rwa [card_units_F4] at h

theorem cube_F4 (c : F4ˣ) : (c : F4) ^ 3 = 1 := by
  rw [← Units.val_pow_eq_pow_val, cube_units_F4, Units.val_one]

theorem frob4_mul_self (c : F4ˣ) : frob4 (c : F4) * (c : F4) = 1 := by
  rw [frob4_apply, ← pow_succ]
  exact cube_F4 c

theorem exists_isPrimitiveRoot_three_F4 : ∃ ζ : F4, IsPrimitiveRoot ζ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ξ, hξ⟩ := exists_prime_orderOf_dvd_card' (G := F4ˣ) 3 (by simp [card_units_F4])
  have hprim : IsPrimitiveRoot ξ 3 := by
    have := IsPrimitiveRoot.orderOf ξ
    rwa [hξ] at this
  exact ⟨ξ, IsPrimitiveRoot.coe_units_iff.mpr hprim⟩

@[expose] noncomputable def snoc4 : (Fin 3 → F4ˣ) →* (Fin 4 → F4ˣ) where
  toFun x := Fin.snoc (α := fun _ => F4ˣ) x (∏ i, x i)⁻¹
  map_one' := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Pi.one_apply, Finset.prod_const_one, inv_one]
    · simp only [Fin.snoc_castSucc, Pi.one_apply]
  map_mul' x y := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
    · simp only [Fin.snoc_castSucc, Pi.mul_apply]

theorem snoc4_castSucc (x : Fin 3 → F4ˣ) (i : Fin 3) : snoc4 x i.castSucc = x i :=
  Fin.snoc_castSucc (α := fun _ => F4ˣ) _ _ _

theorem snoc4_last (x : Fin 3 → F4ˣ) : snoc4 x (Fin.last 3) = (∏ i, x i)⁻¹ := by
  show Fin.snoc (α := fun _ => F4ˣ) x (∏ i, x i)⁻¹ (Fin.last 3) = (∏ i, x i)⁻¹
  exact Fin.snoc_last (α := fun _ => F4ˣ) _ _

theorem prod_snoc4 (x : Fin 3 → F4ˣ) : ∏ j, snoc4 x j = 1 := by
  rw [Fin.prod_univ_castSucc, snoc4_last]
  simp only [snoc4_castSucc, mul_inv_cancel]

@[expose] noncomputable def diagT4 : (Fin 4 → F4ˣ) →* GL (Fin 4) F4 :=
  (Units.map (diagonalRingHom (Fin 4) F4).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

@[expose] noncomputable def torusGL4 : (Fin 3 → F4ˣ) →* GL (Fin 4) F4 := diagT4.comp snoc4

theorem coe_torusGL4 (x : Fin 3 → F4ˣ) :
    ((torusGL4 x : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
      diagonal fun i => (snoc4 x i : F4) :=
  rfl

theorem torusGL4_mem (x : Fin 3 → F4ˣ) : torusGL4 x ∈ SUid frob4 4 := by
  rw [CFSG.LieType.Universal.Unitary.mem_SUid]
  refine ⟨?_, ?_⟩
  · rw [coe_torusGL4, det_diagonal, ← Units.coe_prod, prod_snoc4, Units.val_one]
  · rw [coe_torusGL4, CFSG.LieType.Universal.Unitary.conjTr, Matrix.diagonal_map (map_zero frob4),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact frob4_mul_self (snoc4 x i)

@[expose] noncomputable def torusSU4 : (Fin 3 → F4ˣ) →* SUid frob4 4 :=
  MonoidHom.codRestrict torusGL4 (SUid frob4 4) torusGL4_mem

theorem torusSU4_injective : Function.Injective torusSU4 := by
  intro x y hxy
  have h1 : torusGL4 x = torusGL4 y := congrArg Subtype.val hxy
  have h2 : ∀ i, snoc4 x i = snoc4 y i := by
    intro i
    have h3 : ((torusGL4 x : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) i i =
        ((torusGL4 y : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) i i := by rw [h1]
    rw [coe_torusGL4, coe_torusGL4, diagonal_apply_eq, diagonal_apply_eq] at h3
    exact Units.ext h3
  funext i
  have h4 := h2 i.castSucc
  rwa [snoc4_castSucc, snoc4_castSucc] at h4

theorem card_torusSU4_range : Nat.card torusSU4.range = 3 ^ 3 := by
  rw [card_range_eq_of_injective torusSU4 torusSU4_injective, Nat.card_fun, card_units_F4,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isElemAbelian_torusSU4_range : IsElemAbelian 3 torusSU4.range :=
  isElemAbelian_range torusSU4 fun a => by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    exact cube_units_F4 (a i)

theorem mem_torusSU4_range_of_isDiag (y : SUid frob4 4)
    (hy : ((y : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4).IsDiag) : y ∈ torusSU4.range := by
  set A : Matrix (Fin 4) (Fin 4) F4 := ((y : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) with hA
  have hdet : A.det = 1 := (CFSG.LieType.Universal.Unitary.mem_SUid.1 y.2).1
  have hdiagA : diagonal (fun i => A i i) = A := hy.diagonal_diag
  have hprod : ∏ i, A i i = 1 := by
    rw [← det_diagonal, hdiagA, hdet]
  have hne : ∀ i, A i i ≠ 0 := fun i h0 => by
    have h1 : ∏ j, A j j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hprod] at h1
    exact one_ne_zero h1
  let a : Fin 3 → F4ˣ := fun i => Units.mk0 (A i.castSucc i.castSucc) (hne _)
  refine ⟨a, Subtype.ext (Units.ext ?_)⟩
  show diagonal (fun i => (snoc4 a i : F4)) = A
  conv_rhs => rw [← hdiagA]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h1 : (∏ j : Fin 4, A j j) =
        (∏ j : Fin 3, A j.castSucc j.castSucc) * A (Fin.last 3) (Fin.last 3) :=
      Fin.prod_univ_castSucc _
    rw [hprod] at h1
    have h2 : A (Fin.last 3) (Fin.last 3) = (∏ j : Fin 3, A j.castSucc j.castSucc)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1.symm
    rw [snoc4_last, Units.val_inv_eq_inv_val, Units.coe_prod, h2]
    rfl
  · rw [snoc4_castSucc]
    rfl

theorem su4_le_primeForm4 :
    SUid frob4 4 ≤ primeFormUnitary unitaryFieldData_F4 (idGram F4 4) := by
  intro x hx
  have hconj : conjTr frob4 (x : Matrix (Fin 4) (Fin 4) F4) * (x : Matrix (Fin 4) (Fin 4) F4) = 1 :=
    (CFSG.LieType.Universal.Unitary.mem_SUid.1 hx).2
  show ((x : Matrix (Fin 4) (Fin 4) F4).map unitaryFieldData_F4.bar)ᵀ *
      ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) * (x : Matrix (Fin 4) (Fin 4) F4) =
      ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
  rw [bar_F4, Units.val_one, Matrix.mul_one]
  exact hconj

theorem scalar_mem_primeForm4 (c : F4ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈
      primeFormUnitary unitaryFieldData_F4 (idGram F4 4) := by
  show (((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F4) :
      Matrix (Fin 4) (Fin 4) F4).map unitaryFieldData_F4.bar)ᵀ *
      ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) *
      ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
      ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, bar_F4, Units.val_one,
    Matrix.mul_one, Matrix.diagonal_map (map_zero frob4), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact frob4_mul_self c

theorem det_scalar_F4 (c : F4ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F4) :
      Matrix (Fin 4) (Fin 4) F4).det = (c : F4) ^ 4 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal]
  simp

theorem exists_conj_torus (P : Subgroup (SUid frob4 4)) (hP : IsElemAbelian 3 P) :
    ∃ g : SUid frob4 4, ∀ x ∈ P, g * x * g⁻¹ ∈ torusSU4.range := by
  let ι : SUid frob4 4 →* primeFormUnitary unitaryFieldData_F4 (idGram F4 4) :=
    Subgroup.inclusion su4_le_primeForm4
  have hcomm : ∀ x ∈ P.map ι, ∀ y ∈ P.map ι, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hP.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpow : ∀ x ∈ P.map ι, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hP.2 x hx, map_one]
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three_F4
  obtain ⟨P₀, hP₀⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m
    unitaryFieldData_F4 hζ (by norm_num) (P.map ι) hcomm hpow
  obtain ⟨d, hd⟩ : ∃ d : F4ˣ, d = Matrix.GeneralLinearGroup.det (P₀ : GL (Fin 4) F4) :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : F4ˣ, c = d⁻¹ := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : GL (Fin 4) F4, s = Matrix.GeneralLinearGroup.scalar (Fin 4) c :=
    ⟨_, rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ q : GL (Fin 4) F4, q = s * (P₀ : GL (Fin 4) F4) := ⟨_, rfl⟩
  have hsP : s ∈ primeFormUnitary unitaryFieldData_F4 (idGram F4 4) := by
    rw [hs_def]
    exact scalar_mem_primeForm4 c
  have hqP : q ∈ primeFormUnitary unitaryFieldData_F4 (idGram F4 4) := by
    rw [hq_def]
    exact mul_mem hsP P₀.2
  have hunit : c ^ 4 * d = 1 := by
    rw [hc, show (d⁻¹) ^ 4 = (d⁻¹) ^ 3 * d⁻¹ from pow_succ _ 3, cube_units_F4, one_mul,
      inv_mul_cancel]
  have hqdet : (q : Matrix (Fin 4) (Fin 4) F4).det = 1 := by
    have h1 := congrArg Units.val hunit
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at h1
    rw [hq_def, Units.val_mul, det_mul, hs_def, det_scalar_F4,
      ← Matrix.GeneralLinearGroup.val_det_apply, ← hd]
    exact h1
  have hqconj :
      conjTr frob4 (q : Matrix (Fin 4) (Fin 4) F4) * (q : Matrix (Fin 4) (Fin 4) F4) = 1 := by
    have h := hqP
    change ((q : Matrix (Fin 4) (Fin 4) F4).map unitaryFieldData_F4.bar)ᵀ *
      ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) * (q : Matrix (Fin 4) (Fin 4) F4) =
      ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) at h
    rw [bar_F4, Units.val_one, Matrix.mul_one] at h
    exact h
  have hqS : q ∈ SUid frob4 4 := CFSG.LieType.Universal.Unitary.mem_SUid.2 ⟨hqdet, hqconj⟩
  have hsx : ∀ y : GL (Fin 4) F4, s * y = y * s := by
    intro y
    apply Units.ext
    rw [hs_def, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  have hs : ∀ y : GL (Fin 4) F4, s⁻¹ * y * s = y := by
    intro y
    rw [mul_assoc, ← hsx, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨(⟨q, hqS⟩ : SUid frob4 4)⁻¹, fun x hx => ?_⟩
  apply mem_torusSU4_range_of_isDiag
  have hdiag := hP₀ (ι x) (Subgroup.mem_map_of_mem ι hx)
  have key : (q : GL (Fin 4) F4)⁻¹ * (x : GL (Fin 4) F4) * q =
      (P₀ : GL (Fin 4) F4)⁻¹ * (x : GL (Fin 4) F4) * P₀ := by
    rw [hq_def, _root_.mul_inv_rev]
    calc (P₀ : GL (Fin 4) F4)⁻¹ * s⁻¹ * (x : GL (Fin 4) F4) * (s * P₀)
        = (P₀ : GL (Fin 4) F4)⁻¹ * (s⁻¹ * (x : GL (Fin 4) F4) * s) * P₀ := by group
      _ = (P₀ : GL (Fin 4) F4)⁻¹ * (x : GL (Fin 4) F4) * P₀ := by rw [hs]
  have e1 : (((⟨q, hqS⟩ : SUid frob4 4)⁻¹ * x * ((⟨q, hqS⟩ : SUid frob4 4)⁻¹)⁻¹ :
      SUid frob4 4) : GL (Fin 4) F4) =
      (P₀ : GL (Fin 4) F4)⁻¹ * (x : GL (Fin 4) F4) * (P₀ : GL (Fin 4) F4) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact key
  rw [e1]
  exact hdiag

theorem exists_E27_of_isElemAbelian (E : Subgroup (SUid frob4 4)) (hE : IsElemAbelian 3 E) :
    ∃ F : Subgroup (SUid frob4 4), E ≤ F ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 3 := by
  obtain ⟨g, hg⟩ := exists_conj_torus E hE
  refine ⟨torusSU4.range.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx
    refine Subgroup.mem_map.2 ⟨g * x * g⁻¹, hg x hx, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group
  · exact CFSG.SectionRank.isElemAbelian_map isElemAbelian_torusSU4_range _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, card_torusSU4_range]

noncomputable def psp43EquivSU4 : CFSG.GH74.Exceptional.PSp43 ≃* SUid frob4 4 :=
  CFSG.GH74.Exceptional.psp43EquivU2.trans <| CFSG.GH74.Exceptional.u2FourEquiv.trans <|
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot (K := F4)
        (2 ^ 1))).trans <|
    QuotientGroup.quotientBot.trans
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_F4 4).symm)

end FourTwo

section Rows

variable {G : Type} [Group G] [Finite G]

theorem i1024aU42At_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : I1024aU42At G := by
  intro X J E hJ hcat hEJ hE
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hZ := center_pQuot_eq_bot_u4two hGA hq hcat
  obtain ⟨e⟩ := bridge_u4two hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv (e.trans psp43EquivSU4)
  have hk3 : ¬ 3 ∣ Nat.card π.ker := not_three_dvd_card_ker J hkc hZ
  have hmapE : (E.subgroupOf J).map J.subtype = E := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEJ]
  have hE'el : IsElemAbelian 3 (E.subgroupOf J) :=
    isElemAbelian_of_injective_comp_subtype J.subtype
      (fun a b h => Subtype.ext (Subtype.ext h)) (by rw [hmapE]; exact hE)
  have hE'p : IsPGroup 3 (E.subgroupOf J) := isPGroup_of_isElemAbelian hE'el
  have hEπ : IsElemAbelian 3 ((E.subgroupOf J).map π) :=
    CFSG.SectionRank.isElemAbelian_map hE'el π
  obtain ⟨F, hEF, hFel, hFcard⟩ := exists_E27_of_isElemAbelian ((E.subgroupOf J).map π) hEπ
  have hFπ : F ≤ π.range := by
    rw [MonoidHom.range_eq_top_of_surjective π hπs]
    exact le_top
  have hFp : IsPGroup 3 F := isPGroup_of_isElemAbelian hFel
  obtain ⟨W, -, hEW, hWmap, hWinj⟩ :=
    exists_pSubgroup_lift_of_le Nat.prime_three π hk3 hFp hFπ hE'p hEF
  obtain ⟨hWel, hWcard⟩ := map_subtype_isElemAbelian_card π hWmap hWinj hFel
  refine ⟨W.map J.subtype, ?_, ?_, hWel, hWcard.trans hFcard⟩
  · intro x hx
    exact ⟨⟨x, hEJ hx⟩, hEW (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · exact Subgroup.map_subtype_le W

end Rows

section Holds

theorem i1024aU42At_holds (G : Type) [Group G] [Finite G] : I1024aU42At G :=
  i1024aU42At_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB
