module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8BlkGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5LinBlk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open Matrix
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield mem_fixSubfield)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (compIndicator)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  (coordBlockSU mem_coordBlockSU_iff_indicator)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp (statedSU_eq_gramSU)
open CFSG.LocalAnalysis.GLTheoremA.S265F5 (diagonal_mul_comm_of_fiber)

variable {K : Type} [Field K]

theorem exists_coordBlockSU_eq_conj {f : ℕ} (h : UnitaryFieldData 2 f K) {σ : K ≃+* K}
    [Finite (fixSubfield σ)] [CharP (fixSubfield σ) 2] (h₀ : UnitaryFieldData 2 1 (fixSubfield σ))
    (hbar₀ : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) {n : ℕ}
    {X₀ : primeFormUnitary h (idGram K n)} {e : Fin n → K}
    (hX₀ : ((X₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal e) {J : Finset (Fin n)}
    (hJe : ∀ l, l ∈ J ↔ e l = 1) (hJ : Jᶜ.card < J.card) {Y : gramSU h (idGram K n)}
    (hYσ : (Y : primeFormP h (idGram K n)) ∈
      fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ))
    (hYX : (Y : primeFormP h (idGram K n)) ∈ fixSubgroup (primeFormConjHom h (idGram K n) X₀))
    {B : Su (fixSubfield σ) 2 1 n} (hB : B ∈ coordBlockSU (fixSubfield σ) 2 1 J) :
    ∃ Z ∈ coordBlockSU (fixSubfield σ) 2 1 J,
      subfieldGL (fixSubfield σ) n (Z : GL (Fin n) (fixSubfield σ)) =
        (Y : GL (Fin n) K) * subfieldGL (fixSubfield σ) n (B : GL (Fin n) (fixSubfield σ)) *
          (Y : GL (Fin n) K)⁻¹ := by
  classical
  set K₀ := fixSubfield σ with hK₀def
  haveI : Finite K₀ := h₀.finite
  haveI : CharP K₀ 2 := h₀.charP
  set hC := isPrimeFormGram_idGram (K := K) (n := n) with hCdef
  have heq₀ : SUid (unitaryInvolution K₀ 2 1) n = gramSU h₀ (idGram K₀ n) :=
    (SUid_eq_statedSU (h₀.card.trans (by norm_num)) n).trans (statedSU_eq_gramSU h₀ n)
  have hσB : ∀ g : GL (Fin n) K₀, glAut σ (subfieldGL K₀ n g) = subfieldGL K₀ n g := by
    intro g
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact (mem_fixSubfield σ).1 ((g : Matrix (Fin n) (Fin n) K₀) i j).2
  have hPmap : (compIndicator K₀ J).map K₀.subtype = compIndicator K J := by
    rw [compIndicator, compIndicator, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  rw [mem_fixSubgroup] at hYσ hYX
  rw [primeFormConjHom_mk, QuotientGroup.eq] at hYX
  obtain ⟨ν, -, -, hν⟩ := hYX
  have hν' : ((X₀ : GL (Fin n) K) * Y * (X₀ : GL (Fin n) K)⁻¹)⁻¹ * (Y : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) ν := hν
  set s := GeneralLinearGroup.scalar (Fin n) ν with hs
  have hsc : ∀ g : GL (Fin n) K, s * g = g * s := fun g =>
    GeneralLinearGroup.scalar_commute ν g
  have hYX' : (Y : GL (Fin n) K) * X₀ = s * ((X₀ : GL (Fin n) K) * Y) := by
    have h1 : (Y : GL (Fin n) K) = (X₀ : GL (Fin n) K) * Y * (X₀ : GL (Fin n) K)⁻¹ * s := by
      rw [← hν', mul_inv_cancel_left]
    nth_rewrite 1 [h1]
    rw [mul_assoc _ s, hsc, ← mul_assoc, inv_mul_cancel_right, ← hsc]
  have hYXm : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal e =
      (ν : K) • (diagonal e * ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hYX'
    simp only [Units.val_mul, hs, GeneralLinearGroup.coe_scalar, hX₀] at h2
    rw [h2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hdet : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [(mem_gramSU.1 Y.2).2]
    exact one_ne_zero
  have hYd : diagonal e * ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal e := by
    rw [hYXm, eq_one_of_mul_diagonal_eq_smul hJe hJ hdet hYXm, one_smul]
  have hYP : compIndicator K J * ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compIndicator K J := by
    rw [compIndicator]
    refine diagonal_mul_comm_of_fiber (fun i j hij => ?_) hYd
    simp only [hJe, hij]
  have hYσ' : primeFormFieldAut h hC σ (Y : primeFormP h (idGram K n)) = Y := hYσ
  rw [primeFormFieldAut_mk, QuotientGroup.eq] at hYσ'
  obtain ⟨w, -, -, hw⟩ := hYσ'
  have hw' : (glAut σ (Y : GL (Fin n) K))⁻¹ * (Y : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) w := hw
  have hσY : glAut σ (Y : GL (Fin n) K) =
      (Y : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) w)⁻¹ := by
    rw [← hw', _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : GL (Fin n) K₀, B₀ = (B : GL (Fin n) K₀) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) K, u = (Y : GL (Fin n) K) := ⟨_, rfl⟩
  rw [← hu] at hσY hYP
  have humem : u ∈ gramSU h (idGram K n) := hu ▸ Y.2
  have hBmem : subfieldGL K₀ n B₀ ∈ gramSU h (idGram K n) := by
    rw [hB₀]
    exact (subfieldSU h h₀ hbar₀ n ⟨_, (SetLike.ext_iff.1 heq₀ _).1 B.2⟩).2
  have hsB : (GeneralLinearGroup.scalar (Fin n) w)⁻¹ * subfieldGL K₀ n B₀ =
      subfieldGL K₀ n B₀ * (GeneralLinearGroup.scalar (Fin n) w)⁻¹ :=
    (show Commute (GeneralLinearGroup.scalar (Fin n) w) (subfieldGL K₀ n B₀) from
      GeneralLinearGroup.scalar_commute w _).inv_left.eq
  obtain ⟨Z, hZ⟩ : ∃ Z : GL (Fin n) K, Z = u * subfieldGL K₀ n B₀ * u⁻¹ := ⟨_, rfl⟩
  have hZσ : glAut σ Z = Z := by
    rw [hZ, map_mul, map_mul, map_inv, hσY, hσB]
    calc u * (GeneralLinearGroup.scalar (Fin n) w)⁻¹ * subfieldGL K₀ n B₀ *
          (u * (GeneralLinearGroup.scalar (Fin n) w)⁻¹)⁻¹
        = u * ((GeneralLinearGroup.scalar (Fin n) w)⁻¹ * subfieldGL K₀ n B₀) *
            GeneralLinearGroup.scalar (Fin n) w * u⁻¹ := by group
      _ = u * (subfieldGL K₀ n B₀ * (GeneralLinearGroup.scalar (Fin n) w)⁻¹) *
            GeneralLinearGroup.scalar (Fin n) w * u⁻¹ := by rw [hsB]
      _ = u * subfieldGL K₀ n B₀ * u⁻¹ := by group
  have hZmem : Z ∈ gramSU h (idGram K n) := by
    rw [hZ]
    exact mul_mem (mul_mem humem hBmem) (inv_mem humem)
  obtain ⟨Z₀, hZ₀⟩ := exists_subfieldGL_eq_of_fixed n hZσ
  have hZ₀g : Z₀ ∈ gramSU h₀ (idGram K₀ n) :=
    mem_gramSU_of_subfieldGL h n h₀ hbar₀ (g₀ := Z₀) (by rw [hZ₀]; exact hZmem)
  have hB' : B ∈ coordBlockSU K₀ 2 1 J := hB
  obtain ⟨hg1, hg2⟩ := mem_coordBlockSU_iff_indicator.1 hB'
  rw [← hB₀] at hg1 hg2
  have hPB := congrArg (fun M : Matrix (Fin n) (Fin n) K₀ => M.map K₀.subtype) hg1
  have hBP := congrArg (fun M : Matrix (Fin n) (Fin n) K₀ => M.map K₀.subtype) hg2
  simp only [Matrix.map_mul, hPmap] at hPB hBP
  obtain ⟨hPZ, hZP⟩ := mul_conj_eq_of_mul_eq
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hYP hPB hBP
  have hZ₀m : (Z₀ : Matrix (Fin n) (Fin n) K₀).map K₀.subtype =
      (u : Matrix (Fin n) (Fin n) K) * (B₀ : Matrix (Fin n) (Fin n) K₀).map K₀.subtype *
        ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← coe_subfieldGL, hZ₀, hZ, Units.val_mul, Units.val_mul, coe_subfieldGL]
  have hinj := Matrix.map_injective (m := Fin n) (n := Fin n)
    (f := (K₀.subtype : K₀ → K)) Subtype.val_injective
  set Z₀s : Su K₀ 2 1 n := ⟨Z₀, (SetLike.ext_iff.1 heq₀ Z₀).2 hZ₀g⟩
  have hZ₀J : Z₀s ∈ coordBlockSU K₀ 2 1 J := by
    rw [mem_coordBlockSU_iff_indicator]
    refine ⟨hinj ?_, hinj ?_⟩
    · change (compIndicator K₀ J * (Z₀ : Matrix (Fin n) (Fin n) K₀)).map K₀.subtype =
        (compIndicator K₀ J).map K₀.subtype
      rw [Matrix.map_mul, hPmap, hZ₀m, hPZ]
    · change ((Z₀ : Matrix (Fin n) (Fin n) K₀) * compIndicator K₀ J).map K₀.subtype =
        (compIndicator K₀ J).map K₀.subtype
      rw [Matrix.map_mul, hPmap, hZ₀m, hZP]
  refine ⟨Z₀s, hZ₀J, ?_⟩
  show subfieldGL K₀ n Z₀ = (Y : GL (Fin n) K) * subfieldGL K₀ n (B : GL (Fin n) K₀) *
    (Y : GL (Fin n) K)⁻¹
  rw [hZ₀, hZ, hu, hB₀]

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
