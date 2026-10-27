module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem mem_center_of_isCU_fix {A : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h A α) {Y : unitarySU p f K 4}
    (hY : α (thU p f K Y) = thU p f K Y) :
    (Y : GL (Fin 4) K) * A * (Y : GL (Fin 4) K)⁻¹ * A⁻¹ ∈ Subgroup.center (GL (Fin 4) K) := by
  rw [hα.apply h, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hY
  have hY' : (((⟨_, conj_mem_SU h hα.1 Y⟩ : unitarySU p f K 4)⁻¹ * Y : unitarySU p f K 4) :
      GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := hY
  obtain ⟨c, hc⟩ := hY'
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  change GeneralLinearGroup.scalar (Fin 4) c = (A * (Y : GL (Fin 4) K) * A⁻¹)⁻¹ * Y at hc
  have hcen : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  set z := GeneralLinearGroup.scalar (Fin 4) c with hz
  have e1 : (Y : GL (Fin 4) K) * A * (Y : GL (Fin 4) K)⁻¹ * A⁻¹ =
      (Y : GL (Fin 4) K) * ((A * (Y : GL (Fin 4) K) * A⁻¹)⁻¹ * Y) * (Y : GL (Fin 4) K)⁻¹ := by
    group
  rw [e1, ← hc, Subgroup.mem_center_iff.mp hcen (Y : GL (Fin 4) K), mul_assoc, mul_inv_cancel,
    mul_one]
  exact hcen

include h in
theorem exists_sq_eq_neg_one (hp2 : p ≠ 2) : ∃ i : K, i ^ 2 = -1 := by
  classical
  have : Finite K := h.finite
  let := Fintype.ofFinite K
  have hq : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have hcard : Fintype.card K = (p ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card, ← pow_mul, mul_comm]
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.2 (by
    rw [hcard]
    obtain ⟨t, ht⟩ := hq
    rw [ht]
    ring_nf
    omega)
  exact ⟨i, by rw [sq, hi]⟩

theorem eq_of_perfect_diag (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K} {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hJα : ∀ x ∈ J', α x = x)
    (hJp : ⁅J', J'⁆ = J') (hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J') :
    (∀ c : K, thU p f K (uU h P hP c) ∈ J') ∧ (∀ c : K, thU p f K (uL h P hP c) ∈ J') ∧
      2 * Nat.card J' ≤ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one h hp2
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hi
    exact one_ne_zero (by linear_combination hi : (1 : K) = 0)
  set θ := thU p f K with hθdef
  obtain ⟨C, hC⟩ : ∃ C : Subgroup (unitarySU p f K 4),
      C = (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype := ⟨_, rfl⟩
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAm : (A : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hAP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hmemC_iff : ∀ g : unitarySU p f K 4, g ∈ C ↔ cP P g * X1 l = X1 l * cP P g := by
    intro g
    rw [hC, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have e := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K)) hg
      simp only [Units.val_mul] at e
      rw [hAm] at e
      have e' := congrArg (fun M => (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * M *
        (P : Matrix (Fin 4) (Fin 4) K)) e
      simp only [Matrix.mul_assoc, hPP', Matrix.mul_one] at e'
      simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul] at e'
      simpa only [cP, Matrix.mul_assoc] using e'
    · intro hg
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hAm, val_eq_cP P g]
      have e1 : (P : Matrix (Fin 4) (Fin 4) K) * cP P g * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
          (P : Matrix (Fin 4) (Fin 4) K) * (cP P g * X1 l) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
          hPP', Matrix.one_mul]
      have e2 : (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((P : Matrix (Fin 4) (Fin 4) K) * cP P g * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
          (P : Matrix (Fin 4) (Fin 4) K) * (X1 l * cP P g) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
          hPP', Matrix.one_mul]
      rw [e1, e2, hg]
  have hcomm_le : ⁅J', J'⁆ ≤ C.map θ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨Y₁, rfl⟩ := thU_surjective u
    obtain ⟨Y₂, rfl⟩ := thU_surjective v
    refine ⟨⁅Y₁, Y₂⁆, ?_, by rw [map_commutatorElement]⟩
    rw [hC, SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement,
      Subgroup.mem_centralizer_singleton_iff]
    exact commutator_comm_of_comm_mod (le_refl _) (mem_center_of_isCU_fix h hα (hJα _ hu))
      (mem_center_of_isCU_fix h hα (hJα _ hv))
  have hJC : J' ≤ (⁅C, C⁆).map θ := by
    have h1 : J' ≤ C.map θ := by
      rw [← hJp]
      exact hcomm_le
    rw [Subgroup.map_commutator, ← hJp]
    exact Subgroup.commutator_mono h1 h1
  have hBD : ∀ g ∈ C, IsBD (cP P g) := fun g hg => isBD_of_comm_X1 h2K hl0 ((hmemC_iff g).1 hg)
  let β : C →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => ul (cP P g.1)
      map_one' := by
        change ul (cP P (1 : unitarySU p f K 4)) = 1
        rw [cP_one, ul_one]
      map_mul' := fun g g' => by
        change ul (cP P (g.1 * g'.1)) = ul (cP P g.1) * ul (cP P g'.1)
        rw [cP_mul, ul_mul (hBD g.1 g.2) (hBD g'.1 g'.2)] }
  have hβ : ∀ g : C, β g = ul (cP P g.1) := fun g => rfl
  have hβinj : Function.Injective β := by
    intro g g' hgg
    have h1 : β (g⁻¹ * g') = 1 := by
      rw [map_mul, ← hgg, ← map_mul, inv_mul_cancel, map_one]
    rw [hβ] at h1
    have h2 := eq_one_of_ul_eq_one h (hBD _ (g⁻¹ * g').2) (unitary_cP h P hP _) h1
    have h3 : (g⁻¹ * g').1 = 1 := eq_of_cP_eq P (by rw [h2, cP_one])
    have h4 : g⁻¹ * g' = 1 := Subtype.ext h3
    rw [← inv_mul_eq_one, h4]
  let δ : C →* Kˣ := (Matrix.detMonoidHom.comp β).toHomUnits
  have hSC : ⁅C, C⁆ ≤ C := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hS : ⁅C, C⁆ ≤ δ.ker.map C.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : C), (⟨b, hb⟩ : C)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  let F : ↥(⁅C, C⁆ : Subgroup (unitarySU p f K 4)) → SpecialLinearGroup (Fin 2) K := fun x =>
    ⟨β ⟨x.1, hSC x.2⟩, by
      obtain ⟨y, hy, hyx⟩ := hS x.2
      have hy' : y = ⟨x.1, hSC x.2⟩ := Subtype.ext hyx
      rw [← hy']
      have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
      simpa [δ] using this⟩
  have hF : Function.Injective F := by
    intro x y hxy
    have h1 : β ⟨x.1, hSC x.2⟩ = β ⟨y.1, hSC y.2⟩ := congrArg Subtype.val hxy
    have h2 := hβinj h1
    exact Subtype.ext (congrArg (fun z : C => (z : unitarySU p f K 4)) h2)
  have hKcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hcardS : Nat.card (⁅C, C⁆ : Subgroup (unitarySU p f K 4)) ≤
      (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
    calc Nat.card (⁅C, C⁆ : Subgroup (unitarySU p f K 4)) ≤
          Nat.card (SpecialLinearGroup (Fin 2) K) := Nat.card_le_card_of_injective F hF
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := by
          let := Fintype.ofFinite K
          have hq : 1 < Fintype.card K := Fintype.one_lt_card
          rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
            Fin.val_one, pow_zero, pow_one, Nat.card_eq_fintype_card,
            show Fintype.card K ^ 2 - Fintype.card K =
              Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
            Nat.mul_div_cancel _ (by omega), mul_comm]
      _ = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
          rw [hKcard, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring]
  set a := hypSU h P hP (Hd h i) (unitary_Hd h hi0) (det_Hd h hi0) with ha
  have haC : a ∈ C := (hmemC_iff a).2 (by rw [ha, cP_hypSU]; exact Hd_comm_X1 h i l)
  have hainv : Hd h i⁻¹ * cP P a = 1 := by
    rw [ha, cP_hypSU]
    have := Hd_mul_Hd_inv h (inv_ne_zero hi0)
    rwa [inv_inv] at this
  set b := hypSU h P hP Wm (unitary_Wm h) det_Wm with hb
  have hbC : b ∈ C := (hmemC_iff b).2 (by rw [hb, cP_hypSU]; exact Wm_comm_X1 l)
  have hz : cP P ⁅a, b⁆ = -1 := by
    rw [cP_commutator P hainv (show -Wm * cP P b = 1 by rw [hb, cP_hypSU]; exact neg_Wm_mul_Wm),
      ha, hb, cP_hypSU, cP_hypSU]
    exact commutator_Hd_Wm h hi
  have hzS : ⁅a, b⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator haC hbC
  have hz1 : ⁅a, b⁆ ≠ 1 := by
    intro h1
    have := congrFun (congrFun hz 0) 0
    rw [h1, cP_one] at this
    simp only [Matrix.one_apply_eq, Matrix.neg_apply] at this
    exact h2K (by linear_combination this)
  have hzθ : θ ⁅a, b⁆ = 1 := by
    rw [hθdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    show ((⁅a, b⁆ : unitarySU p f K 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K
    refine ⟨-1, Units.ext ?_⟩
    rw [val_eq_cP P, hz, GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one,
      Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, map_neg, map_one]
  have hcardJ : 2 * Nat.card ((⁅C, C⁆ : Subgroup (unitarySU p f K 4)).map θ) ≤
      (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
    set φ : (⁅C, C⁆ : Subgroup (unitarySU p f K 4)) →* StatedProj (StatedSU 4 (p ^ f) K) :=
      θ.comp (⁅C, C⁆ : Subgroup (unitarySU p f K 4)).subtype with hφ
    have hrange : φ.range = (⁅C, C⁆ : Subgroup (unitarySU p f K 4)).map θ := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : 2 ≤ Nat.card φ.ker := by
      have : 1 < Nat.card φ.ker := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hbot
        have hmem : (⟨⁅a, b⁆, hzS⟩ : (⁅C, C⁆ : Subgroup (unitarySU p f K 4))) ∈ φ.ker := by
          rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype]
          exact hzθ
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hz1 (congrArg Subtype.val hmem)
      omega
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hrange] at hmul
    calc 2 * Nat.card ((⁅C, C⁆ : Subgroup (unitarySU p f K 4)).map θ) ≤
        Nat.card φ.ker * Nat.card ((⁅C, C⁆ : Subgroup (unitarySU p f K 4)).map θ) :=
          Nat.mul_le_mul_right _ hker
      _ = Nat.card (⁅C, C⁆ : Subgroup (unitarySU p f K 4)) := hmul
      _ ≤ _ := hcardS
  have hJeq : J' = (⁅C, C⁆ : Subgroup (unitarySU p f K 4)).map θ :=
    Subgroup.eq_of_le_of_card_ge hJC (by omega)
  have hc2 : ∀ c : K, (i ^ 2 - 1) * (-(c / 2)) = c := fun c => by
    rw [hi]
    field_simp
    ring
  have hc2' : ∀ c : K, (i⁻¹ ^ 2 - 1) * (-(c / 2)) = c := fun c => by
    rw [inv_pow, hi]
    field_simp
    ring
  have hU : ∀ c : K, uU h P hP c ∈ ⁅C, C⁆ := by
    intro c
    set u := uU h P hP (-(c / 2)) with hu
    have huC : u ∈ C := (hmemC_iff u).2 (by rw [hu, cP_uU]; exact U12_comm_X1 h _ l)
    have hinv : U12 h (-(-(c / 2))) * cP P u = 1 := by
      rw [hu, cP_uU, U12_mul, neg_add_cancel, U12_zero]
    have e : ⁅a, u⁆ = uU h P hP c := by
      apply eq_of_cP_eq P
      rw [cP_commutator P hainv hinv, ha, hu, cP_hypSU, cP_uU, cP_uU, Hd_comm_U12 h hi0, hc2]
    rw [← e]
    exact Subgroup.commutator_mem_commutator haC huC
  have hL : ∀ c : K, uL h P hP c ∈ ⁅C, C⁆ := by
    intro c
    set u := uL h P hP (-(c / 2)) with hu
    have huC : u ∈ C := (hmemC_iff u).2 (by rw [hu, cP_uL]; exact U21_comm_X1 h _ l)
    have hinv : U21 h (-(-(c / 2))) * cP P u = 1 := by
      rw [hu, cP_uL, U21_mul, neg_add_cancel, U21_zero]
    have e : ⁅a, u⁆ = uL h P hP c := by
      apply eq_of_cP_eq P
      rw [cP_commutator P hainv hinv, ha, hu, cP_hypSU, cP_uL, cP_uL, Hd_comm_U21 h hi0, hc2']
    rw [← e]
    exact Subgroup.commutator_mem_commutator haC huC
  refine ⟨fun c => ?_, fun c => ?_, by rw [hJeq]; exact hcardJ⟩
  · rw [hJeq]
    exact ⟨_, hU c, rfl⟩
  · rw [hJeq]
    exact ⟨_, hL c, rfl⟩

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
