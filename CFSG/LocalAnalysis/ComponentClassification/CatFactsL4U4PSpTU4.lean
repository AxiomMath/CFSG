module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTU4Cls
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameU

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank TBlocks
  Subgroup PSpL CFSG.ComponentClassification.GSThmB

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem mem_center_of_map_eq_smul {a : SpecialLinearGroup (Fin 2) h.fixedField} {c : K}
    (ha : (a : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype = c • 1) :
    a ∈ center (SpecialLinearGroup (Fin 2) h.fixedField) := by
  set r : h.fixedField := (a : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 with hr
  have hrc : (r : K) = c := by
    have := congrFun (congrFun ha 0) 0
    simpa using this
  have hsc : (a : Matrix (Fin 2) (Fin 2) h.fixedField) = Matrix.scalar (Fin 2) r := by
    ext i j
    have := congrFun (congrFun ha i) j
    simp only [Matrix.map_apply, Subfield.coe_subtype, Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.scalar_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, this, Matrix.one_apply_eq, mul_one, hrc]
    · rw [Matrix.diagonal_apply_ne _ hij, this, Matrix.one_apply_ne hij, mul_zero]
      rfl
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨r, ?_, hsc.symm⟩
  have hd := a.2
  rw [hsc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hd
  rw [Fintype.card_fin, sq]
  simpa using hd

theorem mem_center_of_ker_bdHomU {R : GL (Fin 4) K} {t : K}
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    {x : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField}
    (hx : x ∈ ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).ker) :
    x.1 ∈ center (SpecialLinearGroup (Fin 2) h.fixedField) ∧
      x.2 ∈ center (SpecialLinearGroup (Fin 2) h.fixedField) := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  obtain ⟨c, hc⟩ := val_of_mem_scal hx
  have h1 : bdK h x = (c : K) • 1 := by
    have e1 : cP R (bdHomU h hR x) = (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((c : K) • 1) * R := by
      rw [cP, hc]
    rw [cP_bdHomU, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one] at e1
    exact e1
  have hul : ul ((c : K) • (1 : Matrix (Fin 4) (Fin 4) K)) = (c : K) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ul]
  have hlr : lr ((c : K) • (1 : Matrix (Fin 4) (Fin 4) K)) = (c : K) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lr]
  refine ⟨mem_center_of_map_eq_smul h (c := (c : K)) ?_, mem_center_of_map_eq_smul h
    (c := (c : K)) ?_⟩
  · have := congrArg ul h1
    rwa [bdK, ul_bd, hul] at this
  · have := congrArg lr h1
    rwa [bdK, lr_bd, hlr] at this

include h in
theorem innerPSpAt_t_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (X : unitarySU p f K 4)
    (hXX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1)
    (hX1 : (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) ≠ 1) :
    InnerPSpAt (p ^ f) p f (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) := by
  classical
  have : Finite K := h.finite
  have hq3 : p ^ f ≠ 3 := by omega
  set θ := QuotientGroup.mk' (scal p f K) with hθ
  have hθX : (QuotientGroup.mk X : StatedProj (StatedSU 4 (p ^ f) K)) = θ X := rfl
  have hscal : ∀ c : K, c ≠ 0 → ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ c • 1 := by
    intro c hc0 hXc
    apply hX1
    rw [QuotientGroup.eq_one_iff]
    change (X : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, hXc, Matrix.smul_one_eq_diagonal]
    rfl
  have h1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1 := by
    have := hscal 1 one_ne_zero
    rwa [one_smul] at this
  have hm1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1 := by
    have := hscal (-1) (neg_ne_zero.mpr one_ne_zero)
    rwa [neg_smul, one_smul] at this
  obtain ⟨R, t, ht0, -, hR, hXR⟩ := exists_frame_t2_U4 h hp2 hq X hXX h1 hm1
  set φ := θ.comp (bdHomU h hR) with hφ
  have hSC : φ.range ≤ centralizer {θ X} := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff, hφ, MonoidHom.comp_apply, ← map_mul, ← map_mul,
      bdHomU_comm h hR hXR x]
  have hNS := centralizerCore516_le_tU h hp2 hq3 ht0 hR hXR
  have hker : ∀ x ∈ φ.ker, x.1 ∈ center (SpecialLinearGroup (Fin 2) h.fixedField) ∧
      x.2 ∈ center (SpecialLinearGroup (Fin 2) h.fixedField) :=
    fun x hx => mem_center_of_ker_bdHomU h hR hx
  have hcardF : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hoddpp : GorensteinWalter.IsOddPrimePower (Nat.card h.fixedField) :=
    ⟨p, f, h.prime, h.prime.odd_of_ne_two hp2, h.one_le, hcardF⟩
  let : Fintype h.fixedField := Fintype.ofFinite _
  have h4F : 4 ≤ Fintype.card h.fixedField := by
    rw [Fintype.card_eq_nat_card, hcardF]
    have h3 : 3 ≤ p := by have := h.prime.two_le; omega
    have hpf : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_prod h4F]
  have hgN : ∀ x ∈ bdGens, θ (bdHomU h hR x) ∈ centralizerCore516 (p ^ f) (θ X) := by
    intro x _
    unfold centralizerCore516
    rw [ite_eq_right hq3]
    exact Quasithin.le_perfectCore_of_perfect hSC hperf ⟨x, rfl⟩
  rw [hθX]
  refine ⟨pPrimeCore_centralizerCore516_eq_bot hSC hNS
    (fun R' hRS hR' hodd => eq_bot_of_odd_block hoddpp φ hker R' hRS hR' hodd),
    fun ε hε2 hε1 hεℓ _ hεN => ?_⟩
  rcases inner_or_psp_t h hp2 hq ht0 hR hXR ε hε2 (fun x hx => hεN _ (hgN x hx)) with
    hh | hh | hM
  · exact absurd hh hε1
  · exact absurd hh hεℓ
  · exact hM

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
