module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLModel
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical CFSG.LieType.Chevalley Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut primeFormP)

variable {p f : ℕ} {F : Type} [Field F]

theorem bglu_mem_fixGL_iff (σ : F ≃+* F) (g : GL (Fin 3) F) :
    g ∈ BGL.fixGL σ ↔ glAut σ g = g := by
  change GeneralLinearGroup.map σ.toRingHom g = g ↔ glAut σ g = g
  constructor
  · intro h
    exact Units.ext (congrArg Units.val h)
  · intro h
    exact Units.ext (congrArg Units.val h)

@[expose] def bgluSub (hF : UnitaryFieldData p f F) (σ : F ≃+* F) : Subgroup (unitaryPSU hF 3) :=
  ((unitarySU p f F 3 ⊓ BGL.fixGL σ).subgroupOf (unitarySU p f F 3)).map (unitaryProj hF 3)

theorem mem_bgluSub {hF : UnitaryFieldData p f F} {σ : F ≃+* F} {x : unitaryPSU hF 3} :
    x ∈ bgluSub hF σ ↔ ∃ S : unitarySU p f F 3, glAut σ (S : GL (Fin 3) F) = S ∧
      unitaryProj hF 3 S = x := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    refine ⟨S, ?_, rfl⟩
    have hS' : (S : GL (Fin 3) F) ∈ unitarySU p f F 3 ⊓ BGL.fixGL σ := hS
    exact (bglu_mem_fixGL_iff σ _).1 hS'.2
  · rintro ⟨S, hS, rfl⟩
    refine ⟨S, ?_, rfl⟩
    change (S : GL (Fin 3) F) ∈ unitarySU p f F 3 ⊓ BGL.fixGL σ
    exact ⟨S.2, (bglu_mem_fixGL_iff σ _).2 hS⟩

theorem bgluSub_le_fix (hF : UnitaryFieldData p f F) (σ : F ≃+* F) :
    bgluSub hF σ ≤ fixSubgroup (psuField hF σ) := by
  intro x hx
  obtain ⟨S, hS, rfl⟩ := mem_bgluSub.1 hx
  rw [mem_fixSubgroup]
  change psuField hF σ (S : unitaryPSU hF 3) = (S : unitaryPSU hF 3)
  rw [psuField_mk]
  congr 1
  exact Subtype.ext hS

theorem bgluSub_normal (hF : UnitaryFieldData p f F) (σ : F ≃+* F) :
    ((bgluSub hF σ).subgroupOf (fixSubgroup (psuField hF σ))).Normal := by
  refine ⟨fun a ha y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  obtain ⟨S, hS, hSa⟩ := mem_bgluSub.1 ha
  obtain ⟨G, hG⟩ := unitaryProj_surjective hF 3 (y : unitaryPSU hF 3)
  have hy : psuField hF σ (y : unitaryPSU hF 3) = y := y.2
  rw [← hG] at hy
  have hy' : unitaryProj hF 3 (suField hF σ G) = unitaryProj hF 3 G := hy
  have hw : G⁻¹ * suField hF σ G ∈ unitaryScalars hF 3 := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hy', inv_mul_cancel]
  have hwc := unitaryScalars_le_center hF 3 hw
  set w := G⁻¹ * suField hF σ G with hwdef
  have hmapG : suField hF σ G = G * w := by rw [hwdef]; group
  have hmapS : suField hF σ S = S := Subtype.ext hS
  have hSw : S * w = w * S := Subgroup.mem_center_iff.1 hwc S
  refine mem_bgluSub.2 ⟨G * S * G⁻¹, ?_, ?_⟩
  · have hT : suField hF σ (G * S * G⁻¹) = G * S * G⁻¹ := by
      rw [map_mul, map_mul, map_inv, hmapG, hmapS]
      calc G * w * S * (G * w)⁻¹ = G * (w * S * w⁻¹) * G⁻¹ := by group
        _ = G * S * G⁻¹ := by rw [← hSw]; group
    exact congrArg Subtype.val hT
  · change unitaryProj hF 3 (G * S * G⁻¹) =
      (y : unitaryPSU hF 3) * (a : unitaryPSU hF 3) * (y : unitaryPSU hF 3)⁻¹
    rw [map_mul, map_mul, map_inv, hG, hSa]

section Subfield

theorem bglu_psuPrimeFormEquiv_mk (hF : UnitaryFieldData p f F) (g : unitarySU p f F 3) :
    psuPrimeFormEquiv hF (g : unitaryPSU hF 3) =
      ((suGramEquiv hF g : gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
        primeFormP hF _) :=
  rfl

theorem bglu_h₀ (hF : UnitaryFieldData p f F) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    UnitaryFieldData p (f / 3) (fixSubfield σ) :=
  fixSubfield_unitaryFieldData hF Nat.prime_three (by norm_num) hσ

theorem bglu_hbar (hF : UnitaryFieldData p f F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (c : fixSubfield σ) :
    (((bglu_h₀ hF hσ).bar c : fixSubfield σ) : F) = hF.bar c :=
  fixSubfield_unitaryFieldData_bar hF Nat.prime_three (by norm_num) hσ c

theorem bgluSub_map_eq_range (hF : UnitaryFieldData p f F) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    (bgluSub hF σ).map (psuPrimeFormEquiv hF).toMonoidHom =
      (subfieldPSU hF (bglu_h₀ hF hσ) (bglu_hbar hF hσ) 3).range := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨S, hS, rfl⟩ := mem_bgluSub.1 hx
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed 3 hS
    have hSg : (S : GL (Fin 3) F) ∈ gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← unitarySU_three_eq_gramSU hF]
      exact S.2
    have hg₀mem := mem_gramSU_of_subfieldGL hF 3 (bglu_h₀ hF hσ) (bglu_hbar hF hσ) (g₀ := g₀)
      (by rw [hg₀]; exact hSg)
    refine ⟨((⟨g₀, hg₀mem⟩ : gramSU (bglu_h₀ hF hσ) _) : primeFormP (bglu_h₀ hF hσ) _), ?_⟩
    rw [subfieldPSU_mk]
    change _ = psuPrimeFormEquiv hF (S : unitaryPSU hF 3)
    rw [bglu_psuPrimeFormEquiv_mk]
    congr 1
    exact Subtype.ext hg₀
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H g =>
      set T : gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
        subfieldSU hF (bglu_h₀ hF hσ) (bglu_hbar hF hσ) 3 g with hT
      set S : unitarySU p f F 3 := (suGramEquiv hF).symm T with hS
      have hST : (S : GL (Fin 3) F) = T := rfl
      have hfix : glAut σ (S : GL (Fin 3) F) = S := by
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [coe_glAut, Matrix.map_apply, hST, hT, coe_subfieldSU, coe_subfieldGL, Matrix.map_apply]
        exact (((g : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) i j).2
      refine ⟨(S : unitaryPSU hF 3), mem_bgluSub.2 ⟨S, hfix, rfl⟩, ?_⟩
      change psuPrimeFormEquiv hF (S : unitaryPSU hF 3) = _
      rw [subfieldPSU_mk, bglu_psuPrimeFormEquiv_mk]
      congr 1

@[expose] noncomputable def bgluSubEquiv (hF : UnitaryFieldData p f F) {σ : F ≃+* F}
    (hσ : orderOf σ = 3) :
    bgluSub hF σ ≃* primeFormP (bglu_h₀ hF hσ) ((1 : GL (Fin 3) (fixSubfield σ)) :
      Matrix (Fin 3) (Fin 3) (fixSubfield σ)) :=
  ((Subgroup.equivMapOfInjective _ (psuPrimeFormEquiv hF).toMonoidHom
      (psuPrimeFormEquiv hF).injective).trans
    (MulEquiv.subgroupCongr (bgluSub_map_eq_range hF hσ))).trans
    (MonoidHom.ofInjective (subfieldPSU_injective hF (bglu_h₀ hF hσ) (bglu_hbar hF hσ) 3
      (by norm_num))).symm

end Subfield

section Three

variable {ℓ e : ℕ} {L : Type} [Field L] (h₀ : UnitaryFieldData ℓ e L)

theorem three_dvd_card_primeFormP_one :
    3 ∣ Nat.card (primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) := by
  have hsign : Equiv.Perm.sign (finRotate 3) = 1 := by
    rw [sign_finRotate]
    norm_num
  have hmem := unitaryPermGL_mem_gramSU (L := L) h₀ hsign
  have hc3 : finRotate 3 * finRotate 3 * finRotate 3 = 1 := by
    refine Equiv.ext fun i => ?_
    fin_cases i <;> rfl
  have hU : ∀ π τ : Equiv.Perm (Fin 3), (unitaryPermGL (π * τ) : GL (Fin 3) L) =
      unitaryPermGL τ * unitaryPermGL π := fun π τ => Units.ext (by
    rw [Units.val_mul, coe_unitaryPermGL, coe_unitaryPermGL, coe_unitaryPermGL,
      Matrix.permMatrix_mul])
  have hU1 : (unitaryPermGL (1 : Equiv.Perm (Fin 3)) : GL (Fin 3) L) = 1 :=
    Units.ext (by rw [coe_unitaryPermGL, Matrix.permMatrix_one]; rfl)
  have hG3 : (unitaryPermGL (finRotate 3) : GL (Fin 3) L) ^ 3 = 1 := by
    rw [pow_three, ← hU, ← hU, hc3, hU1]
  have hP3 : (⟨unitaryPermGL (finRotate 3), hmem⟩ :
      gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) ^ 3 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hG3)
  have h0 : (finRotate 3) 0 ≠ 0 := by
    rw [finRotate_apply_zero]
    decide
  have hP1 : ((⟨unitaryPermGL (finRotate 3), hmem⟩ :
      gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) : primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, -, -, hc⟩ := h1
    have h00 : ((unitaryPermGL (finRotate 3) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 0 =
        ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 0 :=
      congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L) 0 0) hc
    rw [coe_unitaryPermGL, CFSG.RankThree.Classical.permMatrix_apply', ite_eq_right h0,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
    exact c.ne_zero h00.symm
  have hord : orderOf ((⟨unitaryPermGL (finRotate 3), hmem⟩ :
      gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) : primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ hP1
    have h3 := congrArg (QuotientGroup.mk' (normOneScalars h₀
      (gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) 3)) hP3
    rw [map_pow, map_one] at h3
    exact h3
  have hd := orderOf_dvd_natCard ((⟨unitaryPermGL (finRotate 3), hmem⟩ :
      gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) :
    primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L))
  rwa [hord] at hd

end Three

theorem bgluSub_nsp (hF : UnitaryFieldData p f F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (hq8 : p ^ f ≠ 8) : BglNSP (psuField hF σ) (bgluSub hF σ) := by
  have hdvd := (dvd_and_card_fixSubfield_unitary hF Nat.prime_three (by norm_num) hσ).1
  have hq₀ : ¬(3 = 3 ∧ p ^ (f / 3) = 2) := by
    rintro ⟨-, h2⟩
    apply hq8
    rw [← Nat.mul_div_cancel' hdvd, pow_mul', h2]
    norm_num
  set e := bgluSubEquiv hF hσ
  have hsimple := isSimpleGroup_primeFormP_one (bglu_h₀ hF hσ) (n := 3) le_rfl hq₀
  have hnc := not_commute_primeFormP_one (bglu_h₀ hF hσ) (n := 3) le_rfl hq₀
  refine ⟨bgluSub_le_fix hF σ, bgluSub_normal hF σ, e.isSimpleGroup, ?_, ?_⟩
  · by_contra hcon
    apply hnc
    intro x y
    by_contra hxy
    apply hcon
    refine ⟨e.symm x, e.symm y, fun hc => hxy (e.symm.injective ?_)⟩
    rw [map_mul, map_mul, hc]
  · rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_primeFormP_one (bglu_h₀ hF hσ)

end CFSG.HardMathSupport.Solomon.Coordinator
