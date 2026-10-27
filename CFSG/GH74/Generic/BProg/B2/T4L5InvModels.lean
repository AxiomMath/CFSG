module

public import CFSG.GH74.Generic.BProg.B2.T4L5Inv
public import CFSG.GH74.Generic.BProg.B2.T4S1Assembly
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.GH74.Generic.BProg.B2.GenLocDiagU

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.L5InvModels

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KFU
open scoped Classical

theorem invE8_of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (h : ∀ E : Subgroup J', CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E = 8 →
      ∀ v : J', v * v = 1 → v ≠ 1 → ∃ g : J', g * v * g⁻¹ ∈ E) :
    ∀ E : Subgroup J, CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E = 8 →
      ∀ v : J, v * v = 1 → v ≠ 1 → ∃ g : J, g * v * g⁻¹ ∈ E := by
  intro E hE hE8 v hv hv1
  have hE' : CFSG.IsElementaryAbelian 2 ↥(E.map e.toMonoidHom) := CFSG.IsElementaryAbelian.map _
  have hE8' : Nat.card ↥(E.map e.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, hE8]
  obtain ⟨g, hg⟩ := h _ hE' hE8' (e v) (by rw [← map_mul, hv, map_one])
    (fun h1 => hv1 (e.injective (by rw [h1, map_one])))
  obtain ⟨w, hw, hwe⟩ := hg
  refine ⟨e.symm g, ?_⟩
  have : e.symm g * v * (e.symm g)⁻¹ = w := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hwe.symm
  rw [this]
  exact hw

section Linear

variable {F : Type} [Field F]

theorem mem_statedSL_iff' (A : GL (Fin 5) F) :
    A ∈ StatedSL 5 F ↔ (A : Matrix (Fin 5) (Fin 5) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

noncomputable def diag1 (u : Fˣ) : GL (Fin 5) F := diagU (Pi.mulSingle 0 u)

theorem diag1_isDiag (u : Fˣ) : ((diag1 u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag := by
  rw [diag1, diagU_val]
  exact Matrix.isDiag_diagonal _

theorem det_diag1 (u : Fˣ) : ((diag1 u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = u := by
  rw [diag1, diagU_val, Matrix.det_diagonal, Fin.prod_univ_five]
  simp

@[expose] noncomputable def projSL (F : Type) [Field F] : ↥(StatedSL 5 F) →* LinearFlag.projectiveSL 5 F :=
  (LinearFlag.proj 5 F).comp (specialLinearGroupEquivStatedSL 5 F).symm.toMonoidHom

theorem adj_top : ∀ n ∈ (⊤ : Subgroup (GL (Fin 5) F)), ∃ δ ∈ (⊤ : Subgroup (GL (Fin 5) F)),
    (δ : Matrix (Fin 5) (Fin 5) F).IsDiag ∧
      (n : Matrix (Fin 5) (Fin 5) F).det * (δ : Matrix (Fin 5) (Fin 5) F).det = 1 :=
  fun n _ => ⟨diag1 (Units.mk0 _ (Matrix.isUnits_det_units n).ne_zero)⁻¹, Subgroup.mem_top _,
    diag1_isDiag _, by
      rw [det_diag1, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact mul_inv_cancel₀ (Matrix.isUnits_det_units n).ne_zero⟩

theorem lift_projectiveSL [Finite F] (hF : ringChar F ≠ 2) (D : Subgroup (LinearFlag.projectiveSL 5 F))
    (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ (B : GL (Fin 5) F) (ρ : ↥D →* ↥(StatedSL 5 F)), B ∈ (⊤ : Subgroup (GL (Fin 5) F)) ∧
      (∀ d, projSL F (ρ d) = d) ∧
        ∀ d, ((B⁻¹ * ((ρ d : ↥(StatedSL 5 F)) : GL (Fin 5) F) * B : GL (Fin 5) F) :
          Matrix (Fin 5) (Fin 5) F).IsDiag := by
  let φ : SpecialLinearGroup (Fin 5) F ≃* ↥(StatedSL 5 F) := specialLinearGroupEquivStatedSL 5 F
  obtain ⟨σ, hσπ, hσsq⟩ := GenLocDiag.exists_involutive_section (by decide) D hD
  let ρ : ↥D →* ↥(StatedSL 5 F) := φ.toMonoidHom.comp σ
  have hρπ : ∀ d, projSL F (ρ d) = d := fun d => by
    show LinearFlag.proj 5 F ((specialLinearGroupEquivStatedSL 5 F).symm
      (specialLinearGroupEquivStatedSL 5 F (σ d))) = d
    rw [MulEquiv.symm_apply_apply]
    exact hσπ d
  set T : Subgroup (GL (Fin 5) F) := ρ.range.map (StatedSL 5 F).subtype with hT
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩ _ ⟨_, ⟨d', rfl⟩, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm' d d']
  have hexp : ∀ x ∈ T, x ^ 2 = 1 := by
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    rw [pow_two]
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD d, map_one,
      Subgroup.coe_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime
    ⟨-1, IsPrimitiveRoot.neg_one (ringChar F) hF⟩ T hcomm hexp
  refine ⟨g⁻¹, ρ, Subgroup.mem_top _, hρπ, fun d => ?_⟩
  rw [inv_inv]
  intro i j hij
  exact hg _ ⟨ρ d, ⟨d, rfl⟩, rfl⟩ i j hij

theorem invE8_projectiveSL [Finite F] (hF : ringChar F ≠ 2) :
    ∀ E : Subgroup (LinearFlag.projectiveSL 5 F), CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E = 8 →
      ∀ v : LinearFlag.projectiveSL 5 F, v * v = 1 → v ≠ 1 → ∃ g, g * v * g⁻¹ ∈ E := by
  intro E hE hE8 v hv hv1
  exact L5Inv.exists_conj_mem_of_model (Ring.two_ne_zero hF) (StatedSL 5 F) ⊤
    (fun s hs => (mem_statedSL_iff' s).1 hs) (fun n _ hn => (mem_statedSL_iff' n).2 hn)
    (fun _ => Subgroup.mem_top _) adj_top (projSL F) (lift_projectiveSL hF) E hE hE8 v hv hv1

end Linear

section Unitary

variable {K : Type} [Field K] {p f : ℕ}

theorem permGL5_mem_unitary (h : UnitaryFieldData p f K) (σ : Equiv.Perm (Fin 5)) :
    (L5Inv.permGL5 σ : GL (Fin 5) K) ∈ UnitaryHigher.primeFormUnitary h (1 : Matrix (Fin 5) (Fin 5) K) := by
  rw [UnitaryHigher.mem_primeFormUnitary, Matrix.mul_one, L5Inv.coe_permGL5]
  have hmap : (σ⁻¹.permMatrix K).map h.bar = σ⁻¹.permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  rw [hmap, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

theorem two_ne_zero_of_card [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) :
    (2 : K) ≠ 0 := by
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  intro h0
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff K p] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem mem_formU_iff (h : UnitaryFieldData p f K) (n : GL (Fin 5) K) :
    n ∈ UnitaryHigher.primeFormUnitary h (1 : Matrix (Fin 5) (Fin 5) K) ↔
      ((n : Matrix (Fin 5) (Fin 5) K).map h.bar)ᵀ * (n : Matrix (Fin 5) (Fin 5) K) = 1 := by
  rw [UnitaryHigher.mem_primeFormUnitary, Matrix.mul_one]

theorem adj_unitary (h : UnitaryFieldData p f K) :
    ∀ n ∈ UnitaryHigher.primeFormUnitary h (1 : Matrix (Fin 5) (Fin 5) K),
      ∃ δ ∈ UnitaryHigher.primeFormUnitary h (1 : Matrix (Fin 5) (Fin 5) K),
        (δ : Matrix (Fin 5) (Fin 5) K).IsDiag ∧
          (n : Matrix (Fin 5) (Fin 5) K).det * (δ : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  intro n hn
  set u : Kˣ := (Units.mk0 _ (Matrix.isUnits_det_units n).ne_zero)⁻¹ with hu
  refine ⟨L5InvModels.diag1 u, ?_, L5InvModels.diag1_isDiag u, by
    rw [L5InvModels.det_diag1, hu, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact mul_inv_cancel₀ (Matrix.isUnits_det_units n).ne_zero⟩
  rw [mem_formU_iff, L5InvModels.diag1, diagU_val, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  have hnorm : h.bar (n : Matrix (Fin 5) (Fin 5) K).det * (n : Matrix (Fin 5) (Fin 5) K).det = 1 := by
    have h1 := congrArg Matrix.det ((mem_formU_iff h n).1 hn)
    have h3 : ((n : Matrix (Fin 5) (Fin 5) K).map h.bar).det = h.bar (n : Matrix (Fin 5) (Fin 5) K).det :=
      (RingHom.map_det h.bar _).symm
    rw [Matrix.det_mul, Matrix.det_transpose, h3, Matrix.det_one] at h1
    exact h1
  have hu1 : h.bar (u : K) * (u : K) = 1 := by
    rw [hu, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, ← mul_inv, hnorm, inv_one]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst hi
    simp only [Pi.mulSingle_eq_same]
    exact hu1
  · simp only [Pi.mulSingle_eq_of_ne hi, Units.val_one, map_one, mul_one]

theorem lift_statedSU [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (D : Subgroup (StatedProj (StatedSU 5 (p ^ f) K))) (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ (B : GL (Fin 5) K) (ρ : ↥D →* ↥(StatedSU 5 (p ^ f) K)),
      B ∈ UnitaryHigher.primeFormUnitary (GenLocDiagU.unitaryFieldData_of_card hp hK)
        (1 : Matrix (Fin 5) (Fin 5) K) ∧
      (∀ d, (QuotientGroup.mk' _ : ↥(StatedSU 5 (p ^ f) K) →* StatedProj (StatedSU 5 (p ^ f) K)) (ρ d) = d) ∧
        ∀ d, ((B⁻¹ * ((ρ d : ↥(StatedSU 5 (p ^ f) K)) : GL (Fin 5) K) * B : GL (Fin 5) K) :
          Matrix (Fin 5) (Fin 5) K).IsDiag := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨B, ρ, hB, hρ, hcls⟩ := exists_diag_lift_of_odd_unitary hp hp2 hK (by decide) D hD
  let ρS : ↥D →* ↥(StatedSU 5 (p ^ f) K) := ρ.codRestrict _ (fun d => (hcls d).1)
  refine ⟨B, ρS, ?_, fun d => ?_, fun d => (hρ d).1⟩
  · have hbar : (⇑(GenLocDiagU.unitaryFieldData_of_card hp hK).bar : K → K) = fun c => c ^ p ^ f :=
      funext (UnitaryFieldData.bar_apply _)
    rw [mem_formU_iff, hbar]
    exact hB
  · obtain ⟨hd, hd'⟩ := hcls d
    exact hd'

theorem invE8_statedSU [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) :
    ∀ E : Subgroup (StatedProj (StatedSU 5 (p ^ f) K)), CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E = 8 →
      ∀ v : StatedProj (StatedSU 5 (p ^ f) K), v * v = 1 → v ≠ 1 → ∃ g, g * v * g⁻¹ ∈ E := by
  intro E hE hE8 v hv hv1
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  exact L5Inv.exists_conj_mem_of_model (two_ne_zero_of_card hp hp2 hK) (StatedSU 5 (p ^ f) K)
    (UnitaryHigher.primeFormUnitary h (1 : Matrix (Fin 5) (Fin 5) K))
    (fun s hs => ((ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 hs).1)
    (fun n hn hdet => (ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).2 ⟨hdet, (mem_formU_iff h n).1 hn⟩)
    (permGL5_mem_unitary h) (adj_unitary h) (QuotientGroup.mk' _) (lift_statedSU hp hp2 hK) E hE hE8 v hv hv1

end Unitary

theorem puL5InvE8_proved : T4S1.PuL5InvE8 := by
  intro J _ _ hJ
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hJ
  · obtain ⟨⟨hprime, hf', -⟩, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : J ≃* LinearFlag.projectiveSL 5 F :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
    exact invE8_of_mulEquiv ψ
      (invE8_projectiveSL (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hprime hp2 hF))
  · obtain ⟨⟨hprime, hf', -⟩, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    exact invE8_of_mulEquiv e (invE8_statedSU hprime hp2 hK)

end CFSG.GH74.Generic.BProg.B2.T4.L5InvModels
