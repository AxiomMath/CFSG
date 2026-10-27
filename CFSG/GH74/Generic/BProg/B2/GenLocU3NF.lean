module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3Lift
import CFSG.GH74.Generic.BProg.B2.GenLocDiagU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocU3NF

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift

variable {p f : ℕ} {F : Type} [Field F] {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J}

theorem exists_frame (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq : 3 ≤ p ^ f)
    (hθ : IsCover h θ) (hinj : Function.Injective (MulAut.conj : J →* MulAut J))
    {D : Subgroup (MulAut J)} (hD : CFSG.IsElementaryAbelian 2 ↥D) {u : MulAut J} (huD : u ∈ D)
    (hu : ∀ y : J, MulAut.conj y ≠ u) :
    ∃ C : GL (Fin 3) F,
      ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      ∀ x ∈ D, FrameForm h θ C x := by
  classical
  have hFin : Finite F := h.finite
  have : Finite J := Finite.of_surjective θ hθ.surj
  obtain ⟨hab, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  have h2 := GenLocU3Desc.two_ne_zero' h hp2
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  have hPerf : Group.IsPerfect ↥(unitarySU p f F 3) :=
    (CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (le_refl 3)).1
  set E : Subgroup J := D.comap (MulAut.conj : J →* MulAut J) with hEdef
  have hE : CFSG.IsElementaryAbelian 2 ↥E := by
    refine WeakSigGen.isElementaryAbelian_of_forall
      (fun a ha b hb => hinj ?_) (fun a ha => hinj ?_)
    · rw [map_mul, map_mul]; exact hab _ ha _ hb
    · rw [map_mul, map_one]; exact hsq _ ha
  have hodd : ¬ 2 ∣ Nat.card θ.ker := by
    rw [hθ.ker, card_unitaryScalars h (by norm_num : 1 ≤ 3)]
    intro h2'
    have := h2'.trans (Nat.gcd_dvd_left 3 (p ^ f + 1))
    omega
  obtain ⟨σ, hσθ, hσsq⟩ := GenLocDiagU.exists_involutive_section_of_odd_ker
    θ hθ.surj hodd E hE
  let R : ↥E → GL (Fin 3) F := fun e => ((σ e : ↥(unitarySU p f F 3)) : GL (Fin 3) F)
  have hRu : ∀ e, (((R e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((R e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := fun e =>
    ((mem_unitarySU_iff h).1 (σ e).2).2
  have hRdet : ∀ e, ((R e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := fun e =>
    ((mem_unitarySU_iff h).1 (σ e).2).1
  have hRsq : ∀ e, R e * R e = 1 := fun e => by
    have := congrArg Subtype.val (hσsq e)
    simpa using this
  have hRcomm : ∀ e e', R e * R e' = R e' * R e := fun e e' => by
    have h1 : σ e * σ e' = σ e' * σ e := by rw [← map_mul, ← map_mul, mul_comm' e e']
    have := congrArg Subtype.val h1
    simpa using this
  obtain ⟨φ, A, hφ, hAu, hAA, hlu⟩ := exists_typeII h hp2 hq hθ (hsq u huD) hu
  have hlR : ∀ e : ↥E, IsLift θ (R e) 1 (MulAut.conj (e : J)) := fun e => isLift_conj (hσθ e)
  have hφmap : ∀ M : Matrix (Fin 3) (Fin 3) F, M.map φ = M.map h.bar := fun M =>
    Matrix.ext fun i j => hφ _
  have hAdet : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
  have hAR : ∀ e, (A : Matrix (Fin 3) (Fin 3) F) *
      ((R e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
      ((R e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    intro e
    have hcomm := hab u huD (MulAut.conj (e : J)) e.2
    obtain ⟨c, hc⟩ := IsLift.comm h h2 hPerf hker hlu (hlR e) (by rw [mul_one, one_mul]) hcomm
    rw [hφmap] at hc
    have e1 : (A : Matrix (Fin 3) (Fin 3) F).map (1 : F ≃+* F) = (A : Matrix (Fin 3) (Fin 3) F) := rfl
    rw [e1] at hc
    have hc1 := scalar_eq_one_of_twisted h hc (by
      have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) (hRsq e)
      simpa [Units.val_mul] using this) (hRdet e) hAdet
    rw [hc, hc1, one_smul]
  obtain ⟨C, hCu, hCR, hCA⟩ := GenLocU3Desc.exists_unitary_frame h hp2 hq
    A hAu hAA R hRu hRsq hRcomm hAR
  refine ⟨C, hCu, fun x hx => ?_⟩
  by_cases hin : ∃ y : J, MulAut.conj y = x
  · obtain ⟨y, rfl⟩ := hin
    have hyE : y ∈ E := hx
    obtain ⟨Dm, hDm, hRC⟩ := hCR ⟨y, hyE⟩
    refine frameForm_of_eq h (hlR ⟨y, hyE⟩) (Or.inl rfl) (hRu _) hDm ?_
    have e1 : (C : Matrix (Fin 3) (Fin 3) F).map (1 : F ≃+* F) = (C : Matrix (Fin 3) (Fin 3) F) := rfl
    rw [e1]; exact hRC
  · have huxD : u * x ∈ D := D.mul_mem huD hx
    obtain ⟨φ', A', hφ', hA'u, hA'A, hlx⟩ := exists_typeII h hp2 hq hθ (hsq x hx) (fun y hy => hin ⟨y, hy⟩)
    obtain ⟨y, hy⟩ := exists_conj_mul h hp2 hθ (hsq _ huxD) hφ hφ' hAu hA'u hlu hlx
    have hyE : y ∈ E := by
      show MulAut.conj y ∈ D
      rw [hy]; exact huxD
    have hx' : x = u * MulAut.conj y := by
      rw [hy, ← mul_assoc, hsq u huD, one_mul]
    have hl : IsLift θ (A * glAut φ (R ⟨y, hyE⟩)) φ x := by
      have := hlu.mul (hlR ⟨y, hyE⟩)
      rwa [mul_one, ← hx'] at this
    have hAu' : (((A * glAut φ (R ⟨y, hyE⟩) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
        ((A * glAut φ (R ⟨y, hyE⟩) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
      (mem_unitaryIsom3 (h := h)).1 (mul_mem ((mem_unitaryIsom3 (h := h)).2 hAu)
        (glAut_mem_unitaryIsom3 φ ((mem_unitaryIsom3 (h := h)).2 (hRu _))))
    obtain ⟨De, hDe, hReC⟩ := hCR ⟨y, hyE⟩
    obtain ⟨Du, hDu, hAC⟩ := hCA
    refine frameForm_of_eq h hl (Or.inr hφ) hAu' (Dm := Du * De.map h.bar)
      (isDiag_mul' hDu (hDe.map (map_zero _))) ?_
    rw [Units.val_mul, coe_glAut, hφmap, hφmap, Matrix.mul_assoc, ← Matrix.map_mul, hReC,
      Matrix.map_mul, ← Matrix.mul_assoc, hAC, Matrix.mul_assoc]

theorem exists_frame_inner (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hθ : IsCover h θ)
    (hinj : Function.Injective (MulAut.conj : J →* MulAut J))
    {D : Subgroup (MulAut J)} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hin : ∀ x ∈ D, ∃ y : J, MulAut.conj y = x) :
    ∃ C : GL (Fin 3) F,
      ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      ∀ x ∈ D, FrameForm h θ C x := by
  classical
  have hFin : Finite F := h.finite
  have : Finite J := Finite.of_surjective θ hθ.surj
  obtain ⟨hab, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  set E : Subgroup J := D.comap (MulAut.conj : J →* MulAut J) with hEdef
  have hE : CFSG.IsElementaryAbelian 2 ↥E := by
    refine WeakSigGen.isElementaryAbelian_of_forall
      (fun a ha b hb => hinj ?_) (fun a ha => hinj ?_)
    · rw [map_mul, map_mul]; exact hab _ ha _ hb
    · rw [map_mul, map_one]; exact hsq _ ha
  have hodd : ¬ 2 ∣ Nat.card θ.ker := by
    rw [hθ.ker, card_unitaryScalars h (by norm_num : 1 ≤ 3)]
    intro h2'
    have := h2'.trans (Nat.gcd_dvd_left 3 (p ^ f + 1))
    omega
  obtain ⟨σ, hσθ, hσsq⟩ := GenLocDiagU.exists_involutive_section_of_odd_ker θ hθ.surj hodd E hE
  have hpq : 2 ∣ p ^ f + 1 := even_iff_two_dvd.1 ((h.prime.odd_of_ne_two hp2).pow).add_one
  have hle : unitarySU p f F 3 ≤ primeFormUnitary h (idGram F 3) :=
    KFU.unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram F 3)) := σ.range.map (Subgroup.inclusion hle)
  have hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩ _ ⟨_, ⟨d', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm' d d']
  have hpow : ∀ x ∈ G, x ^ 2 = 1 := by
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    rw [pow_two, ← map_mul, hσsq, map_one]
  obtain ⟨P, hP⟩ := KFU.exists_unitary_conj_diag h Nat.prime_two hpq G hcomm hpow
  refine ⟨(P : GL (Fin 3) F), ?_, fun x hx => ?_⟩
  · have hP1 := (mem_primeFormUnitary (h := h)).1 P.2
    simp only [idGram, Units.val_one, Matrix.mul_one] at hP1
    exact hP1
  · obtain ⟨y, rfl⟩ := hin x hx
    have hyE : y ∈ E := hx
    set e : ↥E := ⟨y, hyE⟩ with he
    have hdiag := hP (Subgroup.inclusion hle (σ e)) ⟨σ e, ⟨e, rfl⟩, rfl⟩
    refine frameForm_of_eq h (isLift_conj (hσθ e)) (Or.inl rfl)
      (((mem_unitarySU_iff h).1 (σ e).2).2) hdiag ?_
    have e1 : ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (1 : F ≃+* F) =
        ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
    rw [e1]
    have e2 : (P : GL (Fin 3) F) * ((P⁻¹ * (Subgroup.inclusion hle (σ e) : primeFormUnitary h (idGram F 3)) * P :
        primeFormUnitary h (idGram F 3)) : GL (Fin 3) F) = ((σ e : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * P := by
      change (P : GL (Fin 3) F) * ((P : GL (Fin 3) F)⁻¹ * ((σ e : ↥(unitarySU p f F 3)) : GL (Fin 3) F) *
        (P : GL (Fin 3) F)) = _
      group
    have e3 := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) e2
    simp only [Units.val_mul] at e3
    exact e3.symm

end CFSG.GH74.Generic.BProg.B2.GenLocU3NF
