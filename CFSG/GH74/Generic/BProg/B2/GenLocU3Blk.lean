module

public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.GH74.Generic.BProg.B2.GenLocU3Lift
public import CFSG.GH74.Generic.BProg.B2.GenLocBasic
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocU3Blk

open Matrix CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.GH74.Generic.BProg.B2.GenLocU3Lift
  CFSG.GH74.KGroups.L3Eps.Uni CFSG.GH74.Generic.BProg.B2

variable {F : Type} [Field F]

@[expose] def idx3 (i : Fin 2) (x : Fin 2) : Fin 3 := ⟨i.val + x.val, by omega⟩

theorem map_blockMat (σ : F ≃+* F) {m k : ℕ} (i : ℕ) (A : Matrix (Fin k) (Fin k) F) :
    (blockMat m i A).map σ = blockMat m i (A.map σ) := by
  ext a b
  rw [Matrix.map_apply, blockMat_apply, blockMat_apply]
  by_cases h : (i ≤ a.val ∧ a.val < i + k) ∧ (i ≤ b.val ∧ b.val < i + k)
  · rw [dite_eq_left h, dite_eq_left h]; rfl
  · rw [dite_eq_right h, dite_eq_right h]
    simp only [Matrix.one_apply]
    split_ifs <;> simp

theorem diag_mul_blockMat (d : Fin 3 → F) (hd : ∀ k, d k ≠ 0) (i : Fin 2)
    (Y : Matrix (Fin 2) (Fin 2) F) :
    Matrix.diagonal d * blockMat 3 i.val Y =
      blockMat 3 i.val (Matrix.diagonal (fun x => d (idx3 i x)) * Y *
        Matrix.diagonal (fun x => (d (idx3 i x))⁻¹)) * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, blockMat_apply, blockMat_apply]
  by_cases h : (i.val ≤ a.val ∧ a.val < i.val + 2) ∧ (i.val ≤ b.val ∧ b.val < i.val + 2)
  · rw [dite_eq_left h, dite_eq_left h]
    have ha : idx3 i ⟨a.val - i.val, by omega⟩ = a := Fin.ext (by simp [idx3]; omega)
    have hb : idx3 i ⟨b.val - i.val, by omega⟩ = b := Fin.ext (by simp [idx3]; omega)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [ha, hb]
    have := hd b
    field_simp
  · rw [dite_eq_right h, dite_eq_right h]
    simp only [Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]

section Block

variable {p f : ℕ} [Fact p.Prime] [Finite F] [CharP F p]

@[expose] noncomputable def suEquiv (h : UnitaryFieldData p f F) (n : ℕ) :
    Su F p f n ≃* ↥(unitarySU p f F n) :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)

theorem coe_suEquiv (h : UnitaryFieldData p f F) (n : ℕ) (x : Su F p f n) :
    ((suEquiv h n x : ↥(unitarySU p f F n)) : GL (Fin n) F) = (x : GL (Fin n) F) := rfl

theorem exists_block_conj (h : UnitaryFieldData p f F) {Δ : GL (Fin 3) F}
    (hΔ : ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hΔu : (((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1)
    (ψ : F ≃+* F) (i : Fin 2) (y : Su F p f 2) :
    ∃ y' : Su F p f 2, Δ * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * Δ⁻¹ =
      ((blockEmb2 F p f 2 i y' : Su F p f 3) : GL (Fin 3) F) := by
  classical
  obtain ⟨d, hDd⟩ : ∃ d : Fin 3 → F, Matrix.diagonal d = (Δ : Matrix (Fin 3) (Fin 3) F) :=
    ⟨_, hΔ.diagonal_diag⟩
  have hdn : ∀ k, h.bar (d k) * d k = 1 := by
    intro k
    have h1 := hΔu
    rw [← hDd, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at h1
    have := congrFun (congrFun h1 k) k
    simpa using this
  have hd0 : ∀ k, d k ≠ 0 := by
    intro k h0
    have := hdn k
    rw [h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  set d2 : Fin 2 → F := fun x => d (idx3 i x) with hd2
  let D2 : GL (Fin 2) F := ⟨Matrix.diagonal d2, Matrix.diagonal (fun x => (d2 x)⁻¹),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact mul_inv_cancel₀ (hd0 _),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext x
       exact inv_mul_cancel₀ (hd0 _)⟩
  have hY : (y : GL (Fin 2) F) ∈ unitarySU p f F 2 := (suEquiv h 2 y).2
  have hY1 : glAut ψ (y : GL (Fin 2) F) ∈ unitarySU p f F 2 := by
    rw [unitarySU_eq_gramSU h 2] at hY ⊢
    exact glAut_mem_gramSU h (isPrimeFormGram_one (n := 2)) ψ (by simpa using hY)
  have hD2u : D2 ∈ primeFormUnitary h (idGram F 2) := by
    rw [mem_primeFormUnitary]
    change ((Matrix.diagonal d2).map h.bar)ᵀ * idGram F 2 * Matrix.diagonal d2 = idGram F 2
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1; ext x
    exact hdn _
  have hY2 := KFU.conj_mem_unitarySU h hD2u hY1
  refine ⟨(suEquiv h 2).symm ⟨D2 * glAut ψ (y : GL (Fin 2) F) * D2⁻¹, hY2⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glAut]
  rw [← hDd]
  change Matrix.diagonal d * ((blockMat 3 i.val (((y : Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).map ψ) =
    blockMat 3 i.val ((D2 * glAut ψ (y : GL (Fin 2) F) * D2⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal d
  rw [map_blockMat, diag_mul_blockMat d hd0 i]
  congr 2

theorem exists_restrict_action {H J A : Type} [Group H] [Group J] [Group A] (φ : H →* J)
    (hφ : Function.Injective φ) (α : A →* MulAut J)
    (hpres : ∀ (a : A) (y : H), ∃ z : H, φ z = α a (φ y)) :
    ∃ β : A →* MulAut H, ∀ (a : A) (y : H), α a (φ y) = φ (β a y) := by
  choose g hg using hpres
  have hmul : ∀ a y y', g a (y * y') = g a y * g a y' := fun a y y' => hφ (by
    calc φ (g a (y * y')) = α a (φ y * φ y') := by rw [hg, map_mul]
      _ = φ (g a y * g a y') := by rw [map_mul, map_mul, hg, hg])
  have hone : ∀ y, g 1 y = y := fun y => hφ (by rw [hg, map_one, MulAut.one_apply])
  have hcomp : ∀ a b y, g (a * b) y = g a (g b y) := fun a b y => hφ (by
    rw [hg, map_mul, MulAut.mul_apply, hg, hg])
  let β : A →* MulAut H :=
    { toFun := fun a =>
        { toFun := g a
          invFun := g a⁻¹
          left_inv := fun y => by rw [← hcomp, inv_mul_cancel, hone]
          right_inv := fun y => by rw [← hcomp, mul_inv_cancel, hone]
          map_mul' := hmul a }
      map_one' := MulEquiv.ext fun y => hone y
      map_mul' := fun a b => MulEquiv.ext fun y => hcomp a b y }
  exact ⟨β, fun a y => (hg a y).symm⟩

theorem blockHom_injective {J : Type} [Group J] (h : UnitaryFieldData p f F) {θ : ↥(unitarySU p f F 3) →* J}
    (hθ : IsCover h θ) {C : GL (Fin 3) F} (hC : C ∈ primeFormUnitary h (idGram F 3)) (i : Fin 2) :
    Function.Injective ((θ.comp ((KFU.conjSU h ⟨C, hC⟩).toMonoidHom.comp
      (suEquiv h 3).toMonoidHom)).comp (blockEmb2 F p f 2 i)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : (KFU.conjSU h ⟨C, hC⟩) (suEquiv h 3 (blockEmb2 F p f 2 i y)) ∈ θ.ker := hy
  rw [hθ.ker, mem_unitaryScalars] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  have hm : ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    have h2 : C * ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * C⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hc]; rfl
    have h3 : ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) =
        C⁻¹ * GeneralLinearGroup.scalar (Fin 3) c * C := by
      rw [← h2]; group
    rw [h3, mul_assoc, ← (commute_scalar c C).eq]
    group
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, ¬ (i.val ≤ k.val ∧ k.val < i.val + 2) := by
    fin_cases i
    · exact ⟨2, by simp⟩
    · exact ⟨0, by simp⟩
  have hkk := congrFun (congrFun (congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hm) k) k
  rw [coe_coe_blockEmb2, blockMat_apply_of_not_mem_left _ hk] at hkk
  have hc1 : (c : F) = 1 := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.one_apply] using hkk.symm
  have hc1' : c = 1 := Units.ext hc1
  rw [hc1', map_one] at hm
  have : blockEmb2 F p f 2 i y = 1 := Subtype.ext (by rw [hm]; rfl)
  exact (map_eq_one_iff _ (blockEmb2_injective 2 i)).1 this

theorem gammaAct_eq_top_of_frame (h : UnitaryFieldData p f F) (hq : p ^ f ≠ 2)
    {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ)
    {C : GL (Fin 3) F}
    (hCu : ((C : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) F) = 1)
    {A : Type} [Group A] (α : A →* MulAut J) (hα : ∀ a, FrameForm h θ C (α a))
    (hblk : ∀ β : A →* MulAut (Su F p f 2), gammaAct β = ⊤) : gammaAct α = ⊤ := by
  classical
  have hC : C ∈ primeFormUnitary h (idGram F 3) := by
    rw [mem_primeFormUnitary]; simpa [idGram] using hCu
  let cC : ↥(unitarySU p f F 3) ≃* ↥(unitarySU p f F 3) := KFU.conjSU h ⟨C, hC⟩
  let Ψ : Su F p f 3 →* J := θ.comp (cC.toMonoidHom.comp (suEquiv h 3).toMonoidHom)
  let φ : Fin 2 → (Su F p f 2 →* J) := fun i => Ψ.comp (blockEmb2 F p f 2 i)
  have hφinj : ∀ i, Function.Injective (φ i) := fun i => blockHom_injective h hθ hC i
  have hpres : ∀ (i : Fin 2) (a : A) (y : Su F p f 2), ∃ z : Su F p f 2, φ i z = α a (φ i y) := by
    intro i a y
    obtain ⟨A', Δ, ψ, hl, hψ, hA'u, hΔd, hAC⟩ := hα a
    have hΔmem : Δ ∈ unitaryIsom3 h := by
      have : Δ = C⁻¹ * (A' * glAut ψ C) := by rw [hAC]; group
      rw [this]
      exact mul_mem (inv_mem ((mem_unitaryIsom3 (h := h)).2 hCu))
        (mul_mem ((mem_unitaryIsom3 (h := h)).2 hA'u)
          (glAut_mem_unitaryIsom3 ψ ((mem_unitaryIsom3 (h := h)).2 hCu)))
    obtain ⟨y', hy'⟩ := exists_block_conj h hΔd ((mem_unitaryIsom3 (h := h)).1 hΔmem) ψ i y
    refine ⟨y', ?_⟩
    obtain ⟨g', hg'1, hg'2⟩ := hl (cC (suEquiv h 3 (blockEmb2 F p f 2 i y)))
    have hgg : cC (suEquiv h 3 (blockEmb2 F p f 2 i y')) = g' := by
      apply Subtype.ext
      rw [hg'1]
      change C * ((blockEmb2 F p f 2 i y' : Su F p f 3) : GL (Fin 3) F) * C⁻¹ =
        A' * glAut ψ (C * ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * C⁻¹) * A'⁻¹
      calc C * ((blockEmb2 F p f 2 i y' : Su F p f 3) : GL (Fin 3) F) * C⁻¹
          = C * (Δ * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * Δ⁻¹) * C⁻¹ := by
            rw [hy']
        _ = (C * Δ) * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * (C * Δ)⁻¹ := by
            group
        _ = (A' * glAut ψ C) * glAut ψ ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) *
            (A' * glAut ψ C)⁻¹ := by rw [hAC]
        _ = A' * glAut ψ (C * ((blockEmb2 F p f 2 i y : Su F p f 3) : GL (Fin 3) F) * C⁻¹) * A'⁻¹ := by
            simp only [map_mul, map_inv]; group
    show θ (cC (suEquiv h 3 (blockEmb2 F p f 2 i y'))) =
      α a (θ (cC (suEquiv h 3 (blockEmb2 F p f 2 i y))))
    rw [hgg, hg'2]
  choose β hβ using fun i => exists_restrict_action (φ i) (hφinj i) α (hpres i)
  have htop : ⨆ i, (φ i).range = ⊤ := by
    have hsurj : Function.Surjective Ψ :=
      hθ.surj.comp (cC.surjective.comp (suEquiv h 3).surjective)
    have h1 := iSup_range_blockEmb2 (K := F) (p := p) (f := f) h.card_eq_sq hq 2
    simp only [φ, MonoidHom.range_comp]
    rw [← Subgroup.map_iSup, h1, Subgroup.map_top_of_surjective _ hsurj]
  exact CFSG.GH74.Generic.BProg.B2.gammaAct_eq_top_of_equivariant α (fun _ => Su F p f 2) φ β
    (fun i a y => hβ i a y) htop (fun i => hblk (β i))

end Block

end CFSG.GH74.Generic.BProg.B2.GenLocU3Blk
