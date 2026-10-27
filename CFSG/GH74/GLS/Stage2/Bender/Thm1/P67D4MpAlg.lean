module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnCoord
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnStab
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpLA

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
open scoped Matrix MatrixGroups

theorem mp_diagGL3_inv {L : Type} [Field L] (h : Fin 3 → Lˣ) :
    (diagGL3 h : GL (Fin 3) L)⁻¹ = diagGL3 (fun i => (h i)⁻¹) := Units.ext rfl

theorem mp_toGL_injective {L : Type} [Field L] :
    Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(3, L) →* GL (Fin 3) L) :=
  fun _ _ h => Subtype.ext (congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h)

theorem mp_conjDiag3_conjDiag3_inv {L : Type} [Field L] (h : Fin 3 → Lˣ) (X : SL(3, L)) :
    conjDiag3 h (conjDiag3 (fun i => (h i)⁻¹) X) = X := by
  apply mp_toGL_injective
  rw [toGL_conjDiag3, toGL_conjDiag3, ← mp_diagGL3_inv]
  group

theorem mp_diagGL3_mul {L : Type} [Field L] (d d' : Fin 3 → Lˣ) :
    (diagGL3 d : GL (Fin 3) L) * diagGL3 d' = diagGL3 (fun i => d i * d' i) := by
  apply Units.ext
  simp [diagGL3, Matrix.diagonal_mul_diagonal]

theorem exists_d4LongA2_frame (L : Type) [Field L] :
    ∃ (v : WeylGroup TwistTag.D4.tag) (σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ),
      (∀ i j, σ' i j = v • d4Chain i j) ∧
      IsA2Frame ((MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
        (d4rhoStd L)) σ' ∧
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ' i j} = d4LongA2 := by
  obtain ⟨v, hv0, hv2⟩ := exists_smul_d4LongA2
  refine ⟨v, fun a b => v • d4Chain a b, fun _ _ => rfl, (d4Std_frame' L).transport v, ?_⟩
  obtain ⟨s01, s12, s02, s10, s21, s20⟩ := d4_long_values v hv0 hv2
  ext r
  rw [d4LongA2_eq]
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    match a, b, hab with
    | 0, 0, h => exact absurd rfl h
    | 0, 1, _ => exact Or.inl s01
    | 0, 2, _ => exact Or.inr (Or.inr (Or.inl s02))
    | 1, 0, _ => exact Or.inr (Or.inr (Or.inr (Or.inl s10)))
    | 1, 1, h => exact absurd rfl h
    | 1, 2, _ => exact Or.inr (Or.inl s12)
    | 2, 0, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr s20))))
    | 2, 1, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl s21))))
    | 2, 2, h => exact absurd rfl h
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, s01.symm⟩
    · exact ⟨1, 2, by decide, s12.symm⟩
    · exact ⟨0, 2, by decide, s02.symm⟩
    · exact ⟨1, 0, by decide, s10.symm⟩
    · exact ⟨2, 1, by decide, s21.symm⟩
    · exact ⟨2, 0, by decide, s20.symm⟩

theorem mp_conj_frame {L : Type} [Field L] {ρ : SL(3, L) →* ModGL TwistTag.D4.tag L}
    {σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ} (hfr : IsA2Frame ρ σ')
    (a₀ : Fin TwistTag.D4.tag.rank → Lˣ) (Q A : SL(3, L)) :
    (rootDiagUnit TwistTag.D4.tag a₀ * ρ Q) * ρ A * (rootDiagUnit TwistTag.D4.tag a₀ * ρ Q)⁻¹ =
      ρ (conjDiag3 (fun i => rootChar a₀ (σ' i 0)) (Q * A * Q⁻¹)) := by
  rw [← hfr.torus a₀ (Q * A * Q⁻¹), map_mul, map_mul, map_inv]
  group


theorem d4_toral_conj_A2 {L : Type} [Field L] [IsAlgClosed L] {A : Lˣ} (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) {ν : ModGL TwistTag.D4.tag L} (hνM : ν ∈ monomialSubgroup TwistTag.D4.tag L)
    (hνC : ν ∈ adjointGroup TwistTag.D4.tag L) (hν3 : ν ^ 3 = 1)
    (hνT : ν ∉ torusGroup TwistTag.D4.tag L)
    (hcomm : ν * rootDiagUnit TwistTag.D4.tag
        (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) =
      rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) * ν) :
    ∃ Y ∈ rootSpan TwistTag.D4.tag L d4LongA2, ∃ a : Fin TwistTag.D4.tag.rank → Lˣ,
      Y⁻¹ * ν * Y = rootDiagUnit TwistTag.D4.tag a ∧
        ∀ α ∈ d4LongA2, rootChar a α ≠ 1 ∧ rootChar a α ^ 3 = 1 := by
  classical
  set b₀ : Fin TwistTag.D4.tag.rank → Lˣ := ![A, A, 1, A] with hb₀
  have hS : ∀ α ∈ d4LongA2, IsRoot TwistTag.D4.tag α := fun _ hα => d4LongA2_isRoot hα
  have hker : rootCharKernel b₀ ⊆ d4LongA2 := fun α hα =>
    (d4Minus_rootCharKernel hA3 hA1 α).1 hα
  have hker' : ∀ α ∈ d4LongA2, α ∈ rootCharKernel b₀ := fun α hα =>
    (d4Minus_rootCharKernel hA3 hA1 α).2 hα
  have hstab := d4_stab_three_A2 hA3 hA1
  obtain ⟨h, hh, q, hq, hνhq⟩ := Set.mem_mul.1 (mem_torus_mul_rootSpan_of_commute_of_stab hstab hS
    (fun α hα => d4LongA2_neg_mem hα) hker hνC hcomm)
  obtain ⟨v, σ', hσ', hfr, hSig⟩ := exists_d4LongA2_frame L
  set ρ : SL(3, L) →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
      (d4rhoStd L) with hρ
  have hqr : q ∈ ρ.range := by
    rw [hfr.range, hSig]
    exact hq
  obtain ⟨Q, rfl⟩ := hqr
  obtain ⟨a₀, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  set dh : Fin 3 → Lˣ := fun i => rootChar a₀ (σ' i 0) with hdh
  obtain ⟨w, k, hk, hνk⟩ := monomialSubgroup_le_torusWeylCosets hνM
  have hνW : MapsRootLines ν w := hνk ▸ mapsRootLines_mul_canonicalRep hk w
  have hwν : weylQuotientHom TwistTag.D4.tag L ⟨ν, hνM⟩ = w := weylQuotientHom_eq hνW
  have hxv : ν * rootDiagUnit TwistTag.D4.tag b₀ * ν⁻¹ = rootDiagUnit TwistTag.D4.tag b₀ := by
    rw [hcomm]
    group
  have hchar : ∀ u, rootChar b₀ (w • u) = rootChar b₀ u := by
    have hdbk : rootDiagUnit TwistTag.D4.tag b₀ * k = k * rootDiagUnit TwistTag.D4.tag b₀ :=
      rootDiagUnit_mul_comm_of_mem_torusGroup b₀ hk
    have hconj : rootDiagUnit TwistTag.D4.tag b₀ =
        canonicalRep (coxeterSystem TwistTag.D4.tag) L w * rootDiagUnit TwistTag.D4.tag b₀ *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ := by
      set nw := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hnw
      set db := rootDiagUnit TwistTag.D4.tag b₀ with hdb
      rw [hνk] at hxv
      have h1 : k * (nw * db * nw⁻¹) * k⁻¹ = db := by
        calc k * (nw * db * nw⁻¹) * k⁻¹ = k * nw * db * (k * nw)⁻¹ := by group
          _ = db := hxv
      have h2 : nw * db * nw⁻¹ = k⁻¹ * db * k := by
        calc nw * db * nw⁻¹ = k⁻¹ * (k * (nw * db * nw⁻¹) * k⁻¹) * k := by group
          _ = k⁻¹ * db * k := by rw [h1]
      rw [h2, mul_assoc, hdbk, inv_mul_cancel_left]
    exact (rootDiagUnit_eq_conj_canonicalRep_iff b₀ b₀ w).1 hconj
  have hact : ∀ A : SL(3, L), ν * ρ A * ν⁻¹ = ρ (conjDiag3 dh (Q * A * Q⁻¹)) := fun A => by
    rw [← hνhq]
    exact mp_conj_frame hfr a₀ Q A
  set Xgl : GL (Fin 3) L := diagGL3 dh * Matrix.SpecialLinearGroup.toGL Q with hXgl
  have hXconj : ∀ A : SL(3, L), Matrix.SpecialLinearGroup.toGL (conjDiag3 dh (Q * A * Q⁻¹)) =
      Xgl * Matrix.SpecialLinearGroup.toGL A * Xgl⁻¹ := fun A => by
    rw [toGL_conjDiag3, map_mul, map_mul, map_inv, hXgl]
    group
  have hmat : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) :
        GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = 1 + t • Matrix.single i j (1 : L) := by
    intro i j hij t
    ext a b
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]
  have hpair : ∀ i j : Fin 3, i ≠ j → ∃ (k' l' : Fin 3) (c : L), k' ≠ l' ∧ ∀ t : L,
      (Xgl : Matrix (Fin 3) (Fin 3) L) * (1 + t • Matrix.single i j (1 : L)) =
        (1 + (c * t) • Matrix.single k' l' (1 : L)) * (Xgl : Matrix (Fin 3) (Fin 3) L) := by
    intro i j hij
    obtain ⟨ε, hε⟩ := hfr.transv i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hνM (hfr.isRoot i j hij)
    rw [hwν] at hμ
    have hij_mem : σ' i j ∈ d4LongA2 := by
      rw [← hSig]
      exact ⟨i, j, hij, rfl⟩
    have hrk : rootChar b₀ (w • σ' i j) = 1 := by
      rw [hchar]
      exact (hker' _ hij_mem).2
    have hmem : w • σ' i j ∈ d4LongA2 :=
      hker ⟨IsRoot.smul (hfr.isRoot i j hij) w, hrk⟩
    rw [← hSig] at hmem
    obtain ⟨k', l', hkl, hkl'⟩ := hmem
    obtain ⟨ε', hε'⟩ := hfr.transv k' l' hkl
    refine ⟨k', l', ((ε'⁻¹ * μ * ε : Lˣ) : L), hkl, fun t => ?_⟩
    have h1 : ν * ρ (Matrix.SpecialLinearGroup.transvection hij t) * ν⁻¹ =
        ρ (Matrix.SpecialLinearGroup.transvection hkl (((ε'⁻¹ * μ * ε : Lˣ) : L) * t)) := by
      rw [hε, hμ, hkl', hε']
      congr 1
      have hne := ε'.ne_zero
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    rw [hact] at h1
    have h2 := hfr.injective h1
    have h3 := congrArg Matrix.SpecialLinearGroup.toGL h2
    rw [hXconj] at h3
    have h4 : Xgl * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hkl
          (((ε'⁻¹ * μ * ε : Lˣ) : L) * t)) * Xgl := by
      rw [← h3]
      group
    have h5 := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h4
    simp only [Units.val_mul] at h5
    rw [hmat, hmat] at h5
    rw [h5]
    simp only [Units.val_mul]
  set ψ : SL(3, L) → SL(3, L) := fun B => conjDiag3 dh (Q * B * Q⁻¹) with hψ
  have hψ3 : ∀ B : SL(3, L), ψ (ψ (ψ B)) = B := by
    intro B
    apply hfr.injective
    have h1 : ν * (ν * (ν * ρ B * ν⁻¹) * ν⁻¹) * ν⁻¹ = ρ (ψ (ψ (ψ B))) := by
      rw [hact, hact, hact]
    rw [← h1]
    have hν3' : ν * ν * ν = 1 := by rw [← pow_three']; exact hν3
    have e : ν * (ν * (ν * ρ B * ν⁻¹) * ν⁻¹) * ν⁻¹ =
        (ν * ν * ν) * ρ B * (ν * ν * ν)⁻¹ := by group
    rw [e, hν3']
    group
  have hX3 : ∀ B : SL(3, L), (Xgl * Xgl * Xgl) * Matrix.SpecialLinearGroup.toGL B =
      Matrix.SpecialLinearGroup.toGL B * (Xgl * Xgl * Xgl) := by
    intro B
    have h := congrArg Matrix.SpecialLinearGroup.toGL (hψ3 B)
    simp only [hψ] at h
    rw [hXconj, hXconj, hXconj] at h
    calc (Xgl * Xgl * Xgl) * Matrix.SpecialLinearGroup.toGL B =
        (Xgl * (Xgl * (Xgl * Matrix.SpecialLinearGroup.toGL B * Xgl⁻¹) * Xgl⁻¹) * Xgl⁻¹) *
          (Xgl * Xgl * Xgl) := by group
      _ = Matrix.SpecialLinearGroup.toGL B * (Xgl * Xgl * Xgl) := by rw [h]
  have hcube : ∃ r : L, (Xgl : Matrix (Fin 3) (Fin 3) L) * (Xgl : Matrix (Fin 3) (Fin 3) L) *
      (Xgl : Matrix (Fin 3) (Fin 3) L) = r • (1 : Matrix (Fin 3) (Fin 3) L) := by
    refine la_scalar_of_comm_transvections _ (fun i j hij => ?_)
    have h := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L))
      (hX3 (Matrix.SpecialLinearGroup.transvection hij 1))
    simp only [Units.val_mul, hmat, one_smul] at h
    exact h
  have hnd : ¬ ∀ i j : Fin 3, i ≠ j → (Xgl : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
    intro hdiag
    apply hνT
    rw [← hνhq]
    refine mul_mem hh ?_
    have hQd : ∀ i j : Fin 3, i ≠ j → (Q : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
      intro i j hij
      have h0 := hdiag i j hij
      have hX : (Xgl : Matrix (Fin 3) (Fin 3) L) i j =
          (dh i : L) * (Q : Matrix (Fin 3) (Fin 3) L) i j := by
        simp [hXgl, diagGL3, Matrix.diagonal_mul]
      rw [hX] at h0
      exact (mul_eq_zero.1 h0).resolve_left (dh i).ne_zero
    exact hfr.diag Q hQd
  have hdet : (Xgl : Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det Xgl).ne_zero
    simpa using this
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq ((Xgl : Matrix (Fin 3) (Fin 3) L).det)
    (by norm_num : 0 < 3)
  have hω3 : ((A : Lˣ) : L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hA3, Units.val_one]
  have hω1 : ((A : Lˣ) : L) ≠ 1 := fun h => hA1 (Units.ext h)
  obtain ⟨y, hydet, hXy⟩ := la_diag_of_monomial_cycle hω3 hω1 (Xgl : Matrix (Fin 3) (Fin 3) L)
    hdet hpair hcube hnd lam hlam
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0] at hlam
    exact hdet (by rw [← hlam]; norm_num)
  set lamU : Lˣ := Units.mk0 lam hlam0 with hlamU
  set δ : Fin 3 → Lˣ := fun i => lamU * A ^ (i : ℕ) with hδ
  set ySL : SL(3, L) := ⟨y, hydet⟩ with hySL
  set ygl : GL (Fin 3) L := Matrix.SpecialLinearGroup.toGL ySL with hygl
  have hδmat : ((diagGL3 δ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![lam, ((A : Lˣ) : L) * lam, ((A : Lˣ) : L) ^ 2 * lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagGL3, hδ, hlamU, pow_two, mul_comm]
  have hΔ : Xgl * ygl = ygl * diagGL3 δ := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [hδmat]
    exact hXy
  obtain ⟨Z, hZ⟩ : ∃ Z : SL(3, L), Z = (conjDiag3 (fun i => (dh i)⁻¹) ySL)⁻¹ * (Q * ySL) :=
    ⟨_, rfl⟩
  have hZgl : Matrix.SpecialLinearGroup.toGL Z = diagGL3 (fun i => (dh i)⁻¹ * δ i) := by
    have e1 : Matrix.SpecialLinearGroup.toGL (conjDiag3 (fun i => (dh i)⁻¹) ySL) =
        diagGL3 (fun i => (dh i)⁻¹) * ygl * (diagGL3 (fun i => (dh i)⁻¹))⁻¹ := by
      rw [toGL_conjDiag3]
    have e2 : diagGL3 (fun i => (dh i)⁻¹ * δ i) =
        diagGL3 (fun i => (dh i)⁻¹) * diagGL3 δ := (mp_diagGL3_mul _ _).symm
    have e3 : (diagGL3 (fun i => (dh i)⁻¹) : GL (Fin 3) L) = (diagGL3 dh)⁻¹ :=
      (mp_diagGL3_inv dh).symm
    rw [hZ, map_mul, map_inv, e1, map_mul, e2, e3, inv_inv]
    have hX' : Xgl = diagGL3 dh * Matrix.SpecialLinearGroup.toGL Q := hXgl
    have h5 : (diagGL3 dh)⁻¹ * (ygl⁻¹ * Xgl * ygl) = (diagGL3 dh)⁻¹ * diagGL3 δ := by
      have : ygl⁻¹ * Xgl * ygl = diagGL3 δ := by
        rw [mul_assoc, hΔ]
        group
      rw [this]
    calc _ = (diagGL3 dh)⁻¹ * (ygl⁻¹ * Xgl * ygl) := by rw [hX', ← hygl]; group
      _ = _ := h5
  have hZdiag : ∀ i j : Fin 3, i ≠ j → (Z : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
    intro i j hij
    have h := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L) i j) hZgl
    simp only [diagGL3, Matrix.diagonal_apply_ne _ hij] at h
    exact h
  have hρZ : ρ Z ∈ torusGroup TwistTag.D4.tag L := hfr.diag Z hZdiag
  have hνY : ν * ρ ySL = ρ ySL * (rootDiagUnit TwistTag.D4.tag a₀ * ρ Z) := by
    set c := conjDiag3 (fun i => (dh i)⁻¹) ySL with hc
    have h1 : rootDiagUnit TwistTag.D4.tag a₀ * ρ c =
        ρ ySL * rootDiagUnit TwistTag.D4.tag a₀ := by
      have h := hfr.torus a₀ c
      rw [hc, mp_conjDiag3_conjDiag3_inv] at h
      calc rootDiagUnit TwistTag.D4.tag a₀ * ρ c =
          (rootDiagUnit TwistTag.D4.tag a₀ * ρ c * (rootDiagUnit TwistTag.D4.tag a₀)⁻¹) *
            rootDiagUnit TwistTag.D4.tag a₀ := by group
        _ = ρ ySL * rootDiagUnit TwistTag.D4.tag a₀ := by rw [h]
    have h2 : Q * ySL = c * Z := by
      rw [hZ]
      group
    rw [← hνhq, mul_assoc, ← map_mul, h2, map_mul, ← mul_assoc, h1, mul_assoc]
  have hτH : rootDiagUnit TwistTag.D4.tag a₀ * ρ Z ∈ torusGroup TwistTag.D4.tag L :=
    mul_mem (SetLike.mem_coe.1 hh) hρZ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hτH
  have hτ : (ρ ySL)⁻¹ * ν * ρ ySL = rootDiagUnit TwistTag.D4.tag a := by
    rw [← ha, mul_assoc, hνY]
    group
  have hzU : (diagGL3 (fun i => (dh i)⁻¹ * δ i) : GL (Fin 3) L) =
      Matrix.SpecialLinearGroup.toGL Z := hZgl.symm
  have hconjZ : ∀ B : SL(3, L), Z * B * Z⁻¹ = conjDiag3 (fun i => (dh i)⁻¹ * δ i) B := by
    intro B
    apply mp_toGL_injective
    rw [toGL_conjDiag3, map_mul, map_mul, map_inv, ← hzU]
  have hact2 : ∀ B : SL(3, L),
      (rootDiagUnit TwistTag.D4.tag a₀ * ρ Z) * ρ B * (rootDiagUnit TwistTag.D4.tag a₀ * ρ Z)⁻¹ =
        ρ (conjDiag3 δ B) := by
    intro B
    have h1 : rootDiagUnit TwistTag.D4.tag a₀ * ρ (Z * B * Z⁻¹) *
        (rootDiagUnit TwistTag.D4.tag a₀)⁻¹ = ρ (conjDiag3 dh (Z * B * Z⁻¹)) :=
      hfr.torus a₀ (Z * B * Z⁻¹)
    have e : (rootDiagUnit TwistTag.D4.tag a₀ * ρ Z) * ρ B *
        (rootDiagUnit TwistTag.D4.tag a₀ * ρ Z)⁻¹ =
        rootDiagUnit TwistTag.D4.tag a₀ * ρ (Z * B * Z⁻¹) *
          (rootDiagUnit TwistTag.D4.tag a₀)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e, h1, hconjZ]
    congr 1
    apply mp_toGL_injective
    rw [toGL_conjDiag3, toGL_conjDiag3, toGL_conjDiag3]
    have e2 : diagGL3 δ = diagGL3 dh * diagGL3 (fun i => (dh i)⁻¹ * δ i) := by
      rw [mp_diagGL3_mul]
      congr 1
      funext i
      simp
    rw [e2]
    group
  have hδratio : ∀ i j : Fin 3, i ≠ j → rootChar a (σ' i j) = δ i * (δ j)⁻¹ := by
    intro i j hij
    have h1 := hfr.torus a (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [← ha, hact2] at h1
    have h2 := hfr.injective h1
    rw [conjDiag3_transvection, conjDiag3_transvection] at h2
    have h3 := congrArg (fun M : SL(3, L) => (M : Matrix (Fin 3) (Fin 3) L) i j) h2
    simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      Matrix.one_apply_ne hij, Matrix.single_apply_same, zero_add] at h3
    rw [hfr.eq_sub i j, rootChar_sub]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    simp only [mul_one, Units.val_inv_eq_inv_val] at h3
    exact h3.symm
  refine ⟨ρ ySL, ?_, a, hτ, ?_⟩
  · have hmem : ρ ySL ∈ ρ.range := ⟨ySL, rfl⟩
    rw [hfr.range, hSig] at hmem
    exact hmem
  · intro α hα
    rw [← hSig] at hα
    obtain ⟨i, j, hij, rfl⟩ := hα
    rw [hδratio i j hij]
    have hA2 : A ^ 2 ≠ 1 := fun h => hA1 (by
      have h3 : A ^ 3 = A ^ 2 * A := pow_succ A 2
      rw [hA3, h] at h3
      simpa using h3.symm)
    have hAi : ∀ k : ℕ, (A ^ k) ^ 3 = 1 := fun k => by
      rw [← pow_mul, mul_comm, pow_mul, hA3, one_pow]
    have hA2' : A ≠ A ^ 2 := fun h => hA1 (by
      rw [pow_two] at h
      have h' : A * 1 = A * A := by rw [mul_one]; exact h
      exact (mul_left_cancel h').symm)
    have hratio : δ i * (δ j)⁻¹ = A ^ (i : ℕ) * (A ^ (j : ℕ))⁻¹ := by
      simp only [hδ]
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
    have hdist : A ^ (i : ℕ) ≠ A ^ (j : ℕ) := by
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | simpa using hA1.symm
        | simpa using hA2.symm
        | simpa using hA1
        | simpa using hA2
        | simpa using hA2'
        | simpa using hA2'.symm
    rw [hratio]
    refine ⟨fun h => hdist (mul_inv_eq_one.1 h), ?_⟩
    rw [mul_pow, inv_pow, hAi, hAi, inv_one, mul_one]


end CFSG.GH74.GLS.Stage2.Bender.Thm1
