module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

section Blocks

variable {K : Type} [Field K]

@[expose] def blk2 (B : Matrix (Fin 2) (Fin 2) K) (b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![B 0 0, B 0 1, 0; B 1 0, B 1 1, 0; 0, 0, b]

theorem blk2_mul (B B' : Matrix (Fin 2) (Fin 2) K) (b b' : K) :
    blk2 B b * blk2 B' b' = blk2 (B * B') (b * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blk2_one : blk2 (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2]

theorem ctr_blk2 (σ : K →+* K) (B : Matrix (Fin 2) (Fin 2) K) (b : K) :
    ctr σ (blk2 B b) = blk2 (ctr σ B) (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ctr, blk2]

theorem blk2_comm_D3 (B : Matrix (Fin 2) (Fin 2) K) (b : K) :
    blk2 B b * D3 = D3 * blk2 B b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, D3, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem embPair_comm_D3 (B : Matrix (Fin 2) (Fin 2) K) :
    embPair 2 B * D3 = D3 * embPair 2 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, D3, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem det_blk2 (B : Matrix (Fin 2) (Fin 2) K) (b : K) : (blk2 B b).det = B.det * b := by
  simp [blk2, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem eq_blk2_of_entries {G : Matrix (Fin 3) (Fin 3) K} (h02 : G 0 2 = 0) (h12 : G 1 2 = 0)
    (h20 : G 2 0 = 0) (h21 : G 2 1 = 0) :
    G = blk2 !![G 0 0, G 0 1; G 1 0, G 1 1] (G 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2, h02, h12, h20, h21]

@[expose] def blk2GL (B : GL (Fin 2) K) (b : Kˣ) : GL (Fin 3) K :=
  ⟨blk2 (B : Matrix (Fin 2) (Fin 2) K) (b : K),
    blk2 ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ((b⁻¹ : Kˣ) : K),
    by rw [blk2_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Units.mul_inv, blk2_one],
    by rw [blk2_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Units.inv_mul, blk2_one]⟩

theorem coe_blk2GL (B : GL (Fin 2) K) (b : Kˣ) :
    ((blk2GL B b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blk2 (B : Matrix (Fin 2) (Fin 2) K) (b : K) := rfl

end Blocks

section Orthonormal

variable {p : ℕ} {K : Type} [Field K]

theorem exists_orthonormal_blocks (hK : UnitaryFieldData p 1 K) (h2 : (2 : K) ≠ 0)
    {Q : GL (Fin 3) K} {A : Matrix (Fin 3) (Fin 3) K} (hAu : ctr hK.bar A * A = 1)
    (hAQ : A * (Q : Matrix (Fin 3) (Fin 3) K) = (Q : Matrix (Fin 3) (Fin 3) K) * D3) :
    ∃ (R₂ : GL (Fin 2) K) (r : Kˣ),
      ctr hK.bar (blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K)) *
        (ctr hK.bar (Q : Matrix (Fin 3) (Fin 3) K) * (Q : Matrix (Fin 3) (Fin 3) K)) *
        blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K) = 1 := by
  classical
  set σ : K →+* K := hK.bar with hσ
  set Qm : Matrix (Fin 3) (Fin 3) K := (Q : Matrix (Fin 3) (Fin 3) K) with hQm
  set G : Matrix (Fin 3) (Fin 3) K := ctr σ Qm * Qm with hG
  have hσσ : ∀ x, σ (σ x) = x := hK.bar_bar
  have hD3 : ctr σ (D3 : Matrix (Fin 3) (Fin 3) K) = D3 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ctr, D3, Matrix.diagonal]
  have hctrctr : ∀ M : Matrix (Fin 3) (Fin 3) K, ctr σ (ctr σ M) = M := by
    intro M
    ext i j
    simp [ctr, hσσ]
  have hDGD : D3 * G * D3 = G := by
    have h1 : ctr σ (A * Qm) * (A * Qm) = ctr σ (Qm * D3) * (Qm * D3) := by rw [hAQ]
    rw [ctr_mul, ctr_mul] at h1
    have hL : ctr σ Qm * ctr σ A * (A * Qm) = G := by
      calc ctr σ Qm * ctr σ A * (A * Qm) = ctr σ Qm * (ctr σ A * A) * Qm := by
            simp only [Matrix.mul_assoc]
        _ = G := by rw [hAu, Matrix.mul_one]
    have hR : ctr σ D3 * ctr σ Qm * (Qm * D3) = D3 * G * D3 := by
      rw [hD3]
      simp only [Matrix.mul_assoc, hG]
    rw [hL, hR] at h1
    exact h1.symm
  have hGcomm : G * D3 = D3 * G := by
    calc G * D3 = D3 * D3 * G * D3 := by rw [D3_mul_D3, Matrix.one_mul]
      _ = D3 * (D3 * G * D3) := by simp only [Matrix.mul_assoc]
      _ = D3 * G := by rw [hDGD]
  obtain ⟨h02, h12, h20, h21⟩ := commute_D3_entries h2 hGcomm
  have hGherm : ∀ i j, σ (G j i) = G i j := by
    have h1 : ctr σ G = G := by rw [hG, ctr_mul, hctrctr]
    intro i j
    have := congrFun (congrFun h1 i) j
    simpa [ctr] using this
  have hdetG : G.det ≠ 0 := by
    have hQdet : Qm.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit).ne_zero
    have : G.det = σ Qm.det * Qm.det := by
      rw [hG, Matrix.det_mul]
      congr 1
      simp only [ctr, Matrix.det_transpose]
      exact (RingHom.map_det σ Qm).symm
    rw [this]
    exact mul_ne_zero ((map_ne_zero σ).2 hQdet) hQdet
  have hGblk := eq_blk2_of_entries h02 h12 h20 h21
  set G₂ : Matrix (Fin 2) (Fin 2) K := !![G 0 0, G 0 1; G 1 0, G 1 1] with hG₂
  have hdetblk : G.det = G₂.det * G 2 2 := by
    conv_lhs => rw [hGblk]
    exact det_blk2 G₂ (G 2 2)
  have hdG₂ : G₂.det ≠ 0 := by
    intro h
    apply hdetG
    rw [hdetblk, h, zero_mul]
  have hg22 : G 2 2 ≠ 0 := by
    intro h
    apply hdetG
    rw [hdetblk, h, mul_zero]
  have hG₂herm : ∀ i j, σ (G₂ j i) = G₂ i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hG₂] <;> exact hGherm _ _
  obtain ⟨R₂, hR₂⟩ := exists_ctr_mul_mul_eq_one hK hG₂herm hdG₂
  let G₁ : Matrix (Fin 1) (Fin 1) K := Matrix.of fun _ _ => G 2 2
  have hG₁herm : ∀ i j, σ (G₁ j i) = G₁ i j := by
    intro i j
    simpa [G₁] using hGherm 2 2
  have hdG₁ : G₁.det ≠ 0 := by
    simpa [G₁, Matrix.det_unique] using hg22
  obtain ⟨R₁, hR₁⟩ := exists_ctr_mul_mul_eq_one hK hG₁herm hdG₁
  set r₀ : K := (R₁ : Matrix (Fin 1) (Fin 1) K) 0 0 with hr₀
  have hr₁ : σ r₀ * G 2 2 * r₀ = 1 := by
    have := congrFun (congrFun hR₁ 0) 0
    simpa [ctr, G₁, Matrix.mul_apply, hr₀] using this
  have hr0 : r₀ ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul, zero_mul] at hr₁
    exact zero_ne_one hr₁
  refine ⟨R₂, Units.mk0 r₀ hr0, ?_⟩
  rw [Units.val_mk0, ctr_blk2, hGblk, blk2_mul, blk2_mul, hR₂, hr₁, blk2_one]

theorem exists_orthonormal_adapted (hK : UnitaryFieldData p 1 K) (h2 : (2 : K) ≠ 0)
    {Q : GL (Fin 3) K} {A : Matrix (Fin 3) (Fin 3) K} (hAu : ctr hK.bar A * A = 1)
    (hAQ : A * (Q : Matrix (Fin 3) (Fin 3) K) = (Q : Matrix (Fin 3) (Fin 3) K) * D3) :
    ∃ P : GL (Fin 3) K, ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * 1 *
        (P : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      A * (P : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) * D3 := by
  obtain ⟨R₂, r, hR⟩ := exists_orthonormal_blocks hK h2 hAu hAQ
  refine ⟨Q * blk2GL R₂ r, ?_, ?_⟩
  · rw [Units.val_mul, coe_blk2GL, ctr_mul, Matrix.mul_one]
    calc ctr hK.bar (blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K)) *
          ctr hK.bar (Q : Matrix (Fin 3) (Fin 3) K) *
          ((Q : Matrix (Fin 3) (Fin 3) K) * blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K))
        = ctr hK.bar (blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K)) *
          (ctr hK.bar (Q : Matrix (Fin 3) (Fin 3) K) * (Q : Matrix (Fin 3) (Fin 3) K)) *
          blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := hR
  · rw [Units.val_mul, coe_blk2GL]
    calc A * ((Q : Matrix (Fin 3) (Fin 3) K) * blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K))
        = (A * (Q : Matrix (Fin 3) (Fin 3) K)) * blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K) := by
          rw [Matrix.mul_assoc]
      _ = ((Q : Matrix (Fin 3) (Fin 3) K) * D3) * blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K) := by
          rw [hAQ]
      _ = (Q : Matrix (Fin 3) (Fin 3) K) * (D3 * blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K)) := by
          rw [Matrix.mul_assoc]
      _ = (Q : Matrix (Fin 3) (Fin 3) K) * (blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K) * D3) := by
          rw [blk2_comm_D3]
      _ = ((Q : Matrix (Fin 3) (Fin 3) K) * blk2 (R₂ : Matrix (Fin 2) (Fin 2) K) (r : K)) * D3 := by
          rw [Matrix.mul_assoc]

end Orthonormal

section Stabilizer

variable {p : ℕ} {K : Type} [Field K]

theorem nonempty_mulEquiv_coordPair_Nst [Finite K] [Fact p.Prime] [CharP K p]
    (hK : UnitaryFieldData p 1 K) (P : GL (Fin 3) K)
    (hP : ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * 1 * (P : Matrix (Fin 3) (Fin 3) K) = 1)
    (hSU : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) = StatedSU 3 (p ^ 1) K) :
    Nonempty (coordPairSubgroup hK.bar 1 P 2 ≃* Nst (StatedSU 3 (p ^ 1) K) P) := by
  let ι : coordPairSubgroup hK.bar 1 P 2 →* GL (Fin 3) K :=
    (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)).subtype.comp
      (coordPairSubgroup hK.bar 1 P 2).subtype
  have hinj : Function.Injective ι := fun a b h =>
    Subtype.ext (Subtype.ext h)
  have hrange : ι.range = Nst (StatedSU 3 (p ^ 1) K) P := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hyS : ((y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) ∈
          StatedSU 3 (p ^ 1) K := by
        rw [← hSU]
        exact (y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)).2
      refine mem_Nst_iff.2 ⟨hyS, ?_⟩
      have hfix := mem_coordPairSubgroup_iff.1 y.2
      refine ⟨hfix, ?_⟩
      show (P⁻¹ * ((y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) * P) *
          D3GL = D3GL * (P⁻¹ * ((y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) :
            GL (Fin 3) K) * P)
      let y' : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) :=
        gramEquiv P hP (y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K))
      have hy'coe : (y' : GL (Fin 3) K) =
          P⁻¹ * ((y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) * P := rfl
      have hy'mem : (y' : GL (Fin 3) K) ∈ SUid (unitaryInvolution K p 1) 3 := by
        rw [← SUgram_bar_one hK 3]
        exact y'.2
      let z : SUid (unitaryInvolution K p 1) 3 := ⟨(y' : GL (Fin 3) K), hy'mem⟩
      obtain ⟨B, hB⟩ := exists_embSUid_eq_of_mulVec (σ := unitaryInvolution K p 1) (B := z)
        (c := 2) (by
          change ((y' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 2 1 = Pi.single 2 1
          rw [hy'coe]
          exact hfix)
      have hzc : ((y' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          embPair 2 ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        have := congrArg (fun w : SUid (unitaryInvolution K p 1) 3 =>
          ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hB
        simpa [coe_embSUid, z] using this.symm
      set X : GL (Fin 3) K :=
        P⁻¹ * ((y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) * P with hX
      have hXm : (X : Matrix (Fin 3) (Fin 3) K) =
          embPair 2 ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [← hy'coe]
        exact hzc
      apply Units.ext
      rw [Units.val_mul X D3GL, Units.val_mul D3GL X, hXm, coe_D3GL]
      exact embPair_comm_D3 _
    · intro hx
      obtain ⟨hxH, hxb⟩ := mem_Nst_iff.1 hx
      have hxS : x ∈ SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) := by
        rw [hSU]
        exact hxH
      refine ⟨⟨⟨x, hxS⟩, mem_coordPairSubgroup_iff.2 hxb.1⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

end Stabilizer

section Main

theorem two_ne_zero_of_charP {p : ℕ} {K : Type} [Field K] [CharP K p] (hp3 : 3 ≤ p) :
    (2 : K) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  have h2 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_charTwo_centralizer_statedSU3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (p ^ 1) ^ 2)
    {s : StatedProj (StatedSU 3 (p ^ 1) K)} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ¬ CharTwo (Subgroup.centralizer ({s} : Set (StatedProj (StatedSU 3 (p ^ 1) K)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hUFD : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK]; ring⟩
  have : CharP K p := hUFD.charP
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP (by omega)
  have hSU : SUgram hUFD.bar (1 : Matrix (Fin 3) (Fin 3) K) = StatedSU 3 (p ^ 1) K :=
    (SUgram_bar_one hUFD 3).trans (SUid_eq_statedSU hK 3)
  have hdet : ∀ g ∈ StatedSU 3 (p ^ 1) K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    fun g hg => det_eq_one_of_mem_statedSU hg
  obtain ⟨A, rfl, hA2, hAs⟩ := exists_involution_lift (by simp) (StatedSU 3 (p ^ 1) K) hdet hs2 hs1
  have hA2m : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := congrArg (fun y : StatedSU 3 (p ^ 1) K =>
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hA2
    simpa using this
  have hA1 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
    intro h
    apply hAs
    have : (A : GL (Fin 3) K) = 1 := Units.ext h
    rw [this]
    exact one_mem _
  have hAu : ctr hUFD.bar ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have hmem : (A : GL (Fin 3) K) ∈ SUgram hUFD.bar (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hSU]
      exact A.2
    have := hmem.2
    simpa using this
  obtain ⟨Q, hQ⟩ := exists_adapted_basis h2 hA2m (hdet _ A.2) hA1
  obtain ⟨P, hP1, hPA⟩ := exists_orthonormal_adapted hUFD h2 hAu hQ
  have hAP : (A : GL (Fin 3) K) * P = P * D3GL := Units.ext (by simpa [coe_D3GL] using hPA)
  obtain ⟨e⟩ := nonempty_mulEquiv_coordPair_Nst hUFD P hP1 hSU
  obtain ⟨eSL⟩ := nonempty_coordPairSubgroup_mulEquiv hUFD P hP1 2
  have h4 : 4 ≤ Nat.card hUFD.fixedField := by
    rw [fixedField_eq_fixedSubfield hUFD, card_fixedSubfield hK, pow_one]
    omega
  have hq : CFSG.IsQuasisimple (coordPairSubgroup hUFD.bar 1 P 2) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eSL.symm (isQuasisimple_sl2 h4)
  exact not_charTwo_centralizer_of_adapted (StatedSU 3 (p ^ 1) K) A P h2 hdet hA2 hAP
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)

end Main

end CFSG.QuasithinUnique.Ch1
