module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer fieldSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

theorem gl_one_mul_comm (A B : GL (Fin 1) K) : A * B = B * A := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one,
    Fin.sum_univ_one, mul_comm]
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]

theorem gl_mul_comm_of_eq_one {n : ℕ} (hn : n = 1) (A B : GL (Fin n) K) : A * B = B * A := by
  subst hn
  exact gl_one_mul_comm A B

variable (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)

include hI htI in
theorem cutHom_mem_center (hI1 : ∀ i ∈ I, 1 ≤ i) {α : MulAut (StatedSp r K)}
    (hn : SpNormFix hI htI α) {g : flagStabilizer r K I}
    (hα : ∀ x, α x = (g : StatedSp r K) * fieldSp r K 1 x * (g : StatedSp r K)⁻¹) {b : ℕ}
    (hb : b ∈ I) :
    spFlagCutHom hI (spFlagPrev_mem I b) hb g ∈
      Subgroup.center (GL (Fin (b - spFlagPrev I b)) K) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t' => ?_
  have h := cut_relation hI htI hI1 hn hα hb
    (Matrix.SpecialLinearGroup.transvection t'.hij t'.c)
  have hid : ∀ M : Matrix (Fin (b - spFlagPrev I b)) (Fin (b - spFlagPrev I b)) K,
      M.map (1 : K ≃+* K) = M := fun M => by ext i j; rfl
  rw [hid] at h
  exact h.symm

include hI htI in
theorem cutHom_commute (hI1 : ∀ i ∈ I, 1 ≤ i) {α₁ α₂ : MulAut (StatedSp r K)}
    (hn₁ : SpNormFix hI htI α₁) (hn₂ : SpNormFix hI htI α₂) {g₁ g₂ : flagStabilizer r K I}
    (hα₁ : ∀ x, α₁ x = (g₁ : StatedSp r K) * fieldSp r K 1 x * (g₁ : StatedSp r K)⁻¹)
    (hα₂ : ∀ x, α₂ x = (g₂ : StatedSp r K) * fieldSp r K 1 x * (g₂ : StatedSp r K)⁻¹) {b : ℕ}
    (hb : b ∈ I) :
    spFlagCutHom hI (spFlagPrev_mem I b) hb g₁ * spFlagCutHom hI (spFlagPrev_mem I b) hb g₂ =
      spFlagCutHom hI (spFlagPrev_mem I b) hb g₂ * spFlagCutHom hI (spFlagPrev_mem I b) hb g₁ := by
  have hprev := spFlagPrev_le I b
  have hb1 := hI1 b hb
  by_cases hk : b - spFlagPrev I b = 1
  · exact gl_mul_comm_of_eq_one hk _ _
  · have h2 : 2 ≤ b - spFlagPrev I b := by omega
    have hc := cutHom_mem_center hI htI hI1 hn₁ hα₁ hb
    exact ((Subgroup.mem_center_iff.mp hc _)).symm

include hI htI in
theorem resHom_commute_spResBlock (hmax : ∀ c ∈ I, c ≤ t) {α : MulAut (StatedSp r K)}
    (hn : SpNormFix hI htI α) {g : flagStabilizer r K I}
    (hα : ∀ x, α x = (g : StatedSp r K) * fieldSp r K 1 x * (g : StatedSp r K)⁻¹)
    {c : StatedSp (r - t) K} (hc : c ∈ spResBlock K (r - t)) :
    spFlagResHom hI htI g * c = c * spFlagResHom hI htI g := by
  have h := res_relation hI htI hmax hn hα hc
  rwa [map_one, MulAut.one_apply] at h

theorem sp_model_comm [Finite K] [CharP K 2] (hr : 2 ≤ r) (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
    {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hbig : 1 ≤ r - t ∨ ∃ b ∈ I, 2 ≤ b - spFlagPrev I b) {α₁ α₂ : MulAut (StatedSp r K)}
    (h₁ : Odd (orderOf α₁)) (h₂ : Odd (orderOf α₂)) (h₁₂ : Odd (orderOf ⁅α₁, α₂⁆))
    (hn₁ : SpNormFix (fun i hi => (hI i hi).2) htI α₁)
    (hn₂ : SpNormFix (fun i hi => (hI i hi).2) htI α₂) : ⁅α₁, α₂⁆ = 1 := by
  have hI₀ : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hI₁ : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  obtain ⟨g₁, σ₁, hg₁⟩ := exists_data hr hI htI h₁ hn₁
  obtain ⟨g₂, σ₂, hg₂⟩ := exists_data hr hI htI h₂ hn₂
  have hσ₁ : σ₁ = 1 := sigma_eq_one hI₀ htI hI₁ hmax hbig hn₁ hg₁
  have hσ₂ : σ₂ = 1 := sigma_eq_one hI₀ htI hI₁ hmax hbig hn₂ hg₂
  subst hσ₁ hσ₂
  have hC : spFlagLeviHom hI₀ htI ⁅g₁, g₂⁆ = 1 := by
    refine leviHom_eq_one_of_blocks hI₀ htI (fun b hb => ?_) ?_
    · rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact cutHom_commute hI₀ htI hI₁ hn₁ hn₂ hg₁ hg₂ hb
    · rw [map_commutatorElement]
      refine eq_one_of_commute_spResBlock (r - t)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) ?_
      intro c hc
      have hc₁ : Commute (spFlagResHom hI₀ htI g₁) c :=
        resHom_commute_spResBlock hI₀ htI hmax hn₁ hg₁ hc
      have hc₂ : Commute (spFlagResHom hI₀ htI g₂) c :=
        resHom_commute_spResBlock hI₀ htI hmax hn₂ hg₂ hc
      rw [commutatorElement_def]
      exact ((hc₁.mul_left hc₂).mul_left hc₁.inv_left).mul_left hc₂.inv_left
  obtain ⟨n, hn⟩ := isPGroup_ker_spFlagLeviHom hI₀ htI hI₁
    (⟨⁅g₁, g₂⁆, MonoidHom.mem_ker.mpr hC⟩ : (spFlagLeviHom hI₀ htI).ker)
  have hpow : (⁅g₁, g₂⁆ : flagStabilizer r K I) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hpow' : (⁅(g₁ : StatedSp r K), (g₂ : StatedSp r K)⁆ : StatedSp r K) ^ 2 ^ n = 1 := by
    have := congrArg (flagStabilizer r K I).subtype hpow
    rwa [map_pow, map_commutatorElement, map_one] at this
  have hα₁ : α₁ = MulAut.conj (g₁ : StatedSp r K) := by
    ext x
    rw [hg₁, map_one, MulAut.one_apply, MulAut.conj_apply]
  have hα₂ : α₂ = MulAut.conj (g₂ : StatedSp r K) := by
    ext x
    rw [hg₂, map_one, MulAut.one_apply, MulAut.conj_apply]
  rw [hα₁, hα₂, ← map_commutatorElement] at h₁₂ ⊢
  have hdvd : orderOf (MulAut.conj ⁅(g₁ : StatedSp r K), (g₂ : StatedSp r K)⁆) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow', map_one])
  have h1 : orderOf (MulAut.conj ⁅(g₁ : StatedSp r K), (g₂ : StatedSp r K)⁆) = 1 :=
    (Nat.Coprime.pow_right n h₁₂.coprime_two_right).eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.mp h1

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
