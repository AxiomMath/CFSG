module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLNonsplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem conj_embedding {X T : Type} [Group X] [Group T] {ψ : X →* MulAut T}
    (hψ : Function.Injective ψ) (hInn : (MulAut.conj : T →* MulAut T).range ≤ ψ.range)
    (φ : MulAut T) :
    Function.Injective ((MulAut.conj φ).toMonoidHom.comp ψ) ∧
      (MulAut.conj : T →* MulAut T).range ≤ ((MulAut.conj φ).toMonoidHom.comp ψ).range := by
  refine ⟨fun a b h => hψ ((MulAut.conj φ).injective h), ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hInn ⟨φ⁻¹ x, rfl⟩
  refine ⟨z, ?_⟩
  change φ * ψ z * φ⁻¹ = MulAut.conj x
  rw [hz, mul_conj_mul_inv]
  simp

theorem even_of_sq_eq_nonsquare {A : GL (Fin n) K} {l : Kˣ}
    (hA : A * A = GeneralLinearGroup.scalar (Fin n) l) (hl : ¬ IsSquare (l : K)) : Even n := by
  by_contra hn
  obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.1 hn
  apply hl
  have h := congrArg (fun M : GL (Fin (2 * k + 1)) K =>
    (M : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) K).det) hA
  simp only [Units.val_mul, det_mul, GeneralLinearGroup.scalar] at h
  have hd : (Matrix.scalar (Fin (2 * k + 1)) (l : K)).det = (l : K) ^ (2 * k + 1) := by
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h' : (A : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) K).det *
      (A : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) K).det = (l : K) ^ (2 * k + 1) := by
    rw [← hd, h]
    rfl
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  refine ⟨(A : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) K).det / (l : K) ^ k, ?_⟩
  field_simp
  rw [sq (A : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) K).det, h']
  ring

theorem inner_propAConclusion [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (projectiveSL n K)}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : GL (Fin n) K} (htA : ψ t = conjAut n K A)
    {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsc : ∀ (c : Kˣ) (Z : GL (Fin n) K), Commute (GeneralLinearGroup.scalar (Fin n) c) Z :=
    fun c Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hA2 : conjAut n K (A * A) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← htA, ← map_mul, htt, map_one]
  obtain ⟨-, l, hl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 hA2
  have hns : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin n) c := by
    intro c hc
    have : ψ t = 1 := by rw [htA, hc, conjAut_scalar]
    have ht1 : t = 1 := hψ (by rw [this, map_one])
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hYne : ∀ {ψ' : X →* MulAut (projectiveSL n K)}, Function.Injective ψ' → Y.map ψ' ≠ ⊥ :=
    fun h hmap => hY ((map_eq_bot_iff_of_injective _ h).1 hmap)
  by_cases hsq : IsSquare (l : K)
  ·
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact l.ne_zero (by rw [hr, mul_zero])
    set μ := Units.mk0 r hr0
    have hAμ : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ) := by
      rw [← hl]
      congr 1
      exact Units.ext hr
    obtain ⟨H, J, a, b, ha, hb, hH⟩ := exists_split_normal_form hK hAμ hns
    obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut n K H)
    set ψ' := (MulAut.conj (conjAut n K H)).toMonoidHom.comp ψ with hψ'def
    have hψ't : ψ' t = conjAut n K (signGL K J) := by
      change conjAut n K H * ψ t * (conjAut n K H)⁻¹ = _
      rw [htA, ← map_inv, ← map_mul, ← map_mul, hH, map_mul, conjAut_scalar, one_mul]
    apply PropAConclusion.of_injective hinj'
    rw [hψ't]
    refine split_propAConclusionIn hK hn hinj hInn' ha hb (hYne hinj') ?_
    rw [← hψ't, ← map_oddCentralizerCore_of_injective hinj']
    exact map_mono hYO
  ·
    have hev := even_of_sq_eq_nonsquare hl.symm hsq
    obtain ⟨m, rfl⟩ : ∃ m, n = m * 2 := ⟨n / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
    have hm : 2 ≤ m := by omega
    have hAm : (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * A = (l : K) • 1 := by
      have := congrArg Units.val hl
      rw [Units.val_mul] at this
      rw [← this]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    obtain ⟨H, hH⟩ := exists_quad_normal_form hsq hAm
    have hHGL : H * A * H⁻¹ = quadGL (l : K) m hsq := Units.ext hH
    obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut (m * 2) K H)
    set ψ' := (MulAut.conj (conjAut (m * 2) K H)).toMonoidHom.comp ψ with hψ'def
    have hψ't : ψ' t = conjAut (m * 2) K (quadGL (l : K) m hsq) := by
      change conjAut (m * 2) K H * ψ t * (conjAut (m * 2) K H)⁻¹ = _
      rw [htA, ← map_inv, ← map_mul, ← map_mul, hHGL]
    apply PropAConclusion.of_injective hinj'
    rw [hψ't]
    refine nonsplit_propAConclusionIn hK hsq hm hinj hInn' (hYne hinj') ?_
    rw [← hψ't, ← map_oddCentralizerCore_of_injective hinj']
    exact map_mono hYO

end CFSG.ComponentClassification.Burgoyne.PSL