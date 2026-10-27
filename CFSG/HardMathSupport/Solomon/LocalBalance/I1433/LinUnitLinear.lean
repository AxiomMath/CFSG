module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinearAut

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial
open Polynomial Matrix CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

namespace LinearCore

variable {n : ℕ} {k : Type} [Field k] [Finite k]

theorem glA_mul (A B : GL (Fin n) k) : glA (A * B) = glA A * glA B :=
  map_mul (Matrix.GeneralLinearGroup.toLin : GL (Fin n) k ≃* _) A B

theorem glA_inv (A : GL (Fin n) k) : glA A⁻¹ = (glA A)⁻¹ :=
  map_inv (Matrix.GeneralLinearGroup.toLin : GL (Fin n) k ≃* _) A

theorem mem_gl_centralizer_glA {A B : GL (Fin n) k} (h : B * A = A * B) :
    glA B ∈ gl_centralizer (glA A) := by
  rw [mem_gl_centralizer]
  have : glA B * glA A = glA A * glA B := by
    rw [← glA_mul, ← glA_mul, h]
  exact (commute_iff_eq _ _).2 (by
    have := congrArg (fun u : LinearMap.GeneralLinearGroup k (Fin n → k) =>
      (u : Module.End k (Fin n → k))) this
    simpa using this)

theorem commutator_acts_trivially_of_scalars {A Ba Bb : GL (Fin n) k} {h : k[X]}
    (hcomm : A = Ba * Bb * Ba⁻¹ * Bb⁻¹) (hBa : Ba * A = A * Ba) (hBb : Bb * A = A * Bb)
    (ca cb : AdjoinRoot h)
    (hca : ∀ v : primaryComponent (glA A : Module.End k (Fin n → k)) h,
      (glA Ba : Module.End k (Fin n → k)) (v : Fin n → k) = ((ca • v :
        primaryComponent (glA A : Module.End k (Fin n → k)) h) : Fin n → k))
    (hcb : ∀ v : primaryComponent (glA A : Module.End k (Fin n → k)) h,
      (glA Bb : Module.End k (Fin n → k)) (v : Fin n → k) = ((cb • v :
        primaryComponent (glA A : Module.End k (Fin n → k)) h) : Fin n → k)) :
    ∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) h,
      (glA A : Module.End k (Fin n → k)) v = v := by
  have hcentBa := mem_gl_centralizer_glA hBa
  have hcentBb := mem_gl_centralizer_glA hBb
  have hcentBaI : glA Ba⁻¹ ∈ gl_centralizer (glA A) := by
    rw [glA_inv]; exact inv_mem hcentBa
  have hcentBbI : glA Bb⁻¹ ∈ gl_centralizer (glA A) := by
    rw [glA_inv]; exact inv_mem hcentBb
  intro v hv
  have h1 : ((glA Bb⁻¹ : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) v ∈
      primaryComponent (glA A : Module.End k (Fin n → k)) h :=
    apply_mem_primaryComponent (mem_gl_centralizer.mp hcentBbI) hv
  have h2 : ((glA Ba⁻¹ : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k))
      (((glA Bb⁻¹ : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) v) ∈
      primaryComponent (glA A : Module.End k (Fin n → k)) h :=
    apply_mem_primaryComponent (mem_gl_centralizer.mp hcentBaI) h1
  set u : primaryComponent (glA A : Module.End k (Fin n → k)) h := ⟨_, h2⟩ with hu
  set Ma : Module.End k (Fin n → k) := ((glA Ba : LinearMap.GeneralLinearGroup k (Fin n → k)) :
    Module.End k (Fin n → k)) with hMa
  set Mb : Module.End k (Fin n → k) := ((glA Bb : LinearMap.GeneralLinearGroup k (Fin n → k)) :
    Module.End k (Fin n → k)) with hMb
  set Mai : Module.End k (Fin n → k) := ((glA Ba⁻¹ : LinearMap.GeneralLinearGroup k (Fin n → k)) :
    Module.End k (Fin n → k)) with hMai
  set Mbi : Module.End k (Fin n → k) := ((glA Bb⁻¹ : LinearMap.GeneralLinearGroup k (Fin n → k)) :
    Module.End k (Fin n → k)) with hMbi
  have hMaMai : ∀ w, Ma (Mai w) = w := fun w => by
    have : Ma * Mai = 1 := by
      rw [hMa, hMai, glA_inv, ← Units.val_mul, mul_inv_cancel]; rfl
    exact LinearMap.congr_fun this w
  have hMbMbi : ∀ w, Mb (Mbi w) = w := fun w => by
    have : Mb * Mbi = 1 := by
      rw [hMb, hMbi, glA_inv, ← Units.val_mul, mul_inv_cancel]; rfl
    exact LinearMap.congr_fun this w
  have e1 : ((glA A : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) v =
      Ma (Mb (u : Fin n → k)) := by
    conv_lhs => rw [hcomm]
    simp only [glA_mul, Units.val_mul, Module.End.mul_apply, hu]
    rfl
  have hMaMb : ∀ w : primaryComponent (glA A : Module.End k (Fin n → k)) h,
      Ma (Mb (w : Fin n → k)) = Mb (Ma (w : Fin n → k)) := by
    intro w
    rw [hca w, hcb w, hca (cb • w), hcb (ca • w), smul_comm]
  have e2 : Mb (Ma (u : Fin n → k)) = v := by
    show Mb (Ma (Mai (Mbi v))) = v
    rw [hMaMai, hMbMbi]
  rw [e1, hMaMb u, e2]

theorem commutator_acts_trivially_on_block {A Ba Bb : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    {h : k[X]} (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k)))
    (hcomm : A = Ba * Bb * Ba⁻¹ * Bb⁻¹)
    (hBa : Ba * A = A * Ba) (hBb : Bb * A = A * Bb)
    (hFa : ∀ g ∈ linearSpecialBlock (glA A) h, glA Ba * g = g * glA Ba)
    (hFb : ∀ g ∈ linearSpecialBlock (glA A) h, glA Bb * g = g * glA Bb) :
    ∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) h,
      (glA A : Module.End k (Fin n → k)) v = v := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨ca, hca⟩ := exists_smul_of_commute_pow_char hsq hh (ℓ := ringChar k)
    (mem_gl_centralizer_glA hBa) (fun g hg _ => hFa g hg)
  obtain ⟨cb, hcb⟩ := exists_smul_of_commute_pow_char hsq hh (ℓ := ringChar k)
    (mem_gl_centralizer_glA hBb) (fun g hg _ => hFb g hg)
  exact commutator_acts_trivially_of_scalars hcomm hBa hBb ca cb hca hcb

theorem commutator_acts_trivially_of_mult_le_one {A Ba Bb : GL (Fin n) k}
    {h : k[X]} (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k)))
    (hcomm : A = Ba * Bb * Ba⁻¹ * Bb⁻¹)
    (hBa : Ba * A = A * Ba) (hBb : Bb * A = A * Bb)
    (hm : primaryMultiplicity (glA A : Module.End k (Fin n → k)) h ≤ 1) :
    ∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) h,
      (glA A : Module.End k (Fin n → k)) v = v := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨ca, hca⟩ := exists_scalar_of_multiplicity_le_one (x := glA A) ⟨h, hh⟩ hm
    ((blockRestrict (glA A) h ⟨glA Ba, mem_gl_centralizer_glA hBa⟩ :
      blockGL (glA A : Module.End k (Fin n → k)) h) :
        Module.End (AdjoinRoot h) (primaryComponent (glA A : Module.End k (Fin n → k)) h))
  obtain ⟨cb, hcb⟩ := exists_scalar_of_multiplicity_le_one (x := glA A) ⟨h, hh⟩ hm
    ((blockRestrict (glA A) h ⟨glA Bb, mem_gl_centralizer_glA hBb⟩ :
      blockGL (glA A : Module.End k (Fin n → k)) h) :
        Module.End (AdjoinRoot h) (primaryComponent (glA A : Module.End k (Fin n → k)) h))
  refine commutator_acts_trivially_of_scalars hcomm hBa hBb ca cb (fun v => ?_) (fun v => ?_)
  · have := blockApply_blockRestrict (glA A) h ⟨glA Ba, mem_gl_centralizer_glA hBa⟩ v.1 v.2
    exact this.symm.trans (congrArg Subtype.val (hca v))
  · have := blockApply_blockRestrict (glA A) h ⟨glA Bb, mem_gl_centralizer_glA hBb⟩ v.1 v.2
    exact this.symm.trans (congrArg Subtype.val (hcb v))

theorem eq_one_of_acts_trivially {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (h : ∀ j ∈ primaryFactors (glA A : Module.End k (Fin n → k)),
      ∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) j,
        (glA A : Module.End k (Fin n → k)) v = v) : A = 1 := by
  have h1 : (glA A : Module.End k (Fin n → k)) = 1 :=
    ext_primaryComponent hsq (fun j hj v hv => by simpa using h j hj v hv)
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  simpa [map_one] using h1

theorem slGL_eq_glA (f : Matrix.SpecialLinearGroup (Fin n) k) :
    slGL n k f = glA (Matrix.SpecialLinearGroup.toGL f) := rfl

theorem commute_specialBlock_of_specialFactor {A B : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    {h : k[X]} (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k)))
    (hF : ∀ f ∈ specialFactor A h,
      B * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * B) :
    ∀ g ∈ linearSpecialBlock (glA A) h, glA B * g = g * glA B := by
  intro g hg
  obtain ⟨f, rfl⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  rw [slGL_eq_glA, ← glA_mul, ← glA_mul, hF f hg]

theorem four_le_card_of_ne_one {σ : k} (h3 : (3 : k) ≠ 0) (h0 : σ ≠ 0) (h1 : σ ≠ 1) :
    4 ≤ Nat.card k := by
  classical
  have hfin := Fintype.ofFinite k
  have h3le : 3 ≤ Fintype.card k := by
    have : ({0, 1, σ} : Finset k).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h1)]
      simp [h0.symm, (Ne.symm h1)]
    rw [← this]
    exact Finset.card_le_univ _
  rw [Nat.card_eq_fintype_card]
  by_contra hlt
  have h3eq : Fintype.card k = 3 := by omega
  apply h3
  have := FiniteField.cast_card_eq_zero k
  rwa [h3eq] at this

theorem linear_matrix_core (h3 : (3 : k) ≠ 0) {A Ba Bb : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (hcomm : A = Ba * Bb * Ba⁻¹ * Bb⁻¹)
    (hA1 : ∀ c' : kˣ, A ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c')
    {h : k[X]} (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k)))
    (hFa : ∀ f ∈ specialFactor A h,
      Ba * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * Ba)
    (hFb : ∀ f ∈ specialFactor A h,
      Bb * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * Bb)
    (hA : ∃ f ∈ specialFactor A h, ∃ c' : kˣ,
      A = Matrix.SpecialLinearGroup.toGL f * Matrix.GeneralLinearGroup.scalar (Fin n) c')
    (hQ : ∀ j ∈ primaryFactors (glA A : Module.End k (Fin n → k)), j ≠ h → IsGoodFactor A j →
      (∀ f ∈ specialFactor A j,
        Ba * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * Ba) ∧
      (∀ f ∈ specialFactor A j,
        Bb * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * Bb)) :
    False := by
  obtain ⟨f₀, hf₀, c', hAeq⟩ := hA
  have hBa : Ba * A = A * Ba := by
    rw [hAeq, ← mul_assoc, hFa f₀ hf₀, mul_assoc, mul_assoc,
      (Matrix.GeneralLinearGroup.scalar_commute c' Ba).symm]
  have hBb : Bb * A = A * Bb := by
    rw [hAeq, ← mul_assoc, hFb f₀ hf₀, mul_assoc, mul_assoc,
      (Matrix.GeneralLinearGroup.scalar_commute c' Bb).symm]
  have hAh := commutator_acts_trivially_on_block hsq hh hcomm hBa hBb
    (commute_specialBlock_of_specialFactor hsq hh hFa)
    (commute_specialBlock_of_specialFactor hsq hh hFb)
  have hAj : ∀ j ∈ primaryFactors (glA A : Module.End k (Fin n → k)), j ≠ h →
      ∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) j,
        (glA A : Module.End k (Fin n → k)) v = (c' : k) • v := by
    intro j hj hjh v hv
    have hf := (hf₀ : slGL n k f₀ ∈ linearSpecialBlock (glA A) h)
    have h1 := hf.2.1 j hj hjh v hv
    have e : (glA A : Module.End k (Fin n → k)) v =
        ((glA (Matrix.SpecialLinearGroup.toGL f₀) : LinearMap.GeneralLinearGroup k (Fin n → k)) :
          Module.End k (Fin n → k)) ((c' : k) • v) := by
      conv_lhs => rw [hAeq]
      rw [glA_mul]
      simp only [Units.val_mul, Module.End.mul_apply]
      congr 1
      ext i
      simp [glA, Matrix.GeneralLinearGroup.scalar]
    rw [e, map_smul]
    exact congrArg (fun w => (c' : k) • w) h1
  obtain ⟨j₀, hj₀, hj₀h⟩ : ∃ j ∈ primaryFactors (glA A : Module.End k (Fin n → k)), j ≠ h := by
    by_contra hcon
    push Not at hcon
    apply hA1 1
    rw [map_one]
    refine eq_one_of_acts_trivially hsq (fun j hj v hv => ?_)
    rw [hcon j hj] at hv
    exact hAh v hv
  have hσ1 : (c' : k) ≠ 1 := by
    intro hc1
    apply hA1 1
    rw [map_one]
    refine eq_one_of_acts_trivially hsq (fun j hj v hv => ?_)
    by_cases hjh : j = h
    · subst hjh; exact hAh v hv
    · rw [hAj j hj hjh v hv, hc1, one_smul]
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot hsq hj₀)
  have hcontra : (∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) j₀,
      (glA A : Module.End k (Fin n → k)) v = v) → False := by
    intro hid
    have h1 := hid v₀ hv₀
    rw [hAj j₀ hj₀ hj₀h v₀ hv₀] at h1
    have h2 : ((c' : k) - 1) • v₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact hσ1 (sub_eq_zero.1 h)
    · exact hv₀ne h
  by_cases hm : primaryMultiplicity (glA A : Module.End k (Fin n → k)) j₀ ≤ 1
  · exact hcontra (commutator_acts_trivially_of_mult_le_one hj₀ hcomm hBa hBb hm)
  · push Not at hm
    have hgood : IsGoodFactor A j₀ := by
      unfold IsGoodFactor
      by_cases h3m : 3 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) j₀
      · exact Or.inl h3m
      · refine Or.inr ⟨hm, ?_⟩
        have : Fact (Irreducible j₀) := ⟨irreducible_of_mem_primaryFactors hj₀⟩
        have hfinE : Finite (AdjoinRoot j₀) := Module.finite_of_finite k
        calc 4 ≤ Nat.card k := four_le_card_of_ne_one h3 c'.ne_zero hσ1
          _ ≤ Nat.card (AdjoinRoot j₀) := Nat.card_le_card_of_injective
            (algebraMap k (AdjoinRoot j₀)) (algebraMap k (AdjoinRoot j₀)).injective
    obtain ⟨hQa, hQb⟩ := hQ j₀ hj₀ hj₀h hgood
    exact hcontra (commutator_acts_trivially_on_block hsq hj₀ hcomm hBa hBb
      (commute_specialBlock_of_specialFactor hsq hj₀ hQa)
      (commute_specialBlock_of_specialFactor hsq hj₀ hQb))

theorem commute_of_fixes_proj {n : ℕ} {k : Type} [Field k]
    (F : Subgroup (Matrix.SpecialLinearGroup (Fin n) k)) (hF : ⁅F, F⁆ = F) (B : GL (Fin n) k)
    (hfix : ∀ f ∈ F, LinearFlag.conjAut n k B (LinearFlag.proj n k f) = LinearFlag.proj n k f) :
    ∀ f ∈ F, B * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * B := by
  have h1 := eq_of_perfect_of_central F hF (CatalogueBHigherLinearAction.slConjugation n k B)
    (fun f hf => by
      have h0 := hfix f hf
      rw [LinearFlag.conjAut_proj] at h0
      have h2 : LinearFlag.proj n k
          (f⁻¹ * CatalogueBHigherLinearAction.slConjugation n k B f) = 1 := by
        rw [map_mul, map_inv, h0, inv_mul_cancel]
      exact LinearFlag.scalars_le_center n k (LinearFlag.proj_eq_one_iff.1 h2))
  intro f hf
  have h4 := h1 f hf
  have h5 := LinearFlag.coe_slConjugation B f
  rw [h4] at h5
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have h6 : ((Matrix.SpecialLinearGroup.toGL f : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (f : Matrix (Fin n) (Fin n) k) := rfl
  rw [h6]
  have h7 : ((B⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
      (B : Matrix (Fin n) (Fin n) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (B : Matrix (Fin n) (Fin n) k) * (f : Matrix (Fin n) (Fin n) k)
      = (B : Matrix (Fin n) (Fin n) k) * (f : Matrix (Fin n) (Fin n) k) *
          (((B⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (B : Matrix (Fin n) (Fin n) k)) := by
        rw [h7, mul_one]
    _ = ((B : Matrix (Fin n) (Fin n) k) * (f : Matrix (Fin n) (Fin n) k) *
          ((B⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) * (B : Matrix (Fin n) (Fin n) k) := by
        simp only [mul_assoc]
    _ = (f : Matrix (Fin n) (Fin n) k) * (B : Matrix (Fin n) (Fin n) k) := by rw [← h5]

theorem three_dvd_card_SL {E : Type} [Field E] [Finite E] {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := by
  rw [LinearFlag.card_SL_eq (by omega)]
  set q := Nat.card E with hq
  have hq1 : 2 ≤ q := Finite.one_lt_card
  have hexp : 1 ≤ m * (m - 1) / 2 := by
    have : 2 ≤ m * (m - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    omega
  have hdvd1 : q ∣ q ^ (m * (m - 1) / 2) := dvd_pow_self q (by omega)
  have hdvd2 : (q ^ 2 - 1) ∣ ∏ j ∈ Finset.Icc 2 m, (q ^ j - 1) :=
    Finset.dvd_prod_of_mem (fun j => q ^ j - 1) (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
  have h3 : 3 ∣ q * (q ^ 2 - 1) := by
    have hge : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    rcases (by omega : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2) with h | h | h
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
    · refine Dvd.dvd.mul_left ?_ _
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
      omega
    · refine Dvd.dvd.mul_left ?_ _
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
      omega
  exact h3.trans (mul_dvd_mul hdvd1 hdvd2)

theorem glaPComponent_proj_specialFactor {n : ℕ} {k : Type} [Field k] [Finite k] {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    {j : k[X]} (hj : j ∈ primaryFactors (glA A : Module.End k (Fin n → k)))
    (hgood : IsGoodFactor A j) :
    GLAPComponent 3 (fixSubgroup (LinearFlag.conjAut n k A))
      ((specialFactor A j).map (LinearFlag.proj n k)) := by
  classical
  have hFq : CFSG.IsQuasisimple (specialFactor A j) := isQuasisimple_specialFactor hsq hj hgood
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) j := by
    unfold IsGoodFactor at hgood
    omega
  have : Fact (Irreducible j) := ⟨irreducible_of_mem_primaryFactors hj⟩
  have h3 : 3 ∣ Nat.card (specialFactor A j) := by
    obtain ⟨e⟩ := LieComp.nonempty_mulEquiv_specialFactor hsq hj
    have : Finite (AdjoinRoot j) := Module.finite_of_finite k
    rw [← Nat.card_congr e.toEquiv]
    exact three_dvd_card_SL hm
  have hle := specialFactor_le_fixSubgroup A j
  have hsub : CFSG.Open.IsSubnormal (specialFactor A j)
      (fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)) := by
    refine CFSG.Open.IsSubnormal.step hle ?_ (CFSG.Open.IsSubnormal.refl _)
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro g c hg hc
    exact conj_mem_specialFactor hc hg
  have hcomp := i253_glaPComponent_of_subnormal hle hsub (open_isQuasisimple hFq) h3
  exact glaPComponent_map_fixSubgroup (LinearFlag.proj n k)
    (by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_center n k)
    (CatalogueBHigherLinearAction.slConjugation n k A) (LinearFlag.conjAut n k A)
    (fun g => (LinearFlag.conjAut_proj A g).symm) (LinearFlag.proj_surjective n k)
    Nat.prime_three hcomp

end LinearCore

open LinearCore in
theorem linear_core {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (h3 : (3 : k) ≠ 0)
    (hZ : Subgroup.center (LinearFlag.projectiveSL n k) = ⊥)
    {a b : MulAut (LinearFlag.projectiveSL n k)} {x : LinearFlag.projectiveSL n k}
    {J : Subgroup (LinearFlag.projectiveSL n k)} (c : CoreCfg a b x J) : False := by
  classical
  obtain ⟨Ba, hBa⟩ := exists_conjAut_of_mem_commutator_of_two_le hn c.a_mem
  obtain ⟨Bb, hBb⟩ := exists_conjAut_of_mem_commutator_of_two_le hn c.b_mem
  set A : GL (Fin n) k := Ba * Bb * Ba⁻¹ * Bb⁻¹ with hAdef
  have hdetA : (A : Matrix (Fin n) (Fin n) k).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det A = 1 := by
      rw [hAdef]
      simp only [map_mul, map_inv]
      have := commutatorElement_eq_one_iff_mul_comm.2
        (mul_comm (Matrix.GeneralLinearGroup.det Ba) (Matrix.GeneralLinearGroup.det Bb))
      rwa [commutatorElement_def] at this
    have h2 := congrArg (fun u : kˣ => (u : k)) h1
    simpa using h2
  set t : Matrix.SpecialLinearGroup (Fin n) k := ⟨(A : Matrix (Fin n) (Fin n) k), hdetA⟩ with ht
  have htA : Matrix.SpecialLinearGroup.toGL t = A := Units.ext rfl
  have hconjA : LinearFlag.conjAut n k A = MulAut.conj x := by
    rw [hAdef, map_mul, map_mul, map_mul, map_inv, map_inv, ← hBa, ← hBb]
    exact c.comm
  have hxt : x = LinearFlag.proj n k t := by
    apply conj_injective_of_center_bot hZ
    rw [← hconjA, ← htA, LinearFlag.conjAut_toGL]
  have hx3 : x ^ 3 = 1 := c.order ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    have := c.order
    rw [h1, orderOf_one] at this
    omega
  have hpk : ((3 : ℕ) : k) ≠ 0 := by exact_mod_cast h3
  obtain ⟨c₃, hA3⟩ : ∃ c₃ : kˣ, A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c₃ := by
    have h1 : LinearFlag.proj n k (t ^ 3) = 1 := by rw [map_pow, ← hxt, hx3]
    obtain ⟨c₃, -, hc₃⟩ := LinearFlag.proj_eq_one_iff.1 h1
    refine ⟨c₃, ?_⟩
    rw [← htA, ← map_pow]
    apply Units.ext
    exact hc₃
  have hsq := squarefree_minpoly_glA hpk hA3
  have hA1 : ∀ c' : kˣ, A ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c' := by
    intro c' hc'
    apply hx1
    apply conj_injective_of_center_bot hZ
    rw [← hconjA, hc', LinearFlag.conjAut_scalar, map_one]
  have hfix : fixSubgroup (LinearFlag.conjAut n k A) = Subgroup.centralizer ({x} : Set _) := by
    rw [hconjA]; exact fixSubgroup_conj_eq x
  have hJc : GLAPComponent 3 (fixSubgroup (LinearFlag.conjAut n k A)) J := by
    rw [hfix]; exact c.comp
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJc
  have hlayer := perfectInLayer_conjAut hpk hA3 J hJc.1 hperf
  obtain ⟨hJcomp, -⟩ := glaPComponent_isComponent_of_le_layer hJc hlayer
  obtain ⟨⟨⟨h, hh⟩, hgood⟩, hJeq⟩ := LieComp.linear_inner_components hpk hA3 J hJcomp
  have hFq := isQuasisimple_specialFactor hsq hh hgood
  have hFperf : ⁅specialFactor A h, specialFactor A h⁆ = specialFactor A h :=
    Subgroup.isPerfect_iff.1 hFq.1
  have hfixJ : ∀ f ∈ specialFactor A h, a (LinearFlag.proj n k f) = LinearFlag.proj n k f ∧
      b (LinearFlag.proj n k f) = LinearFlag.proj n k f := fun f hf =>
    c.centralizes J (hfix ▸ hJc) (LinearFlag.proj n k f) (hJeq ▸ ⟨f, hf, rfl⟩)
  have hFa := commute_of_fixes_proj (specialFactor A h) hFperf Ba
    (fun f hf => by rw [← hBa]; exact (hfixJ f hf).1)
  have hFb := commute_of_fixes_proj (specialFactor A h) hFperf Bb
    (fun f hf => by rw [← hBb]; exact (hfixJ f hf).2)
  have hA : ∃ f ∈ specialFactor A h, ∃ c' : kˣ,
      A = Matrix.SpecialLinearGroup.toGL f * Matrix.GeneralLinearGroup.scalar (Fin n) c' := by
    have hxJ : x ∈ (specialFactor A h).map (LinearFlag.proj n k) := hJeq ▸ c.mem
    obtain ⟨f, hf, hfx⟩ := hxJ
    obtain ⟨c', -, hc'⟩ := LinearFlag.proj_eq_proj_iff.1 (hfx.trans hxt)
    refine ⟨f, hf, c', ?_⟩
    have h1 : Matrix.SpecialLinearGroup.toGL (f⁻¹ * t) =
        Matrix.GeneralLinearGroup.scalar (Fin n) c' := Units.ext hc'
    rw [← htA, ← h1, ← map_mul]
    congr 1
    group
  have hQ : ∀ j ∈ primaryFactors (glA A : Module.End k (Fin n → k)), j ≠ h → IsGoodFactor A j →
      (∀ f ∈ specialFactor A j,
        Ba * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * Ba) ∧
      (∀ f ∈ specialFactor A j,
        Bb * Matrix.SpecialLinearGroup.toGL f = Matrix.SpecialLinearGroup.toGL f * Bb) := by
    intro j hj hjh hjg
    have hcomp := glaPComponent_proj_specialFactor hsq hj hjg
    rw [hfix] at hcomp
    have hFjq := isQuasisimple_specialFactor hsq hj hjg
    have hFjperf : ⁅specialFactor A j, specialFactor A j⁆ = specialFactor A j :=
      Subgroup.isPerfect_iff.1 hFjq.1
    have hfixj : ∀ f ∈ specialFactor A j, a (LinearFlag.proj n k f) = LinearFlag.proj n k f ∧
        b (LinearFlag.proj n k f) = LinearFlag.proj n k f := fun f hf =>
      c.centralizes _ hcomp (LinearFlag.proj n k f) ⟨f, hf, rfl⟩
    exact ⟨commute_of_fixes_proj _ hFjperf Ba (fun f hf => by rw [← hBa]; exact (hfixj f hf).1),
      commute_of_fixes_proj _ hFjperf Bb (fun f hf => by rw [← hBb]; exact (hfixj f hf).2)⟩
  exact linear_matrix_core h3 hsq rfl hA1 hh hFa hFb hA hQ

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
