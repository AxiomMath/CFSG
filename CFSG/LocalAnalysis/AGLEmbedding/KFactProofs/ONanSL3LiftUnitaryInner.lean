module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryToral
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

variable {p f : ℕ} {F : Type} [Field F]

theorem scalar_inv_mul_pow_three {M : GL (Fin 3) F} {c₀ u : Fˣ}
    (hM : M ^ 3 = GeneralLinearGroup.scalar (Fin 3) c₀) (hu : u ^ 3 = c₀) :
    (GeneralLinearGroup.scalar (Fin 3) u⁻¹ * M) ^ 3 = 1 := by
  rw [((commute_scalar u⁻¹ M).symm).mul_pow, hM, ← map_pow, ← map_mul, inv_pow, hu,
    inv_mul_cancel, map_one]

theorem closure_fixed_eq_top_unitary_of_conj
    {X : Type} [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    (h : UnitaryFieldData p f F) (h3 : 3 ∣ p ^ f + 1) (hq : 2 < p ^ f)
    (ψ : unitarySU p f F 3 ≃* K)
    (hzc : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    {A : Subgroup X} (hAe : Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27) (hzA : z ∈ A)
    (hconj : ∀ a : A, ∃ B : unitaryIsom3 h, actionAut K ψ (a : X) = suConj h B) :
    Subgroup.closure {x : K | ∃ a ∈ A, a ∉ Subgroup.centralizer (K : Set X) ∧
      a * (x : X) * a⁻¹ = x} = ⊤ := by
  classical
  have hfin := h.finite
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hC
  let φ : A →* MulAut (unitarySU p f F 3) := (actionAut K ψ).comp A.subtype
  have hφψ : ∀ (a : A) (s : unitarySU p f F 3),
      ((ψ (φ a s) : K) : X) = (a : X) * (ψ s : X) * (a : X)⁻¹ := fun a s =>
    coe_psi_actionAut K ψ a s
  have hker : ∀ a : A, a ∈ φ.ker ↔ (a : X) ∈ C := by
    intro a
    rw [MonoidHom.mem_ker, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro hφa κ hκ
      obtain ⟨s, hs⟩ := ψ.surjective ⟨κ, hκ⟩
      have h1 := hφψ a s
      rw [hφa] at h1
      simp only [MulAut.one_apply] at h1
      have h2 : (ψ s : X) = κ := congrArg Subtype.val hs
      rw [h2] at h1
      have : (a : X) * κ = κ * (a : X) := by
        rw [eq_mul_inv_iff_mul_eq] at h1
        exact h1.symm
      exact this.symm
    · intro hκ
      ext1 s
      apply ψ.injective
      apply Subtype.ext
      rw [hφψ]
      have := hκ (ψ s : X) (ψ s).2
      simp only [MulAut.one_apply]
      rw [← this]
      group
  have hAC : ∀ a : A, (a : X) ∈ C → (a : X) ∈ Subgroup.zpowers z := by
    intro a ha
    exact mem_zpowers_of_pow_three_eq_one R hzc hz3 hΩ ha (hAe.2 a a.2)
  have hker_card : Nat.card φ.ker ≤ 3 := by
    have hinj : Function.Injective (fun a : φ.ker => (⟨(a.1 : X), hAC a.1 ((hker a.1).1 a.2)⟩ :
        Subgroup.zpowers z)) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : Subgroup.zpowers z => (x : X)) hab
    calc Nat.card φ.ker ≤ Nat.card (Subgroup.zpowers z) := Nat.card_le_card_of_injective _ hinj
      _ = 3 := by rw [Nat.card_zpowers, hz3]
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (hAe.2 a a.2)
  have hφ3 : ∀ a : A, φ a ^ 3 = 1 := fun a => by rw [← map_pow, hA3, map_one]
  have hφconj : ∀ a : A, ∃ B : unitaryIsom3 h, φ a = suConj h B := hconj
  obtain ⟨f₁, hf₁ker, s₁, hs₁⟩ := exists_inner_of_index h h3 φ hφconj (by omega)
  let B₁ : unitaryIsom3 h := ⟨(s₁ : GL (Fin 3) F), unitarySU_le_unitaryIsom3 s₁.2⟩
  have hB₁ : φ f₁ = suConj h B₁ := by
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [hs₁ t, coe_suConj]
    rfl
  set κ₁ : X := (ψ s₁ : X) with hκ₁
  have hκ₁K : κ₁ ∈ K := (ψ s₁).2
  set c₁ : X := κ₁⁻¹ * (f₁ : X) with hc₁
  have hc₁C : c₁ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro κ hκ
    obtain ⟨t, ht⟩ := ψ.surjective ⟨κ, hκ⟩
    have h2 : (ψ t : X) = κ := congrArg Subtype.val ht
    have h1 := hφψ f₁ t
    rw [hs₁ t, map_mul, map_mul, map_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2] at h1
    rw [hc₁]
    have h3 : (f₁ : X) * κ = κ₁ * κ * κ₁⁻¹ * (f₁ : X) := by
      rw [h1]; group
    calc κ * (κ₁⁻¹ * (f₁ : X)) = κ₁⁻¹ * (κ₁ * κ * κ₁⁻¹ * (f₁ : X)) := by group
      _ = κ₁⁻¹ * ((f₁ : X) * κ) := by rw [h3]
      _ = κ₁⁻¹ * (f₁ : X) * κ := by group
  have hf₁eq : (f₁ : X) = κ₁ * c₁ := by rw [hc₁]; group
  obtain ⟨f₂', hf₂'A, hf₂'not⟩ := exists_mem_not_mem_sup_zpowers hAe hAcard hzA f₁.2
  let f₂ : A := ⟨f₂', hf₂'A⟩
  obtain ⟨B₂, hB₂⟩ := hφconj f₂
  have hcomm : (f₁ : X) * (f₂ : X) = (f₂ : X) * (f₁ : X) :=
    congrArg Subtype.val (hAe.1.is_comm.comm f₁ f₂)
  obtain ⟨hζeq, hζmem⟩ := conj_aux_mem (K := K) hcomm hκ₁K hc₁C hf₁eq
  set ζ' : X := κ₁⁻¹ * ((f₂ : X) * κ₁ * (f₂ : X)⁻¹) with hζ'
  have hζ'K : ζ' ∈ K := hζmem.1
  have hζ'C : ζ' ∈ C := hζmem.2
  set w' : unitarySU p f F 3 := ψ.symm ⟨ζ', hζ'K⟩ with hw'
  have hw'center : w' ∈ Subgroup.center (unitarySU p f F 3) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply ψ.injective
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hζ'C (ψ t : X) (ψ t).2
    simp only [hw', map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    exact this
  have hw'sc : w' ∈ unitaryScalars h 3 := by
    rw [← center_unitarySU_three (h := h) hq]
    exact hw'center
  obtain ⟨c, hcN, hc3, hcw'⟩ := hw'sc
  have hθs₁ : φ f₂ s₁ = s₁ * w' := by
    apply ψ.injective
    apply Subtype.ext
    rw [hφψ]
    simp only [hw', map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    rw [← hκ₁, hζ']
    group
  have hconjB₂ : ∀ t : unitarySU p f F 3, ((φ f₂ t : unitarySU p f F 3) : GL (Fin 3) F) =
      (B₂ : GL (Fin 3) F) * t * (B₂ : GL (Fin 3) F)⁻¹ := fun t => by
    rw [hB₂, coe_suConj]
    rfl
  have hGL : (B₂ : GL (Fin 3) F) * (s₁ : GL (Fin 3) F) * (B₂ : GL (Fin 3) F)⁻¹ =
      (s₁ : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hconjB₂ s₁, hθs₁]
    change (s₁ : GL (Fin 3) F) * (w' : GL (Fin 3) F) = _
    rw [hcw']
  have hdet₁ : ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    ((mem_unitarySU_iff h).1 s₁.2).1
  let s₁sl : SpecialLinearGroup (Fin 3) F :=
    ⟨((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdet₁⟩
  have hc3' : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hmat : ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((B₂ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hGL
    simp only [Units.val_mul, coe_scalar_eq_smul] at this
    rw [this, Matrix.mul_smul, Matrix.mul_one]
  have hc1 : c = 1 := by
    by_contra hc1
    have hc1' : (c : F) ≠ 1 := fun hh => hc1 (Units.ext hh)
    have hs3 : ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 :=
      cube_eq_one_of_conj_eq_smul s₁sl B₂ hc3' hc1' hmat
    have hκ3 : κ₁ ^ 3 = 1 := by
      have h1 : (s₁ ^ 3 : unitarySU p f F 3) = 1 := by
        apply Subtype.ext
        apply Units.ext
        simpa using hs3
      calc κ₁ ^ 3 = ((ψ (s₁ ^ 3) : K) : X) := by simp [hκ₁]
        _ = 1 := by rw [h1]; simp
    have hc3x : c₁ ^ 3 = 1 := by
      have hcm : Commute κ₁ c₁ := Subgroup.mem_centralizer_iff.mp hc₁C κ₁ hκ₁K
      have h1 : (f₁ : X) ^ 3 = 1 := hAe.2 f₁ f₁.2
      rw [hf₁eq, hcm.mul_pow, hκ3, one_mul] at h1
      exact h1
    have hc₁z : c₁ ∈ Subgroup.zpowers z :=
      mem_zpowers_of_pow_three_eq_one R hzc hz3 hΩ hc₁C hc3x
    have hconj : (f₂ : X) * c₁ * (f₂ : X)⁻¹ = c₁ := conj_eq_of_mem_zpowers hzc hc₁z f₂
    have hζ'1 : ζ' = 1 := by rw [hζeq, hconj]; group
    have hw'1 : w' = 1 := by
      have : (⟨ζ', hζ'K⟩ : K) = 1 := Subtype.ext hζ'1
      rw [hw', this, map_one]
    apply hc1
    have h00 : ((w' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by rw [hw'1]; simp
    rw [hcw', coe_scalar_eq_smul] at h00
    apply Units.ext
    simpa using h00
  have hcommg : (B₂ : GL (Fin 3) F) * (s₁ : GL (Fin 3) F) =
      (s₁ : GL (Fin 3) F) * (B₂ : GL (Fin 3) F) := by
    rw [hc1, map_one, mul_one] at hGL
    exact mul_inv_eq_iff_eq_mul.1 hGL
  have hB₁3 : suConj h B₁ ^ 3 = 1 := by rw [← hB₁]; exact hφ3 f₁
  have hB₂3 : suConj h B₂ ^ 3 = 1 := by rw [← hB₂]; exact hφ3 f₂
  obtain ⟨c₀, hc₀N, hc₀⟩ := exists_scalar_pow_three h hB₁3
  obtain ⟨c₂, hc₂N, hc₂⟩ := exists_scalar_pow_three h hB₂3
  have hs3 : ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c₀ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc₀
    rw [coe_scalar_eq_smul, Units.val_pow_eq_pow_val] at this
    exact this
  have hg3 : ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c₂ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc₂
    rw [coe_scalar_eq_smul, Units.val_pow_eq_pow_val] at this
    exact this
  obtain ⟨ωu, hωu⟩ : ∃ ω : Fˣ, orderOf ω = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply exists_prime_orderOf_dvd_card' 3
    rw [Nat.card_units, h.card_eq_sq]
    have hq1 : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
      simpa [sq] using this.symm.symm
    rw [hq1]
    exact Dvd.dvd.mul_right h3 _
  have hω3 : (ωu : F) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ωu
    rw [hωu] at this
    simpa [← Units.val_pow_eq_pow_val] using congrArg Units.val this
  have hω1 : (ωu : F) ≠ 1 := by
    intro hh
    have : ωu = 1 := Units.ext hh
    rw [this, orderOf_one] at hωu
    omega
  obtain ⟨η, hη⟩ := exists_cube_root_of_det_one _ hdet₁ hs3
  have hη0 : η ≠ 0 := by
    rintro rfl
    exact c₀.ne_zero (by rw [← hη]; ring)
  have hns : ∀ c : F, ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ c • 1 := by
    intro c hc
    apply hf₁ker
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [hs₁ t, MulAut.one_apply]
    apply Units.ext
    have hcm : ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hc]; simp
    have := conj_eq_self_of_comm (M := (s₁ : GL (Fin 3) F)) hcm
    simpa [Units.val_mul] using this
  have hsη : ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (η ^ 3) • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [hη]; exact hs3
  have hs_prod := prod_sub_cube_roots ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) hω3 hω1 hsη
  have hsg' : ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((B₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((s₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hcommg
    simp only [Units.val_mul] at this
    exact this.symm
  obtain ⟨b, hb⟩ := exists_cube_root_of_commute _ _ hsg' (fun j : Fin 3 => η * (ωu : F) ^ j.val)
    hs_prod hns hg3
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact c₂.ne_zero (by rw [← hb]; ring)
  let ηu : Fˣ := Units.mk0 η hη0
  let bu : Fˣ := Units.mk0 b hb0
  have hηu : ηu ^ 3 = c₀ := Units.ext (by simpa [ηu] using hη)
  have hbu : bu ^ 3 = c₂ := Units.ext (by simpa [bu] using hb)
  have hNη : h.norm (ηu : F) = 1 := norm_eq_one_of_pow_three h h3 ηu (by rw [hηu]; exact hc₀N)
  have hNb : h.norm (bu : F) = 1 := norm_eq_one_of_pow_three h h3 bu (by rw [hbu]; exact hc₂N)
  have hNinv : ∀ u : Fˣ, h.norm (u : F) = 1 → h.norm ((u⁻¹ : Fˣ) : F) = 1 := fun u hu => by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hu, inv_one]
  let t₁ : unitaryIsom3 h :=
    ⟨GeneralLinearGroup.scalar (Fin 3) ηu⁻¹, scalar_mem_unitaryIsom3 h (hNinv ηu hNη)⟩ * B₁
  let t₂ : unitaryIsom3 h :=
    ⟨GeneralLinearGroup.scalar (Fin 3) bu⁻¹, scalar_mem_unitaryIsom3 h (hNinv bu hNb)⟩ * B₂
  have ht₁ : suConj h t₁ = suConj h B₁ := by
    rw [map_mul, suConj_scalar h (hNinv ηu hNη), one_mul]
  have ht₂ : suConj h t₂ = suConj h B₂ := by
    rw [map_mul, suConj_scalar h (hNinv bu hNb), one_mul]
  have hφt₁ : φ f₁ = suConj h t₁ := hB₁.trans ht₁.symm
  have hφt₂ : φ f₂ = suConj h t₂ := hB₂.trans ht₂.symm
  have ht₁3 : ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) ^ 3 = 1 := scalar_inv_mul_pow_three hc₀ hηu
  have ht₂3 : ((t₂ : unitaryIsom3 h) : GL (Fin 3) F) ^ 3 = 1 := scalar_inv_mul_pow_three hc₂ hbu
  have hcomm₁₂ : ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) * (t₂ : GL (Fin 3) F) =
      (t₂ : GL (Fin 3) F) * (t₁ : GL (Fin 3) F) := by
    have hc : Commute ((t₁ : unitaryIsom3 h) : GL (Fin 3) F)
        ((t₂ : unitaryIsom3 h) : GL (Fin 3) F) :=
      Commute.mul_left
        (Commute.mul_right (commute_scalar bu⁻¹ (GeneralLinearGroup.scalar (Fin 3) ηu⁻¹))
          (commute_scalar ηu⁻¹ (B₂ : GL (Fin 3) F)).symm)
        (Commute.mul_right (commute_scalar bu⁻¹ (s₁ : GL (Fin 3) F)) hcommg.symm)
    exact hc.eq
  have hq2 : p ^ f ≠ 2 := by omega
  have hT := closure_centralizers_unitarySU_pair (n := 2) h h3 hq2 (mem_primeFormUnitary_one t₁.2)
    (mem_primeFormUnitary_one t₂.2) hcomm₁₂ ht₁3 ht₂3
  have hfix : ∀ (a : A) (M : unitaryIsom3 h), φ a = suConj h M → (a : X) ∉ C →
      ∀ t : unitarySU p f F 3, (t : GL (Fin 3) F) * (M : GL (Fin 3) F) =
        (M : GL (Fin 3) F) * (t : GL (Fin 3) F) →
        (ψ t : K) ∈ {x : K | ∃ a ∈ A, a ∉ Subgroup.centralizer (K : Set X) ∧
          a * (x : X) * a⁻¹ = x} := by
    intro a M hM haC t ht
    refine ⟨(a : X), a.2, haC, ?_⟩
    have h1 := hφψ a t
    have h2 : φ a t = t := by
      apply Subtype.ext
      rw [hM, coe_suConj]
      change (M : GL (Fin 3) F) * (t : GL (Fin 3) F) * (M : GL (Fin 3) F)⁻¹ = t
      rw [← ht, mul_inv_cancel_right]
    rw [h2] at h1
    exact h1.symm
  have hf₁C : (f₁ : X) ∉ C := fun hh => hf₁ker ((hker f₁).2 hh)
  have hf₂C : (f₂ : X) ∉ C := fun hh => hf₂'not (Subgroup.mem_sup_left (hAC f₂ hh))
  have hnot := not_mem_zpowers_of_not_mem_sup (z := z) (f₁ := (f₁ : X)) (f₂ := f₂')
    (hAe.2 f₂' hf₂'A) hf₂'not
  have hf₁f₂C : ((f₁ * f₂ : A) : X) ∉ C := fun hh => hnot.1 (hAC (f₁ * f₂) hh)
  have hf₁f₂sqC : ((f₁ * f₂ ^ 2 : A) : X) ∉ C := fun hh => hnot.2 (hAC (f₁ * f₂ ^ 2) hh)
  have hsub : ∀ t ∈ {t : unitarySU p f F 3 |
      ∃ x ∈ ({((t₁ : unitaryIsom3 h) : GL (Fin 3) F), ((t₂ : unitaryIsom3 h) : GL (Fin 3) F),
        ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) * ((t₂ : unitaryIsom3 h) : GL (Fin 3) F),
        ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) * ((t₂ : unitaryIsom3 h) : GL (Fin 3) F) ^ 2} :
          Set (GL (Fin 3) F)), (t : GL (Fin 3) F) * x = x * (t : GL (Fin 3) F)},
      (ψ t : K) ∈ {x : K | ∃ a ∈ A, a ∉ Subgroup.centralizer (K : Set X) ∧
        a * (x : X) * a⁻¹ = x} := by
    rintro t ⟨x, hx, hxt⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hfix f₁ t₁ hφt₁ hf₁C t hxt
    · exact hfix f₂ t₂ hφt₂ hf₂C t hxt
    · exact hfix (f₁ * f₂) (t₁ * t₂) (by rw [map_mul, map_mul, hφt₁, hφt₂]) hf₁f₂C t hxt
    · exact hfix (f₁ * f₂ ^ 2) (t₁ * t₂ ^ 2)
        (by rw [map_mul, map_mul, map_pow, map_pow, hφt₁, hφt₂]) hf₁f₂sqC t hxt
  rw [eq_top_iff]
  have hmap : Subgroup.map (ψ : unitarySU p f F 3 →* K) (Subgroup.closure
      {t : unitarySU p f F 3 |
      ∃ x ∈ ({((t₁ : unitaryIsom3 h) : GL (Fin 3) F), ((t₂ : unitaryIsom3 h) : GL (Fin 3) F),
        ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) * ((t₂ : unitaryIsom3 h) : GL (Fin 3) F),
        ((t₁ : unitaryIsom3 h) : GL (Fin 3) F) * ((t₂ : unitaryIsom3 h) : GL (Fin 3) F) ^ 2} :
          Set (GL (Fin 3) F)), (t : GL (Fin 3) F) * x = x * (t : GL (Fin 3) F)}) = ⊤ := by
    rw [hT, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr ψ.surjective
  rw [MonoidHom.map_closure] at hmap
  rw [← hmap]
  exact Subgroup.closure_mono (Set.image_subset_iff.mpr fun t ht => hsub t ht)

theorem exists_generating_elemAbelian_unitary
    {X : Type} [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    (h : UnitaryFieldData p f F) (h3 : 3 ∣ p ^ f + 1) (hq : 2 < p ^ f)
    (hσ : ∀ σ : F ≃+* F, σ ^ 3 = 1 → σ = 1) (ψ : unitarySU p f F 3 ≃* K)
    (hzc : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    (hrank : Open.pRank 3 (R : Subgroup X) = 3) :
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      Subgroup.closure {x : K | ∃ a ∈ A, a ∉ Subgroup.centralizer (K : Set X) ∧
        a * (x : X) * a⁻¹ = x} = ⊤ := by
  classical
  obtain ⟨A, hAR, hAe, hAcard⟩ := exists_elemAbelian_card_27 hrank
  have hzR : z ∈ (R : Subgroup X) := mem_sylow_of_central R hzc hz3
  have hzA : z ∈ A := mem_of_pRank_eq_three hrank hzc hz3 hzR hAR hAe hAcard
  refine ⟨A, hAR, hAe, hAcard, closure_fixed_eq_top_unitary_of_conj R K z h h3 hq ψ hzc hz3 hΩ hAe
    hAcard hzA fun a => ?_⟩
  have hφ3 : actionAut K ψ (a : X) ^ 3 = 1 := by
    rw [← map_pow, show (a : X) ^ 3 = 1 from hAe.2 a a.2, map_one]
  exact exists_suConj_of_pow_three_eq_one h hq hσ hφ3

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
