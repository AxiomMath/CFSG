module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Irr
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks

variable {F : Type} [Field F] [Fintype F]

theorem card_le_of_fixed_conjAut (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F)
    {M : Subgroup (projectiveSL 4 F)} (hM : ∀ x ∈ M, conjAut 4 F A x = x) :
    Nat.card M ≤ 2 * Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin 4) F))) := by
  classical
  choose L hL using fun x : M => proj_surjective 4 F (x : projectiveSL 4 F)
  set G : M → GL (Fin 4) F := fun x => SpecialLinearGroup.toGL (L x) with hG
  have hGinj : Function.Injective G := by
    intro x y hxy
    apply Subtype.ext
    rw [← hL x, ← hL y]
    congr 1
    exact SpecialLinearGroup.toGL_injective hxy
  have hsign : ∀ x : M, A * G x * A⁻¹ = G x ∨ A * G x * A⁻¹ = -G x := by
    intro x
    have h1 := hM x x.2
    rw [← hL x, conjAut_proj] at h1
    rcases eq_of_proj_eq hF h1.symm with h | h
    · left
      apply Units.ext
      change (A : Matrix (Fin 4) (Fin 4) F) * (L x : Matrix (Fin 4) (Fin 4) F) *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (L x : Matrix (Fin 4) (Fin 4) F)
      rw [← coe_slConjugation A (L x)]
      exact h
    · right
      apply Units.ext
      change (A : Matrix (Fin 4) (Fin 4) F) * (L x : Matrix (Fin 4) (Fin 4) F) *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -(L x : Matrix (Fin 4) (Fin 4) F)
      rw [← coe_slConjugation A (L x)]
      exact h
  have hcomm : ∀ g : GL (Fin 4) F, A * g * A⁻¹ = g → g ∈ Subgroup.centralizer {A} := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * A = A * g * A⁻¹ * A := by rw [hg]
      _ = A * g := by group
  by_cases hex : ∃ g₁ : GL (Fin 4) F, A * g₁ * A⁻¹ = -g₁
  · obtain ⟨g₁, hg₁⟩ := hex
    have hinr : ∀ g : GL (Fin 4) F, A * g * A⁻¹ = -g → A * (g₁⁻¹ * g) * A⁻¹ = g₁⁻¹ * g := by
      intro g hg
      calc A * (g₁⁻¹ * g) * A⁻¹ = (A * g₁ * A⁻¹)⁻¹ * (A * g * A⁻¹) := by group
        _ = g₁⁻¹ * g := by rw [hg₁, hg, inv_neg, neg_mul_neg]
    let φ : M → Subgroup.centralizer ({A} : Set (GL (Fin 4) F)) ⊕
        Subgroup.centralizer ({A} : Set (GL (Fin 4) F)) := fun x =>
      if h : A * G x * A⁻¹ = G x then Sum.inl ⟨G x, hcomm _ h⟩
      else Sum.inr ⟨g₁⁻¹ * G x, hcomm _ (hinr _ ((hsign x).resolve_left h))⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply hGinj
      simp only [φ] at hxy
      split_ifs at hxy with h1 h2 h2
      · exact congrArg Subtype.val (Sum.inl_injective hxy)
      · have := congrArg Subtype.val (Sum.inr_injective hxy)
        exact mul_left_cancel this
    calc Nat.card M ≤ Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin 4) F)) ⊕
          Subgroup.centralizer ({A} : Set (GL (Fin 4) F))) := Nat.card_le_card_of_injective φ hφ
      _ = 2 * Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin 4) F))) := by
          rw [Nat.card_sum, two_mul]
  · simp only [not_exists] at hex
    let φ : M → Subgroup.centralizer ({A} : Set (GL (Fin 4) F)) := fun x =>
      ⟨G x, hcomm _ ((hsign x).resolve_right (hex _))⟩
    have hφ : Function.Injective φ := fun x y hxy => hGinj (congrArg Subtype.val hxy)
    calc Nat.card M ≤ Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin 4) F))) :=
          Nat.card_le_card_of_injective φ hφ
      _ ≤ 2 * Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin 4) F))) := by omega

theorem card_centralizer_le (A : GL (Fin 4) F) (ν : Fˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) ν) (hns : ¬ IsSquare (ν : F)) :
    Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin 4) F))) ≤
      ((Nat.card F ^ 2) ^ 2 - 1) * ((Nat.card F ^ 2) ^ 2 - Nat.card F ^ 2) := by
  classical
  obtain ⟨E, _, _, ρ, hE, hρ⟩ := exists_centralizer_embedding_card A ν hsq hns
  let := Fintype.ofFinite E
  calc Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin 4) F))) ≤ Nat.card (GL (Fin 2) E) :=
        Nat.card_le_card_of_injective ρ hρ
    _ = _ := by
        rw [Matrix.card_GL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
          pow_one, ← Nat.card_eq_fintype_card, hE]

theorem false_of_fixed_conjAut (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F) (ν : Fˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) ν) (hns : ¬ IsSquare (ν : F))
    {M : Subgroup (projectiveSL 4 F)} (hM : ∀ x ∈ M, conjAut 4 F A x = x)
    (hcard : 2 * Nat.card M =
      Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) : False := by
  have h1 := card_le_of_fixed_conjAut hF A hM
  have h2 := card_centralizer_le A ν hsq hns
  set q := Nat.card F with hq
  have hq3 : 3 ≤ q := by
    rw [hq, Nat.card_eq_fintype_card]
    omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e1 : (q ^ 2) ^ 2 = q ^ 4 := by ring
  rw [e1] at h2
  have e2 : q ^ 4 - q ^ 2 = q ^ 2 * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_one, ← pow_add]
  rw [e2] at h2
  set a := q ^ 2 - 1 with ha
  set b := q ^ 4 - 1 with hb
  have ha0 : 0 < a := by
    have : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
    omega
  have hb0 : 0 < b := by
    have : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have hle : q ^ 4 * a * b ≤ 4 * q ^ 2 * a * b := by
    calc q ^ 4 * a * b = 2 * Nat.card M := hcard.symm
      _ ≤ 2 * (2 * (b * (q ^ 2 * a))) := by
          have := h1.trans (Nat.mul_le_mul_left 2 h2)
          omega
      _ = 4 * q ^ 2 * a * b := by ring
  have hab : 0 < a * b := Nat.mul_pos ha0 hb0
  have h4 : q ^ 4 ≤ 4 * q ^ 2 := by
    by_contra hlt
    rw [not_le] at hlt
    have := Nat.mul_lt_mul_of_pos_right hlt hab
    nlinarith
  have h5 : q ^ 2 * q ^ 2 ≤ 4 * q ^ 2 := by
    calc q ^ 2 * q ^ 2 = q ^ 4 := by ring
      _ ≤ 4 * q ^ 2 := h4
  have h6 : q ^ 2 ≤ 4 := Nat.le_of_mul_le_mul_right h5 (by positivity)
  have : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
  omega

theorem sq_eq_nonsquare_of_fixed (hF : Fintype.card F % 4 = 3) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsq : s ∣ Fintype.card F ^ 2 + 1) (A : GL (Fin 4) F)
    (hα1 : conjAut 4 F A ≠ 1) (hα2 : conjAut 4 F A ^ 2 = 1) {y : projectiveSL 4 F}
    (hy : orderOf y = s) (hfix : conjAut 4 F A y = y) :
    ∃ ν : Fˣ, A ^ 2 = GeneralLinearGroup.scalar (Fin 4) ν ∧ ¬ IsSquare (ν : F) := by
  classical
  have h2 := two_ne_zero_of_card_mod_four hF
  obtain ⟨-, ν, hν⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 4) (by norm_num) (A ^ 2) 1
    (by rw [map_one, mul_one, map_pow, hα2])
  refine ⟨ν, hν.symm, fun ⟨r, hr⟩ => hα1 ?_⟩
  obtain ⟨Y, rfl⟩ := proj_surjective 4 F y
  have hY1 : proj 4 F Y ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hy
    exact hs.one_lt.ne' hy.symm
  have hYs : proj 4 F (Y ^ s) = 1 := by rw [map_pow, ← hy, pow_orderOf_eq_one]
  rw [proj_eq_one_iff, mem_scalars] at hYs
  obtain ⟨c, hc4, hYc⟩ := hYs
  have hc4' : (c : F) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
  have hcpm : (c : F) = 1 ∨ (c : F) = -1 := eq_one_or_eq_neg_one_of_pow_four hF hc4'
  have hodd : Odd s := hs.odd_of_ne_two hs2
  set MY := (Y : Matrix (Fin 4) (Fin 4) F) with hMY
  have hMYs : MY ^ s = (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [hMY, ← Matrix.SpecialLinearGroup.coe_pow, hYc, Matrix.scalar_apply, smul_one_eq_diagonal]
  set MA := (A : Matrix (Fin 4) (Fin 4) F) with hMA
  set MAi := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hMAi
  have hAAi : MA * MAi = 1 := by rw [hMA, hMAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : MAi * MA = 1 := by rw [hMA, hMAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconj : MA * MY * MAi = MY ∨ MA * MY * MAi = -MY := by
    rw [conjAut_proj] at hfix
    rcases eq_of_proj_eq hF hfix.symm with h | h
    · left
      rw [hMA, hMY, hMAi, ← coe_slConjugation, h]
    · right
      rw [hMA, hMY, hMAi, ← coe_slConjugation, h]
  have hcomm : MA * MY = MY * MA := by
    rcases hconj with h | h
    · calc MA * MY = MA * MY * MAi * MA := by
            rw [Matrix.mul_assoc _ MAi, hAiA, Matrix.mul_one]
        _ = MY * MA := by rw [h]
    · exfalso
      have hpow' : ∀ n : ℕ, (MA * MY * MAi) ^ n = MA * MY ^ n * MAi := by
        intro n
        induction n with
        | zero => simp [hAAi]
        | succ n ih =>
          rw [pow_succ, ih, pow_succ]
          calc MA * MY ^ n * MAi * (MA * MY * MAi) = MA * MY ^ n * (MAi * MA) * MY * MAi := by
                simp only [Matrix.mul_assoc]
            _ = MA * (MY ^ n * MY) * MAi := by
                rw [hAiA, Matrix.mul_one]
                simp only [Matrix.mul_assoc]
      have hpow := hpow' s
      rw [h, Odd.neg_pow hodd, hMYs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAAi] at hpow
      have h00 := congrFun (congrFun hpow 0) 0
      simp at h00
      rcases hcpm with h1 | h1 <;> rw [h1] at h00 <;> apply h2 <;>
        first | linear_combination h00 | linear_combination -h00
  set G : Module.End F (Fin 4 → F) := Matrix.toLinAlgEquiv' ((c : F) • MY) with hG
  have hGs : G ^ s = 1 := by
    rw [hG, ← map_pow, smul_pow, hMYs, smul_smul, ← pow_succ, ← Units.val_pow_eq_pow_val]
    have : c ^ (s + 1) = 1 := by
      rcases hcpm with h1 | h1
      · have : c = 1 := Units.ext h1
        rw [this, one_pow]
      · have : c = -1 := Units.ext (by rw [h1, Units.val_neg, Units.val_one])
        rw [this, Even.neg_one_pow (by rcases hodd with ⟨t, ht⟩; exact ⟨t + 1, by omega⟩)]
    rw [this, Units.val_one, one_smul, map_one]
  have hG1 : G ≠ 1 := by
    intro h1
    apply hY1
    rw [proj_eq_one_iff, mem_scalars]
    refine ⟨c, hc4, ?_⟩
    have h3 : (c : F) • MY = 1 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_one]
      exact h1
    have hcc : (c : F) * c = 1 := by
      rcases hcpm with h1 | h1 <;> rw [h1] <;> ring
    calc MY = ((c : F) * c) • MY := by rw [hcc, one_smul]
      _ = (c : F) • ((c : F) • MY) := by rw [smul_smul]
      _ = scalar (Fin 4) (c : F) := by rw [h3, Matrix.scalar_apply, smul_one_eq_diagonal]
  have hAG : Commute G (Matrix.toLinAlgEquiv' MA) := by
    rw [hG, Commute, SemiconjBy, ← map_mul, ← map_mul, Matrix.smul_mul, Matrix.mul_smul,
      hcomm]
  set W := LinearMap.ker (Matrix.toLinAlgEquiv' MA - r • 1) with hW
  have hWinv : W ≤ W.comap G := by
    intro v hv
    rw [Submodule.mem_comap, hW, LinearMap.mem_ker]
    rw [hW, LinearMap.mem_ker] at hv
    have : (Matrix.toLinAlgEquiv' MA - r • 1) (G v) = G ((Matrix.toLinAlgEquiv' MA - r • 1) v) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, LinearMap.smul_apply,
        LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
      congr 1
      exact (LinearMap.congr_fun hAG v).symm
    rw [this, hv, map_zero]
  have hdim : Module.finrank F (Fin 4 → F) ≤ 2 ^ (1 + 1) := by
    rw [Module.finrank_fin_fun]
    norm_num
  have hsq' : s ∣ Fintype.card F ^ 2 ^ 1 + 1 := by simpa using hsq
  have hAsq : MA * MA = ((r * r : F)) • 1 := by
    have := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F)) hν
    simp only [GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at this
    rw [hMA, ← sq, ← this, hr, Matrix.scalar_apply, smul_one_eq_diagonal]
  have hscal : ∃ t : F, MA = t • 1 := by
    rcases invariant_eq_bot_or_top hs hs2 hsq' hdim hGs hG1 W hWinv with hbot | htop
    · refine ⟨-r, ?_⟩
      apply Matrix.toLinAlgEquiv'.injective
      apply LinearMap.ext
      intro v
      have hinj : ∀ w, (Matrix.toLinAlgEquiv' MA - r • 1) w = 0 → w = 0 := by
        intro w hw
        have : w ∈ W := hw
        rw [hbot, Submodule.mem_bot] at this
        exact this
      have h0 := hinj ((Matrix.toLinAlgEquiv' MA + r • 1) v) (by
        rw [LinearMap.sub_apply, LinearMap.add_apply, map_add, LinearMap.smul_apply,
          Module.End.one_apply, map_smul, LinearMap.smul_apply, Module.End.one_apply]
        have hAA : Matrix.toLinAlgEquiv' MA (Matrix.toLinAlgEquiv' MA v) = (r * r) • v := by
          rw [← Module.End.mul_apply, ← map_mul, hAsq, map_smul, map_one]
          rfl
        rw [hAA, smul_add, smul_smul]
        abel)
      rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg] at h0
      rw [h0, map_smul, map_one, LinearMap.smul_apply, Module.End.one_apply, neg_smul]
    · refine ⟨r, ?_⟩
      apply Matrix.toLinAlgEquiv'.injective
      apply LinearMap.ext
      intro v
      have : v ∈ W := by rw [htop]; exact Submodule.mem_top
      rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
      rw [this, map_smul, map_one]
  obtain ⟨t, ht⟩ := hscal
  have ht0 : t ≠ 0 := by
    rintro rfl
    have := (GeneralLinearGroup.det A).ne_zero
    rw [GeneralLinearGroup.val_det_apply, ← hMA, ht, zero_smul, Matrix.det_zero] at this
    exact this rfl
  have hAs : A = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 t ht0) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hMA, ht, Matrix.scalar_apply,
      smul_one_eq_diagonal]
  rw [hAs]
  exact conjAut_scalar _

end StabL

end CFSG.ComponentClassification.CatFactsL4U4
