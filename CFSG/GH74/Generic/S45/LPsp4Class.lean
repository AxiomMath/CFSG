module

public import CFSG.GH74.Generic.S45.LPsp4Mat
public import CFSG.GH74.Generic.S45.LEvenBender
public import CFSG.GH74.Generic.S45.LPsl2Field
public import CFSG.GH74.Generic.S45.LPsl2Lin
public import CFSG.GH74.Generic.S45.LCoverEq
public import CFSG.GH74.Generic.S45.LOddG
public import CFSG.GH74.Generic.Front.SpAut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerA

public section

namespace CFSG.GH74.Generic.S45

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.Uniqueness.Bender

theorem eight_dvd_sq_sub_one {n : ℕ} (hn : Odd n) : 8 ∣ n ^ 2 - 1 := by
  have h := odd_sq_mod_eight hn
  rw [pow_two]
  generalize n * n = N at h
  omega

theorem sixteen_dvd_pow_four_sub_one {n : ℕ} (hn : Odd n) : 16 ∣ n ^ 4 - 1 := by
  have h : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨ n % 16 = 9 ∨ n % 16 = 11 ∨
      n % 16 = 13 ∨ n % 16 = 15 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have h4 : n ^ 4 % 16 = 1 := by
    rcases h with h | h | h | h | h | h | h | h <;> simp [Nat.pow_mod, h]
  have hpos : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ (by obtain ⟨k, hk⟩ := hn; omega)
  omega

theorem sixteen_dvd_two_mul_card_SL2 {n : ℕ} (hn : Odd n) : 16 ∣ 2 * (n * (n ^ 2 - 1)) := by
  obtain ⟨m, hm⟩ := eight_dvd_sq_sub_one hn
  rw [hm]
  exact ⟨n * m, by ring⟩

theorem sixteen_dvd_nonsquare_card {n : ℕ} (hn : Odd n) : 16 ∣ n ^ 2 * ((n ^ 2) ^ 2 - 1) := by
  have h : (n ^ 2) ^ 2 = n ^ 4 := by ring
  rw [h]
  exact Dvd.dvd.mul_left (sixteen_dvd_pow_four_sub_one hn) _

theorem sixteen_dvd_field_card {k : ℕ} (hk : Odd k) :
    16 ∣ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) :=
  Dvd.dvd.mul_left (Dvd.dvd.mul_left (sixteen_dvd_pow_four_sub_one hk) _) _

theorem isSquare_mul_of_not_isSquare {F : Type} [Field F] [Finite F] {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by rw [h, mul_zero]⟩
  have hb0 : b ≠ 0 := fun h => hb ⟨0, by rw [h, mul_zero]⟩
  have h1 : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.2 ha
  have h2 : quadraticChar F b = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hb
  have hab : quadraticChar F (a * b) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).1 hab


theorem psp4_fixed_data {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel S .PSp 2 r f) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : ringChar F ≠ 2)
      (e₀ : S ≃* StatedProj (StatedSp 2 F)) (A : gsp 2 F) (c : StatedSp 2 F),
        (∀ s, e₀ (ya s) = conjAut 2 F A (e₀ s)) ∧ conjSp 2 F A c = c ∧
          orderOf (SymplecticFlag.proj 2 F c) = 4 := by
  classical
  obtain ⟨⟨hr, hf, h2n, hne⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hr.ne_zero)
  have hodd : Odd (Nat.card F) := odd_card_of_card_eq hr hr2 hF
  have hqodd : Odd (r ^ f) := hF ▸ hodd
  have h2 := two_ne_zero_of_odd_card hodd
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this
    exact_mod_cast this
  let α : MulAut (StatedProj (StatedSp 2 F)) := e₀.symm.trans (ya.trans e₀)
  have hαya : ∀ s, e₀ (ya s) = α (e₀ s) := fun s => by simp [α]
  have hα2 : α * α = 1 := by
    ext x
    simp only [MulAut.mul_apply, MulAut.one_apply, α, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    have := congrArg (fun φ : MulAut S => φ (e₀.symm x)) hQ.sq
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [this, MulEquiv.apply_symm_apply]
  have hα1 : α ≠ 1 := by
    intro h
    apply hQ.ne
    ext s
    have := hαya s
    rw [h, MulAut.one_apply] at this
    simpa using e₀.injective this
  have hsP : IsSimpleGroup (StatedProj (StatedSp 2 F)) := e₀.symm.isSimpleGroup
  have hfix : fixOf ya = autFixed ya := by
    ext x
    rw [mem_fixOf, mem_autFixed_iff]
  have hLbX : Lb ≤ fixOf ya := by rw [hfix]; exact hQ.le
  have hLbq : CFSG.IsQuasisimple ↥Lb := isQuasisimple_of_simple_nonab hQ.simple hQ.nonab
  have hLbe : Even (Nat.card ↥Lb) := even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans hQ.four_dvd_card)
  have hLbc : CFSG.IsPComponent 2 (Lb.subgroupOf (fixOf ya)) :=
    isPComponent_two_of_quasisimple' hLbX hLbq (by rw [hfix]; exact hQ.sub) hLbe
  obtain ⟨hJX, hJ⟩ := isPComponent_map_fixOf (β := e₀) (α₀ := α) hαya hLbX hLbc
  set J : Subgroup (StatedProj (StatedSp 2 F)) := Lb.map e₀.toMonoidHom with hJdef
  have hcardJ : Nat.card J = Nat.card Lb :=
    (Nat.card_congr (Lb.equivMapOfInjective _ e₀.injective).toEquiv).symm
  have hJ16 : ¬ 16 ∣ 2 * Nat.card J := by
    rw [hcardJ, mul_comm, hQ.card]
    exact not_sixteen_dvd hQ.mod8
  have hnabP : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e₀ a, e₀ b, fun h => hab (e₀.injective (by simpa only [map_mul] using h))⟩
  have hPc : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ :=
    center_eq_bot_of_simple_nonab hsP hnabP
  suffices key : ∃ (A : gsp 2 F) (c : StatedSp 2 F), α = conjAut 2 F A ∧ conjSp 2 F A c = c ∧
      orderOf (SymplecticFlag.proj 2 F c) = 4 by
    obtain ⟨A, c, hA, hc, hord⟩ := key
    exact ⟨F, inferInstance, inferInstance, hchar, e₀, A, c,
      fun s => (hαya s).trans (by rw [hA]), hc, hord⟩
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 F A := by rw [hα, map_one, mul_one]
    set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hAm
    have hAA : Am * Am = (d : F) • 1 := by
      have h1 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2) F =>
        (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hd
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
      have h1' : ((CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) (1 : F ≃+* F)
          (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Am := by
        ext i j
        rfl
      rw [h1'] at h1
      rw [h1, Matrix.smul_one_eq_diagonal]
      rfl
    set μ := multiplierUnit A with hμdef
    have hμ : Amᵀ * formJ 2 F * Am = (μ : F) • formJ 2 F := multiplierUnit_spec A
    have hdμ : (d : F) = μ ∨ (d : F) = -μ := by
      have e1 : (Am * Am)ᵀ * formJ 2 F * (Am * Am) = ((μ : F) * μ) • formJ 2 F := by
        rw [transpose_mul, show Amᵀ * Amᵀ * formJ 2 F * (Am * Am) =
          Amᵀ * (Amᵀ * formJ 2 F * Am) * Am by simp only [Matrix.mul_assoc], hμ,
          Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul]
      rw [hAA, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one, smul_smul] at e1
      exact mul_self_eq_mul_self_iff.mp (smul_formJ_injective 2 e1)
    by_cases hsq : ∃ l : F, l ^ 2 = (μ : F)
    ·
      obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at hl
        exact μ.ne_zero hl.symm
      have hA'sp : (l⁻¹ • Am)ᵀ * formJ 2 F * (l⁻¹ • Am) = formJ 2 F := by
        rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
          smul_smul, ← hl]
        rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
      set A' : StatedSp 2 F := toSp (l⁻¹ • Am) hA'sp with hA'def
      have hAz : (A : GL (Fin 2 ⊕ Fin 2) F) =
          GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
            (A' : GL (Fin 2 ⊕ Fin 2) F) := by
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
          Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
          Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
      have hαu : α = MulAut.conj (SymplecticFlag.proj 2 F A') :=
        hα'.trans (conjAut_eq_conj_of_scalar_mul A _ A' hAz)
      set u := SymplecticFlag.proj 2 F A' with hudef
      have hu1 : u ≠ 1 := fun h => hα1 (by rw [hαu, h, map_one])
      have hu2 : u * u = 1 := by
        have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
        have hmem : u * u ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
          rw [mem_center_iff]
          intro g
          have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ g) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
            _ = u * u * g := by group
        rw [hPc, Subgroup.mem_bot] at hmem
        exact hmem
      have hu : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd hu
      rcases hg with hg | hg
      ·
        exfalso
        let φ : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) := MulAut.conj g⁻¹
        have hφu : φ u = u1 F := by
          simpa only [φ, MulAut.conj_apply, inv_inv] using hg
        have hcomm : ∀ x, φ (α x) = MulAut.conj (φ u) (φ x) := fun x => by
          rw [hαu]
          exact conj_comm φ u x
        obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hJX hJ
        rw [fixOf_conj, hφu] at hJ0X hJ0
        obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hJ0X hJ0
        have hcardφ : Nat.card (J.map φ.toMonoidHom) = Nat.card J :=
          (Nat.card_congr (J.equivMapOfInjective _ φ.injective).toEquiv).symm
        have hc : Nat.card J = Nat.card F * (Nat.card F ^ 2 - 1) := by
          rcases hE with hE | hE
          · rw [← hcardφ, hE, ← Nat.card_congr (E1Equiv h2).toEquiv, card_SL2]
          · rw [← hcardφ, hE, ← Nat.card_congr (E2Equiv h2).toEquiv, card_SL2]
        apply hJ16
        rw [hc]
        exact sixteen_dvd_two_mul_card_SL2 hodd
      ·
        obtain ⟨A₂, c, hA₂, hc, hord⟩ := exists_data_u2 h2 hg
        exact ⟨A₂, c, hαu.trans hA₂.symm, hc, hord⟩
    · push Not at hsq
      rcases hdμ with hdm | hdm
      ·
        exfalso
        have hdsq : ∀ l : F, l ^ 2 ≠ (d : F) := by rw [hdm]; exact hsq
        have hμd : Amᵀ * formJ 2 F * Am = (d : F) • formJ 2 F := by rw [hdm]; exact hμ
        obtain ⟨hQs, hcard⟩ := fixOf_conjSp_nonsquare hr hr2 hf hF A d.ne_zero hdsq hAA hμd
        have hθα : ∀ g, α (SymplecticFlag.proj 2 F g) = SymplecticFlag.proj 2 F (conjSp 2 F A g) := fun g => by
          rw [hα', conjAut_proj]
        have hJeq := eq_map_fixOf_of_isPComponent (conjSp 2 F A) hθα hQs hJX hJ
        have h2c := card_map_fixOf_mul_two h2 (conjSp 2 F A) fun z hz => conjSp_scalar A hz
        rw [← hJeq, hcard] at h2c
        apply hJ16
        rw [mul_comm, h2c]
        exact sixteen_dvd_nonsquare_card hqodd
      ·
        have ha : (d : F) ≠ 0 := d.ne_zero
        have hA : Amᵀ * formJ 2 F * Am = (-(d : F)) • formJ 2 F := by
          rw [hμ, hdm, neg_neg]
        obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
        by_cases h2sq : ∃ s : F, s * s = 2
        · obtain ⟨s, hs⟩ := h2sq
          obtain ⟨c, hc, hord⟩ := exists_data_alphaI_sq h2 ha hs hg
          exact ⟨A, c, hα', hc, hord⟩
        · push Not at h2sq
          have h2ns : ¬ IsSquare (2 : F) := fun ⟨s, hs⟩ => h2sq s hs.symm
          have hμns : ¬ IsSquare (μ : F) := fun ⟨s, hs⟩ => hsq s (by rw [sq]; exact hs.symm)
          obtain ⟨t, ht⟩ := isSquare_mul_of_not_isSquare h2ns hμns
          have ht0 : t ≠ 0 := by
            rintro rfl
            rw [mul_zero] at ht
            exact mul_ne_zero h2 μ.ne_zero ht
          have hy : 2 * (t⁻¹ * t⁻¹) * (d : F) = -1 := by
            rw [hdm]
            calc 2 * (t⁻¹ * t⁻¹) * -(μ : F) = -((2 * (μ : F)) * (t⁻¹ * t⁻¹)) := by ring
              _ = -1 := by rw [ht]; field_simp
          obtain ⟨c, hc, hord⟩ := exists_data_alphaI ha hy hg
          exact ⟨A, c, hα', hc, hord⟩
  ·
    exfalso
    have hθα : ∀ g, α (SymplecticFlag.proj 2 F g) = SymplecticFlag.proj 2 F ((conjSp 2 F A * fieldSp 2 F σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQs, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    have hJeq := eq_map_fixOf_of_isPComponent _ hθα hQs hJX hJ
    have h2c := card_map_fixOf_mul_two h2 (conjSp 2 F A * fieldSp 2 F σ)
      fun z hz => conjSp_fieldSp_scalar A σ hz
    rw [← hJeq, hcard] at h2c
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : F // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield F σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield F σ c).symm)
    rw [hk] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield F σ)
    have hkodd : Odd k := by
      have : Odd (k ^ 2) := hKk ▸ hodd
      exact (Nat.odd_mul.mp (by rwa [sq] at this)).1
    apply hJ16
    rw [mul_comm, h2c]
    exact sixteen_dvd_field_card hkodd

theorem Hyp1310.false_of_sp4_fixed {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L) {yb : MulAut (K ⧸ Subgroup.center K)}
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (ψ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSp 2 F)) (A : gsp 2 F) (c : StatedSp 2 F)
    (hψ : ∀ s, ψ (yb s) = conjAut 2 F A (ψ s)) (hc : conjSp 2 F A c = c)
    (hord : orderOf (SymplecticFlag.proj 2 F c) = 4) : False := by
  classical
  obtain ⟨hKp, hZ2, -, -, hno4, -⟩ := hyp.data
  have hodd : Odd (Nat.card F) := by
    have := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    rw [Nat.card_eq_fintype_card, hn]
    exact (hp.odd_of_ne_two hF).pow
  have hPp : Group.IsPerfect (StatedSp 2 F) := CFSG.GH74.Generic.isPerfect_statedSp2_of_odd hodd
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSp 2 F), Function.Surjective π →
      π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
        ∃ σ : StatedSp 2 F →* E, ∀ x, π (σ x) = x :=
    fun E _ _ π hπ hcen h2' =>
      (CFSG.LieType.Steinberg.odd_symplectic_central_two_extension_splitting hF 2 hπ hcen
        h2').imp fun _ h => h.1
  let η : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hηker : η.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have hη2 : IsPGroup 2 η.ker := by rw [hηker]; exact hZ2
  let β : StatedSp 2 F →* K ⧸ Subgroup.center K :=
    ψ.symm.toMonoidHom.comp (SymplecticFlag.proj 2 F)
  have hβ : Function.Surjective β :=
    ψ.symm.surjective.comp (SymplecticHigher.proj_surjective (K := F) (r := 2))
  have hτ : ∀ g, β (conjSp 2 F A g) = yb (β g) := by
    intro g
    change ψ.symm (SymplecticFlag.proj 2 F (conjSp 2 F A g)) =
      yb (ψ.symm (SymplecticFlag.proj 2 F g))
    rw [← conjAut_proj]
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply, hψ, MulEquiv.apply_symm_apply]
  have hordβ : orderOf (β c) = 4 := by
    change orderOf (ψ.symm (SymplecticFlag.proj 2 F c)) = 4
    rw [MulEquiv.orderOf_eq]
    exact hord
  obtain ⟨x, hx, h4⟩ := exists_fixed_dvd_of_cover hKp hPp hsplit hη hηker.le hη2 hβ
    (y := y) (yb := yb) (fun k => (hyb k).symm) hτ hc (by rw [hordβ])
  exact hno4 x hx h4

theorem oddRow_psp4 {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ center K) .PSp 2 r f) : False := by
  obtain ⟨yb, Lb, q, hyb, hQ, -⟩ := hyp.quot_data
  obtain ⟨F, _, _, hF, e₀, A, c, he, hc, hord⟩ :=
    psp4_fixed_data hyp.1.1.2.1 hyp.1.1.2.2 hr2 hmodel hQ
  exact hyp.false_of_sp4_fixed hyb hF e₀ A c he hc hord

theorem oddRowG_PSp4 : OddRowG_PSp4 :=
  fun _ _ _ _ _ hypg _ _ hr2 hmodel => oddRow_psp4 hypg.2 hr2 hmodel

end CFSG.GH74.Generic.S45
