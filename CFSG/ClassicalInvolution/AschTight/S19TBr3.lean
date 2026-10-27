module

public import CFSG.ClassicalInvolution.AschTight.S19QF2a
public import CFSG.ClassicalInvolution.AschTight.S19QF2b
public import CFSG.ClassicalInvolution.AschTight.S1911F0c
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem orderOf_slQuatI (hF : ringChar F ≠ 2) : orderOf (QuaternionMatrices.slQuatI F) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := QuaternionMatrices.slQuatI F) ?_ ?_
  · simpa using h
  · intro h1
    have h2 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [pow_one] at h2
    rw [QuaternionMatrices.coe_slQuatI_sq] at h2
    exact QuaternionMatrices.neg_one_ne_one_matrix hF (by simpa using h2)
  · simpa using QuaternionMatrices.slQuatI_pow_four (K := F)

variable {p e : ℕ} [Fact p.Prime]

theorem exists_fixed_of_isSquare (hp : p ≠ 2) (hq : 5 ≤ p ^ e)
    (β : MulAut SL(2, GaloisField p e)) (hβ : β * β = 1) (G₀ : GL (Fin 2) (GaloisField p e))
    (hβG : ∀ b, β b = semilinHom G₀ (RingEquiv.refl _) b)
    (hsq : IsSquare ((G₀ : Matrix (Fin 2) (Fin 2) (GaloisField p e)).det)) :
    ∃ h : SL(2, GaloisField p e), orderOf h = 4 ∧ β h = h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (GaloisField p e)) := Generic.odd_natCard_galoisField hp hq
  have hF : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp
  obtain ⟨μ, hμ⟩ := hsq
  have hdet : (G₀ : Matrix (Fin 2) (Fin 2) (GaloisField p e)).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel G₀))
    rw [Units.val_mul, Matrix.det_mul, Units.val_one, Matrix.det_one] at h1
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [hμ, zero_mul])
  have hdet1 : (μ⁻¹ • (G₀ : Matrix (Fin 2) (Fin 2) (GaloisField p e))).det = 1 := by
    rw [Matrix.det_smul, hμ, Fintype.card_fin]
    field_simp
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : SL(2, GaloisField p e),
      (g₀ : Matrix (Fin 2) (Fin 2) (GaloisField p e)) = μ⁻¹ • (G₀ : Matrix (Fin 2) (Fin 2) _) :=
    ⟨⟨_, hdet1⟩, rfl⟩
  have hcomm : ∀ b, β b * g₀ = g₀ * b := by
    intro b
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hβG,
      coe_semilinHom, hg₀]
    have hmap : (b : Matrix (Fin 2) (Fin 2) (GaloisField p e)).map (RingEquiv.refl _) =
        (b : Matrix (Fin 2) (Fin 2) (GaloisField p e)) := by
      ext i j
      rfl
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  have hβg : ∀ b, β b = g₀ * b * g₀⁻¹ := fun b => by
    rw [← hcomm b]
    group
  have hββ : ∀ b, β (β b) = b := fun b => by
    have := congrArg (fun φ : MulAut SL(2, GaloisField p e) => φ b) hβ
    simpa [MulAut.mul_apply] using this
  have hcen : g₀ ^ 2 ∈ Subgroup.center SL(2, GaloisField p e) := by
    rw [Subgroup.mem_center_iff]
    intro b
    have h1 := hββ b
    rw [hβg, hβg] at h1
    calc b * g₀ ^ 2 = g₀ * (g₀ * b * g₀⁻¹) * g₀⁻¹ * g₀ ^ 2 := by rw [h1]
      _ = g₀ ^ 2 * b := by rw [sq]; group
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  have hr2 : r * r = 1 := by simpa [sq] using hr
  rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
  ·
    have hg2 : g₀ * g₀ = 1 := by
      apply Subtype.ext
      rw [← sq, ← hrg]
      simp
    have hβ1 : ∀ b, β b = b := by
      intro b
      rcases (isUniqueInvolution_top_neg_one hodd).unique g₀ (Subgroup.mem_top _) hg2 with h | h
      · rw [hβg, h]
        group
      · rw [hβg, h]
        apply Subtype.ext
        simp
    exact ⟨QuaternionMatrices.slQuatI _, orderOf_slQuatI hF, hβ1 _⟩
  ·
    refine ⟨g₀, ?_, ?_⟩
    · have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g₀) ?_ ?_
      · simpa using h
      · intro h1
        have h2 := congrArg
          (fun g : SL(2, GaloisField p e) => (g : Matrix (Fin 2) (Fin 2) (GaloisField p e))) h1
        simp only [pow_one] at h2
        rw [← hrg, map_neg, map_one, Matrix.SpecialLinearGroup.coe_one] at h2
        exact QuaternionMatrices.neg_one_ne_one_matrix hF h2
      · have h4 : g₀ ^ (2 ^ (1 + 1)) = (g₀ ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
        rw [h4]
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg]
        simp [sq]
    · rw [hβg]
      group

theorem fixed_or_nonsquare (hp : p ≠ 2) (hq : 5 ≤ p ^ e)
    (β : MulAut SL(2, GaloisField p e)) (hβ : β * β = 1) :
    (∃ h : SL(2, GaloisField p e), orderOf h = 4 ∧ β h = h) ∨
      ∃ G₀ : GL (Fin 2) (GaloisField p e), (∀ b, β b = semilinHom G₀ (RingEquiv.refl _) b) ∧
        ¬ IsSquare ((G₀ : Matrix (Fin 2) (Fin 2) (GaloisField p e)).det) := by
  obtain ⟨G₀, σ, hβG, hσ2⟩ := mulAut_involution_structure hp hq β hβ
  by_cases hσ1 : σ = 1
  · have hβ' : ∀ b, β b = semilinHom G₀ (RingEquiv.refl _) b := fun b => by rw [hβG b, hσ1]; rfl
    by_cases hsq : IsSquare ((G₀ : Matrix (Fin 2) (Fin 2) (GaloisField p e)).det)
    · exact Or.inl (exists_fixed_of_isSquare hp hq β hβ G₀ hβ' hsq)
    · exact Or.inr ⟨G₀, hβ', hsq⟩
  left
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨k, hek, -⟩ := eq_frobenius_of_sq_eq_one he hσ2 hσ1
  subst hek
  have hk : 0 < k := by omega
  have hinv : ∀ b, semilinHom G₀ σ (semilinHom G₀ σ b) = b := by
    intro b
    rw [← hβG, ← hβG]
    have := congrArg (fun φ : MulAut SL(2, GaloisField p (2 * k)) => φ b) hβ
    simpa [MulAut.mul_apply] using this
  obtain ⟨ι⟩ := S1911.factF0 p k hp hk σ hσ1 hσ2 G₀ hinv
  have hF : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]
    exact hp
  refine ⟨(ι.symm (QuaternionMatrices.slQuatI _) : SL(2, GaloisField p (2 * k))), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_slQuatI hF]
  · rw [hβG]
    exact (ι.symm (QuaternionMatrices.slQuatI _)).2

theorem isSquare_mul_of_not_isSquare {K : Type} [Field K] [Finite K]
    {a b : K} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have := Fintype.ofFinite K
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ IsSquare.zero)
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

end SL2

section Act

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def oddAct (J : Subgroup G) {H : Type} [Group H]
    (e₁ : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* H) :
    Subgroup.normalizer (J : Set G) →* MulAut H :=
  (MulAut.congr e₁).toMonoidHom.comp ((oddCoreQuotientAut ↥J).comp (normalizerConj J))

theorem exists_orderOf_four_of_fixed (J : Subgroup G) {H : Type} [Group H]
    (e₁ : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* H) (n : Subgroup.normalizer (J : Set G))
    (hn2 : IsPGroup 2 (Subgroup.zpowers (n : G))) {h : H} (hh : orderOf h = 4)
    (hfix : oddAct J e₁ n h = h) :
    ∃ w ∈ J, orderOf w = 4 ∧ w * n = n * w := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e₁.symm h)
  have hA : oddCoreQuotientAut ↥J (normalizerConj J n) (e₁.symm h) = e₁.symm h := by
    have := congrArg e₁.symm hfix
    simpa [oddAct, MulAut.congr] using this
  rw [← hl, oddCoreQuotientAut_mk] at hA
  have hl' : (l : G)⁻¹ * ((n : G) * l * (n : G)⁻¹) ∈ oddCoreOf J := by
    have h1 := QuotientGroup.eq.mp hA.symm
    rw [mem_oddCoreOf_iff]
    refine ⟨J.mul_mem (J.inv_mem l.2) (normalizerConj J n l).2, ?_⟩
    convert h1 using 1
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe])
  obtain ⟨o, ho, hno⟩ := S19Q.exists_mul_mem_centralizer_of_odd (oddCoreOf_odd_natCard J) hn2
    (mem_normalizer_oddCoreOf_of_mem_normalizer n.2) hl'
  have hoJ : o ∈ J := by
    obtain ⟨o', -, rfl⟩ := ho
    exact o'.2
  have hwJ : (l : G) * o ∈ J := J.mul_mem l.2 hoJ
  have hmk : (QuotientGroup.mk (⟨(l : G) * o, hwJ⟩ : ↥J) :
      ↥J ⧸ classicalInvolutionOddCore ↥J) = e₁.symm h := by
    rw [← hl]
    apply QuotientGroup.eq.mpr
    rw [mem_oddCoreOf_iff] at ho
    obtain ⟨hoJ', ho'⟩ := ho
    convert (classicalInvolutionOddCore ↥J).inv_mem ho' using 1
    apply Subtype.ext
    simp
  have h4 : 4 ∣ orderOf (⟨(l : G) * o, hwJ⟩ : ↥J) := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (classicalInvolutionOddCore ↥J))
      (⟨(l : G) * o, hwJ⟩ : ↥J)
    rw [QuotientGroup.mk'_apply, hmk, MulEquiv.orderOf_eq, hh] at h1
    exact h1
  obtain ⟨m, hm⟩ := h4
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (orderOf_pos _).ne' hm
  refine ⟨((l : G) * o) ^ m, J.pow_mem hwJ m, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe (⟨(l : G) * o, hwJ⟩ : ↥J)] at hm
    rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left 4 hm.symm), hm, Nat.mul_div_cancel _
      (Nat.pos_of_ne_zero hm0)]
  · exact ((Commute.pow_left (Commute.symm hno) m) : Commute _ _).eq

variable {p e : ℕ} [Fact p.Prime]

theorem exists_orderOf_four_of_four_group (J : Subgroup G) (hp : p ≠ 2) (hq : 5 ≤ p ^ e)
    (e₁ : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* SL(2, GaloisField p e))
    (a b : Subgroup.normalizer (J : Set G)) (ha2 : (a : G) * a = 1) (hb2 : (b : G) * b = 1)
    (hab : (a : G) * b = b * a) (hna : ¬ ∃ w ∈ J, orderOf w = 4 ∧ w * a = a * w) :
    (∃ w ∈ J, orderOf w = 4 ∧ w * b = b * w) ∨
      ∃ w ∈ J, orderOf w = 4 ∧ w * ((a : G) * b) = ((a : G) * b) * w := by
  have hinv : ∀ n : Subgroup.normalizer (J : Set G), (n : G) * n = 1 →
      oddAct J e₁ n * oddAct J e₁ n = 1 := by
    intro n hn
    rw [← map_mul, show n * n = 1 from Subtype.ext hn, map_one]
  have h2grp : ∀ n : Subgroup.normalizer (J : Set G), (n : G) * n = 1 →
      IsPGroup 2 (Subgroup.zpowers (n : G)) := fun n hn =>
    (S19Q.isPGroup_zpowers_iff_exists_pow (n : G)).mpr ⟨1, by rw [pow_one, sq, hn]⟩
  rcases fixed_or_nonsquare hp hq (oddAct J e₁ a) (hinv a ha2) with ⟨h, hh, hfix⟩ |
    ⟨Ga, hGa, hsqa⟩
  · exact absurd (exists_orderOf_four_of_fixed J e₁ a (h2grp a ha2) hh hfix) hna
  rcases fixed_or_nonsquare hp hq (oddAct J e₁ b) (hinv b hb2) with ⟨h, hh, hfix⟩ |
    ⟨Gb, hGb, hsqb⟩
  · exact Or.inl (exists_orderOf_four_of_fixed J e₁ b (h2grp b hb2) hh hfix)
  right
  have hab2 : ((a * b : Subgroup.normalizer (J : Set G)) : G) * (a * b) = 1 := by
    rw [Subgroup.coe_mul]
    calc (a : G) * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by
        rw [← mul_assoc, ha2, one_mul, hb2]
  have hβab : ∀ x, oddAct J e₁ (a * b) x = semilinHom (Ga * Gb) (RingEquiv.refl _) x := by
    intro x
    rw [map_mul, MulAut.mul_apply, hGa, hGb]
    apply Subtype.ext
    rw [coe_semilinHom, coe_semilinHom, coe_semilinHom]
    simp only [RingEquiv.coe_refl, Matrix.map_id, Units.val_mul, _root_.mul_inv_rev, mul_assoc]
  have hsq : IsSquare (((Ga * Gb : GL (Fin 2) (GaloisField p e)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p e))).det := by
    rw [Units.val_mul, Matrix.det_mul]
    exact isSquare_mul_of_not_isSquare hsqa hsqb
  obtain ⟨h, hh, hfix⟩ := exists_fixed_of_isSquare hp hq (oddAct J e₁ (a * b)) (hinv _ hab2)
    (Ga * Gb) hβab hsq
  obtain ⟨w, hw, hw4, hwc⟩ := exists_orderOf_four_of_fixed J e₁ (a * b) (h2grp _ hab2) hh hfix
  exact ⟨w, hw, hw4, by rw [← Subgroup.coe_mul]; exact hwc⟩

end Act

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
