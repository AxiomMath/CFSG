module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3A
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

theorem det_sq_eq_pow [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {g : V ≃ₗ[K] V} {μ : K} (hμ : ∀ v, Q (g v) = μ * Q v) :
    LinearMap.det (g : V →ₗ[K] V) ^ 2 = μ ^ Module.finrank K V := by
  classical
  set b := Module.finBasis K V
  set B : LinearMap.BilinForm K V := polarBilin Q
  have hB : LinearMap.BilinForm.comp B (g : V →ₗ[K] V) (g : V →ₗ[K] V) = μ • B := by
    ext u v
    show polar Q (g u) (g v) = μ * polar Q u v
    rw [polar, polar, ← map_add, hμ, hμ, hμ]
    ring
  have h1 := congrArg (fun M => M.det) (LinearMap.BilinForm.toMatrix_comp b b B
    (g : V →ₗ[K] V) (g : V →ₗ[K] V))
  rw [hB, map_smul, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix, Fintype.card_fin] at h1
  have h0 : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin, _root_.sq]
  exact mul_right_cancel₀ h0 (by rw [h1]; ring)

theorem false_of_odd_of_neg [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V} (hμ : ∀ v, Q (g v) = -1 * Q v)
    (hodd : Odd (Module.finrank K V)) : False := by
  have h := det_sq_eq_pow hQ hμ
  rw [hodd.neg_one_pow, _root_.sq] at h
  exact sq_ne_neg_one hK _ h

theorem exists_ne_zero_mem_perp' [FiniteDimensional K V] (F : Frame Q)
    (hn : 5 ≤ Module.finrank K V) : ∃ v ∈ F.perp, v ≠ 0 := by
  have h := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank K F.perp by omega)
  exact ⟨v, v.2, fun h0 => hv (Subtype.ext h0)⟩

theorem exists_conj_of_norm [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 5 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {F₁ : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x)
    (hg₁ : g * F₁.La (-1) = F₁.La (-1) * g)
    (hnorm : ∀ y ∈ frameMember θ F₁, x y ∈ frameMember θ F₁) :
    ∀ b ∈ commutator SL(2, K), ∃ b' ∈ commutator SL(2, K), g * F₁.La b * g⁻¹ = F₁.La b' := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  intro b hb
  have hLb : F₁.La b ∈ orthDerived Q := frameQ8_le F₁ (La_mem_frameQ8 F₁ hb)
  obtain ⟨b', hb', hθ⟩ := (mem_frameMember_iff θ F₁).mp (hnorm _ (La_mem_frameMember θ F₁ hb))
  refine ⟨b', hb', ?_⟩
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_mem_perp' F₁ hn
  refine eq_of_theta_eq_of_apply hQ hker (hx.mem _ hLb) (frameQ8_le F₁ (La_mem_frameQ8 F₁ hb'))
    ?_ hv₀0 ?_
  · rw [← hx.act ⟨F₁.La b, hLb⟩]
    exact hθ.symm
  · have hperp : g⁻¹ v₀ ∈ F₁.perp := Frame.map_mem_perp h2 (Frame.inv_commute_La hg₁) hv₀
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      F₁.La_apply_of_coords_eq_zero b ((Frame.mem_perp_iff F₁).mp hperp),
      F₁.La_apply_of_coords_eq_zero b' ((Frame.mem_perp_iff F₁).mp hv₀)]
    simp

theorem eq_one_or_neg_one_of_sq [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 5 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    (F₁ : Frame Q) {b : SL(2, K)} (hb : b ∈ commutator SL(2, K))
    (hsq : θ ⟨F₁.La b, frameQ8_le F₁ (La_mem_frameQ8 F₁ hb)⟩ *
      θ ⟨F₁.La b, frameQ8_le F₁ (La_mem_frameQ8 F₁ hb)⟩ = 1) : b = 1 ∨ b = -1 := by
  have hbb : b * b ∈ commutator SL(2, K) := mul_mem hb hb
  have hL : F₁.La (b * b) ∈ orthDerived Q := frameQ8_le F₁ (La_mem_frameQ8 F₁ hbb)
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_mem_perp' F₁ hn
  have h1 : F₁.La (b * b) = 1 := by
    refine eq_of_theta_eq_of_apply hQ hker hL (orthDerived Q).one_mem ?_ hv₀0 ?_
    · have e1 : (⟨F₁.La (b * b), hL⟩ : ↥(orthDerived Q)) =
          ⟨F₁.La b, frameQ8_le F₁ (La_mem_frameQ8 F₁ hb)⟩ *
            ⟨F₁.La b, frameQ8_le F₁ (La_mem_frameQ8 F₁ hb)⟩ :=
        Subtype.ext (map_mul F₁.La b b)
      rw [e1, map_mul, hsq]
      exact (map_one θ).symm
    · rw [F₁.La_apply_of_coords_eq_zero _ ((Frame.mem_perp_iff F₁).mp hv₀)]
      rfl
  have h2 : b * b = 1 := F₁.La_injective (by rw [h1, map_one])
  exact eq_one_or_neg_one hK (by rw [_root_.sq]; exact h2)

theorem La_swap_incl (F : Frame Q) (b : SL(2, K)) (Y : Matrix (Fin 2) (Fin 2) K) :
    F.swap.La b (F.incl Y) = F.incl (Y * sigmaLin (b : Matrix (Fin 2) (Fin 2) K)) := by
  rw [Frame.La_swap_apply, Frame.embLin_apply_eq, Frame.coords_incl, sub_self, add_zero]
  rfl

theorem sigmaLin_one : sigmaLin (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

theorem det_eq_neg_one_of_sProp [Finite K] (hK : Nat.card K = 3)
    {P : Matrix (Fin 2) (Fin 2) K} {c : K} (hPP : P * P = c • 1) (hdet0 : P.det ≠ 0)
    (hrel : ∀ b ∈ commutator SL(2, K), ∃ b' ∈ commutator SL(2, K),
      sigmaLin (b : Matrix (Fin 2) (Fin 2) K) * P = P * sigmaLin (b' : Matrix (Fin 2) (Fin 2) K) ∧
        (b' = b → b = 1 ∨ b = -1)) :
    P.det = -1 ∧ c = 1 := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  have hd2 := OrthQ8.mul_self_eq_one hK hdet0
  have hd : P.det = 1 ∨ P.det = -1 := by
    have h : (P.det - 1) * (P.det + 1) = 0 := by linear_combination hd2
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hPP
    have := congrArg Matrix.det hPP
    rw [Matrix.det_mul, Matrix.det_zero] at this
    exact hdet0 (mul_self_eq_zero.mp this)
  have hc2 := OrthQ8.mul_self_eq_one hK hc0
  have hc : c = 1 ∨ c = -1 := by
    have h : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hcancel : ∀ X Y : Matrix (Fin 2) (Fin 2) K, P * X = P * Y → X = Y := by
    intro X Y h
    have h1 := congrArg (fun M => Matrix.adjugate P * M) h
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h1
    exact smul_right_injective _ hdet0 h1
  have hσinj : ∀ b b' : SL(2, K), sigmaLin (b : Matrix (Fin 2) (Fin 2) K) =
      sigmaLin (b' : Matrix (Fin 2) (Fin 2) K) → b' = b := by
    intro b b' h
    apply Subtype.ext
    have := congrArg sigmaLin h
    rw [sigmaLin_sigmaLin, sigmaLin_sigmaLin] at this
    exact this.symm
  have hI : (sl2I : SL(2, K)) ≠ 1 ∧ (sl2I : SL(2, K)) ≠ -1 := by
    constructor
    · intro h
      have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp [coe_sl2I] at this
    · intro h
      have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp [coe_sl2I] at this
  have hdetP : P.det = -1 := by
    rcases hd with hd | hd
    · exfalso
      rcases hc with rfl | rfl
      ·
        rw [one_smul] at hPP
        rcases eq_one_or_neg_one_of_det_eq_one hK hd hPP with hP | hP
        · obtain ⟨b', -, hrel1, hfix⟩ := hrel sl2I (sl2I_mem_commutator hK)
          rw [hP, Matrix.mul_one, Matrix.one_mul] at hrel1
          rcases hfix (hσinj _ _ hrel1) with h | h
          · exact hI.1 h
          · exact hI.2 h
        · obtain ⟨b', -, hrel1, hfix⟩ := hrel sl2I (sl2I_mem_commutator hK)
          rw [hP, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, neg_inj] at hrel1
          rcases hfix (hσinj _ _ hrel1) with h | h
          · exact hI.1 h
          · exact hI.2 h
      ·
        have hPP' : P * P = -1 := by rw [hPP, neg_one_smul]
        have hσP : sigmaLin P * sigmaLin P = -1 := by
          rw [← sigmaLin_mul, hPP', map_neg, sigmaLin_one]
        set b : SL(2, K) := ⟨sigmaLin P, by rw [det_sigmaLin]; exact hd⟩ with hbdef
        have hbb : b * b = -1 := by
          ext i j
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
            Matrix.SpecialLinearGroup.coe_one]
          exact congrFun (congrFun hσP i) j
        have hb4 : b ^ 4 = 1 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, _root_.sq b, hbb, neg_one_sq]
        obtain ⟨b', -, hrel1, hfix⟩ := hrel b ((mem_commutator_sl2_iff hK).mpr hb4)
        have hσb : sigmaLin (b : Matrix (Fin 2) (Fin 2) K) = P := sigmaLin_sigmaLin P
        rw [hσb] at hrel1
        have hb'b : sigmaLin (b' : Matrix (Fin 2) (Fin 2) K) = P := (hcancel _ _ hrel1).symm
        rcases hfix (hσinj _ _ (hσb.trans hb'b.symm)) with h | h
        · have := congrArg (fun A : SL(2, K) => sigmaLin (A : Matrix (Fin 2) (Fin 2) K)) h
          simp only [hσb, Matrix.SpecialLinearGroup.coe_one, sigmaLin_one] at this
          rw [this, Matrix.one_mul] at hPP'
          have h00 := congrFun (congrFun hPP' 0) 0
          simp at h00
          exact h2 (by linear_combination h00)
        · have := congrArg (fun A : SL(2, K) => sigmaLin (A : Matrix (Fin 2) (Fin 2) K)) h
          simp only [hσb, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
            map_neg, sigmaLin_one] at this
          rw [this, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul] at hPP'
          have h00 := congrFun (congrFun hPP' 0) 0
          simp at h00
          exact h2 (by linear_combination h00)
    · exact hd
  refine ⟨hdetP, ?_⟩
  rcases hc with hc | hc
  · exact hc
  · exfalso
    have hPP' : P * P = -1 := by rw [hPP, hc, neg_one_smul]
    have := det_eq_one_of_mul_self_eq_neg_one hK hPP'
    rw [hdetP] at this
    exact h2 (by linear_combination -this)

theorem mu_eq_neg_one_of_swap [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 5 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {F : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x)
    (hfix : ∀ a ∈ frameMember θ F, x a = a)
    (hnorm : ∀ y ∈ frameMember θ F.swap, x y ∈ frameMember θ F.swap)
    (hcB : ∀ y ∈ frameMember θ F.swap, x y = y → y * y = 1) {μ c : K} (hμ0 : μ ≠ 0)
    (hμ : ∀ v, Q (g v) = μ * Q v) (hc : ∀ v, g (g v) = c • v) : μ = -1 ∧ c = 1 := by
  have hFg := commute_La_of_fix hK hQ hn hker hx hfix
  have hg₁ : g * F.swap.La (-1) = F.swap.La (-1) * g := by
    rw [Frame.La_swap_neg_one]
    exact hFg (-1) (neg_one_mem_commutator hK)
  obtain ⟨P, hP⟩ := exists_mulRight_of_commute_Q8 hK F hFg
  have hg1 : g (F.incl 1) = F.incl P := by rw [hP, Matrix.one_mul]
  have hrel : ∀ b ∈ commutator SL(2, K), ∃ b' ∈ commutator SL(2, K),
      sigmaLin (b : Matrix (Fin 2) (Fin 2) K) * P = P * sigmaLin (b' : Matrix (Fin 2) (Fin 2) K) ∧
        (b' = b → b = 1 ∨ b = -1) := by
    intro b hb
    obtain ⟨b', hb', hconj⟩ := exists_conj_of_norm hK hQ hn hker hx hg₁ hnorm b hb
    refine ⟨b', hb', ?_, ?_⟩
    · have h1 : g * F.swap.La b = F.swap.La b' * g := mul_inv_eq_iff_eq_mul.mp hconj
      have h2 := LinearEquiv.congr_fun h1 (F.incl 1)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_swap_incl, hP, hg1, La_swap_incl,
        Matrix.one_mul] at h2
      exact F.incl_injective h2
    · intro hbb
      rw [hbb] at hconj
      have hLb : F.swap.La b ∈ orthDerived Q := frameQ8_le F.swap (La_mem_frameQ8 F.swap hb)
      have hxfix : x (θ ⟨F.swap.La b, hLb⟩) = θ ⟨F.swap.La b, hLb⟩ := by
        rw [hx.act]
        congr 1
        exact Subtype.ext hconj
      exact eq_one_or_neg_one_of_sq hK hQ hn hker F.swap hb
        (hcB _ (La_mem_frameMember θ F.swap hb) hxfix)
  have hPP : P * P = c • 1 := by
    have h1 := hc (F.incl 1)
    rw [hg1, hP, ← map_smul] at h1
    exact F.incl_injective h1
  have hdet : P.det = μ := by
    have h1 := hμ (F.incl 1)
    rw [hg1, F.Q_incl, F.Q_incl, Matrix.det_one, mul_one] at h1
    exact h1
  obtain ⟨hd, hc1⟩ := det_eq_neg_one_of_sProp hK hPP (hdet ▸ hμ0) hrel
  exact ⟨hdet ▸ hd, hc1⟩

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
