module

public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthTwin
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthFrame4
public import CFSG.ClassicalInvolution.SmallOrth.Orth3OddCoreAll

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Models.OrthogonalPairs
  Matrix
open scoped MatrixGroups

section Matrices

open CFSG.ClassicalGroups.Orthogonal.Small

variable {K : Type} [Field K] [Finite K]

theorem exists_sl2_pow_three_of_mul (hK : Nat.card K = 3) {a b : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ X, a * a * a * X * (b * b * b) = X) :
    ∃ a' b' : SL(2, K), a' ^ 3 = 1 ∧ b' ^ 3 = 1 ∧ ∀ X, a * X * b = a' * X * b' := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  set z := a * a * a with hz
  set w := b * b * b with hw
  have hzw : z * w = 1 := by simpa using h 1
  have hwz : w * z = 1 := mul_eq_one_comm.mp hzw
  have hcomm : ∀ X, z * X = X * z := fun X => by
    calc z * X = z * X * (w * z) := by rw [hwz, mul_one]
      _ = (z * X * w) * z := by simp only [Matrix.mul_assoc]
      _ = X * z := by rw [h X]
  obtain ⟨c, hc⟩ : z ∈ Set.range (Matrix.scalar (Fin 2) (α := K)) :=
    Matrix.mem_range_scalar_of_commute_single fun i j _ => (hcomm _).symm
  have hzc : z = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hzc
    rw [hzc, zero_mul] at hzw
    exact zero_ne_one hzw
  have hc2 : c ^ 2 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hcard] at this
  have hdz : z.det = 1 := by
    rw [hzc, Matrix.det_smul]
    simpa using hc2
  have hdw : w.det = 1 := by
    have := congrArg Matrix.det hzw
    rwa [Matrix.det_mul, hdz, one_mul, Matrix.det_one] at this
  have hx3 : ∀ x : K, x ^ 3 = x := fun x => by
    have := FiniteField.pow_card x
    rwa [hcard] at this
  have hda : a.det = 1 := by
    have : a.det ^ 3 = 1 := by
      rw [← hdz, hz, Matrix.det_mul, Matrix.det_mul]
      ring
    rw [← hx3 a.det, this]
  have hdb : b.det = 1 := by
    have : b.det ^ 3 = 1 := by
      rw [← hdw, hw, Matrix.det_mul, Matrix.det_mul]
      ring
    rw [← hx3 b.det, this]
  have hdna : (-a).det = 1 := by rw [Matrix.det_neg]; simp [hda]
  have hdnb : (-b).det = 1 := by rw [Matrix.det_neg]; simp [hdb]
  have hcube : ∀ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) * A * A = 1 → A ^ 3 = 1 :=
    fun A hA => Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, pow_three, ← mul_assoc]
      exact hA)
  rcases sq_eq_one_iff.mp hc2 with h1 | h1
  ·
    have hz1 : z = 1 := by rw [hzc, h1, one_smul]
    have hw1 : w = 1 := by rw [hz1, one_mul] at hzw; exact hzw
    exact ⟨⟨a, hda⟩, ⟨b, hdb⟩, hcube _ hz1, hcube _ hw1, fun X => rfl⟩
  ·
    have hz1 : z = -1 := by rw [hzc, h1, neg_smul, one_smul]
    have hw1 : w = -1 := by
      rw [hz1, Matrix.neg_mul, one_mul] at hzw
      exact neg_eq_iff_eq_neg.mp hzw
    refine ⟨⟨-a, hdna⟩, ⟨-b, hdnb⟩, hcube _ ?_, hcube _ ?_, fun X => ?_⟩
    · change (-a) * (-a) * (-a) = 1
      have e : (-a) * (-a) * (-a) = -(a * a * a) := by
        simp
      rw [e, ← hz, hz1, neg_neg]
    · change (-b) * (-b) * (-b) = 1
      have e : (-b) * (-b) * (-b) = -(b * b * b) := by
        simp
      rw [e, ← hw, hw1, neg_neg]
    · change a * X * b = (-a) * X * (-b)
      simp

theorem exists_sl2_of_pow_three (hK : Nat.card K = 3)
    {T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) (hT3 : T ^ 3 = 1) :
    ∃ a b : SL(2, K), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ ∀ X, T X = a * X * b := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hdet : LinearEquiv.det T = 1 := by
    have h2' : LinearEquiv.det T ^ 2 = 1 := by
      have := TauCeti.QuadraticMap.orthogonalDet_sq
        (QuadraticMap.nondegenerate_polar_iff.mpr (nondegenerate_detQ (K := K))).1 ⟨T, hT⟩
      simpa using this
    have h3' : LinearEquiv.det T ^ 3 = 1 := by rw [← map_pow, hT3, map_one]
    calc LinearEquiv.det T = LinearEquiv.det T ^ 3 * (LinearEquiv.det T ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2']; simp
  have hSO : T ∈ TauCeti.QuadraticMap.specialOrthogonalGroup (detQ (K := K)) :=
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨hT, hdet⟩
  obtain ⟨a, b, hab⟩ := specialOrthogonalGroup_le_bimulGrp h2 hSO
  have hcube : ∀ X, a * a * a * X * (b * b * b) = X := fun X => by
    have h : T (T (T X)) = X := by
      have := LinearEquiv.congr_fun hT3 X
      simpa [pow_succ, LinearEquiv.mul_apply] using this
    calc a * a * a * X * (b * b * b) = T (T (T X)) := by simp only [hab, Matrix.mul_assoc]
      _ = X := h
  obtain ⟨a', b', ha', hb', hX⟩ := exists_sl2_pow_three_of_mul hK hcube
  exact ⟨a', b', ha', hb', fun X => by rw [hab, hX]⟩

end Matrices

section Frames

open CFSG.ClassicalGroups.Orthogonal.Small

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem mul_self_eq_one_of_commute_all {a : SL(2, K)}
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, (a : Matrix (Fin 2) (Fin 2) K) * X = X * a) :
    a * a = 1 := by
  obtain ⟨c, hc⟩ : (a : Matrix (Fin 2) (Fin 2) K) ∈ Set.range (Matrix.scalar (Fin 2) (α := K)) :=
    Matrix.mem_range_scalar_of_commute_single fun i j _ => (h _).symm
  have hac : (a : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hdet : c ^ 2 = 1 := by
    have := a.2
    rw [hac, Matrix.det_smul] at this
    simpa using this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hac, smul_mul_smul_comm, one_mul, ← pow_two, hdet,
    one_smul]
  rfl

variable (fr : Frame Q)

omit [Finite K] in
theorem La_mul_self_eq_one_of_mem_swap {g : V ≃ₗ[K] V} (hg1 : g ∈ fr.La.range)
    (hg2 : g ∈ fr.swap.La.range) : g * g = 1 := by
  obtain ⟨a, rfl⟩ := hg1
  obtain ⟨b, hb⟩ := hg2
  have h1 : lmulEquiv a = rmulEquiv (Frame.sigmaSL b) := by
    apply fr.embGrp_injective
    rw [← Frame.La_eq_embGrp, ← Frame.swap_La_eq_embGrp]
    exact hb.symm
  have h2 : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (a : Matrix (Fin 2) (Fin 2) K) * X = X * (Frame.sigmaSL b : Matrix (Fin 2) (Fin 2) K) :=
    fun X => by
      have := LinearEquiv.congr_fun h1 X
      rwa [lmulEquiv_apply, rmulEquiv_apply] at this
  have h3 : (a : Matrix (Fin 2) (Fin 2) K) = (Frame.sigmaSL b : Matrix (Fin 2) (Fin 2) K) := by
    simpa using h2 1
  have h4 : ∀ X : Matrix (Fin 2) (Fin 2) K, (a : Matrix (Fin 2) (Fin 2) K) * X = X * a :=
    fun X => by rw [h2 X, ← h3]
  rw [← map_mul, mul_self_eq_one_of_commute_all h4, map_one]

theorem range_le_of_pow_three (hK : Nat.card K = 3) {G : Type*} [Group G] (ψ : SL(2, K) →* G)
    {T : Subgroup G} (h : ∀ x : SL(2, K), x ^ 3 = 1 → ψ x ∈ T) : ψ.range ≤ T := by
  obtain ⟨e₃⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hK
  rintro _ ⟨g, rfl⟩
  obtain ⟨a, b, c, ha, hb, hc, hg⟩ := sl2Three_exists_cubes (e₃ g)
  have hg' : g = e₃.symm a * e₃.symm b * e₃.symm c := by
    rw [← map_mul, ← map_mul, ← hg, MulEquiv.symm_apply_apply]
  have key : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 → ψ (e₃.symm x) ∈ T := fun x hx =>
    h _ (by rw [← map_pow, hx, map_one])
  rw [hg', map_mul, map_mul]
  exact T.mul_mem (T.mul_mem (key a ha) (key b hb)) (key c hc)

theorem eq_La_range_or_eq_swap3 (hK : Nat.card K = 3) (φ : SL(2, ZMod 3) →* (V ≃ₗ[K] V))
    (hφinj : Function.Injective φ) (hφO : ∀ g, φ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hφc : ∀ g, φ g * fr.La (-1) = fr.La (-1) * φ g) (hφfix : ∀ g, ∀ x ∈ fr.perp, φ g x = x)
    {T : Subgroup (V ≃ₗ[K] V)} (hsub : IsSubnormal φ.range T)
    (hT3 : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * fr.La (-1) = fr.La (-1) * g →
      g ^ 3 = 1 → g ∈ T) :
    φ.range = fr.La.range ∨ φ.range = fr.swap.La.range := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  obtain ⟨e₃⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hK
  have hR₁ : fr.La.range ≤ T := range_le_of_pow_three hK fr.La fun x hx =>
    hT3 _ (fr.La_mem_orthogonalGroup x) (Frame.La_neg_one_comm fr x).symm
      (by rw [← map_pow, hx, map_one])
  have hR₂ : fr.swap.La.range ≤ T := range_le_of_pow_three hK fr.swap.La fun x hx =>
    hT3 _ (fr.swap.La_mem_orthogonalGroup x) (Frame.La_swap_neg_one_comm fr x).symm
      (by rw [← map_pow, hx, map_one])
  refine eq_or_eq_of_isSubnormal_twin (MonoidHom.ofInjective hφinj)
    (e₃.symm.trans (MonoidHom.ofInjective fr.La_injective))
    (e₃.symm.trans (MonoidHom.ofInjective fr.swap.La_injective)) ?_ ?_ ?_ hsub hR₁ hR₂
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact fr.La_comm_La_swap a b
  · exact fun g hg1 hg2 => La_mul_self_eq_one_of_mem_swap fr hg1 hg2
  · rintro _ ⟨g, rfl⟩ hu3
    have hc := hφc g
    have hfix := hφfix g
    have hTu_emb := Frame4.embGrp_transportEquiv_eq (F := fr) h2 hc hfix
    have hTuO := Frame.transportEquiv_mem_orthogonalGroup (F := fr) h2 (hφO g) hc
    have hTu3 : Frame.transportEquiv (F := fr) h2 hc ^ 3 = 1 :=
      fr.embGrp_injective (by rw [map_pow, hTu_emb, hu3, map_one])
    obtain ⟨a, b, ha, hb, hX⟩ := exists_sl2_of_pow_three hK hTuO hTu3
    have hTuab : Frame.transportEquiv (F := fr) h2 hc = lmulEquiv a * rmulEquiv b :=
      LinearEquiv.ext fun X => by
        rw [hX X, LinearEquiv.mul_apply, rmulEquiv_apply, lmulEquiv_apply, Matrix.mul_assoc]
    have hb' : (b : Matrix (Fin 2) (Fin 2) K) * b * b = 1 := by
      have := congrArg Subtype.val hb
      rwa [Matrix.SpecialLinearGroup.coe_pow, pow_three, ← mul_assoc] at this
    have hs3 : (rmulEquiv b) ^ 3 = 1 := by
      refine LinearEquiv.ext fun X => ?_
      rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply, rmulEquiv_apply,
        rmulEquiv_apply, rmulEquiv_apply]
      change X * b * b * b = X
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (b : Matrix (Fin 2) (Fin 2) K),
        hb', Matrix.mul_one]
    refine ⟨fr.La a, ⟨a, rfl⟩, fr.embGrp (rmulEquiv b), ⟨Frame.sigmaSL b, ?_⟩, ?_, ?_, ?_⟩
    · rw [Frame.swap_La_eq_embGrp, Frame.sigmaSL_sigmaSL]
    · rw [← map_pow, ha, map_one]
    · rw [← map_pow, hs3, map_one]
    · rw [← hTu_emb, hTuab, map_mul, Frame.La_eq_embGrp]

end Frames

end CFSG.ClassicalInvolution.Q3
