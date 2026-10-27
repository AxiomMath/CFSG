module

public import CFSG.LieType.SteinbergBRParabolicResidualImage
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LieType.SteinbergBRBlockParabolicDInf

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag SemidirectProduct

variable {F : Type*} [Field F]

variable (F) in
@[expose] noncomputable def natTheta (s : SpecialLinearGroup (Fin 3) F) :
    Multiplicative (Matrix (Fin 2) (Fin 1) F) ⋊[phiL F (Fin 1)] SpecialLinearGroup (Fin 2) F →*
      SpecialLinearGroup (Fin 3) F :=
  (transportSL F (show 2 + 1 = 3 from rfl) s).toMonoidHom.comp (thetaL F (Fin 2) (Fin 1))

variable (F) in
@[expose] noncomputable def dualTheta (s : SpecialLinearGroup (Fin 3) F) :
    Multiplicative (Matrix (Fin 1) (Fin 2) F) ⋊[phiR F (Fin 1)] SpecialLinearGroup (Fin 2) F →*
      SpecialLinearGroup (Fin 3) F :=
  (transportSL F (show 1 + 2 = 3 from rfl) s).toMonoidHom.comp (thetaR F (Fin 1) (Fin 2))

theorem natTheta_val (s : SpecialLinearGroup (Fin 3) F)
    (x : Multiplicative (Matrix (Fin 2) (Fin 1) F) ⋊[phiL F (Fin 1)]
      SpecialLinearGroup (Fin 2) F) :
    (natTheta F s x).val = s.val * reindex (sumEquiv (show 2 + 1 = 3 from rfl))
      (sumEquiv (show 2 + 1 = 3 from rfl))
        (fromBlocks x.right.val (Multiplicative.toAdd x.left) 0 1) * (s⁻¹).val := by
  change s.val * (reindexSL F _ (thetaL F (Fin 2) (Fin 1) x)).val * (s⁻¹).val = _
  rw [reindexSL_val, thetaL_val]

theorem dualTheta_val (s : SpecialLinearGroup (Fin 3) F)
    (x : Multiplicative (Matrix (Fin 1) (Fin 2) F) ⋊[phiR F (Fin 1)]
      SpecialLinearGroup (Fin 2) F) :
    (dualTheta F s x).val = s.val * reindex (sumEquiv (show 1 + 2 = 3 from rfl))
      (sumEquiv (show 1 + 2 = 3 from rfl))
        (fromBlocks 1 (Multiplicative.toAdd x.left * x.right.val) 0 x.right.val) * (s⁻¹).val := by
  change s.val * (reindexSL F _ (thetaR F (Fin 1) (Fin 2) x)).val * (s⁻¹).val = _
  rw [reindexSL_val, thetaR_val]

theorem natTheta_conj (s : SpecialLinearGroup (Fin 3) F) (A : SpecialLinearGroup (Fin 2) F)
    (X : Multiplicative (Matrix (Fin 2) (Fin 1) F)) :
    natTheta F s (inr A) * natTheta F s (inl X) * (natTheta F s (inr A))⁻¹ =
      natTheta F s (inl (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X))) := by
  rw [← map_inv (natTheta F s), ← map_inv inr, ← map_mul, ← map_mul, ← inl_aut]
  rfl

theorem dualTheta_conj (s : SpecialLinearGroup (Fin 3) F) (D : SpecialLinearGroup (Fin 2) F)
    (X : Multiplicative (Matrix (Fin 1) (Fin 2) F)) :
    dualTheta F s (inr D) * dualTheta F s (inl X) * (dualTheta F s (inr D))⁻¹ =
      dualTheta F s (inl (Multiplicative.ofAdd (Multiplicative.toAdd X * (D⁻¹).val))) := by
  rw [← map_inv (dualTheta F s), ← map_inv inr, ← map_mul, ← map_mul, ← inl_aut]
  rfl

theorem natTheta_spec [Finite F] (hSL : commutator (SpecialLinearGroup (Fin 2) F) = ⊤)
    {s : SpecialLinearGroup (Fin 3) F} {W : Submodule F (Fin 3 → F)}
    (hs : (flagSpace 3 F 2).map (mulVecLin s.val) = W) :
    Function.Injective (natTheta F s) ∧
    (natTheta F s).range = (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
    ((natTheta F s).comp inl).range = radU F W ∧
    (natTheta F s).range ⊓ scalars 3 F = ⊥ := by
  have hJ := perfectResidual_stabilizer_eq (show 2 + 1 = 3 from rfl) hs parJL_le_parQ
    (perfectResidual_parQ_eq_parJL hSL)
  have hrange : (natTheta F s).range = (parJL F (Fin 2) (Fin 1)).map
      (transportSL F (show 2 + 1 = 3 from rfl) s).toMonoidHom := by
    rw [natTheta, MonoidHom.range_comp]
    rfl
  refine ⟨(transportSL F _ s).injective.comp thetaL_injective, hrange.trans hJ.symm, ?_, ?_⟩
  · have hcomp : (natTheta F s).comp inl =
        (transportSL F (show 2 + 1 = 3 from rfl) s).toMonoidHom.comp (uniHom F (Fin 2) (Fin 1)) :=
      MonoidHom.ext fun x => congrArg (transportSL F _ s) (SemidirectProduct.lift_inl _ _ _ x)
    rw [hcomp, MonoidHom.range_comp]
    exact map_uniHom_range_transport _ hs
  · rw [hrange]
    exact map_inf_scalars_eq_bot_right _ s fun g hg => (mem_parJL.1 hg).2

theorem dualTheta_spec [Finite F] (hSL : commutator (SpecialLinearGroup (Fin 2) F) = ⊤)
    {s : SpecialLinearGroup (Fin 3) F} {W : Submodule F (Fin 3 → F)}
    (hs : (flagSpace 3 F 1).map (mulVecLin s.val) = W) :
    Function.Injective (dualTheta F s) ∧
    (dualTheta F s).range = (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
    ((dualTheta F s).comp inl).range = radU F W ∧
    (dualTheta F s).range ⊓ scalars 3 F = ⊥ := by
  have hJ := perfectResidual_stabilizer_eq (show 1 + 2 = 3 from rfl) hs parJR_le_parQ
    (perfectResidual_parQ_eq_parJR hSL)
  have hrange : (dualTheta F s).range = (parJR F (Fin 1) (Fin 2)).map
      (transportSL F (show 1 + 2 = 3 from rfl) s).toMonoidHom := by
    rw [dualTheta, MonoidHom.range_comp]
    rfl
  refine ⟨(transportSL F _ s).injective.comp thetaR_injective, hrange.trans hJ.symm, ?_, ?_⟩
  · have hcomp : (dualTheta F s).comp inl =
        (transportSL F (show 1 + 2 = 3 from rfl) s).toMonoidHom.comp (uniHom F (Fin 1) (Fin 2)) :=
      MonoidHom.ext fun x => congrArg (transportSL F _ s) (SemidirectProduct.lift_inl _ _ _ x)
    rw [hcomp, MonoidHom.range_comp]
    exact map_uniHom_range_transport _ hs
  · rw [hrange]
    exact map_inf_scalars_eq_bot_left _ s fun g hg => (mem_parJR.1 hg).2

omit [Field F] in
theorem card_multiplicative_matrix [Finite F] (a b : ℕ) :
    Nat.card (Multiplicative (Matrix (Fin a) (Fin b) F)) = Nat.card F ^ (b * a) := by
  rw [Nat.card_congr Multiplicative.toAdd, Matrix.card_matrix, Nat.card_fin, Nat.card_fin]

theorem isPGroup_multiplicative_matrix {p : ℕ} [CharP F p] (a b : ℕ) :
    IsPGroup p (Multiplicative (Matrix (Fin a) (Fin b) F)) := fun g => ⟨1, by
  apply Multiplicative.toAdd.injective
  rw [pow_one, toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]⟩

theorem phiL_injective :
    Function.Injective (phiL F (Fin 1) : SpecialLinearGroup (Fin 2) F →* _) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  apply Subtype.ext
  ext i j
  have h := congrArg (fun f : MulAut (Multiplicative (Matrix (Fin 2) (Fin 1) F)) =>
    Multiplicative.toAdd (f (Multiplicative.ofAdd (single j 0 1))) i 0) hA
  change (A.val * single j 0 (1 : F)) i 0 = (single j 0 (1 : F)) i 0 at h
  rw [mul_single_apply_same, mul_one, single_apply] at h
  change A.val i j = (1 : Matrix (Fin 2) (Fin 2) F) i j
  rw [h, one_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, Ne.symm hij]

theorem phiR_injective :
    Function.Injective (phiR F (Fin 1) : SpecialLinearGroup (Fin 2) F →* _) := by
  rw [injective_iff_map_eq_one]
  intro D hD
  rw [← inv_eq_one]
  apply Subtype.ext
  ext i j
  have h := congrArg (fun f : MulAut (Multiplicative (Matrix (Fin 1) (Fin 2) F)) =>
    Multiplicative.toAdd (f (Multiplicative.ofAdd (single 0 i 1))) 0 j) hD
  change (single 0 i (1 : F) * (D⁻¹).val) 0 j = (single 0 i (1 : F)) 0 j at h
  rw [single_mul_apply_same, one_mul, single_apply] at h
  change (D⁻¹).val i j = (1 : Matrix (Fin 2) (Fin 2) F) i j
  rw [h, one_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij]

theorem structure_of_param [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (h4 : ∃ s : Finset F, s.card = 4) {N : Type*} [CommGroup N] [Finite N] (hNp : IsPGroup p N)
    {φ : SpecialLinearGroup (Fin 2) F →* MulAut N} (hφ : Function.Injective φ)
    {D : Subgroup (SpecialLinearGroup (Fin 3) F)} [D.Normal]
    {J : Subgroup (SpecialLinearGroup (Fin 3) F)}
    {B : Subgroup (SpecialLinearGroup (Fin 3) F ⧸ D)}
    (θ : N ⋊[φ] SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F)
    (hθ : Function.Injective θ) (hJ : θ.range = J) (hJD : J ⊓ D = ⊥)
    (hB : B = J.map (QuotientGroup.mk' D)) :
    Function.Injective ((QuotientGroup.mk' D).comp θ) ∧
    ((QuotientGroup.mk' D).comp θ).range = B ∧
    (∀ x, QuotientGroup.mk' D (θ x) ∈ (CFSG.solvableRadical B).map B.subtype ↔
      x.right.val = 1 ∨ x.right.val = -1) ∧
    Nat.card B = Nat.card N * Nat.card (SpecialLinearGroup (Fin 2) F) ∧
    Nat.card (CFSG.solvableRadical B) = Nat.card N * 2 ∧
    Nonempty (B ⧸ CFSG.solvableRadical B ≃* ProjectiveSpecialLinearGroup (Fin 2) F) ∧
    CFSG.pCore 2 B = ⊥ := by
  have hinjOn := injOn_mk_of_inf_eq_bot hJD
  have hinj : Function.Injective ((QuotientGroup.mk' D).comp θ) := fun x y hxy =>
    hθ (hinjOn (hJ ▸ ⟨x, rfl⟩) (hJ ▸ ⟨y, rfl⟩) hxy)
  have hrange : ((QuotientGroup.mk' D).comp θ).range = B := by
    rw [MonoidHom.range_comp, hJ, hB]
  let Φ : N ⋊[φ] SpecialLinearGroup (Fin 2) F ≃* B :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hcomp : B.subtype.comp Φ.toMonoidHom = (QuotientGroup.mk' D).comp θ :=
    MonoidHom.ext fun _ => rfl
  obtain ⟨hRad, hcard, hcardRad, hquot, hO2⟩ := semidirect_SL2_structure hp2 h4 hNp hφ Φ
  refine ⟨hinj, hrange, fun x => ?_, hcard, hcardRad, hquot, hO2⟩
  rw [hRad, Subgroup.map_map, hcomp]
  change ((QuotientGroup.mk' D).comp θ) x ∈ _ ↔ _
  rw [Subgroup.mem_map_iff_mem hinj]
  exact mem_center_SL2_iff

theorem not_dvd_pow_sub_one {p q k : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hk : k ≠ 0) (hq : 1 ≤ q) :
    ¬ p ∣ q ^ k - 1 := by
  intro h
  have h1 : p ∣ q ^ k := dvd_pow hpq hk
  have h2 : q ^ k - 1 + 1 = q ^ k := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)
  rw [← h2] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))

theorem not_dvd_card_of_le_scalars [Finite F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    {D : Subgroup (SpecialLinearGroup (Fin 3) F)} (hD : D ≤ scalars 3 F) :
    ¬ p ∣ Nat.card D := by
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨c, hc3, hgc⟩ := hD g.2
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((g : SpecialLinearGroup (Fin 3) F) ^ 3).val = 1
    rw [Matrix.SpecialLinearGroup.coe_pow, hgc, ← map_pow, ← Units.val_pow_eq_pow_val, hc3,
      Units.val_one, map_one]
  have hp3 : p = 3 := by
    have h := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at h
    exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h
  subst hp3
  have hc1 : (c : F) = 1 := by
    have h := sub_pow_char (p := 3) (c : F) 1
    rw [one_pow, ← Units.val_pow_eq_pow_val, hc3, Units.val_one, sub_self] at h
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)
  have hg1 : g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (g : SpecialLinearGroup (Fin 3) F).val = 1
    rw [hgc, hc1, map_one]
  rw [hg1, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem card_SL_two' [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [card_SL_eq (by norm_num), Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem card_SL_three' [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  rw [card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair (by norm_num)]

theorem normal_of_le_scalars {n : ℕ} {D : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hD : D ≤ scalars n F) : D.Normal :=
  Subgroup.normal_of_le_center (hD.trans (scalars_le_center n F))

end CFSG.LieType.SteinbergBR.BlockPar

namespace CFSG.LieType

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag SemidirectProduct
  CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar

theorem odd_linear_three_parabolic_affine_residual_structure {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F)
    (D : Subgroup (SpecialLinearGroup (Fin 3) F)) [D.Normal] (hD : D ≤ scalars 3 F)
    (W : Submodule F (Fin 3 → F)) (hW : finrank F W = 1 ∨ finrank F W = 2)
    {P B : Subgroup (SpecialLinearGroup (Fin 3) F ⧸ D)}
    (hP : P = (stabilizer W).map (QuotientGroup.mk' D))
    (hB : B = (CFSG.perfectResidual P).map P.subtype) :
    (∀ M : Matrix (Fin 3) (Fin 3) F, (∀ v, M *ᵥ v - v ∈ W) → (∀ w ∈ W, M *ᵥ w = w) →
      M.det = 1) ∧
    Set.InjOn (QuotientGroup.mk' D) (radU F W) ∧
    Set.InjOn (QuotientGroup.mk' D)
      ((CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype) ∧
    B = ((CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype).map
      (QuotientGroup.mk' D) ∧
    (finrank F W = 2 →
      (∃ s : SpecialLinearGroup (Fin 3) F, (flagSpace 3 F 2).map (mulVecLin s.val) = W) ∧
      ∀ s : SpecialLinearGroup (Fin 3) F, (flagSpace 3 F 2).map (mulVecLin s.val) = W →
        Function.Injective (natTheta F s) ∧
        (∀ x, (natTheta F s x).val = s.val * reindex (sumEquiv (show 2 + 1 = 3 from rfl))
          (sumEquiv (show 2 + 1 = 3 from rfl))
            (fromBlocks x.right.val (Multiplicative.toAdd x.left) 0 1) * (s⁻¹).val) ∧
        (∀ A X, natTheta F s (inr A) * natTheta F s (inl X) * (natTheta F s (inr A))⁻¹ =
          natTheta F s (inl (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X)))) ∧
        ((natTheta F s).comp inl).range = radU F W ∧
        (natTheta F s).range =
          (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
        Function.Injective ((QuotientGroup.mk' D).comp (natTheta F s)) ∧
        ((QuotientGroup.mk' D).comp (natTheta F s)).range = B ∧
        ∀ x, QuotientGroup.mk' D (natTheta F s x) ∈ (CFSG.solvableRadical B).map B.subtype ↔
          x.right.val = 1 ∨ x.right.val = -1) ∧
    (finrank F W = 1 →
      (∃ s : SpecialLinearGroup (Fin 3) F, (flagSpace 3 F 1).map (mulVecLin s.val) = W) ∧
      ∀ s : SpecialLinearGroup (Fin 3) F, (flagSpace 3 F 1).map (mulVecLin s.val) = W →
        Function.Injective (dualTheta F s) ∧
        (∀ x, (dualTheta F s x).val = s.val * reindex (sumEquiv (show 1 + 2 = 3 from rfl))
          (sumEquiv (show 1 + 2 = 3 from rfl))
            (fromBlocks 1 (Multiplicative.toAdd x.left * x.right.val) 0 x.right.val) *
              (s⁻¹).val) ∧
        (∀ D' X, dualTheta F s (inr D') * dualTheta F s (inl X) * (dualTheta F s (inr D'))⁻¹ =
          dualTheta F s (inl (Multiplicative.ofAdd (Multiplicative.toAdd X * (D'⁻¹).val)))) ∧
        ((dualTheta F s).comp inl).range = radU F W ∧
        (dualTheta F s).range =
          (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
        Function.Injective ((QuotientGroup.mk' D).comp (dualTheta F s)) ∧
        ((QuotientGroup.mk' D).comp (dualTheta F s)).range = B ∧
        ∀ x, QuotientGroup.mk' D (dualTheta F s x) ∈ (CFSG.solvableRadical B).map B.subtype ↔
          x.right.val = 1 ∨ x.right.val = -1) ∧
    Nat.card (radU F W) = Nat.card F ^ 2 ∧
    Nat.card B = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) ∧
    Nat.card (CFSG.solvableRadical B) = 2 * Nat.card F ^ 2 ∧
    Nonempty (B ⧸ CFSG.solvableRadical B ≃* ProjectiveSpecialLinearGroup (Fin 2) F) ∧
    CFSG.pCore 2 B = ⊥ ∧
    ordProj[p] (Nat.card B) = Nat.card F ^ 3 ∧
    ordProj[p] (Nat.card (SpecialLinearGroup (Fin 3) F ⧸ D)) = Nat.card F ^ 3 ∧
    ordProj[p] (Nat.card (B ⧸ CFSG.solvableRadical B)) = Nat.card F := by
  have hp : p.Prime := Fact.out
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have hSL : commutator (SpecialLinearGroup (Fin 2) F) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect h4).commutator_eq_top
  set J := (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype with hJdef
  have hBJ : B = J.map (QuotientGroup.mk' D) := by
    rw [hB, hP]
    exact (map_perfectResidual_subgroup _ _).symm
  obtain ⟨hJD, hUJ, hcardU, hcardB, hcardR, hquot, hO2⟩ : J ⊓ D = ⊥ ∧ radU F W ≤ J ∧
      Nat.card (radU F W) = Nat.card F ^ 2 ∧
      Nat.card B = Nat.card F ^ 2 * Nat.card (SpecialLinearGroup (Fin 2) F) ∧
      Nat.card (CFSG.solvableRadical B) = Nat.card F ^ 2 * 2 ∧
      Nonempty (B ⧸ CFSG.solvableRadical B ≃* ProjectiveSpecialLinearGroup (Fin 2) F) ∧
      CFSG.pCore 2 B = ⊥ := by
    obtain ⟨s, hs⟩ := exists_map_flagSpace_eq W
    rcases hW with hW1 | hW2
    · rw [hW1] at hs
      obtain ⟨hinj, hrange, hU, hZ⟩ := dualTheta_spec hSL hs
      have hJD : J ⊓ D = ⊥ := by
        rw [eq_bot_iff, ← hZ, hrange]
        exact inf_le_inf_left _ hD
      obtain ⟨-, -, -, hcard, hcardR, hquot, hO2⟩ := structure_of_param hp2 h4
        (isPGroup_multiplicative_matrix 1 2) phiR_injective (dualTheta F s) hinj hrange hJD hBJ
      refine ⟨hJD, ?_, ?_, ?_, ?_, hquot, hO2⟩
      · rw [← hU]
        refine le_trans ?_ hrange.le
        rintro _ ⟨x, rfl⟩
        exact ⟨inl x, rfl⟩
      · rw [← hU, ← Nat.card_congr (MonoidHom.ofInjective (f := (dualTheta F s).comp inl)
          (hinj.comp inl_injective)).toEquiv, card_multiplicative_matrix]
      · rw [hcard, card_multiplicative_matrix]
      · rw [hcardR, card_multiplicative_matrix]
    · rw [hW2] at hs
      obtain ⟨hinj, hrange, hU, hZ⟩ := natTheta_spec hSL hs
      have hJD : J ⊓ D = ⊥ := by
        rw [eq_bot_iff, ← hZ, hrange]
        exact inf_le_inf_left _ hD
      obtain ⟨-, -, -, hcard, hcardR, hquot, hO2⟩ := structure_of_param hp2 h4
        (isPGroup_multiplicative_matrix 2 1) phiL_injective (natTheta F s) hinj hrange hJD hBJ
      refine ⟨hJD, ?_, ?_, ?_, ?_, hquot, hO2⟩
      · rw [← hU]
        refine le_trans ?_ hrange.le
        rintro _ ⟨x, rfl⟩
        exact ⟨inl x, rfl⟩
      · rw [← hU, ← Nat.card_congr (MonoidHom.ofInjective (f := (natTheta F s).comp inl)
          (hinj.comp inl_injective)).toEquiv, card_multiplicative_matrix]
      · rw [hcard, card_multiplicative_matrix]
      · rw [hcardR, card_multiplicative_matrix]
  obtain ⟨f, hf0, hqf⟩ : ∃ f : ℕ, f ≠ 0 ∧ Nat.card F = p ^ f := by
    have := Fintype.ofFinite F
    obtain ⟨k, -, hk⟩ := FiniteField.card F p
    exact ⟨k, k.ne_zero, by rw [Nat.card_eq_fintype_card, hk]⟩
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hpq : p ∣ Nat.card F := hqf ▸ dvd_pow_self p hf0
  have hnd2 := not_dvd_pow_sub_one hp hpq two_ne_zero hq1
  have hnd3 := not_dvd_pow_sub_one hp hpq three_ne_zero hq1
  have hpow : ∀ k, Nat.card F ^ k = p ^ (f * k) := fun k => by rw [hqf, pow_mul]
  have hord : ∀ k x, ¬ p ∣ x → ordProj[p] (Nat.card F ^ k * x) = Nat.card F ^ k :=
    fun k x hx => by
      rw [hpow k]
      exact ordProj_prime_pow_mul hp _ hx
  have hcardB' : Nat.card B = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) := by
    rw [hcardB, card_SL_two']
    ring
  have hcardR' : Nat.card (CFSG.solvableRadical B) = 2 * Nat.card F ^ 2 := by
    rw [hcardR, mul_comm]
  have hordB : ordProj[p] (Nat.card B) = Nat.card F ^ 3 := by
    rw [hcardB']
    exact hord 3 _ hnd2
  have hordA : ordProj[p] (Nat.card (SpecialLinearGroup (Fin 3) F ⧸ D)) = Nat.card F ^ 3 := by
    have hmul := Nat.ordProj_mul p (Nat.card_pos (α := SpecialLinearGroup (Fin 3) F ⧸ D)).ne'
      (Nat.card_pos (α := D)).ne'
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup, card_SL_three',
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_of_le_scalars hD), pow_zero, mul_one,
      hord 3 _ (fun h => (hp.dvd_mul.1 h).elim hnd2 hnd3)] at hmul
    exact hmul.symm
  have hordQ : ordProj[p] (Nat.card (B ⧸ CFSG.solvableRadical B)) = Nat.card F := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.solvableRadical B)
    rw [hcardB', hcardR'] at h1
    have h2 : Nat.card (B ⧸ CFSG.solvableRadical B) * 2 =
        Nat.card F ^ 1 * (Nat.card F ^ 2 - 1) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hq1 2)
      calc Nat.card F ^ 2 * (Nat.card (B ⧸ CFSG.solvableRadical B) * 2)
          = Nat.card (B ⧸ CFSG.solvableRadical B) * (2 * Nat.card F ^ 2) := by ring
        _ = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) := h1.symm
        _ = Nat.card F ^ 2 * (Nat.card F ^ 1 * (Nat.card F ^ 2 - 1)) := by ring
    have hmul := Nat.ordProj_mul p (Nat.card_pos (α := B ⧸ CFSG.solvableRadical B)).ne'
      two_ne_zero
    rw [h2, Nat.factorization_eq_zero_of_not_dvd
      (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)), pow_zero,
      mul_one, hord 1 _ hnd2, pow_one] at hmul
    exact hmul.symm
  refine ⟨fun M h1 h2 => det_eq_one_of_unipotent h1 h2,
    (injOn_mk_of_inf_eq_bot hJD).mono hUJ, injOn_mk_of_inf_eq_bot hJD, hBJ,
    fun hW2 => ⟨?_, fun s hs => ?_⟩, fun hW1 => ⟨?_, fun s hs => ?_⟩, hcardU, hcardB', hcardR',
    hquot, hO2, hordB, hordA, hordQ⟩
  · obtain ⟨s, hs⟩ := exists_map_flagSpace_eq W
    rw [hW2] at hs
    exact ⟨s, hs⟩
  · obtain ⟨hinj, hrange, hU, hZ⟩ := natTheta_spec hSL hs
    obtain ⟨hinj', hrange', hrad, -⟩ := structure_of_param hp2 h4
      (isPGroup_multiplicative_matrix 2 1) phiL_injective (natTheta F s) hinj hrange hJD hBJ
    exact ⟨hinj, natTheta_val s, natTheta_conj s, hU, hrange, hinj', hrange', hrad⟩
  · obtain ⟨s, hs⟩ := exists_map_flagSpace_eq W
    rw [hW1] at hs
    exact ⟨s, hs⟩
  · obtain ⟨hinj, hrange, hU, hZ⟩ := dualTheta_spec hSL hs
    obtain ⟨hinj', hrange', hrad, -⟩ := structure_of_param hp2 h4
      (isPGroup_multiplicative_matrix 1 2) phiR_injective (dualTheta F s) hinj hrange hJD hBJ
    exact ⟨hinj, dualTheta_val s, dualTheta_conj s, hU, hrange, hinj', hrange', hrad⟩

end CFSG.LieType
