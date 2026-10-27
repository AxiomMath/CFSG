module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3C
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Unitary
open CFSG.ComponentClassification.CatFactsL4U4 DiagU StabU UnitaryOut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_unitary_of_lieModel {X : Type} [Group X] (hm : Blueprint.LieModel X .PSU 4 p f)
    (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (K : Type) (_ : Field K), UnitaryFieldData p f K ∧
      Nonempty (X ≃* StatedProj (StatedSU 4 (p ^ f) K)) := by
  obtain ⟨-, Kf, _, _, hKf, ⟨φ⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
  exact ⟨Kf, inferInstance, ⟨hp, hf, by rw [hKf, ← pow_mul, mul_comm]⟩, ⟨φ⟩⟩

@[expose] def scalU (c : K) (hc4 : c ^ 4 = 1) (hcN : h.norm c = 1) : unitarySU p f K 4 :=
  ⟨GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c (fun h0 => by
      rw [h0] at hc4
      norm_num at hc4)), by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hc4]
    · rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.scalar_apply,
          Matrix.diagonal_apply, Matrix.one_apply_eq]
        rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
        simp only [ite_true]
        rw [mul_comm]
        exact hcN
      · simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, hij,
          Matrix.one_apply_ne hij]⟩

theorem scalU_mem_scal (c : K) (hc4 : c ^ 4 = 1) (hcN : h.norm c = 1) :
    scalU h c hc4 hcN ∈ scal p f K :=
  ⟨Units.mk0 c _, rfl⟩

@[expose] def negOneU : unitarySU p f K 4 :=
  scalU h (-1) (by norm_num) (by rw [UnitaryFieldData.norm, map_neg, map_one]; ring)

theorem thU_negOneU : thU p f K (negOneU h) = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact scalU_mem_scal h _ _ _

theorem coe_negOneU : (((negOneU h : unitarySU p f K 4) : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K) = -1 := by
  change ((GeneralLinearGroup.scalar (Fin 4) _ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, map_neg, map_one]

variable {G : Type} [Group G] [Finite G] {Q : Subgroup G}

theorem exists_thetaU (hp2 : p ≠ 2) (e : ↥Q ⧸ center ↥Q ≃* StatedProj (StatedSU 4 (p ^ f) K))
    (hQ : IsQuasisimple ↥Q)
    (hZ : Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ p ^ f + 1)) :
    ∃ θ : unitarySU p f K 4 →* ↥Q, Function.Surjective θ ∧
      (∀ s, piQ e (θ s) = thU p f K s) ∧ θ.ker ≤ center (unitarySU p f K 4) ∧
      θ (negOneU h) = 1 := by
  classical
  have : Finite K := h.finite
  have hkerU : (thU p f K).ker ≤ center (unitarySU p f K 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  rcases hZ with hZ | ⟨hZ, h4⟩
  ·
    have hbot : center ↥Q = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
    have hinj : Function.Injective (piQ e) := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_piQ, hbot]
    let eQ : ↥Q ≃* StatedProj (StatedSU 4 (p ^ f) K) :=
      MulEquiv.ofBijective (piQ e) ⟨hinj, piQ_surjective e⟩
    refine ⟨eQ.symm.toMonoidHom.comp (thU p f K), eQ.symm.surjective.comp thU_surjective,
      fun s => ?_, ?_, ?_⟩
    · change eQ (eQ.symm (thU p f K s)) = thU p f K s
      rw [MulEquiv.apply_symm_apply]
    · intro s hs
      apply hkerU
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff] at hs
      exact hs
    · rw [MonoidHom.comp_apply, thU_negOneU, map_one]
  ·
    have : Fact p.Prime := ⟨h.prime⟩
    have := h.charP
    have : Group.IsPerfect ↥Q := hQ.1
    have hK : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
    set ι := equivStatedSU hK 4 with hι
    set β : SU (CFSG.LieType.BorelTits.unitaryInvolution K p f) 4 →*
        StatedProj (StatedSU 4 (p ^ f) K) := (thU p f K).comp ι.toMonoidHom with hβ
    have hβs : Function.Surjective β := thU_surjective.comp ι.surjective
    have hZ2 : IsPGroup 2 (center ↥Q) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
    have hsplit : ∀ (E : Type) [Group E] [Finite E]
        (π : E →* SU (CFSG.LieType.BorelTits.unitaryInvolution K p f) 4),
        Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
          ∃ σ : SU (CFSG.LieType.BorelTits.unitaryInvolution K p f) 4 →* E,
            ∀ x, π (σ x) = x := by
      intro E _ _ π hπ hker h2
      obtain ⟨σ, hσ, -, -⟩ :=
        LieType.Steinberg.su_central_two_extension_splitting hK hp2 (n := 4) (by norm_num) hπ
          hker h2
      exact ⟨σ, hσ⟩
    obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβs
      (piQ_surjective e) ((ker_piQ e).le) (by rw [ker_piQ]; exact hZ2)
    refine ⟨α.comp ι.symm.toMonoidHom, hαs.comp ι.symm.surjective, fun s => ?_, ?_, ?_⟩
    · change piQ e (α (ι.symm s)) = thU p f K s
      rw [hα, hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    · intro s hs
      apply hkerU
      rw [MonoidHom.mem_ker] at hs ⊢
      have h1 := hα (ι.symm s)
      change α (ι.symm s) = 1 at hs
      rw [hs, map_one, hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    ·
      have := Fintype.ofFinite K
      have hsq : IsSquare (-1 : K) := by
        rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
        obtain ⟨r, hr⟩ := (h.prime.odd_of_ne_two hp2).pow (n := f)
        rw [hr]
        ring_nf
        omega
      obtain ⟨i, hi⟩ := hsq
      have hi4 : i ^ 4 = 1 := by
        rw [show i ^ 4 = (i * i) * (i * i) by ring, ← hi]
        norm_num
      have hiN : h.norm i = 1 := by
        rw [h.norm_eq_pow]
        obtain ⟨m, hm⟩ := h4
        rw [hm, pow_mul, hi4, one_pow]
      set c := scalU h i hi4 hiN with hc
      have hcZ : (α.comp ι.symm.toMonoidHom) c ∈ center ↥Q := by
        rw [← ker_piQ e, hker]
        refine ⟨ι.symm c, (MonoidHom.mem_ker).mpr ?_, rfl⟩
        rw [hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact scalU_mem_scal h _ _ _
      have hcc : c * c = negOneU h := by
        apply Subtype.ext
        apply Units.ext
        change ((GeneralLinearGroup.scalar (Fin 4) _ * GeneralLinearGroup.scalar (Fin 4) _ :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = ((GeneralLinearGroup.scalar (Fin 4) _ :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        rw [← map_mul, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
        congr 1
        simp only [Units.val_mul, Units.val_mk0, ← hi]
      rw [← hcc, map_mul]
      exact GSThmB.Cent516.sq_eq_one_of_mem_center hZ hcZ

@[expose] def conjU {M : GL (Fin 4) K} (hM : M ∈ uMat h 4) :
    unitarySU p f K 4 →* unitarySU p f K 4 where
  toFun s := ⟨M * s * M⁻¹, conj_mem_SU h hM s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjU {M : GL (Fin 4) K} (hM : M ∈ uMat h 4) (s : unitarySU p f K 4) :
    ((conjU h hM s : unitarySU p f K 4) : GL (Fin 4) K) = M * s * M⁻¹ := rfl

omit [Finite G] in
theorem xAut_thetaU {x : G} (hx : x ∈ normalizer (Q : Set G))
    (e : ↥Q ⧸ center ↥Q ≃* StatedProj (StatedSU 4 (p ^ f) K))
    {θ : unitarySU p f K 4 →* ↥Q} (hθ : ∀ s, piQ e (θ s) = thU p f K s)
    {M : GL (Fin 4) K} (hM : IsCU h M (phi hx e)) (s : unitarySU p f K 4) :
    xAut hx (θ s) = θ (conjU h hM.1 s) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have := h.charP
  have : Group.IsPerfect (unitarySU p f K 4) :=
    LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU h.card_eq_sq (by norm_num)
  have h1 := eq_of_perfect_of_center (α := (xAut hx).toMonoidHom.comp θ)
    (β := θ.comp (conjU h hM.1)) fun g => by
      rw [← piQ_eq_iff e]
      change piQ e (xAut hx (θ g)) = piQ e (θ (conjU h hM.1 g))
      rw [← phi_piQ, hθ, hθ, hM.apply h]
      rfl
  exact DFunLike.congr_fun h1 s

end CFSG.ComponentClassification.HarrisLit.C3
