module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidM123Syl
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOTheta

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ABGLocalTools
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Def

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def OrthM123 (Q₀ : (ι → K) → K) (M : GL ι K) (hMH : M ∈ StatedOmega Q₀) : Prop :=
  (∃ S : Subgroup (StatedProj (StatedOmega Q₀)), IsSylowOf 2 S ⊤ ∧
      S ≤ perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ :
        StatedProj (StatedOmega Q₀))} : Set (StatedProj (StatedOmega Q₀))))) ∧
    (∀ z : StatedProj (StatedOmega Q₀), orderOf z = 2 →
      (∃ S : Subgroup (StatedProj (StatedOmega Q₀)), IsSylowOf 2 S ⊤ ∧
        S ≤ centralizer ({z} : Set _)) →
        ∃ a : StatedProj (StatedOmega Q₀), a * z * a⁻¹ = QuotientGroup.mk ⟨M, hMH⟩) ∧
    ∀ z : StatedProj (StatedOmega Q₀), orderOf z = 2 →
      z ∈ centralizer (perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ :
        StatedProj (StatedOmega Q₀))} : Set (StatedProj (StatedOmega Q₀)))) :
          Set (StatedProj (StatedOmega Q₀))) →
        ∃ (N : GL ι K) (hN : N ∈ StatedOmega Q₀),
          (QuotientGroup.mk ⟨N, hN⟩ : StatedProj (StatedOmega Q₀)) = z ∧
          ∃ a : K, (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1)

end Def

section Sylow

theorem isSylowOf_top_of_card_eq_mul_odd {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) {R : ℤ} (hR : Odd R) (h : (Nat.card G : ℤ) = Nat.card S * R) :
    IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_iff.mpr ⟨le_top, hS, fun h2 => ?_⟩
  rw [relIndex_top_right] at h2
  have hpos : (Nat.card S : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hidx : (S.index : ℤ) = R := by
    apply mul_left_cancel₀ hpos
    rw [← h]
    exact_mod_cast S.card_mul_index
  obtain ⟨m, hm⟩ := h2
  rw [hm] at hidx
  exact Int.not_even_iff_odd.mpr hR ⟨m, by rw [← hidx]; push_cast; ring⟩

end Sylow

section Torus

variable {K : Type} [Field K]

theorem torus_mul_slTr {t : K} (ht : t ≠ 0) {A : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹]) (a : K) :
    A * slTr a * A⁻¹ = slTr (t * t * a) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (A : Matrix (Fin 2) (Fin 2) K) * (1 + single 0 1 a) =
    (1 + single 0 1 (t * t * a)) * (A : Matrix (Fin 2) (Fin 2) K)
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, single_apply]
  field_simp

end Torus

section Root

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hSL : commutator SL(2, K) = ⊤) [Nonempty ι₂] (hnd : Q₂.polarBilin.Nondegenerate) {t : K}
  (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hinj : Function.Injective (oProj ⇑Q))
include hQ hSL hnd ht0 ht1 hinj

omit [Finite K] in
theorem exists_eq_oProj_oRhoOne_of_commute {z : StatedProj (StatedOmega ⇑Q)}
    (hz : ∀ u c, oProj ⇑Q ⟨qEGL oe Q₂ u c, qEGL_mem_statedOmega hQ hSL ht0 ht1 u c⟩ * z =
      z * oProj ⇑Q ⟨qEGL oe Q₂ u c, qEGL_mem_statedOmega hQ hSL ht0 ht1 u c⟩) :
    ∃ a : K, z = oProj ⇑Q (oRhoOne oe hQ hSL (slTr a)) := by
  obtain ⟨g, rfl⟩ := oProj_surjective ⇑Q z
  have hcomm : ∀ u c, (g : GL ι K) * qEGL oe Q₂ u c = qEGL oe Q₂ u c * g := fun u c => by
    set q : StatedOmega ⇑Q := ⟨qEGL oe Q₂ u c, qEGL_mem_statedOmega hQ hSL ht0 ht1 u c⟩
    have h : g * q = q * g := hinj (by rw [map_mul, map_mul, hz u c])
    have h1 := congrArg Subtype.val h
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h1
  obtain ⟨a, ha⟩ := eq_qEGL_zero_of_commute hQ hnd (quad_mulVec_of_mem_statedOmega g.2) hcomm
  refine ⟨a, congrArg _ (Subtype.ext ?_)⟩
  rw [ha, qEGL_zero]
  rfl

variable (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤) {S₂ : Subgroup (GL ι₂ K)}
  (hS₂ : S₂ ≤ StatedOmega ⇑Q₂) (hS₂p : IsPGroup 2 S₂) {R : ℤ} (hR : Odd R)
  (hcard : (Nat.card (StatedProj (StatedOmega ⇑Q)) : ℤ) =
    (Nat.card K : ℤ) ^ (2 * Fintype.card ι₂ + 2) * Nat.card S₂ * R)
include hperf₂ hS₂ hS₂p hR hcard

theorem orthM123_oM₀ : OrthM123 ⇑Q _ (oRhoOne oe hQ hSL (slTr 1)).2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := oXt_le_statedOmega hQ hSL ht0 ht1
  have hSX : oSylStep oe Q₂ S₂ ≤ oXt oe Q₂ := oSylStep_le_oXt hS₂
  set Sbar := ((oSylStep oe Q₂ S₂).subgroupOf (StatedOmega ⇑Q)).map (oProj ⇑Q) with hSbar
  have hcore := perfectCore_centralizer_oPsi hQ hSL hperf₂ hnd ht0 ht1 hle hinj
  have hSle : Sbar ≤ perfectCore (centralizer
      ({oProj ⇑Q (oRhoOne oe hQ hSL (slTr 1))} : Set (StatedProj (StatedOmega ⇑Q)))) := by
    rw [hcore, range_oPsi]
    exact map_mono (comap_mono hSX)
  have hcardS : Nat.card Sbar = Nat.card (oSylStep oe Q₂ S₂) := by
    rw [hSbar, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (subgroupOfEquivOfLe (hSX.trans hle)).toEquiv
  have hSyl : IsSylowOf 2 Sbar ⊤ := by
    refine isSylowOf_top_of_card_eq_mul_odd
      ((isPGroup_oSylStep hQ hS₂ hS₂p).comap_subtype.map _) hR ?_
    rw [hcard, hcardS, card_oSylStep hQ hS₂]
    push_cast
    ring
  have hqS : ∀ u c,
      oProj ⇑Q ⟨qEGL oe Q₂ u c, qEGL_mem_statedOmega hQ hSL ht0 ht1 u c⟩ ∈ Sbar :=
    fun u c => ⟨_, mem_sup_left (qEGL_mem_oQE oe Q₂ u c), rfl⟩
  refine ⟨⟨Sbar, hSyl, hSle⟩, ?_, ?_⟩
  ·
    rintro z hz2 ⟨S', hS', hS'z⟩
    obtain ⟨k, -, hk⟩ := hSyl.exists_mem_conj hS'
    have hz' : ∀ s ∈ Sbar, s * (k⁻¹ * z * k) = k⁻¹ * z * k * s := by
      intro s hs
      have hmem : k * s * k⁻¹ ∈ S' :=
        (hk _).mpr (by rwa [show k⁻¹ * (k * s * k⁻¹) * k = s by group])
      have h2 := mem_centralizer_singleton_iff.mp (hS'z hmem)
      calc s * (k⁻¹ * z * k) = k⁻¹ * (k * s * k⁻¹ * z) * k := by group
        _ = k⁻¹ * (z * (k * s * k⁻¹)) * k := by rw [h2]
        _ = k⁻¹ * z * k * s := by group
    obtain ⟨a, ha⟩ := exists_eq_oProj_oRhoOne_of_commute hQ hSL hnd ht0 ht1 hinj
      fun u c => hz' _ (hqS u c)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [slTr_zero, map_one, map_one] at ha
      have hz1 : z = 1 := by
        have h1 := congrArg (fun x => k * x * k⁻¹) ha
        simp only [mul_one, mul_inv_cancel] at h1
        rw [← h1]
        group
      rw [hz1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a⁻¹
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hμ
      exact inv_ne_zero ha0 hμ
    obtain ⟨D, hD⟩ := exists_torusSL hμ0
    have hDa : D * slTr a * D⁻¹ = slTr 1 := by
      rw [torus_mul_slTr hμ0 hD, ← hμ, inv_mul_cancel₀ ha0]
    refine ⟨oProj ⇑Q (oRhoOne oe hQ hSL D) * k⁻¹, ?_⟩
    calc oProj ⇑Q (oRhoOne oe hQ hSL D) * k⁻¹ * z * (oProj ⇑Q (oRhoOne oe hQ hSL D) * k⁻¹)⁻¹
        = oProj ⇑Q (oRhoOne oe hQ hSL D) * (k⁻¹ * z * k) *
            (oProj ⇑Q (oRhoOne oe hQ hSL D))⁻¹ := by group
      _ = oProj ⇑Q (oRhoOne oe hQ hSL (D * slTr a * D⁻¹)) := by
        rw [ha, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
      _ = oProj ⇑Q (oRhoOne oe hQ hSL (slTr 1)) := by rw [hDa]
  ·
    intro z _ hzC
    obtain ⟨a, rfl⟩ := exists_eq_oProj_oRhoOne_of_commute hQ hSL hnd ht0 ht1 hinj
      fun u c => mem_centralizer_iff.mp hzC _ (hSle (hqS u c))
    refine ⟨oRhoOneGL oe (slTr a), (oRhoOne oe hQ hSL (slTr a)).2, rfl, a, ?_⟩
    rw [oRhoOneGL_slTr_eq, show ((oRhoOne oe hQ hSL (slTr 1) : StatedOmega ⇑Q) : GL ι K) =
      oRhoOneGL oe (slTr 1) from rfl, oRhoOneGL_slTr_one, add_sub_cancel_left,
      add_sub_cancel_left]

end Root

section Conj

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q₀ : (ι → K) → K}

omit [Finite K] in
theorem conj_one_add_smul_sub_one (G : GL ι K) (a : K) (X : Matrix ι ι K) :
    ((G⁻¹ : GL ι K) : Matrix ι ι K) * (1 + a • X) * G - 1 =
      a • (((G⁻¹ : GL ι K) : Matrix ι ι K) * X * G) := by
  have hGG : ((G⁻¹ : GL ι K) : Matrix ι ι K) * G = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hGG, Matrix.mul_smul, Matrix.smul_mul,
    add_sub_cancel_left]

theorem orthM123_of_conj {G : GL ι K} (hG : ∀ v, Q₀ ((G : Matrix ι ι K) *ᵥ v) = Q₀ v)
    {M M₀ : GL ι K} (hMH : M ∈ StatedOmega Q₀) (hM₀H : M₀ ∈ StatedOmega Q₀)
    (hGM : G * M * G⁻¹ = M₀) (h : OrthM123 Q₀ M₀ hM₀H) : OrthM123 Q₀ M hMH := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨S₀, hS₀, hS₀le⟩, hconj, hcen⟩ := h
  set φ := projConj hG
  set m : StatedProj (StatedOmega Q₀) := QuotientGroup.mk ⟨M, hMH⟩ with hm
  set m₀ : StatedProj (StatedOmega Q₀) := QuotientGroup.mk ⟨M₀, hM₀H⟩ with hm₀
  have hφ : φ m = m₀ := by
    rw [hm, projConj_mk, hm₀]
    congr 1
    apply Subtype.ext
    rw [coe_isoConj]
    exact hGM
  have hX : (perfectCore (centralizer ({m} : Set (StatedProj (StatedOmega Q₀))))).map
      φ.toMonoidHom = perfectCore (centralizer {m₀}) := by
    rw [CFSG.Quasithin.map_perfectCore, URigid.map_centralizer_singleton_mulEquiv, hφ]
  refine ⟨⟨S₀.map φ.symm.toMonoidHom, isSylowOf_map_top hS₀ φ.symm.surjective, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    have h1 := hS₀le hs
    rw [← hX] at h1
    obtain ⟨w, hw, hws⟩ := h1
    rw [← hws, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, φ.symm_apply_apply]
    exact hw
  · rintro z hz2 ⟨S', hS', hS'z⟩
    obtain ⟨a, ha⟩ := hconj (φ z) (by rw [MulEquiv.orderOf_eq]; exact hz2)
      ⟨S'.map φ.toMonoidHom, isSylowOf_map_top hS' φ.surjective,
        (map_mono hS'z).trans (URigid.map_centralizer_singleton_mulEquiv φ z).le⟩
    refine ⟨φ.symm a, φ.injective ?_⟩
    rw [map_mul, map_mul, map_inv, φ.apply_symm_apply, ha, hφ]
  · intro z hz2 hzC
    have hzC' : φ z ∈ centralizer (perfectCore (centralizer ({m₀} : Set _)) :
        Set (StatedProj (StatedOmega Q₀))) := by
      rw [← hX, mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, mem_centralizer_iff.mp hzC w hw]
    obtain ⟨N₀, hN₀, hN₀z, a, ha⟩ := hcen (φ z) (by rw [MulEquiv.orderOf_eq]; exact hz2) hzC'
    have hNH : G⁻¹ * N₀ * G ∈ StatedOmega Q₀ := by
      have h1 := conj_mem_statedOmega (isometry_inv hG) hN₀
      rwa [inv_inv] at h1
    refine ⟨G⁻¹ * N₀ * G, hNH, φ.injective ?_, a, ?_⟩
    · rw [← hN₀z, projConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_isoConj, Subgroup.coe_mk]
      group
    · have hM : G⁻¹ * M₀ * G = M := by
        rw [← hGM]
        group
      have hN₀e : (N₀ : Matrix ι ι K) = 1 + a • ((M₀ : Matrix ι ι K) - 1) := by
        rw [← ha, add_sub_cancel]
      rw [Units.val_mul, Units.val_mul, hN₀e, conj_one_add_smul_sub_one, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul, ← Units.val_mul, hM,
        ← Units.val_mul, inv_mul_cancel, Units.val_one]

end Conj

section Singular

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} [Nonempty ι₂]

theorem orthM123_of_singular {Q₀ : (ι → K) → K} {Q₂₀ : (ι₂ → K) → K}
    {Qf : QuadraticForm K (ι → K)} {Q₂f : QuadraticForm K (ι₂ → K)} (hQf : ⇑Qf = Q₀)
    (hQ₂f : ⇑Q₂f = Q₂₀) (hnd : Qf.polarBilin.Nondegenerate)
    (hnd₂ : Q₂f.polarBilin.Nondegenerate)
    (hQ : ∀ v, Q₀ v = Q₂₀ (fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    (hSL : commutator SL(2, K) = ⊤) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hperf₂ : commutator (StatedOmega Q₂₀) = ⊤) (hinj : Function.Injective (oProj Q₀))
    {S₂ : Subgroup (GL ι₂ K)} (hS₂ : S₂ ≤ StatedOmega Q₂₀) (hS₂p : IsPGroup 2 S₂) {R : ℤ}
    (hR : Odd R) (hcard : (Nat.card (StatedProj (StatedOmega Q₀)) : ℤ) =
      (Nat.card K : ℤ) ^ (2 * Fintype.card ι₂ + 2) * Nat.card S₂ * R)
    {M : GL ι K} (hMH : M ∈ StatedOmega Q₀) (hM2 : orderOf M = 2) (hr : commRank M = 2)
    (hsing : ∀ v, Q₀ (((M : Matrix ι ι K) - 1) *ᵥ v) = 0) : OrthM123 Q₀ M hMH := by
  subst hQf hQ₂f
  obtain ⟨a₁, a₂, hN, hQa₁, hQa₂, h12, hli'⟩ :=
    exists_cTwoX_of_singular hnd (quad_mulVec_of_mem_statedOmega hMH) hM2 hr hsing
  have hQu : ∀ s : Fin 2, Qf (oVec oe 0 (uE (.inl s))) = 0 := fun s => by
    rw [quad_oVec_inr hQ, quadPlus_two_uE_inl]
  have hB : ∀ c c' : Fin 2 ⊕ Fin 2, Qf.polarBilin (oVec oe 0 (uE c)) (oVec oe 0 (uE c')) =
      (quadPlus 2 K).polarBilin (uE c) (uE c') := fun c c' => by
    rw [polarBilin_oVec_inr_inr hQ]
  obtain ⟨G, hG, hGa₂, hGa₁⟩ := exists_isometryGL_pair hnd hli'
    (b₁ := oVec oe 0 (uE (.inl 0))) (b₂ := oVec oe 0 (uE (.inl 1)))
    (linearIndependent_pair_of_polar (y := oVec oe 0 (uE (.inr 0)))
      (x := oVec oe 0 (uE (.inr 1))) (by rw [hB, polarBilin_uE_inl_inr]; simp)
      (by rw [hB, polarBilin_uE_inl_inr]; simp) (by rw [hB, polarBilin_uE_inl_inr]; simp))
    hQa₂ hQa₁ (hQu 0) (hQu 1) (by rw [polarBilin_comm]; exact h12)
    (by rw [hB, polarBilin_uE_inl_inl])
  have hconj : (G : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) * ((G⁻¹ : GL ι K) : Matrix ι ι K) =
      cTwoX Qf (oVec oe 0 (uE (.inl 0))) (oVec oe 0 (uE (.inl 1))) := by
    have h1 := conj_cTwoX (D := G⁻¹) (isometry_inv hG) a₂ a₁
    rw [inv_inv, hGa₂, hGa₁] at h1
    rw [hN, h1]
  have hGG : (G : Matrix ι ι K) * ((G⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGM : G * M * G⁻¹ = oRhoOneGL oe (slTr 1) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, oRhoOneGL_slTr hQ 1, one_smul, ← hconj, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hGG, add_sub_cancel]
  exact orthM123_of_conj hG hMH (oRhoOne oe hQ hSL (slTr 1)).2 hGM
    (orthM123_oM₀ hQ hSL hnd₂ ht0 ht1 hinj hperf₂ hS₂ hS₂p hR hcard)

end Singular

end CFSG.ComponentClassification.RankTwoClassical.ORigid
