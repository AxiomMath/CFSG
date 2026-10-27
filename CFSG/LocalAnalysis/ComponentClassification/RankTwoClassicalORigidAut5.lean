module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidFactor
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidFix

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Inner

variable {K : Type} [Field K] {ι₃ ι₂ : Type} [Fintype ι₃] [DecidableEq ι₃] [Fintype ι₂]
  [DecidableEq ι₂] (oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂)

omit [DecidableEq ι₃] in
theorem finrank_fixVec_eq_card {H : Subgroup (GL ι₂ K)}
    (hH : ∀ w, w ∈ fixVec H ↔ ∀ b, w (oe₂ (.inr b)) = 0) :
    Module.finrank K (fixVec H) = Fintype.card ι₃ := by
  have hker : fixVec H = LinearMap.ker (LinearMap.funLeft K K fun b => oe₂ (.inr b)) := by
    ext w
    rw [hH, LinearMap.mem_ker, funext_iff]
    rfl
  have hsurj : Function.Surjective
      (LinearMap.funLeft K K fun b : Fin 2 ⊕ Fin 2 => oe₂ (.inr b)) :=
    LinearMap.funLeft_surjective_of_injective K K _ fun b b' h =>
      Sum.inr_injective (oe₂.injective h)
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft K K fun b : Fin 2 ⊕ Fin 2 => oe₂ (.inr b))
  have hcard : Fintype.card ι₂ = Fintype.card ι₃ + 4 := by
    rw [← Fintype.card_congr oe₂, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, ← hker, hcard, Fintype.card_sum, Fintype.card_fin] at h1
  omega

theorem oInnerGL_mulVec_eq_self (X : GL (Fin 2 ⊕ Fin 2) K) {w : ι₂ → K}
    (hw : ∀ b, w (oe₂ (.inr b)) = 0) :
    ((oInnerGL oe₂ X : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ w = w := by
  have h0 : (fun b => w (oe₂ (.inr b))) = 0 := funext hw
  rw [coe_oInnerGL, oblk_mulVec_eq, one_mulVec, h0, mulVec_zero]
  refine oVec_ext oe₂ (fun a => ?_) (fun b => ?_)
  · rw [oVec_apply_inl]
  · rw [oVec_apply_inr, Pi.zero_apply, hw b]

theorem oY₂_le_range_oInnerGL : oY₂ oe₂ ≤ (oInnerGL (K := K) oe₂).range := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact ⟨rhoTwoMat.toHomUnits A, rfl⟩
  · rintro _ ⟨B, rfl⟩
    exact ⟨rhoOneMat.toHomUnits B, rfl⟩

theorem inner_eq_zero_of_torus {t : K} (ht1 : t ≠ 1) {A : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹]) {w : ι₂ → K}
    (hw : ((oRhoTwoGL oe₂ A : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ w = w) (b : Fin 2 ⊕ Fin 2) :
    w (oe₂ (.inr b)) = 0 := by
  have key : ∀ c : K, c ≠ 1 → ∀ x : K, c * x = x → x = 0 := fun c hc x hx => by
    have h : (c - 1) * x = 0 := by rw [sub_mul, hx, one_mul, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc)
  have ht1' : t⁻¹ ≠ 1 := fun h => ht1 (inv_eq_one.mp h)
  have h1 := congrFun hw (oe₂ (.inr b))
  rw [coe_oRhoTwoGL, oblk_mulVec_inr, rhoTwoMat_apply, hA, fromBlocks_mulVec] at h1
  rcases b with s | s <;> fin_cases s
  · exact key t ht1 _ (by simpa [mulVec, dotProduct, Fin.sum_univ_two] using h1)
  · exact key t⁻¹ ht1' _ (by simpa [mulVec, dotProduct, Fin.sum_univ_two] using h1)
  · exact key t⁻¹ ht1' _
      (by simpa [mulVec, dotProduct, Fin.sum_univ_two, adjugate_fin_two] using h1)
  · exact key t ht1 _ (by simpa [mulVec, dotProduct, Fin.sum_univ_two, adjugate_fin_two] using h1)

theorem mem_fixVec_oY₂_iff {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (w : ι₂ → K) :
    w ∈ fixVec (oY₂ (K := K) oe₂) ↔ ∀ b, w (oe₂ (.inr b)) = 0 := by
  constructor
  · intro hw
    obtain ⟨A, hA⟩ := exists_torusSL ht0
    exact inner_eq_zero_of_torus oe₂ ht1 hA (hw _ (mem_sup_left ⟨A, rfl⟩))
  · intro hw Y hY
    obtain ⟨X, rfl⟩ := oY₂_le_range_oInnerGL oe₂ hY
    exact oInnerGL_mulVec_eq_self oe₂ X hw

theorem mem_fixVec_torus_iff {t : K} (ht1 : t ≠ 1) {A : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹]) (w : ι₂ → K) :
    w ∈ fixVec (zpowers (oRhoTwoGL oe₂ A)) ↔ ∀ b, w (oe₂ (.inr b)) = 0 := by
  constructor
  · intro hw
    exact inner_eq_zero_of_torus oe₂ ht1 hA (hw _ (mem_zpowers _))
  · intro hw
    have hd : oRhoTwoGL oe₂ A = oInnerGL oe₂ (rhoTwoMat.toHomUnits A) := rfl
    exact mem_fixVec_zpowers (by rw [hd]; exact oInnerGL_mulVec_eq_self oe₂ _ hw)

theorem commutator_oY₂ (hSL : commutator SL(2, K) = ⊤) :
    ⁅oY₂ (K := K) oe₂, oY₂ (K := K) oe₂⁆ = oY₂ (K := K) oe₂ := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · conv_lhs => rw [← commutator_range_of_perfect (oRhoTwoGL oe₂) hSL]
    exact commutator_mono le_sup_left le_sup_left
  · conv_lhs => rw [← commutator_range_of_perfect (oRhoOneGL oe₂) hSL]
    exact commutator_mono le_sup_right le_sup_right

theorem oY₂_le_statedOmega [CharP K 2] {Q₂ : (ι₂ → K) → K} {Q₃ : (ι₃ → K) → K}
    (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
    (hSL : commutator SL(2, K) = ⊤) : oY₂ oe₂ ≤ StatedOmega Q₂ := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact (oRhoTwo oe₂ hQ₂ hSL A).2
  · rintro _ ⟨B, rfl⟩
    exact (oRhoOne oe₂ hQ₂ hSL B).2

end Inner

section Aut

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₃ ι₂ ι : Type} [Fintype ι₃]
  [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι]
  {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {Q : QuadraticForm K (ι → K)} {Q₂ : QuadraticForm K (ι₂ → K)} {Q₃ : QuadraticForm K (ι₃ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
    StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
include hQ hQ₂

theorem exists_map_oY₂_eq_conj (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K))) (hO₂ : NoNormalTwo (StatedOmega ⇑Q₂))
    (hSL : commutator SL(2, K) = ⊤) (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega ⇑Q₂, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    (hnd₂ : Q₂.polarBilin.Nondegenerate) (hsimpSL : IsSimpleGroup SL(2, K))
    (hsimp : IsSimpleGroup ↥(StatedOmega ⇑Q₂))
    (hcard : Nat.card ↥(StatedOmega ⇑Q₂) ≠ Nat.card SL(2, K)) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (β : MulAut ↥(oXt oe Q₂)) :
    ∃ g : GL ι K, (∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v) ∧
      ((((oY₂ oe₂).map (oKappaGL oe)).subgroupOf (oXt oe Q₂)).map β.toMonoidHom).map
        (oXt oe Q₂).subtype = ((oY₂ oe₂).map (oKappaGL oe)).map (MulAut.conj g).toMonoidHom := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨y, hyQ, hy⟩ := exists_map_oL₀_eq_conj hQ hle hSL₂ hO₂ hSL hperf₂ hfix ht0 ht1 β
  have hyX : y ∈ oXt oe Q₂ := mem_sup_left hyQ
  obtain ⟨β', hβ'⟩ : ∃ β' : MulAut ↥(oXt oe Q₂), β' = MulAut.conj ⟨y, hyX⟩ * β := ⟨_, rfl⟩
  have hβ'v : ∀ z, ((β' z : ↥(oXt oe Q₂)) : GL ι K) = y * β z * y⁻¹ := fun z => by
    rw [hβ', MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
  have hL : ∀ g : GL ι K, g ∈ oL₀ oe Q₂ ↔ g ∈ ((((oL₀ oe Q₂).subgroupOf (oXt oe Q₂)).map
      β.toMonoidHom).map (oXt oe Q₂).subtype).map (MulAut.conj y).toMonoidHom := fun g => by
    rw [hy]
  have hβ'L : ((oL₀ oe Q₂).subgroupOf (oXt oe Q₂)).map β'.toMonoidHom =
      (oL₀ oe Q₂).subgroupOf (oXt oe Q₂) := by
    ext z
    rw [mem_subgroupOf, hL]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨((β l : ↥(oXt oe Q₂)) : GL ι K), ⟨β l, ⟨l, hl, rfl⟩, rfl⟩, (hβ'v l).symm⟩
    · rintro ⟨_, ⟨w, ⟨l, hl, rfl⟩, rfl⟩, hwz⟩
      refine ⟨l, hl, Subtype.ext ?_⟩
      rw [MulEquiv.coe_toMonoidHom, hβ'v]
      exact hwz
  have hκinj : Function.Injective (oKappaGL (K := K) oe) := fun Y Y' h => by
    have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
    simp only [coe_oKappaGL] at h1
    exact Units.ext (oblk_injective h1).1
  have hY₂Ω : oY₂ oe₂ ≤ StatedOmega ⇑Q₂ := oY₂_le_statedOmega oe₂ hQ₂ hSL
  have hκX : (oY₂ oe₂).map (oKappaGL oe) ≤ oXt oe Q₂ :=
    (Subgroup.map_mono hY₂Ω).trans (le_sup_right.trans le_sup_right)
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup ↥(oXt oe Q₂),
      Z = ((oY₂ oe₂).map (oKappaGL oe)).subgroupOf (oXt oe Q₂) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (GL ι K),
      R = (Z.map β'.toMonoidHom).map (oXt oe Q₂).subtype := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (GL ι₂ K), H = R.comap (oKappaGL oe) := ⟨_, rfl⟩
  have hRκ : ∀ r ∈ R, ∃ Y' ∈ StatedOmega ⇑Q₂, r = oKappaGL oe Y' := by
    rw [hR]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [hZ] at hz
    obtain ⟨Y, hY, hYz⟩ := Subgroup.mem_map.mp (mem_subgroupOf.mp hz)
    have hzeq : z = ⟨oKappaGL oe Y, oKappaGL_mem_oXt (hY₂Ω hY)⟩ := Subtype.ext hYz.symm
    subst hzeq
    obtain ⟨Y', hY', hYY'⟩ := exists_beta_oKappaGL hQ hle hsimpSL hsimp hcard β' hβ'L (hY₂Ω hY)
    exact ⟨Y', hY', hYY'⟩
  have hHmap : H.map (oKappaGL oe) = R := by
    rw [hH]
    refine le_antisymm (Subgroup.map_comap_le _ _) fun r hr => ?_
    obtain ⟨Y', -, rfl⟩ := hRκ r hr
    exact ⟨Y', hr, rfl⟩
  have hHΩ : H ≤ StatedOmega ⇑Q₂ := fun Y' hY' => by
    rw [hH] at hY'
    obtain ⟨Y'', hY'', hYY⟩ := hRκ _ hY'
    rw [hκinj hYY]
    exact hY''
  have hHsub : (H.map (oKappaGL oe)).subgroupOf (oXt oe Q₂) = Z.map β'.toMonoidHom := by
    rw [hHmap, hR]
    exact Subgroup.comap_map_eq_self_of_injective (oXt oe Q₂).subtype_injective _
  have hZperf : ⁅Z, Z⁆ = Z := by
    apply Subgroup.map_injective (oXt oe Q₂).subtype_injective
    rw [Subgroup.map_commutator, hZ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hκX,
      ← Subgroup.map_commutator, commutator_oY₂ oe₂ hSL]
  have hHperf : ⁅H, H⁆ = H := by
    apply Subgroup.map_injective hκinj
    rw [Subgroup.map_commutator, hHmap, hR, ← Subgroup.map_commutator,
      ← Subgroup.map_commutator, hZperf]
  have hHcard : Nat.card H = Nat.card (oY₂ (K := K) oe₂) := by
    rw [← Subgroup.card_map_of_injective hκinj, hHmap, hR,
      Subgroup.card_map_of_injective (oXt oe Q₂).subtype_injective,
      Subgroup.card_map_of_injective (f := β'.toMonoidHom) β'.injective, hZ,
      ← Subgroup.card_map_of_injective (oXt oe Q₂).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hκX, Subgroup.card_map_of_injective hκinj]
  obtain ⟨A₀, hA₀⟩ := exists_torusSL ht0
  have hd₀Y : oRhoTwoGL oe₂ A₀ ∈ oY₂ oe₂ := mem_sup_left ⟨A₀, rfl⟩
  obtain ⟨h, hhΩ, hh⟩ :=
    exists_beta_oKappaGL hQ hle hsimpSL hsimp hcard β' hβ'L (hY₂Ω hd₀Y)
  have hhH : h ∈ H := by
    rw [hH]
    show oKappaGL oe h ∈ R
    rw [hR, ← hh, hZ]
    exact ⟨_, ⟨⟨oKappaGL oe (oRhoTwoGL oe₂ A₀), oKappaGL_mem_oXt (hY₂Ω hd₀Y)⟩,
      ⟨oRhoTwoGL oe₂ A₀, hd₀Y, rfl⟩, rfl⟩, rfl⟩
  have hA₀pow : A₀ ^ (Fintype.card K - 1) = 1 := by
    have htq : t ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one t ht0
    have htq' : t⁻¹ ^ (Fintype.card K - 1) = 1 := by rw [inv_pow, htq, inv_one]
    have hdiag : (A₀ : Matrix (Fin 2) (Fin 2) K) = diagonal ![t, t⁻¹] := by
      rw [hA₀]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hdiag, diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [htq, htq']
  have hhpow : h ^ (Fintype.card K - 1) = 1 := by
    have h1 : (⟨oKappaGL oe (oRhoTwoGL oe₂ A₀), oKappaGL_mem_oXt (hY₂Ω hd₀Y)⟩ :
        ↥(oXt oe Q₂)) ^ (Fintype.card K - 1) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, Subgroup.coe_one]
      show oKappaGL oe (oRhoTwoGL oe₂ A₀) ^ (Fintype.card K - 1) = 1
      rw [← map_pow, ← map_pow, hA₀pow, map_one, map_one]
    apply hκinj
    rw [map_one, map_pow, ← hh, ← SubmonoidClass.coe_pow, ← map_pow, h1, map_one,
      Subgroup.coe_one]
  have hC : Module.finrank K (fixVec H) = Fintype.card ι₃ := by
    rw [← finrank_fixVec_eq_card oe₂ (mem_fixVec_oY₂_iff oe₂ ht0 ht1)]
    exact (finrank_fixVec_eq_of_map hQ hle hSL₂ hO₂ β' hY₂Ω hHΩ (by rw [hHsub, hZ])).symm
  have hzκ : ∀ g : GL ι₂ K, ∀ hg : g ∈ StatedOmega ⇑Q₂,
      ((zpowers g).map (oKappaGL oe)).subgroupOf (oXt oe Q₂) =
        zpowers ⟨oKappaGL oe g, oKappaGL_mem_oXt hg⟩ := fun g hg => by
    apply Subgroup.map_injective (oXt oe Q₂).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      Subgroup.coe_subtype]
    exact inf_of_le_left (zpowers_le.mpr (oKappaGL_mem_oXt hg))
  have hCh : Module.finrank K (fixVec (zpowers h)) = Fintype.card ι₃ := by
    rw [← finrank_fixVec_eq_card oe₂ (mem_fixVec_torus_iff oe₂ ht1 hA₀)]
    refine (finrank_fixVec_eq_of_map hQ hle hSL₂ hO₂ β' (zpowers_le.mpr (hY₂Ω hd₀Y))
      (zpowers_le.mpr hhΩ) ?_).symm
    rw [hzκ _ (hY₂Ω hd₀Y), hzκ _ hhΩ, MonoidHom.map_zpowers]
    congr 1
    exact Subtype.ext hh
  obtain ⟨G, hGQ, hGH⟩ := exists_conj_eq_oY₂ hQ₂ hnd₂ hHΩ hHperf hHcard hhH hhpow hC hCh
  have hκG : ∀ v, Q (((oKappaGL oe G : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := fun v =>
    quad_oblk_mulVec_eq hQ hGQ (fun u => by simp) v
  have hβv : ∀ z, ((β z : ↥(oXt oe Q₂)) : GL ι K) = y⁻¹ * β' z * y := fun z => by
    rw [hβ'v]
    group
  refine ⟨y⁻¹ * oKappaGL oe G,
    isometry_mul (isometry_inv' (quad_mulVec_of_mem_statedOmega (hle hyX))) hκG, ?_⟩
  ext g
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hr : ((β' z : ↥(oXt oe Q₂)) : GL ι K) ∈ R := by
      rw [hR]
      exact ⟨_, ⟨z, by rw [hZ]; exact hz, rfl⟩, rfl⟩
    rw [← hHmap, hGH] at hr
    obtain ⟨_, ⟨Y, hY, rfl⟩, hYr⟩ := hr
    refine ⟨oKappaGL oe Y, ⟨Y, hY, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv] at hYr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
    rw [hβv, ← hYr]
    group
  · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
    have hr : oKappaGL oe (G * Y * G⁻¹) ∈ R := by
      rw [← hHmap, hGH]
      exact ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
    rw [hR] at hr
    obtain ⟨_, ⟨z, hz, rfl⟩, hzr⟩ := hr
    refine ⟨β z, ⟨z, by rw [← hZ]; exact hz, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype] at hzr ⊢
    rw [hβv, hzr, map_mul, map_mul, map_inv]
    group

end Aut

end CFSG.ComponentClassification.RankTwoClassical.ORigid
