module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Levi

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem commute_oKappaGL_oRhoTwoGL (Y : GL ι₂ K) (A : SL(2, K)) :
    Commute (oKappaGL oe Y) (oRhoTwoGL oe A) := by
  show oKappaGL oe Y * oRhoTwoGL oe A = oRhoTwoGL oe A * oKappaGL oe Y
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_oKappaGL, coe_oRhoTwoGL, oblk_mul, oblk_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]

variable (oe) in
@[expose] noncomputable def oLeviHom (Q₂ : QuadraticForm K (ι₂ → K)) :
    ↥(StatedOmega ⇑Q₂) × SL(2, K) →* GL ι K :=
  ((oKappaGL oe).comp (StatedOmega ⇑Q₂).subtype).noncommCoprod (oRhoTwoGL oe)
    fun Y A => commute_oKappaGL_oRhoTwoGL (Y : GL ι₂ K) A

variable [CharP K 2] {Q₂ : QuadraticForm K (ι₂ → K)}

omit [CharP K 2] in
theorem range_oLeviHom : (oLeviHom oe Q₂).range = oL₀ oe Q₂ := by
  refine (MonoidHom.noncommCoprod_range _ _ _).trans ?_
  rw [MonoidHom.range_comp, range_subtype, oL₀, sup_comm]

omit [CharP K 2] in
theorem mem_oL₀_iff {g : GL ι K} : g ∈ oL₀ oe Q₂ ↔
    ∃ Y ∈ StatedOmega ⇑Q₂, ∃ A : SL(2, K), g = oKappaGL oe Y * oRhoTwoGL oe A := by
  rw [← range_oLeviHom]
  constructor
  · rintro ⟨⟨Y, A⟩, rfl⟩
    exact ⟨Y, Y.2, A, rfl⟩
  · rintro ⟨Y, hY, A, rfl⟩
    exact ⟨⟨⟨Y, hY⟩, A⟩, rfl⟩

theorem oL₀_inf_oQE : oL₀ oe Q₂ ⊓ oQE oe Q₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgL, hgQ⟩
  obtain ⟨Y, -, A, rfl⟩ := mem_oL₀_iff.mp hgL
  obtain ⟨u, c, hq⟩ := (mem_oQE oe Q₂).mp hgQ
  have hm : qE oe Q₂ u c = oblk oe (Y : Matrix ι₂ ι₂ K) (rhoTwoMat A) := by
    have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) hq
    simp only [coe_qEGL, Units.val_mul, coe_oKappaGL, coe_oRhoTwoGL, oblk_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    exact h1
  have hA : A = 1 := by
    have h1 := congrArg (eBlk oe) hm
    rw [eBlk_qE, eBlk_oblk] at h1
    apply Subtype.ext
    ext s t
    have h2 := congrFun (congrFun h1 s) t
    rw [rhoTwoMat_apply, fromBlocks_apply₁₁] at h2
    exact h2.symm
  have hY : Y = 1 := by
    have h1 := congrArg (uBlk oe) hm
    rw [uBlk_qE, uBlk_oblk] at h1
    exact Units.ext h1.symm
  rw [mem_bot, hY, hA, map_one, map_one, one_mul]

variable {Q : QuadraticForm K (ι → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem conj_mem_oQE {l : GL ι K} (hl : l ∈ oL₀ oe Q₂) {g : GL ι K} (hg : g ∈ oQE oe Q₂) :
    l * g * l⁻¹ ∈ oQE oe Q₂ := by
  obtain ⟨Y, hY, A, rfl⟩ := mem_oL₀_iff.mp hl
  obtain ⟨u, c, rfl⟩ := (mem_oQE oe Q₂).mp hg
  obtain ⟨c', hc'⟩ := conj_qE_levi hQ (quad_mulVec_of_mem_statedOmega hY) A u c
  rw [hc']
  exact qEGL_mem_oQE oe Q₂ _ _

theorem oXt_le_normalizer_oQE : oXt oe Q₂ ≤ normalizer (oQE oe Q₂ : Set (GL ι K)) := by
  refine sup_le (le_normalizer) fun l hl => ?_
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_oQE hQ hl, fun h => ?_⟩
  have h1 := conj_mem_oQE hQ (inv_mem hl) h
  rwa [inv_inv, show l⁻¹ * (l * g * l⁻¹) * l = g by group] at h1

omit hQ [Fintype ι₂] [DecidableEq ι₂] in
theorem isPGroup_oQE : IsPGroup 2 ↥(oQE oe Q₂) := by
  rintro ⟨_, ⟨⟨u, c⟩, rfl⟩⟩
  refine ⟨2, Subtype.ext ?_⟩
  have h2 : qEGL oe Q₂ u c * qEGL oe Q₂ u c = qEGL oe Q₂ 0 (Q₂.polarBilin (u 0) (u 1)) := by
    apply Units.ext
    rw [Units.val_mul, coe_qEGL, qE_mul, coe_qEGL]
    congr 1
    · funext t a
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    · linear_combination c * CharTwo.two_eq_zero (R := K)
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, _root_.sq (qEGL oe Q₂ u c), h2, _root_.sq,
    qEGL_zero_mul_self]

end Levi

section Generic

variable {G : Type*} [Group G]

theorem le_normalizer_of_conj_mem {H X : Subgroup G}
    (h : ∀ x ∈ X, ∀ g ∈ H, x * g * x⁻¹ ∈ H) : X ≤ normalizer (H : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h x hx g, fun hg => ?_⟩
  have h1 := h x⁻¹ (inv_mem hx) _ hg
  rwa [inv_inv, show x⁻¹ * (x * g * x⁻¹) * x = g by group] at h1

theorem commutatorElement_mem_of_mem_coset {N X : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set G)) {g₁ g₂ l₁ l₂ : G} (hg₁ : g₁ ∈ X) (hg₂ : g₂ ∈ X)
    (hl₁ : l₁ ∈ X) (hl₂ : l₂ ∈ X) (h₁ : l₁⁻¹ * g₁ ∈ N) (h₂ : l₂⁻¹ * g₂ ∈ N)
    (hc : l₁ * l₂ = l₂ * l₁) : ⁅g₁, g₂⁆ ∈ N := by
  have : (N.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have key : ∀ {g l : G} (hg : g ∈ X) (hl : l ∈ X), l⁻¹ * g ∈ N →
      ((⟨g, hg⟩ : ↥X) : ↥X ⧸ N.subgroupOf X) = ((⟨l, hl⟩ : ↥X) : ↥X ⧸ N.subgroupOf X) :=
    fun {g l} hg hl h =>
      (QuotientGroup.eq.mpr (show (⟨l, hl⟩ : ↥X)⁻¹ * ⟨g, hg⟩ ∈ N.subgroupOf X from h)).symm
  have hl : ⁅(⟨l₁, hl₁⟩ : ↥X), (⟨l₂, hl₂⟩ : ↥X)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subtype.ext hc)
  have h1 : ((⁅(⟨g₁, hg₁⟩ : ↥X), (⟨g₂, hg₂⟩ : ↥X)⁆ : ↥X) : ↥X ⧸ N.subgroupOf X) = 1 := by
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, key hg₁ hl₁ h₁, key hg₂ hl₂ h₂, ← QuotientGroup.mk'_apply,
      ← QuotientGroup.mk'_apply, ← map_commutatorElement, hl, map_one]
  have h2 := (QuotientGroup.eq_one_iff (N := N.subgroupOf X) _).mp h1
  exact h2

end Generic

section Decomp

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem exists_mul_of_mem_oXt {g : GL ι K} (hg : g ∈ oXt oe Q₂) :
    ∃ l ∈ oL₀ oe Q₂, ∃ q ∈ oQE oe Q₂, g = l * q := by
  have h := coe_mul_of_left_le_normalizer_right (oL₀ oe Q₂) (oQE oe Q₂)
    ((le_sup_right : oL₀ oe Q₂ ≤ oXt oe Q₂).trans (oXt_le_normalizer_oQE hQ))
  rw [sup_comm] at h
  have hg' : g ∈ ((oQE oe Q₂ ⊔ oL₀ oe Q₂ : Subgroup (GL ι K)) : Set (GL ι K)) := hg
  rw [h] at hg'
  obtain ⟨l, hl, q, hq, hlq⟩ := hg'
  exact ⟨l, hl, q, hq, hlq.symm⟩

omit hQ [CharP K 2] in
theorem blk_oKappaGL_mul_oRhoTwoGL_mul [CharP K 2] (Y : GL ι₂ K) (A : SL(2, K))
    (u : Fin 2 → ι₂ → K) (c : K) :
    uBlk oe ((oKappaGL oe Y * oRhoTwoGL oe A * qEGL oe Q₂ u c : GL ι K) : Matrix ι ι K) =
        (Y : Matrix ι₂ ι₂ K) ∧
      eBlk oe ((oKappaGL oe Y * oRhoTwoGL oe A * qEGL oe Q₂ u c : GL ι K) : Matrix ι ι K) =
        (A : Matrix (Fin 2) (Fin 2) K) := by
  have hl : ((oKappaGL oe Y * oRhoTwoGL oe A : GL ι K) : Matrix ι ι K) =
      oblk oe (Y : Matrix ι₂ ι₂ K) (rhoTwoMat A) := by
    rw [Units.val_mul, coe_oKappaGL, coe_oRhoTwoGL, oblk_mul, Matrix.mul_one, Matrix.one_mul]
  have hlS : IsEShape oe ((oKappaGL oe Y * oRhoTwoGL oe A : GL ι K) : Matrix ι ι K) :=
    isEShape_of_mem (mul_mem (oKappaGL_mem_cenM₀ Y) (oRhoTwoGL_mem_cenM₀ A))
  have hqS : IsEShape oe ((qEGL oe Q₂ u c : GL ι K) : Matrix ι ι K) :=
    isEShape_of_mem (qEGL_mem_cenM₀ oe Q₂ u c)
  rw [Units.val_mul]
  refine ⟨?_, ?_⟩
  · rw [uBlk_mul hlS hqS, coe_qEGL, uBlk_qE, Matrix.mul_one, hl, uBlk_oblk]
  · rw [eBlk_mul _ hqS, coe_qEGL, eBlk_qE, Matrix.mul_one, hl, eBlk_oblk]
    ext s t
    simp [rhoTwoMat_apply]

end Decomp

section Char

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem uBlk_mem_statedOmega_of_mem_oXt {g : GL ι K} (hg : g ∈ oXt oe Q₂)
    (hgC : g ∈ cenM₀ K oe) : (uBlkHom K oe).toHomUnits ⟨g, hgC⟩ ∈ StatedOmega ⇑Q₂ := by
  obtain ⟨l, hl, q, hq, rfl⟩ := exists_mul_of_mem_oXt hQ hg
  obtain ⟨Y, hY, A, rfl⟩ := mem_oL₀_iff.mp hl
  obtain ⟨u, c, rfl⟩ := (mem_oQE oe Q₂).mp hq
  have h1 : (uBlkHom K oe).toHomUnits ⟨_, hgC⟩ = Y := by
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, uBlkHom_apply]
    exact (blk_oKappaGL_mul_oRhoTwoGL_mul Y A u c).1
  rw [h1]
  exact hY

theorem le_oQE_of_normal (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K))) (hO₂ : NoNormalTwo (StatedOmega ⇑Q₂))
    {R : Subgroup (GL ι K)} (hR : R ≤ oXt oe Q₂) (hR2 : IsPGroup 2 ↥R)
    (hRN : oXt oe Q₂ ≤ normalizer (R : Set (GL ι K))) : R ≤ oQE oe Q₂ := by
  have hRC : R ≤ cenM₀ K oe := hR.trans (oXt_le_cenM₀ oe Q₂)
  have hR2' : IsPGroup 2 ↥(R.subgroupOf (cenM₀ K oe)) :=
    hR2.of_equiv (subgroupOfEquivOfLe hRC).symm
  have hconj : ∀ x ∈ oXt oe Q₂, ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hx r hr =>
    (mem_normalizer_iff.mp (hRN hx) r).mp hr
  set φU := (uBlkHom K oe).toHomUnits
  have hU : (R.subgroupOf (cenM₀ K oe)).map φU = ⊥ := by
    refine hO₂ _ ?_ (hR2'.map φU) (le_normalizer_of_conj_mem fun Y hY g hg => ?_)
    · rintro _ ⟨r, hr, rfl⟩
      exact uBlk_mem_statedOmega_of_mem_oXt hQ (hR hr) r.2
    · obtain ⟨r, hr, rfl⟩ := hg
      have hk : oKappaGL oe Y ∈ oXt oe Q₂ := mem_sup_right (mem_sup_right ⟨Y, hY, rfl⟩)
      have hkC := oKappaGL_mem_cenM₀ (oe := oe) Y
      refine ⟨⟨_, hkC⟩ * r * ⟨_, hkC⟩⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, Subgroup.coe_mk]
        exact hconj _ hk _ hr
      have hφk : φU ⟨_, hkC⟩ = Y := by
        apply Units.ext
        rw [MonoidHom.coe_toHomUnits, uBlkHom_apply]
        show uBlk oe ((oKappaGL oe Y : GL ι K) : Matrix ι ι K) = _
        rw [coe_oKappaGL, uBlk_oblk]
      simp only [map_mul, map_inv, hφk]
  set φE := (eBlkHom K oe).toHomUnits
  have hE : ((R.subgroupOf (cenM₀ K oe)).map φE).comap
      (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K) = ⊥ := by
    refine hSL₂ _ le_top ((hR2'.map φE).comap_of_injective _
      Matrix.SpecialLinearGroup.toGL_injective) (le_normalizer_of_conj_mem fun A _ B hB => ?_)
    obtain ⟨r, hr, hrB⟩ := hB
    have hk : oRhoTwoGL oe A ∈ oXt oe Q₂ := mem_sup_right (mem_sup_left ⟨A, rfl⟩)
    have hkC := oRhoTwoGL_mem_cenM₀ (oe := oe) A
    refine ⟨⟨_, hkC⟩ * r * ⟨_, hkC⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_mk]
      exact hconj _ hk _ hr
    have hφk : φE ⟨_, hkC⟩ = Matrix.SpecialLinearGroup.toGL A := by
      apply Units.ext
      rw [MonoidHom.coe_toHomUnits, eBlkHom_apply]
      show eBlk oe ((oRhoTwoGL oe A : GL ι K) : Matrix ι ι K) = (A : Matrix (Fin 2) (Fin 2) K)
      rw [coe_oRhoTwoGL, eBlk_oblk]
      funext s t
      rw [rhoTwoMat_apply, fromBlocks_apply₁₁]
    simp only [map_mul, map_inv, hφk, hrB]
  intro r hr
  have hrC := hRC hr
  have hrQ := quad_mulVec_of_mem_statedOmega (hle (hR hr))
  have hu : uBlk oe (r : Matrix ι ι K) = 1 := by
    have h1 : φU ⟨r, hrC⟩ ∈ (R.subgroupOf (cenM₀ K oe)).map φU := ⟨⟨r, hrC⟩, hr, rfl⟩
    rw [hU, mem_bot] at h1
    exact congrArg Units.val h1
  have he : eBlk oe (r : Matrix ι ι K) = 1 := by
    obtain ⟨A₀, hA₀⟩ : ∃ A₀ : SL(2, K),
        (A₀ : Matrix (Fin 2) (Fin 2) K) = eBlk oe (r : Matrix ι ι K) :=
      ⟨⟨_, det_eBlk hQ (commute_oN₀_of_mem hrC) hrQ⟩, rfl⟩
    have h1 : A₀ ∈ ((R.subgroupOf (cenM₀ K oe)).map φE).comap
        (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K) := by
      refine ⟨⟨r, hrC⟩, hr, ?_⟩
      apply Units.ext
      rw [MonoidHom.coe_toHomUnits, eBlkHom_apply]
      show eBlk oe (r : Matrix ι ι K) = (A₀ : Matrix (Fin 2) (Fin 2) K)
      exact hA₀.symm
    rw [hE] at h1
    have h2 : A₀ = 1 := Subgroup.mem_bot.mp h1
    rw [← hA₀, h2]
    rfl
  have h1 := eq_qE_of hQ (commute_oN₀_of_mem hrC) hrQ he hu
  exact ⟨⟨_, _⟩, Units.ext h1.symm⟩

theorem map_oQE [Finite K] (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K))) (hO₂ : NoNormalTwo (StatedOmega ⇑Q₂))
    (β : MulAut ↥(oXt oe Q₂)) :
    ((oQE oe Q₂).subgroupOf (oXt oe Q₂)).map β.toMonoidHom =
      (oQE oe Q₂).subgroupOf (oXt oe Q₂) := by
  set N := (oQE oe Q₂).subgroupOf (oXt oe Q₂)
  have hQX : oQE oe Q₂ ≤ oXt oe Q₂ := le_sup_left
  have hN2 : IsPGroup 2 ↥N :=
    (isPGroup_oQE (oe := oe) (Q₂ := Q₂)).of_equiv (subgroupOfEquivOfLe hQX).symm
  have hNn : N.Normal :=
    (normal_subgroupOf_iff_le_normalizer hQX).mpr (oXt_le_normalizer_oQE hQ)
  have hβn : (N.map β.toMonoidHom).Normal := hNn.map _ β.surjective
  have hR : (N.map β.toMonoidHom).map (oXt oe Q₂).subtype ≤ oQE oe Q₂ := by
    refine le_oQE_of_normal hQ hle hSL₂ hO₂ (map_subtype_le _) ((hN2.map _).map _) ?_
    refine le_normalizer_of_conj_mem fun x hx g hg => ?_
    obtain ⟨g', hg', rfl⟩ := hg
    have h1 := hβn.conj_mem g' hg' ⟨x, hx⟩
    refine ⟨_, h1, ?_⟩
    rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype, Subgroup.coe_mk]
  exact Subgroup.eq_of_le_of_card_ge (fun g hg => hR ⟨g, hg, rfl⟩)
    (Subgroup.card_map_of_injective β.injective).ge

end Char

end CFSG.ComponentClassification.RankTwoClassical.ORigid
