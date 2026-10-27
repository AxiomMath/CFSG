module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinBarW

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Shapes

variable {K : Type} [Field K] {k : ℕ}

theorem inv_mul_conj_mul_GL {ι : Type} [Fintype ι] [DecidableEq ι] (A : GL ι K)
    (M : Matrix ι ι K) :
    ((A⁻¹ : GL ι K) : Matrix ι ι K) * ((A : Matrix ι ι K) * M * ((A⁻¹ : GL ι K) : Matrix ι ι K)) *
      (A : Matrix ι ι K) = M := by
  calc ((A⁻¹ : GL ι K) : Matrix ι ι K) * ((A : Matrix ι ι K) * M *
        ((A⁻¹ : GL ι K) : Matrix ι ι K)) * (A : Matrix ι ι K) =
      (((A⁻¹ : GL ι K) : Matrix ι ι K) * (A : Matrix ι ι K)) * M *
        (((A⁻¹ : GL ι K) : Matrix ι ι K) * (A : Matrix ι ι K)) := by
        simp only [Matrix.mul_assoc]
    _ = M := by rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_one]

theorem midBlockShape_conj_of_form {hk : 2 ≤ k} {β : MulAut (SpecialLinearGroup (StdMid hk) K)}
    {A : GL (StdMid hk) K} {σ : K ≃+* K}
    (hform : (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A : Matrix (StdMid hk) (StdMid hk) K) * (g : Matrix (StdMid hk) (StdMid hk) K).map σ *
          ((A⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)) ∨
      (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A : Matrix (StdMid hk) (StdMid hk) K) * ((g⁻¹ : SpecialLinearGroup (StdMid hk) K) :
          Matrix (StdMid hk) (StdMid hk) K).transpose.map σ *
            ((A⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)))
    {g : SpecialLinearGroup (StdMid hk) K} (hg : MidBlockShape hk (g : Matrix (StdMid hk)
      (StdMid hk) K)) :
    MidBlockShape hk (((A⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K) *
      (β g : Matrix (StdMid hk) (StdMid hk) K) * (A : Matrix (StdMid hk) (StdMid hk) K)) := by
  rcases hform with h | h
  · rw [h, inv_mul_conj_mul_GL]
    exact hg.map σ
  · rw [h, inv_mul_conj_mul_GL]
    refine (MidBlockShape.of_mul_eq_one hg ?_ ?_).transpose.map σ
    · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem midTorusShape_conj_of_form {hk : 2 ≤ k} {β : MulAut (SpecialLinearGroup (StdMid hk) K)}
    {A : GL (StdMid hk) K} {σ : K ≃+* K}
    (hform : (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A : Matrix (StdMid hk) (StdMid hk) K) * (g : Matrix (StdMid hk) (StdMid hk) K).map σ *
          ((A⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)) ∨
      (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A : Matrix (StdMid hk) (StdMid hk) K) * ((g⁻¹ : SpecialLinearGroup (StdMid hk) K) :
          Matrix (StdMid hk) (StdMid hk) K).transpose.map σ *
            ((A⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)))
    {g : SpecialLinearGroup (StdMid hk) K} {l : K} (hl : l ≠ 1)
    (hg : MidTorusShape hk l (g : Matrix (StdMid hk) (StdMid hk) K)) :
    ∃ μ : K, μ ≠ 1 ∧ MidTorusShape hk μ (((A⁻¹ : GL (StdMid hk) K) :
      Matrix (StdMid hk) (StdMid hk) K) * (β g : Matrix (StdMid hk) (StdMid hk) K) *
        (A : Matrix (StdMid hk) (StdMid hk) K)) := by
  rcases hform with h | h
  · refine ⟨σ l, fun h1 => hl (σ.injective (h1.trans σ.map_one.symm)), ?_⟩
    rw [h, inv_mul_conj_mul_GL]
    exact hg.map σ
  · refine ⟨σ l⁻¹, fun h1 => hl (inv_eq_one.mp (σ.injective (h1.trans σ.map_one.symm))), ?_⟩
    rw [h, inv_mul_conj_mul_GL]
    refine (MidTorusShape.of_mul_eq_one hg ?_ ?_).transpose.map σ
    · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem blk_one_apply_of_not_blockOne (X : Matrix (Fin 2) (Fin 2) K) {x y : Fin (2 + k)}
    (hxy : ¬ (IsBlockOne k x ∧ IsBlockOne k y)) :
    blk X (1 : Matrix (Fin k) (Fin k) K) x y = (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y := by
  have hB : ∀ i : Fin 2, IsBlockOne k (finSumFinEquiv (Sum.inl i)) := by
    intro i
    fin_cases i
    exacts [Or.inl rfl, Or.inr rfl]
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
  rw [blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rcases x with x | x <;> rcases y with y | y
  · exact absurd ⟨hB x, hB y⟩ hxy
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, one_apply]
    simp

theorem midBlockShape_blkSL₁ (hk : 2 ≤ k) (X : SpecialLinearGroup (Fin 2) K) :
    MidBlockShape hk (stdRhoMat hk ((blkSL₁ X : SpecialLinearGroup (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K)) := by
  intro a b hab
  rw [stdRhoMat, submatrix_apply, coe_blkSL₁, blk_one_apply_of_not_blockOne _ hab, one_apply,
    one_apply]
  simp only [Subtype.ext_iff]

end Shapes

theorem exists_ne_zero_ne_one_of_four {K : Type} [Field K] (h4 : ∃ s : Finset K, s.card = 4) :
    ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := h4
  by_contra hcon
  push Not at hcon
  have hsub : s ⊆ {0, 1} := fun x _ => by
    by_cases h0 : x = 0
    · simp [h0]
    · simp [hcon x h0]
  have := (Finset.card_le_card hsub).trans Finset.card_le_two
  omega

section ConjHelpers

variable {K : Type} [Field K]

theorem slConjugation_toGL_eq_mul_mul_inv {n : ℕ} (u g : SpecialLinearGroup (Fin n) K) :
    CatalogueBHigherLinearAction.slConjugation n K (SpecialLinearGroup.toGL u) g = u * g * u⁻¹ := by
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← map_inv]
  rfl

theorem proj_slConjugation_mul_conj {n : ℕ} (H₁ : GL (Fin n) K)
    (u g : SpecialLinearGroup (Fin n) K) :
    proj n K (CatalogueBHigherLinearAction.slConjugation n K H₁ (u * g * u⁻¹)) =
      conjAut n K (H₁ * SpecialLinearGroup.toGL u) (proj n K g) := by
  rw [map_mul (conjAut n K), MulAut.mul_apply, conjAut_proj, conjAut_proj,
    slConjugation_toGL_eq_mul_mul_inv]

end ConjHelpers

theorem commutator_subgroupOf_eq_self {G : Type*} [Group G] {Y X : Subgroup G} (hYX : Y ≤ X)
    (hY : ⁅Y, Y⁆ = Y) : ⁅Y.subgroupOf X, Y.subgroupOf X⁆ = Y.subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYX, hY]

section Levi

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {k : ℕ}

omit [Finite G] [Finite K] [CharP K 2] in
theorem proj_stdT_mem_barL (hk : 2 ≤ k) :
    proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1) ∈ barL K k := by
  refine ⟨trn ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff]) 1, ?_⟩
  simp only [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  rw [coe_blkSL₂, coe_trn, coe_trSL, ← one_add_smul_stdE hk, one_smul, stdE_eq_single]
  rfl

omit [Finite G] [Finite K] [CharP K 2] in
theorem leviW_le_perfectCore (hk : 2 ≤ k) {θ : ↥A →* projectiveSL (2 + k) K}
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4)
    {p : G} (hpA : p ∈ A)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1)) :
    leviW θ ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) := by
  refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf levLift_le ?_)
    (commutator_levLift hker hθ (commutator_barW h4))
  refine levLift_le_centralizer hker hpA fun s hs => ?_
  rw [hθp]
  exact (barW_commute_barL hs (proj_stdT_mem_barL hk)).symm

omit [Finite G] [Finite K] [CharP K 2] in
theorem exists_lam_eq_blkSL₁ (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K)
    {θ : ↥A →* projectiveSL (2 + k) K} {p : G}
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    {x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))} (hx : (x : G) ∈ leviW θ) :
    ∃ X₂ : SpecialLinearGroup (Fin 2) K, lam x = blkSL₁ X₂ := by
  obtain ⟨X₂, hX₂⟩ := theta_mem_of_mem_levLift hx
  refine ⟨X₂, proj_injOn_stdX hk (hlamX x) (perfectCore_stdCen_le_stdX hk
    (blkSL₁_range_le_perfectCore hk h4 ⟨X₂, rfl⟩)) ?_⟩
  rw [hlam]
  exact hX₂.symm

omit [Finite K] in
theorem center_leviW_eq_bot [Finite K] (hk : 2 ≤ k) {m : ℕ} (hm2 : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) {θ : ↥A →* projectiveSL (2 + k) K}
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (hodd : Odd (Nat.card (center ↥A)))
    (h4 : ∃ s : Finset K, s.card = 4) : center ↥(leviW θ) = ⊥ := by
  obtain ⟨eY⟩ := nonempty_levLift_equiv_SL2 hker hθ hodd hm2 hK (commutator_barW h4)
    (barWEquiv K k (by omega))
  change center ↥(levLift θ (barW K k)) = ⊥
  rw [eq_bot_iff]
  intro z hz
  have h1 : eY z ∈ center (SpecialLinearGroup (Fin 2) K) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := eY.surjective g
    rw [← map_mul eY, ← map_mul eY, mem_center_iff.mp hz y]
  rw [center_SL2_eq_bot', mem_bot] at h1
  exact (mem_bot).mpr (eY.injective (h1.trans eY.map_one.symm))

theorem card_map_theta_rightConjugate_leviW (hk : 2 ≤ k) {m : ℕ} (hm2 : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) {θ : ↥A →* projectiveSL (2 + k) K}
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ) (hodd : Odd (Nat.card (center ↥A)))
    (h4 : ∃ s : Finset K, s.card = 4) {c : G}
    (hYA : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤ A) :
    Nat.card ↥(((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ) =
      Nat.card ↥(barW K k) := by
  set Yc := AschbacherTightEmbedding.rightConjugate (leviW θ) c
  set H := Yc.subgroupOf A
  have hZ := center_leviW_eq_bot hk hm2 hK hker hθ hodd h4
  have hinj : Function.Injective (θ.comp H.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hz
    have hzc : (z : ↥A) ∈ center ↥A := by rw [← hker]; exact hz
    have hzY : ((z : ↥A) : G) ∈ Yc := z.2
    rw [AschbacherTightEmbedding.mem_rightConjugate_iff] at hzY
    have hcen : (⟨c * z * c⁻¹, hzY⟩ : ↥(leviW θ)) ∈ center ↥(leviW θ) := by
      rw [mem_center_iff]
      intro y
      have hy : c⁻¹ * y * c ∈ A := hYA ((AschbacherTightEmbedding.mem_rightConjugate_iff _ _ _).2
        (by simp [mul_assoc]))
      have e := congrArg Subtype.val (mem_center_iff.mp hzc ⟨c⁻¹ * y * c, hy⟩)
      apply Subtype.ext
      change (y : G) * (c * z * c⁻¹) = c * z * c⁻¹ * y
      change c⁻¹ * y * c * ((z : ↥A) : G) = ((z : ↥A) : G) * (c⁻¹ * y * c) at e
      calc (y : G) * (c * z * c⁻¹) = c * (c⁻¹ * y * c * z) * c⁻¹ := by group
        _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [e]
        _ = c * z * c⁻¹ * y := by group
    rw [hZ, mem_bot] at hcen
    have h1 : c * ((z : ↥A) : G) * c⁻¹ = 1 := congrArg Subtype.val hcen
    have h2 : ((z : ↥A) : G) = 1 := by
      calc ((z : ↥A) : G) = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    exact (mem_bot).mpr (Subtype.ext (Subtype.ext h2))
  have hrange : (θ.comp H.subtype).range = H.map θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨eY⟩ := nonempty_levLift_equiv_SL2 hker hθ hodd hm2 hK (commutator_barW h4)
    (barWEquiv K k (by omega))
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (subgroupOfEquivOfLe hYA).toEquiv,
    show Yc = (leviW θ).map (MulAut.conj c⁻¹).toMonoidHom from rfl,
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
  change Nat.card ↥(levLift θ (barW K k)) = Nat.card ↥(barW K k)
  rw [Nat.card_congr eY.toEquiv, Nat.card_congr (barWEquiv K k (by omega)).toEquiv]

end Levi

section Core

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {k : ℕ}

omit [Finite G] [Finite K] [CharP K 2] in
theorem stdRhoMat_slConj_lam_eq (hk : 2 ≤ k) {p : G}
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))}
    {β : MulAut (SpecialLinearGroup (StdMid hk) K)} (hβ : ∀ x, β (ψ x) = ψ (γ x))
    (A' : GL (StdMid hk) K) (x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) :
    stdRhoMat hk ((CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A')⁻¹
      (lam (γ x)) : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      ((A'⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K) *
        (β (ψ x) : Matrix (StdMid hk) (StdMid hk) K) * (A' : Matrix (StdMid hk) (StdMid hk) K) := by
  rw [stdRhoMat_slConjugation_midGL hk A' (hlamX _), hβ, hψ]

omit [Finite G] [Finite K] [CharP K 2] in
theorem blockOneShape_slConj_lam (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K)
    {θ : ↥A →* projectiveSL (2 + k) K} {p : G}
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))}
    {β : MulAut (SpecialLinearGroup (StdMid hk) K)} (hβ : ∀ x, β (ψ x) = ψ (γ x))
    {A' : GL (StdMid hk) K} {σ : K ≃+* K}
    (hform : (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A' : Matrix (StdMid hk) (StdMid hk) K) * (g : Matrix (StdMid hk) (StdMid hk) K).map σ *
          ((A'⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)) ∨
      (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A' : Matrix (StdMid hk) (StdMid hk) K) * ((g⁻¹ : SpecialLinearGroup (StdMid hk) K) :
          Matrix (StdMid hk) (StdMid hk) K).transpose.map σ *
            ((A'⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)))
    {x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))} (hx : (x : G) ∈ leviW θ) :
    BlockOneShape hk ((CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A')⁻¹
      (lam (γ x)) : SpecialLinearGroup (Fin (2 + k)) K) :
        Matrix (Fin (2 + k)) (Fin (2 + k)) K) := by
  rw [blockOneShape_iff_mid, stdRhoMat_slConj_lam_eq hk hlamX hψ hβ]
  refine midBlockShape_conj_of_form hform ?_
  obtain ⟨X₂, hX₂⟩ := exists_lam_eq_blkSL₁ hk h4 hlamX hlam hx
  rw [hψ, hX₂]
  exact midBlockShape_blkSL₁ hk X₂

omit [Finite G] [Finite K] [CharP K 2] in
theorem torusOneShape_slConj_lam (hk : 2 ≤ k) (hk3 : 3 ≤ k) {p : G}
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))}
    {β : MulAut (SpecialLinearGroup (StdMid hk) K)} (hβ : ∀ x, β (ψ x) = ψ (γ x))
    {A' : GL (StdMid hk) K} {σ : K ≃+* K}
    (hform : (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A' : Matrix (StdMid hk) (StdMid hk) K) * (g : Matrix (StdMid hk) (StdMid hk) K).map σ *
          ((A'⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)) ∨
      (∀ g : SpecialLinearGroup (StdMid hk) K, (β g : Matrix (StdMid hk) (StdMid hk) K) =
        (A' : Matrix (StdMid hk) (StdMid hk) K) * ((g⁻¹ : SpecialLinearGroup (StdMid hk) K) :
          Matrix (StdMid hk) (StdMid hk) K).transpose.map σ *
            ((A'⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K)))
    {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1) {x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))}
    (hx : lam x = linTorus K hk3 hl0) :
    ∃ μ : K, μ ≠ 1 ∧ TorusOneShape hk μ ((CatalogueBHigherLinearAction.slConjugation (2 + k) K
      (midGL K hk A')⁻¹ (lam (γ x)) : SpecialLinearGroup (Fin (2 + k)) K) :
        Matrix (Fin (2 + k)) (Fin (2 + k)) K) := by
  have hg : MidTorusShape hk l (ψ x : Matrix (StdMid hk) (StdMid hk) K) := by
    rw [hψ, hx]
    exact midTorusShape_linTorus hk3 hl0
  obtain ⟨μ, hμ, hs⟩ := midTorusShape_conj_of_form hform hl1 hg
  refine ⟨μ, hμ, ?_⟩
  rw [torusOneShape_iff_mid, stdRhoMat_slConj_lam_eq hk hlamX hψ hβ]
  exact hs

omit [Finite G] [Finite K] [CharP K 2] in
theorem commute_of_lam_eq_linTorus (hk : 2 ≤ k) (hk3 : 3 ≤ k) (h4 : 4 ≤ Nat.card K)
    (hq4 : ∃ s : Finset K, s.card = 4) {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) {p : G}
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    {l : K} (hl0 : l ≠ 0) {x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))}
    (hx : lam x = linTorus K hk3 hl0) (hYX : leviW θ ≤ perfectCore (A ⊓ centralizer ({p} : Set G)))
    {y : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))} (hy : (y : G) ∈ leviW θ) :
    x * y = y * x := by
  have hc := mem_centralizer_of_theta_commute hker (show leviW θ ≤ A from levLift_le)
    (show ⁅leviW θ, leviW θ⁆ = leviW θ from commutator_levLift hker hθ (commutator_barW hq4))
    (a := Subgroup.inclusion (perfectCore_inf_le A p) x) fun z hz => by
      obtain ⟨X₂, hX₂⟩ := exists_lam_eq_blkSL₁ hk h4 hlamX hlam (x := ⟨z, hYX hz⟩) hz
      have e1 : θ (Subgroup.inclusion (perfectCore_inf_le A p) x) =
          proj (2 + k) K (linTorus K hk3 hl0) := by rw [← hlam, hx]
      have e2 : θ ⟨z, (show leviW θ ≤ A from levLift_le) hz⟩ = proj (2 + k) K (blkSL₁ X₂) := by
        rw [← hX₂, hlam]
        rfl
      rw [e1, e2, ← map_mul, ← map_mul, linTorus_commute_blkSL₁]
  exact Subtype.ext (mem_centralizer_iff.mp hc y hy).symm

theorem exists_map_theta_rightConjugate_le (hk : 2 ≤ k) (hk3 : 3 ≤ k) (h4 : 4 ≤ Nat.card K)
    (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {θ : ↥A →* projectiveSL (2 + k) K} (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1)) {c : G}
    (hXc : AschbacherTightEmbedding.rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G)))
      c = perfectCore (A ⊓ centralizer ({p} : Set G))) :
    ∃ H : GL (Fin (2 + k)) K,
      ((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ ≤
        (barW K k).map (conjAut (2 + k) K H).toMonoidHom := by
  obtain ⟨lam, ψ, hlamX, hlam, hψ⟩ := exists_linPsi hk hθ hker hodd hpA hp2 hθp
  have hYX := leviW_le_perfectCore hk hker hθ hq4 hpA hθp
  obtain ⟨γ, hγ⟩ : ∃ γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G))),
      ∀ x, ((γ x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) : G) = c⁻¹ * x * c :=
    ⟨((MulAut.conj c⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr hXc), fun x => by
      change c⁻¹ * (x : G) * c⁻¹⁻¹ = _
      rw [inv_inv]⟩
  obtain ⟨β, hβ⟩ := exists_mulAut_linPsi hk h4 hq4 hm hK hθ hker hodd hpA hp2 hθp hlamX hlam hψ γ
  obtain ⟨A', σ, hform⟩ :=
    exists_matrix_form_of_mulAut_slIndex (by rw [card_stdMid]; exact hk3) β
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →*
      SpecialLinearGroup (Fin (2 + k)) K, ∀ x, Φ x =
        CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A')⁻¹ (lam (γ x)) :=
    ⟨(CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A')⁻¹).toMonoidHom.comp
      (lam.comp γ.toMonoidHom), fun x => rfl⟩
  have hYperf : ⁅leviW θ, leviW θ⁆ = leviW θ := commutator_levLift hker hθ (commutator_barW hq4)
  have hW₃perf : ⁅((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Φ,
      ((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Φ⁆ =
      ((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Φ := by
    rw [← map_commutator, commutator_subgroupOf_eq_self hYX hYperf]
  have hW₃X : ((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Φ ≤
      stdX K hk := by
    rintro _ ⟨y, -, rfl⟩
    rw [hΦ]
    exact slConjugation_midGL_mem_stdX hk A' (hlamX _)
  have hW₃s : ∀ g ∈ ((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Φ,
      BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hΦ]
    exact blockOneShape_slConj_lam hk h4 hlamX hlam hψ hβ hform hy
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one_of_four hq4
  obtain ⟨xz, hxz⟩ := exists_lam_eq_of_mem_perfectCore hk hθ hker hodd hpA hp2 hθp hlamX hlam
    (linTorus_mem_perfectCore hk3 hq4 hl0)
  obtain ⟨μ, hμ, hzs⟩ := torusOneShape_slConj_lam hk hk3 hlamX hψ hβ hform hl0 hl1 hxz
  rw [← hΦ] at hzs
  have hzX : Φ xz ∈ stdX K hk := by
    rw [hΦ]
    exact slConjugation_midGL_mem_stdX hk A' (hlamX _)
  have hzW : ∀ g ∈ ((leviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Φ,
      Φ xz * g = g * Φ xz := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul,
      commute_of_lam_eq_linTorus hk hk3 h4 hq4 hθ hker hlamX hlam hl0 hxz hYX hy]
  obtain ⟨u₀, hu₀⟩ := exists_conj_mem_range_blkSL₁ hk hW₃perf hW₃X hW₃s hzX hμ hzs hzW
  refine ⟨midGL K hk A' * SpecialLinearGroup.toGL u₀, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hy : c * (a : G) * c⁻¹ ∈ leviW θ :=
    (AschbacherTightEmbedding.mem_rightConjugate_iff _ _ _).mp ha
  have hθa : θ a = proj (2 + k) K (lam (γ ⟨c * a * c⁻¹, hYX hy⟩)) := by
    rw [hlam]
    congr 1
    apply Subtype.ext
    change (a : G) = ((γ ⟨c * a * c⁻¹, hYX hy⟩ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))))
      : G)
    rw [hγ]
    change (a : G) = c⁻¹ * (c * a * c⁻¹) * c
    group
  obtain ⟨X₃, hX₃⟩ := hu₀ (Φ ⟨c * a * c⁻¹, hYX hy⟩) ⟨⟨c * a * c⁻¹, hYX hy⟩, hy, rfl⟩
  have h1 : Φ ⟨c * a * c⁻¹, hYX hy⟩ = u₀ * blkSL₁ X₃ * u₀⁻¹ := by
    rw [hX₃]
    group
  have h2 : lam (γ ⟨c * a * c⁻¹, hYX hy⟩) =
      CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A')
        (u₀ * blkSL₁ X₃ * u₀⁻¹) := by
    rw [← h1, hΦ, map_inv, MulAut.apply_inv_self]
  refine ⟨proj (2 + k) K (blkSL₁ X₃), ⟨X₃, rfl⟩, ?_⟩
  rw [hθa, h2, proj_slConjugation_mul_conj]
  rfl

theorem rigidCore_leviW_of_three_le (hk : 2 ≤ k) (hk3 : 3 ≤ k) (h4 : 4 ≤ Nat.card K)
    (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm2 : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    {θ : ↥A →* projectiveSL (2 + k) K} (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1)) :
    RigidCore A p (leviW θ) := by
  intro c hXc _ _
  obtain ⟨H, hle⟩ := exists_map_theta_rightConjugate_le hk hk3 h4 hq4 (by omega) hK hθ hker hodd
    hpA hp2 hθp hXc
  have hYX := leviW_le_perfectCore hk hker hθ hq4 hpA hθp
  have hYcA : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤ A := by
    have h1 : AschbacherTightEmbedding.rightConjugate (leviW θ) c ≤
        AschbacherTightEmbedding.rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) c :=
      Subgroup.map_mono hYX
    rw [hXc] at h1
    exact h1.trans (perfectCore_inf_le A p)
  have hYperf : ⁅leviW θ, leviW θ⁆ = leviW θ := commutator_levLift hker hθ (commutator_barW hq4)
  have hYcperf : ⁅AschbacherTightEmbedding.rightConjugate (leviW θ) c,
      AschbacherTightEmbedding.rightConjugate (leviW θ) c⁆ =
        AschbacherTightEmbedding.rightConjugate (leviW θ) c := by
    unfold AschbacherTightEmbedding.rightConjugate
    rw [← map_commutator, hYperf]
  have heq : ((AschbacherTightEmbedding.rightConjugate (leviW θ) c).subgroupOf A).map θ =
      (barW K k).map (conjAut (2 + k) K H).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (f := (conjAut (2 + k) K H).toMonoidHom)
        (conjAut (2 + k) K H).injective,
      card_map_theta_rightConjugate_leviW hk hm2 hK hker hθ hodd hq4 hYcA]
  refine noNormalTwo_inf_centralizer_of_quot hθ hker hodd hYcA hYcperf ?_
  rw [heq, ← centralizer_map_mulAut]
  exact noNormalTwo_map_mulAut (noNormalTwo_centralizer_barW hk hq4 (by omega) hK) _

end Core

end CFSG.ComponentClassification.RankTwoClassical
