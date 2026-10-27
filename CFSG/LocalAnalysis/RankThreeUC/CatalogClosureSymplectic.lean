module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSympMain
import CFSG.LieType.Classical.SteinbergBLSymplectic
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

namespace SpClosure

variable {n : ℕ} {K : Type} [Field K]

abbrev spMat (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 1 (-1) 0

@[expose] noncomputable def spB (n : ℕ) (K : Type) [Field K] :
    LinearMap.BilinForm K (Fin n ⊕ Fin n → K) :=
  Matrix.toBilin' (spMat n K)

theorem spB_apply (x y : Fin n ⊕ Fin n → K) : spB n K x y = x ⬝ᵥ (spMat n K *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem spMat_mul_self : spMat n K * spMat n K = -1 := by
  simp [spMat, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem dotProduct_spMat_mulVec (u v : Fin n ⊕ Fin n → K) :
    u ⬝ᵥ (spMat n K *ᵥ v) = (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) - (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inl) := by
  simp [spMat, dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, neg_mulVec, sub_eq_add_neg]

theorem spB_isAlt : (spB n K).IsAlt := fun x => by
  rw [spB_apply, dotProduct_spMat_mulVec, dotProduct_comm (x ∘ Sum.inr), sub_self]

theorem spB_nondegenerate : (spB n K).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  have h : spMat n K * (-spMat n K) = 1 := by rw [Matrix.mul_neg, spMat_mul_self, neg_neg]
  exact (Matrix.isUnit_det_of_right_inverse h).ne_zero

@[expose] noncomputable def spB₀ (n : ℕ) (K : Type) [Field K] :
    LinearMap.BilinForm K (Fin n ⊕ Fin n → K) :=
  Matrix.toBilin' (fromBlocks 0 1 0 0)

theorem dotProduct_spU_mulVec (u v : Fin n ⊕ Fin n → K) :
    u ⬝ᵥ ((fromBlocks 0 1 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) =
      (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec]

theorem spB₀_add_swap [CharP K 2] (x y : Fin n ⊕ Fin n → K) :
    spB₀ n K x y + spB₀ n K y x = spB n K x y := by
  simp only [spB₀, spB, Matrix.toBilin'_apply', dotProduct_spU_mulVec, dotProduct_spMat_mulVec]
  rw [CharTwo.sub_eq_add, dotProduct_comm (y ∘ Sum.inl)]

@[expose] noncomputable def toLinEquiv (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type)
    [Field K] : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  (Matrix.GeneralLinearGroup.toLin).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

theorem toLinEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K) (x : ι → K) :
    toLinEquiv ι K g x = (g : Matrix ι ι K) *ᵥ x := rfl

theorem mem_statedSp_iff (g : GL (Fin n ⊕ Fin n) K) :
    g ∈ StatedSp n K ↔
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * spMat n K *
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = spMat n K :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem mem_statedSp_iff_isom (g : GL (Fin n ⊕ Fin n) K) :
    g ∈ StatedSp n K ↔ toLinEquiv _ K g ∈ isom (spB n K) := by
  rw [mem_statedSp_iff, mem_isom]
  constructor
  · intro h x y
    rw [toLinEquiv_apply, toLinEquiv_apply, spB_apply, spB_apply, mulVec_mulVec,
      dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, h,
      ← dotProduct_mulVec]
  · intro h
    refine ext_iff_mulVec.mpr fun v => dotProduct_eq_iff.mp fun u => ?_
    rw [dotProduct_comm _ u, dotProduct_comm _ u, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose]
    have := h u v
    rw [toLinEquiv_apply, toLinEquiv_apply, spB_apply, spB_apply] at this
    exact this

noncomputable def spIsom (n : ℕ) (K : Type) [Field K] : StatedSp n K ≃* isom (spB n K) :=
  ((toLinEquiv (Fin n ⊕ Fin n) K).subgroupMap (StatedSp n K)).trans
    (MulEquiv.subgroupCongr (by
      ext g'
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact (mem_statedSp_iff_isom g).1 hg
      · intro hg'
        refine ⟨(toLinEquiv (Fin n ⊕ Fin n) K).symm g', (mem_statedSp_iff_isom _).2 ?_, by simp⟩
        simpa using hg'))

theorem scalars_subgroupOf_eq_bot [CharP K 2] (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K := by
    rw [hc]; exact g.2
  have hsq : c ^ 2 = 1 := (CFSG.LieType.Classical.scalar_mem_statedSp_iff hn c).1 hmem
  have hc1 : c = 1 := by
    apply Units.ext
    have h2 : (c : K) ^ 2 = 1 := by simpa using congrArg Units.val hsq
    have h1 : ((c : K) - 1) ^ 2 = 0 := by
      linear_combination h2 + (1 - (c : K)) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have := (pow_eq_zero_iff two_ne_zero).mp h1
    simpa [sub_eq_zero] using this
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

noncomputable def projEquiv [CharP K 2] (hn : 1 ≤ n) :
    StatedProj (StatedSp n K) ≃* StatedSp n K :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_subgroupOf_eq_bot hn)).trans
    QuotientGroup.quotientBot

noncomputable def spModelEquiv [CharP K 2] (hn : 1 ≤ n) :
    StatedProj (StatedSp n K) ≃* isom (spB n K) :=
  (projEquiv hn).trans (spIsom n K)


end SpClosure

theorem not_rankThreeUC_of_closure_top {G : Type} [Group G] [Finite G] (hS : Standing G)
    (h : ∀ E S₀ : Subgroup G, Odd (Nat.card E) → S₀ ≠ ⊥ → IsPGroup 2 S₀ →
      E ≤ normalizer (S₀ : Set G) → twoLocalClosure E = ⊤) : ¬ rankThreeUC G := by
  intro hUC
  obtain ⟨p, hp⟩ := sigmaA_nonempty_of_evenRank_three hS.rank
  have hprime : p.Prime := sigmaA_prime p hp
  have hp2 : p ≠ 2 := (sigmaA_odd p hp)
  have h3 : rankThreeLocalRank p G = 3 := sigmaA_local_rank_three hS.rank p hp
  obtain ⟨H, hH2, hHr⟩ := rankThreeLocalRank_attained p (by rw [h3]; norm_num)
  obtain ⟨E, hEH, hEab, hEcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained p hprime H
  rw [hHr, h3] at hEcard
  obtain ⟨S0, hS0bot, hS02, hHeq⟩ := hH2
  have hEp : IsPGroup p E := fun x => ⟨1, by
    have := hEab.2 x x.2
    apply Subtype.ext
    simpa using this⟩
  have hE2 : 2 ≤ CFSG.Open.pRank p E := by
    have := CFSG.SectionRank.le_pRank hprime.one_lt (le_refl E) hEab hEcard
    omega
  have hEodd : Odd (Nat.card E) := by
    rw [hEcard]
    exact (hprime.odd_of_ne_two hp2).pow
  have hEN : E ≤ normalizer (S0 : Set G) := hHeq ▸ hEH
  exact twoLocalClosure_ne_top hS hUC hp hEp hE2 (h E S0 hEodd hS0bot hS02 hEN)

theorem twoLocalClosure_eq_top_of_equiv {G H : Type} [Group G] [Group H] (Φ : G ≃* H)
    (E : Subgroup G) (h : twoLocalClosure (E.map Φ.toMonoidHom) = ⊤) :
    twoLocalClosure E = ⊤ := by
  have hle := map_twoLocalClosure_le Φ.symm (E.map Φ.toMonoidHom)
  have hE : (E.map Φ.toMonoidHom).map Φ.symm.toMonoidHom = E := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨Φ x, ⟨x, hx, rfl⟩, by simp⟩
  rw [hE, h, Subgroup.map_top, MonoidHom.range_eq_top.2 Φ.symm.surjective] at hle
  exact top_le_iff.mp hle

theorem not_rankThreeUC_of_PSp {G : Type} [Group G] [Finite G] (hS : Standing G) {n : ℕ}
    (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : G ≃* StatedProj (StatedSp n K)) : ¬ rankThreeUC G := by
  refine not_rankThreeUC_of_closure_top hS (fun E S₀ hE hS₀ hS₀2 hEN => ?_)
  let Φ : G ≃* SpClosure.isom (SpClosure.spB n K) := e.trans (SpClosure.spModelEquiv hn)
  have : IsSimpleGroup G := hS.simple
  have : IsSimpleGroup (SpClosure.isom (SpClosure.spB n K)) := Φ.symm.isSimpleGroup
  refine twoLocalClosure_eq_top_of_equiv Φ E ?_
  refine SpClosure.twoLocalClosure_eq_top_isom SpClosure.spB_isAlt SpClosure.spB_nondegenerate
    (SpClosure.spB₀ n K) SpClosure.spB₀_add_swap
    (E.map Φ.toMonoidHom) (S₀.map Φ.toMonoidHom) ?_ ?_ (hS₀2.map Φ.toMonoidHom) ?_
  · rwa [Subgroup.card_map_of_injective Φ.injective]
  · intro hbot
    exact hS₀ ((Subgroup.map_eq_bot_iff_of_injective S₀ Φ.injective).1 hbot)
  · exact (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map Φ.toMonoidHom)

theorem not_rankThreeUC_of_lift {G A : Type} [Group G] [Finite G] [Group A] [Finite A]
    (hS : Standing G) (φ : A →* G) (hφ : Function.Surjective φ)
    (hc : φ.ker ≤ Subgroup.center A) (hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1)
    (h : ∀ E P : Subgroup A, Odd (Nat.card E) → P ≠ ⊥ → IsPGroup 2 P →
      E ≤ normalizer (P : Set A) → twoLocalClosure E = ⊤) : ¬ rankThreeUC G := by
  refine not_rankThreeUC_of_closure_top hS (fun E S₀ hE hS₀ hS₀2 hEN => ?_)
  obtain ⟨P, hP, hP2, hEP⟩ := exists_normalized_two_subgroup φ hφ hc hS₀ hS₀2 hEN
  have hcl := h (E.comap φ) P (odd_card_comap φ hker hE) hP hP2 hEP
  have hle := map_twoLocalClosure_le_of_ker φ hker (E.comap φ)
  rw [hcl, Subgroup.map_top, MonoidHom.range_eq_top.2 hφ,
    Subgroup.map_comap_eq_self_of_surjective hφ] at hle
  exact top_le_iff.mp hle

theorem not_rankThreeUC_of_lift_gen {G A : Type} [Group G] [Finite G] [Group A] [Finite A]
    (hS : Standing G) (φ : A →* G) (hφ : Function.Surjective φ)
    (hc : φ.ker ≤ Subgroup.center A) (hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1)
    (𝒯 : Set A) (hconj : ∀ g t, t ∈ 𝒯 → g * t * g⁻¹ ∈ 𝒯) (hnt : ∃ t ∈ 𝒯, φ t ≠ 1)
    (h : ∀ E P : Subgroup A, Odd (Nat.card E) → P ≠ ⊥ → IsPGroup 2 P →
      E ≤ normalizer (P : Set A) → 𝒯 ⊆ (twoLocalClosure E : Set A)) : ¬ rankThreeUC G := by
  refine not_rankThreeUC_of_closure_top hS (fun E S₀ hE hS₀ hS₀2 hEN => ?_)
  obtain ⟨P, hP, hP2, hEP⟩ := exists_normalized_two_subgroup φ hφ hc hS₀ hS₀2 hEN
  have hT := h (E.comap φ) P (odd_card_comap φ hker hE) hP hP2 hEP
  have hle := map_twoLocalClosure_le_of_ker φ hker (E.comap φ)
  rw [Subgroup.map_comap_eq_self_of_surjective hφ] at hle
  have hsimple : IsSimpleGroup G := hS.simple
  set N := Subgroup.normalClosure (φ '' 𝒯) with hN
  obtain ⟨t, ht, ht1⟩ := hnt
  have hNne : N ≠ ⊥ := by
    intro hbot
    have : φ t ∈ N := Subgroup.subset_normalClosure ⟨t, ht, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ht1 this
  have hNtop : N = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_left hNne
  have hNle : N ≤ twoLocalClosure E := by
    rw [hN, Subgroup.normalClosure, Subgroup.closure_le]
    intro g hg
    rw [Group.mem_conjugatesOfSet_iff] at hg
    obtain ⟨b, ⟨t', ht', rfl⟩, hbg⟩ := hg
    rw [isConj_iff] at hbg
    obtain ⟨d, rfl⟩ := hbg
    obtain ⟨a, rfl⟩ := hφ d
    have : φ a * φ t' * (φ a)⁻¹ = φ (a * t' * a⁻¹) := by simp [map_mul, map_inv]
    rw [this]
    exact hle ⟨a * t' * a⁻¹, hT (hconj a t' ht'), rfl⟩
  exact top_le_iff.mp (hNtop ▸ hNle)

section Scalars

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem statedScalars_subgroupOf_le_center (A : Subgroup (GL ι K)) :
    (StatedScalars ι K).subgroupOf A ≤ Subgroup.center A :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

theorem eq_one_of_sq_eq_one_of_mem_statedScalars [CharP K 2] (A : Subgroup (GL ι K)) {z : A}
    (hz : z ∈ (StatedScalars ι K).subgroupOf A) (h2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨c, hc⟩ := hz
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i
    exact isEmptyElim i
  · have h2' : (Matrix.GeneralLinearGroup.scalar ι c) ^ 2 = 1 := by
      rw [hc]
      exact congrArg Subtype.val h2
    have hsq : (c : K) ^ 2 = 1 := by
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i₀ i₀) h2'
      simpa [← map_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] using this
    have hc1 : c = 1 := by
      apply Units.ext
      have h1 : ((c : K) - 1) ^ 2 = 0 := by
        linear_combination hsq + (1 - (c : K)) * (CharTwo.two_eq_zero : (2 : K) = 0)
      have := (pow_eq_zero_iff two_ne_zero).mp h1
      simpa [sub_eq_zero] using this
    apply Subtype.ext
    have hz1 : (z : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c := hc.symm
    show (z : GL ι K) = 1
    rw [hz1, hc1, map_one]

theorem not_rankThreeUC_of_proj {G : Type} [Group G] [Finite G] (hS : Standing G)
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2]
    (A : Subgroup (GL ι K)) [Finite A] (e : G ≃* StatedProj A)
    (h : ∀ E P : Subgroup A, Odd (Nat.card E) → P ≠ ⊥ → IsPGroup 2 P →
      E ≤ normalizer (P : Set A) → twoLocalClosure E = ⊤) : ¬ rankThreeUC G := by
  let φ : A →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf A))
  have hφ : Function.Surjective φ := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = (StatedScalars ι K).subgroupOf A := by
    ext z
    rw [MonoidHom.mem_ker]
    show e.symm (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff _ e.symm.injective, QuotientGroup.eq_one_iff]
  exact not_rankThreeUC_of_lift hS φ hφ (hker ▸ statedScalars_subgroupOf_le_center A)
    (fun z hz h2 => eq_one_of_sq_eq_one_of_mem_statedScalars A (hker ▸ hz) h2) h

theorem not_rankThreeUC_of_proj_gen {G : Type} [Group G] [Finite G] (hS : Standing G)
    [CharP K 2] (A : Subgroup (GL ι K)) [Finite A] (e : G ≃* StatedProj A) (𝒯 : Set A)
    (hconj : ∀ g t, t ∈ 𝒯 → g * t * g⁻¹ ∈ 𝒯)
    (hnt : ∃ t ∈ 𝒯, t ∉ (StatedScalars ι K).subgroupOf A)
    (h : ∀ E P : Subgroup A, Odd (Nat.card E) → P ≠ ⊥ → IsPGroup 2 P →
      E ≤ normalizer (P : Set A) → 𝒯 ⊆ (twoLocalClosure E : Set A)) : ¬ rankThreeUC G := by
  let φ : A →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf A))
  have hφ : Function.Surjective φ := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = (StatedScalars ι K).subgroupOf A := by
    ext z
    rw [MonoidHom.mem_ker]
    show e.symm (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff _ e.symm.injective, QuotientGroup.eq_one_iff]
  obtain ⟨t, ht, htn⟩ := hnt
  refine not_rankThreeUC_of_lift_gen hS φ hφ (hker ▸ statedScalars_subgroupOf_le_center A)
    (fun z hz h2 => eq_one_of_sq_eq_one_of_mem_statedScalars A (hker ▸ hz) h2) 𝒯 hconj
    ⟨t, ht, fun h1 => htn (hker ▸ h1)⟩ h

end Scalars

end CFSG.LocalAnalysis.RankThreeUC
