module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviNoInv

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate mem_rightConjugate_iff)
open scoped commutatorElement

section Conj

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] {θ : ↥A →* P}

theorem rightConjugate_liftSub {s : G} (hs : s ∈ A) (S : Subgroup P) :
    rightConjugate (liftSub θ S) s =
      liftSub θ (S.map (MulAut.conj (θ ⟨s, hs⟩)⁻¹).toMonoidHom) := by
  ext x
  rw [mem_rightConjugate_iff, mem_liftSub, mem_liftSub]
  have key : ∀ (hxA : x ∈ A) (h' : s * x * s⁻¹ ∈ A),
      θ ⟨s * x * s⁻¹, h'⟩ = θ ⟨s, hs⟩ * θ ⟨x, hxA⟩ * (θ ⟨s, hs⟩)⁻¹ := fun hxA h' => by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  constructor
  · rintro ⟨h', hS⟩
    have hxA : x ∈ A := by
      have h1 := mul_mem (mul_mem (inv_mem hs) h') hs
      rwa [show s⁻¹ * (s * x * s⁻¹) * s = x by group] at h1
    refine ⟨hxA, ?_⟩
    rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv, ← key hxA h']
    exact hS
  · rintro ⟨hxA, hS⟩
    have h' : s * x * s⁻¹ ∈ A := mul_mem (mul_mem hs hxA) (inv_mem hs)
    rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at hS
    exact ⟨h', by rw [key hxA h']; exact hS⟩

theorem rightConjugate_levLift {s : G} (hs : s ∈ A) (S : Subgroup P) :
    rightConjugate (levLift θ S) s =
      levLift θ (S.map (MulAut.conj (θ ⟨s, hs⟩)⁻¹).toMonoidHom) := by
  change (⁅liftSub θ S, liftSub θ S⁆).map (MulAut.conj s⁻¹).toMonoidHom = _
  rw [map_commutator]
  change ⁅rightConjugate (liftSub θ S) s, rightConjugate (liftSub θ S) s⁆ = _
  rw [rightConjugate_liftSub hs]
  rfl

end Conj

section Blocks

variable {K : Type} [Field K] {k : ℕ}

theorem mem_range_blkSL₁ {g : SpecialLinearGroup (Fin (2 + k)) K}
    {X : Matrix (Fin 2) (Fin 2) K} (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk X 1) :
    g ∈ (blkSL₁ : SpecialLinearGroup (Fin 2) K →* _).range := by
  have hX : X.det = 1 := by
    have := g.2
    rw [hg, det_blk, det_one, mul_one] at this
    exact this
  refine ⟨⟨X, hX⟩, Subtype.ext ?_⟩
  change blk X 1 = (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
  exact hg.symm

theorem exists_inv_blk' {g : SpecialLinearGroup (Fin (2 + k)) K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K}
    (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk X D) :
    ∃ (X' : Matrix (Fin 2) (Fin 2) K) (D' : Matrix (Fin k) (Fin k) K),
      ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
        blk X' D' ∧ X * X' = 1 ∧ D * D' = 1 := by
  obtain ⟨A, B, C, E, hgi⟩ := eq_reindex_fromBlocks
    ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
  have h1 : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [hg, hgi, blk, ← map_mul, ← blk_one, blk] at h1
  have e1 := (reindexAlgEquiv K K finSumFinEquiv).injective h1
  rw [fromBlocks_multiply, fromBlocks_inj] at e1
  simp only [Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨hA, hB, hC, hE⟩ := e1
  have hXd : X.det ≠ 0 := by
    intro h0
    have := congrArg det hA
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hDd : D.det ≠ 0 := by
    intro h0
    have := congrArg det hE
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hB0 : B = 0 := by
    have := congrArg (fun M => X⁻¹ * M) hB
    simp only [Matrix.mul_zero, ← Matrix.mul_assoc,
      nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hXd), Matrix.one_mul] at this
    exact this
  have hC0 : C = 0 := by
    have := congrArg (fun M => D⁻¹ * M) hC
    simp only [Matrix.mul_zero, ← Matrix.mul_assoc,
      nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hDd), Matrix.one_mul] at this
    exact this
  exact ⟨A, E, by rw [hgi, hB0, hC0, blk], hA, hE⟩

end Blocks

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* projectiveSL (2 + 2) K}

omit [Finite K] in
theorem exists_blk_of_mem_centralizer (hθ : Function.Surjective θ) {c : Kˣ} (hc : c ≠ 1)
    {ω : K} {x : G} (hxA : x ∈ A)
    (hxθ : θ ⟨x, hxA⟩ = proj (2 + 2) K (blkSL₂ (fiveSL ω))) {m : G}
    (hm : m ∈ centralizer ((liftSub θ (barT K) ⊔ zpowers x : Subgroup G) : Set G))
    (hmA : m ∈ A) :
    ∃ g : SpecialLinearGroup (Fin (2 + 2)) K, proj (2 + 2) K g = θ ⟨m, hmA⟩ ∧
      ∃ X D : Matrix (Fin 2) (Fin 2) K,
        (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) = blk X D ∧ D * fiveM ω = fiveM ω * D := by
  obtain ⟨g, hg⟩ := proj_surjective (2 + 2) K (θ ⟨m, hmA⟩)
  refine ⟨g, hg, ?_⟩
  have hcomm : ∀ y : G, ∀ hy : y ∈ liftSub θ (barT K) ⊔ zpowers x, ∀ hyA : y ∈ A,
      θ ⟨m, hmA⟩ * θ ⟨y, hyA⟩ = θ ⟨y, hyA⟩ * θ ⟨m, hmA⟩ := by
    intro y hy hyA
    have h1 := mem_centralizer_iff.mp hm y hy
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext h1.symm)
  obtain ⟨t, ht⟩ := hθ (proj (2 + 2) K (torus c))
  have htT : (t : G) ∈ liftSub θ (barT K) ⊔ zpowers x :=
    mem_sup_left (mem_liftSub.mpr ⟨t.2, by rw [ht]; exact ⟨c, rfl⟩⟩)
  have h1 := hcomm t htT t.2
  rw [show (⟨(t : G), t.2⟩ : ↥A) = t from rfl, ht, ← hg, ← map_mul, ← map_mul] at h1
  have h1' : (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) *
      (torus c : SpecialLinearGroup (Fin (2 + 2)) K) =
      (torus c : SpecialLinearGroup (Fin (2 + 2)) K) * g := by
    have := congrArg Subtype.val (proj_injective_four h1)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
  obtain ⟨X, D, hXD⟩ := exists_blk_of_commute_torus hc h1'
  refine ⟨X, D, hXD, ?_⟩
  have h2 := hcomm x (mem_sup_right (mem_zpowers x)) hxA
  rw [hxθ, ← hg, ← map_mul, ← map_mul] at h2
  have h3 := congrArg Subtype.val (proj_injective_four h2)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blkSL₂, hXD,
    blk_mul, blk_mul] at h3
  exact (blk_injective h3).2

omit [Finite K] [CharP K 2] in
theorem barT_commute_barW {t w : projectiveSL (2 + 2) K} (ht : t ∈ barT K) (hw : w ∈ barW K 2) :
    t * w = w * t := by
  obtain ⟨c, rfl⟩ := ht
  obtain ⟨X, rfl⟩ := hw
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blkSL₁]
  exact (blk_mul_torus _ _ c).symm

omit [Finite K] [CharP K 2] in
theorem proj_mem_normalizer_barW {k : ℕ} {g : SpecialLinearGroup (Fin (2 + k)) K}
    {X : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K}
    (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk X D) :
    proj (2 + k) K g ∈ normalizer (barW K k : Set (projectiveSL (2 + k) K)) := by
  have key : ∀ {h : SpecialLinearGroup (Fin (2 + k)) K} {Y : Matrix (Fin 2) (Fin 2) K}
      {E : Matrix (Fin k) (Fin k) K}, (h : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk Y E →
      ∀ w ∈ barW K k, proj (2 + k) K h * w * (proj (2 + k) K h)⁻¹ ∈ barW K k := by
    intro h Y E hh w hw
    obtain ⟨Z, rfl⟩ := hw
    obtain ⟨Y', E', hinv, hYY, hEE⟩ := exists_inv_blk' hh
    obtain ⟨Z', hZ'⟩ := mem_range_blkSL₁ (g := h * blkSL₁ Z * h⁻¹)
      (X := Y * (Z : Matrix (Fin 2) (Fin 2) K) * Y') (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hh, hinv,
          coe_blkSL₁, blk_mul, blk_mul, Matrix.mul_one, hEE])
    refine ⟨Z', ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [hZ', map_mul, map_mul, map_inv]
  obtain ⟨X', D', hinv, -, -⟩ := exists_inv_blk' hg
  refine mem_normalizer_iff.mpr fun w => ⟨key hg w, fun hw => ?_⟩
  have h1 := key hinv _ hw
  rw [map_inv, inv_inv] at h1
  rwa [show (proj (2 + k) K g)⁻¹ * (proj (2 + k) K g * w * (proj (2 + k) K g)⁻¹) *
    proj (2 + k) K g = w by group] at h1

omit [Finite K] [CharP K 2] in
theorem commutatorElement_proj_mem_barW {k : ℕ} {g g' : SpecialLinearGroup (Fin (2 + k)) K}
    {X X' : Matrix (Fin 2) (Fin 2) K} {D D' : Matrix (Fin k) (Fin k) K}
    (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk X D)
    (hg' : (g' : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk X' D') (hDD : D * D' = D' * D) :
    ⁅proj (2 + k) K g, proj (2 + k) K g'⁆ ∈ barW K k := by
  rw [← map_commutatorElement]
  obtain ⟨Xi, Di, hi, -, hDi⟩ := exists_inv_blk' hg
  obtain ⟨Xi', Di', hi', -, hDi'⟩ := exists_inv_blk' hg'
  obtain ⟨Z, hZ⟩ := mem_range_blkSL₁ (g := ⁅g, g'⁆) (X := X * X' * Xi * Xi') (by
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, hg', hi, hi',
      blk_mul, blk_mul, blk_mul]
    congr 1
    rw [hDD, Matrix.mul_assoc D' D Di, hDi, Matrix.mul_one, hDi'])
  exact ⟨Z, by simp only [MonoidHom.comp_apply]; rw [hZ]⟩

omit [Finite K] in
theorem layerCentralizer_eq_leviW (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (h4 : ∃ s : Finset K, s.card = 4) {c : Kˣ} (hc : c ≠ 1) {ω : K} {x : G}
    (hxL : x ∈ leviL θ) (hxA : x ∈ A)
    (hxθ : θ ⟨x, hxA⟩ = proj (2 + 2) K (blkSL₂ (fiveSL ω))) :
    AS76b.layerCentralizer A (liftSub θ (barT K) ⊔ zpowers x) = leviW θ := by
  refine layerCentralizer_eq_levLift hker hθ (commutator_barW h4)
    (isQuasisimple_barW (by norm_num) h4) ?_ ?_ ?_
  · refine le_inf levLift_le ?_
    rw [le_centralizer_iff]
    refine sup_le (fun d hd => ?_) ?_
    · obtain ⟨hdA, hdT⟩ := mem_liftSub.mp hd
      have hle := levLift_le_centralizer hker hdA (S := barW K 2) fun s hs =>
        barT_commute_barW hdT hs
      rw [mem_centralizer_iff]
      intro w hw
      exact mem_centralizer_singleton_iff.mp (hle hw)
    · rw [zpowers_le]
      exact le_centralizer_iff.mp (leviW_le_centralizer_leviL hker) hxL
  · intro m hmM hm
    obtain ⟨g, hg, X, D, hXD, -⟩ :=
      exists_blk_of_mem_centralizer hθ hc hxA hxθ (mem_inf.mp hmM).2 hm
    rw [← hg]
    exact proj_mem_normalizer_barW hXD
  · intro a ha b hb haA hbA
    obtain ⟨g, hg, X, D, hXD, hD⟩ :=
      exists_blk_of_mem_centralizer hθ hc hxA hxθ (mem_inf.mp ha).2 haA
    obtain ⟨g', hg', X', D', hXD', hD'⟩ :=
      exists_blk_of_mem_centralizer hθ hc hxA hxθ (mem_inf.mp hb).2 hbA
    rw [← hg, ← hg']
    exact commutatorElement_proj_mem_barW hXD hXD' (commute_of_mul_fiveM hD hD')

theorem noInv_five (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4) {c : Kˣ} (hc : c ≠ 1)
    {ω : K} (hω0 : ω ≠ 0) {x : G} (hxA : x ∈ A)
    (hxθ : θ ⟨x, hxA⟩ = proj (2 + 2) K (blkSL₂ (fiveSL ω))) :
    NoInvolutoryCentralizing A (liftSub θ (barT K) ⊔ zpowers x ⊔ leviW θ) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hT := inducedAut_fix_of_liftSub hθ (le_sup_left.trans le_sup_left) hfix hα _ ⟨c, rfl⟩
  have hx : α (proj (2 + 2) K (blkSL₂ (fiveSL ω))) = proj (2 + 2) K (blkSL₂ (fiveSL ω)) := by
    rw [← hxθ, hα, hfix ⟨x, hxA⟩ (mem_sup_left (mem_sup_right (mem_zpowers x)))]
  have h1 := eq_one_of_fixes_five α (inducedAut_sq hθ hσ hα)
    (inducedAut_fix_of_levLift hθ (commutator_barW h4) le_sup_right hfix hα) hc hT hω0 hx
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

theorem exists_mem_leviL_orderOf_five [Finite G] (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hZ : Odd (Nat.card (center ↥A))) (hK : Nat.card K = 4)
    (h4 : ∃ s : Finset K, s.card = 4) {ω : K} (hω : ω * ω + ω + 1 = 0) :
    ∃ x ∈ leviL θ, ∃ hxA : x ∈ A,
      θ ⟨x, hxA⟩ = proj (2 + 2) K (blkSL₂ (fiveSL ω)) ∧ orderOf x = 5 := by
  have hperf := commutator_barL (K := K) le_rfl h4
  obtain ⟨x, hx, hxθ⟩ := exists_mem_levLift hθ hperf
    (⟨fiveSL ω, rfl⟩ : proj (2 + 2) K (blkSL₂ (fiveSL ω)) ∈ barL K 2)
  refine ⟨x, hx, levLift_le hx, hxθ, ?_⟩
  obtain ⟨e⟩ := nonempty_levLift_equiv_SL2 hker hθ hZ (m := 2) le_rfl (by rw [hK]; norm_num)
    hperf (barLEquiv K 2)
  set L := levLift θ (barL K 2) with hL
  have hcen : center ↥L = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [card_center_congr e, center_SL2_eq_bot', Subgroup.card_bot]
  set xL : ↥L := ⟨x, hx⟩
  have hx5 : xL ^ 5 = 1 := by
    have hc : xL ^ 5 ∈ center ↥L := by
      refine mem_center_levLift_of hker ?_
      have h1 : levLiftHom θ (barL K 2) (xL ^ 5) = 1 := by
        apply Subtype.ext
        rw [map_pow, Subgroup.coe_pow, levLiftHom_apply, Subgroup.coe_one]
        change (θ ⟨x, levLift_le hx⟩) ^ 5 = 1
        rw [hxθ, ← map_pow, ← map_pow, fiveSL_pow_five hω, map_one, map_one]
      rw [h1]
      exact one_mem _
    rw [hcen, mem_bot] at hc
    exact hc
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hx5' : x ^ 5 = 1 := by
    have := congrArg Subtype.val hx5
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  refine orderOf_eq_prime hx5' fun h1 => ?_
  have h2 : θ ⟨x, levLift_le hx⟩ = 1 := by
    rw [show (⟨x, levLift_le hx⟩ : ↥A) = 1 from Subtype.ext h1, map_one]
  rw [hxθ] at h2
  have h3 : ((proj (2 + 2) K).comp blkSL₂) (fiveSL ω) = ((proj (2 + 2) K).comp blkSL₂) 1 := by
    rw [map_one]
    exact h2
  exact fiveSL_ne_one ω (blkSL₂_injective_proj h3)

omit [CharP K 2] in
theorem exists_cube_root_of_card_four (hK : Nat.card K = 4) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 ∧ ω * ω + ω + 1 = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at h1
    omega
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [← Nat.card_eq_fintype_card, hK] at this
  refine ⟨ω, hω0, hω1, ?_⟩
  have h4 : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hω1)

theorem sym_two_four [Finite G] (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hZ : Odd (Nat.card (center ↥A))) (hK : Nat.card K = 4)
    (h4 : ∃ s : Finset K, s.card = 4) :
    ∃ (D' : Subgroup G) (s x : G), liftSub θ (barT K) ⊔ leviW θ = D' ⊔ leviW θ ∧ s ∈ A ∧
      rightConjugate (leviW θ) s = leviL θ ∧ rightConjugate (leviL θ) s = leviW θ ∧
      rightConjugate D' s = D' ∧ x ∈ leviL θ ∧ orderOf x = 5 ∧
      AS76b.layerCentralizer A (D' ⊔ zpowers x) = leviW θ ∧
      NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ leviW θ) := by
  obtain ⟨ω, hω0, hω1, hω⟩ := exists_cube_root_of_card_four hK
  set c : Kˣ := Units.mk0 ω hω0
  have hc : c ≠ 1 := fun h => hω1 (by rw [← Units.val_mk0 hω0, show Units.mk0 ω hω0 = c from rfl,
    h, Units.val_one])
  obtain ⟨sA, hsA⟩ := hθ (proj (2 + 2) K swapSL)
  have hsθ : (θ ⟨(sA : G), sA.2⟩)⁻¹ = proj (2 + 2) K swapSL := by
    rw [show (⟨(sA : G), sA.2⟩ : ↥A) = sA from rfl, hsA, ← map_inv, swapSL_inv]
  obtain ⟨x, hxL, hxA, hxθ, hx5⟩ := exists_mem_leviL_orderOf_five hker hθ hZ hK h4 hω
  refine ⟨liftSub θ (barT K), sA, x, rfl, sA.2, ?_, ?_, ?_, hxL, hx5,
    layerCentralizer_eq_leviW hker hθ h4 hc hxL hxA hxθ,
    noInv_five hA hker hθ h4 hc hω0 hxA hxθ⟩
  · rw [leviW, rightConjugate_levLift sA.2, hsθ, map_conj_barW]
    rfl
  · rw [leviL, rightConjugate_levLift sA.2, hsθ, map_conj_barL]
    rfl
  · rw [rightConjugate_liftSub sA.2, hsθ, map_conj_barT]

end Lift

end CFSG.ComponentClassification.RankTwoClassical
