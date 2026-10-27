module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotPositionBSp4

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt elt E)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)

variable {K : Type} [Field K]

section Row

@[expose] noncomputable def bRowT (Z : StatedSp 3 K) : Fin 2 ⊕ Fin 2 → K :=
  fun x => mat 3 K Z (Sum.inl 1)
    (Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove (1 : Fin 3)) x)

theorem sumMap_succAbove_one_not_mem_coords (x : Fin 2 ⊕ Fin 2) :
    Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove (1 : Fin 3)) x ∉ coords (1 : Fin 3) := by
  rcases x with x | x <;> simp [mem_coords, Fin.succAbove_ne]

theorem bRowT_mul {Z Z' : StatedSp 3 K} (hZ : Z ∈ transvRadical K (1 : Fin 3))
    (hZ' : Z' ∈ transvRadical K (1 : Fin 3)) (x : Fin 2 ⊕ Fin 2) :
    bRowT (Z * Z') x = bRowT Z x + bRowT Z' x := by
  set t := Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove (1 : Fin 3)) x with htdef
  have ht : t ∉ coords (1 : Fin 3) := sumMap_succAbove_one_not_mem_coords x
  have hti : t ≠ Sum.inl 1 := fun h => ht (h ▸ inl_mem_coords 1)
  simp only [bRowT, ← htdef]
  rw [map_mul, Matrix.mul_apply, Fintype.sum_eq_add t (Sum.inl 1) hti]
  · rw [hZ'.2 t ht t hti, Matrix.one_apply_eq, mul_one, hZ.1, Matrix.one_apply_eq, one_mul]
  · rintro b ⟨hbt, hbi⟩
    rw [hZ'.2 t ht b hbi, Matrix.one_apply_ne hbt, mul_zero]

theorem bRowT_one : bRowT (1 : StatedSp 3 K) = 0 := by
  funext x
  simp only [bRowT, map_one, Pi.zero_apply]
  exact Matrix.one_apply_ne (fun h => sumMap_succAbove_one_not_mem_coords x
    (h ▸ inl_mem_coords 1))

theorem bRowT_conj {A B : StatedSp 3 K} (hA : A ∈ transvRadical K (1 : Fin 3))
    (hB : B ∈ transvRadical K (1 : Fin 3)) : bRowT (A * B * A⁻¹) = bRowT B := by
  funext x
  have hAi : A⁻¹ ∈ transvRadical K (1 : Fin 3) := inv_mem hA
  have h1 := bRowT_mul (mul_mem hA hB) hAi x
  have h2 := bRowT_mul hA hB x
  have h3 := bRowT_mul hA hAi x
  rw [mul_inv_cancel, bRowT_one] at h3
  simp only [Pi.zero_apply] at h3
  rw [h1, h2]
  linear_combination -h3

theorem bRowT_mul_left {h : StatedSp 3 K} (hh : h ∈ complSp K (1 : Fin 3)) (Z : StatedSp 3 K) :
    bRowT (h * Z) = bRowT Z := by
  have hrow : ∀ b, mat 3 K h (Sum.inl 1) b =
      (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl 1) b :=
    fun b => hh (Sum.inl 1) b fun h1 => h1.1 (inl_mem_coords 1)
  funext x
  simp only [bRowT]
  rw [map_mul, Matrix.mul_apply]
  simp_rw [hrow]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem bRowT_mul_spEmbed (Z : StatedSp 3 K) (g : StatedSp 2 K) :
    bRowT (Z * spEmbed (Fin.succAbove (1 : Fin 3)) Fin.succAbove_right_injective g) =
      Matrix.vecMul (bRowT Z) (mat 2 K g) := by
  have hinj : Function.Injective
      (Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove (1 : Fin 3))) :=
    Sum.map_injective.2 ⟨Fin.succAbove_right_injective, Fin.succAbove_right_injective⟩
  funext y
  simp only [bRowT, Matrix.vecMul, dotProduct]
  rw [map_mul, mat_spEmbed, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => ?_) (fun x => ?_)
  · rw [spEmbedMat_apply_of_not_mem _ (fun h => hb h.1),
      Matrix.one_apply_ne (fun h => hb ⟨y, h.symm⟩), mul_zero]
  · rw [spEmbedMat_apply_image Fin.succAbove_right_injective]

theorem eq_siegDiag_of_bRowT_eq_zero {Z : StatedSp 3 K} (hZ : Z ∈ transvRadical K (1 : Fin 3))
    (h0 : bRowT Z = 0) :
    Z = siegDiag K (1 : Fin 3) (mat 3 K Z (Sum.inl 1) (Sum.inr 1)) := by
  refine eq_siegDiag_of_mem_transvRadical hZ fun t ht => ?_
  obtain ⟨x, rfl⟩ : ∃ x, Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove (1 : Fin 3)) x = t := by
    rcases t with j | j
    · have hj : j ≠ 1 := fun h => ht (h ▸ inl_mem_coords _)
      obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq hj
      exact ⟨Sum.inl x, by simp [hx]⟩
    · have hj : j ≠ 1 := fun h => ht (h ▸ inr_mem_coords _)
      obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq hj
      exact ⟨Sum.inr x, by simp [hx]⟩
  exact congrFun h0 x

theorem commute_siegDiag_of_mem_centralizer [CharP K 2] {m : ℕ} {p : Fin m} {g : StatedSp m K}
    (hg : g ∈ centralizer ({siegDiag K p 1} : Set (StatedSp m K))) (c : K) :
    g * siegDiag K p c = siegDiag K p c * g := by
  have hcol := mem_centralizer_siegDiag_iff.1 hg
  apply mat_injective
  rw [map_mul, map_mul, mat_siegDiag_eq_add', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, mul_single_of_col hcol, single_mul_of_row (mat_inr_apply_of_col_inl hcol)]

end Row

section QZero

theorem siegPair_one_two_mem_transvRadical :
    siegPair K (1 : Fin 3) 2 1 ∈ transvRadical K (1 : Fin 3) :=
  siegPair_mem_transvRadical (p := 1) (j := 2) 1

theorem commute_siegPair_one_two {j : StatedSp 3 K} (hj : j ∈ longRootSp2 K 3 0) :
    j * siegPair K (1 : Fin 3) 2 1 = siegPair K (1 : Fin 3) 2 1 * j := by
  rw [longRootSp2_eq_suppGroup] at hj
  refine (commute_suppGroup_compl hj ?_).eq
  rw [mem_suppGroup]
  intro r t hrt
  rw [mat_siegPair]
  have hrt' : r ∈ coords (0 : Fin 3) ∨ t ∈ coords (0 : Fin 3) := by
    by_contra h
    push Not at h
    exact hrt ⟨h.1, h.2⟩
  rcases r with a | a <;> rcases t with b | b
  · simp [Matrix.one_apply]
  · rcases hrt' with h | h <;> simp only [mem_coords, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, or_false, false_or] at h <;> subst h <;> simp
  · simp
  · simp [Matrix.one_apply]

theorem bRowT_siegPair_one_two : bRowT (siegPair K (1 : Fin 3) 2 1) (Sum.inr 1) = 1 := by
  simp only [bRowT]
  have h : (Fin.succAbove (1 : Fin 3) (1 : Fin 2)) = 2 := by decide
  rw [Sum.map_inr, h, mat_siegPair, fromBlocks_apply₁₂]
  simp

end QZero

section F5

variable [Finite K] [CharP K 2]

theorem exists_conj_of_leviAutOfAut_transvRadical_zero
    (hQM : Disjoint (transvRadical K (1 : Fin 3)) (complSp K (1 : Fin 3)))
    (hMN : complSp K (1 : Fin 3) ≤
      normalizer (transvRadical K (1 : Fin 3) : Set (StatedSp 3 K)))
    (β : (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) : Subgroup (StatedSp 3 K)) ≃*
      (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) : Subgroup (StatedSp 3 K)))
    (hβ : ((transvRadical K (1 : Fin 3)).subgroupOf
      (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3))).map β.toMonoidHom =
        (transvRadical K (1 : Fin 3)).subgroupOf
          (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3))) :
    ∃ c : StatedSp 3 K,
      (((longRootSp2 K 3 0).subgroupOf (complSp K (1 : Fin 3))).map
        (EPilot.leviAutOfAut _ _ hQM hMN β hβ).toMonoidHom).map (complSp K (1 : Fin 3)).subtype =
        (longRootSp2 K 3 0).map (MulAut.conj c).toMonoidHom := by
  generalize hιdef : EPilot.leviAutOfAut _ _ hQM hMN β hβ = ι
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (StatedSp 2 K),
      α = (complSpEquiv (K := K) (m := 2) 1).trans
        (ι.trans (complSpEquiv (K := K) (m := 2) 1).symm) :=
    ⟨_, rfl⟩
  have hιE : ∀ (m : complSp K (1 : Fin 3)) (g : StatedSp 2 K),
      (m : StatedSp 3 K) = (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) →
      (ι m : StatedSp 3 K) = (complSpEquiv (K := K) (m := 2) 1 (α g) : StatedSp 3 K) := by
    intro m g hmg
    have hm : m = complSpEquiv (K := K) (m := 2) 1 g := Subtype.ext hmg
    subst hm
    rw [hαdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hs : (1 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
  have hJE : ∀ x : StatedSp 3 K, x ∈ longRootSp2 K 3 0 ↔
      ∃ g ∈ longRootSp2 K 2 0, (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) = x := by
    intro x
    have h0 := map_complSpEquiv_longRootSp2 (K := K) (m := 2) 1 0
    rw [hs] at h0
    rw [← h0]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨s, σ, h | h⟩ := F4Pilot.exists_eq_conj_mul_fieldSp_tauSp α
  ·
    refine ⟨(complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K), ?_⟩
    have hfJ := map_fieldSp_longRootSp2 (K := K) (n := 2) σ 0
    have hconj : ∀ g : StatedSp 2 K,
        (complSpEquiv (K := K) (m := 2) 1 (α g) : StatedSp 3 K) =
          (complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K) *
          (complSpEquiv (K := K) (m := 2) 1 (fieldSp 2 K σ g) : StatedSp 3 K) *
          (complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K)⁻¹ := by
      intro g
      rw [h g, map_mul, map_mul, map_inv]
      rfl
    ext x
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      obtain ⟨g, hg, hgm⟩ := (hJE _).1 (mem_subgroupOf.1 hm)
      refine ⟨(complSpEquiv (K := K) (m := 2) 1 (fieldSp 2 K σ g) : StatedSp 3 K),
        (hJE _).2 ⟨_, hfJ ▸ mem_map_of_mem _ hg, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype]
      rw [hιE m g hgm.symm, hconj g]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g', hg', rfl⟩ := (hJE _).1 hy
      rw [← hfJ] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      refine ⟨_, ⟨complSpEquiv (K := K) (m := 2) 1 g,
        mem_subgroupOf.2 ((hJE _).2 ⟨g, hg, rfl⟩), rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype]
      rw [hιE _ g rfl, hconj g]
  ·
    exfalso
    have hq₀Q := siegPair_one_two_mem_transvRadical (K := K)
    obtain ⟨qq, hqq⟩ : ∃ qq : (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) :
        Subgroup (StatedSp 3 K)), (qq : StatedSp 3 K) = siegPair K (1 : Fin 3) 2 1 :=
      ⟨⟨_, mem_sup_left hq₀Q⟩, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X : StatedSp 3 K, X = (β qq : StatedSp 3 K) := ⟨_, rfl⟩
    have hXQ : X ∈ transvRadical K (1 : Fin 3) := by
      rw [hX]
      exact (EPilot.coe_mem_iff_of_map_eq hβ qq).2 (by rw [hqq]; exact hq₀Q)
    have key : ∀ g ∈ longRootSp2 K 2 0, bRowT X = Matrix.vecMul (bRowT X) (mat 2 K (α g)) := by
      intro g hg
      obtain ⟨jm, hjm⟩ : ∃ jm : complSp K (1 : Fin 3),
          (jm : StatedSp 3 K) = (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) :=
        ⟨_, rfl⟩
      have hjJ : (jm : StatedSp 3 K) ∈ longRootSp2 K 3 0 := (hJE _).2 ⟨g, hg, hjm.symm⟩
      obtain ⟨B, hB⟩ : ∃ B : StatedSp 3 K,
          B = (β (inclusion le_sup_right jm) : StatedSp 3 K) := ⟨_, rfl⟩
      have hβc : B * X = X * B := by
        have hcomm : inclusion le_sup_right jm * qq = qq * inclusion le_sup_right jm := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inclusion, hqq]
          exact commute_siegPair_one_two hjJ
        rw [hB, hX, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm]
      obtain ⟨A, hA⟩ : ∃ A : StatedSp 3 K, A = (ι jm : StatedSp 3 K) := ⟨_, rfl⟩
      have hdQ : A⁻¹ * B ∈ transvRadical K (1 : Fin 3) := by
        have h0 := EPilot.leviAutOfAut_inv_mul_mem hQM hMN hβ jm
        rw [hιdef] at h0
        rw [hA, hB]
        exact h0
      have hrel : A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) = X * A := by
        calc A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) = (B * X) * B⁻¹ * A := by group
          _ = X * A := by rw [hβc]; group
      have hAS : A ∈ complSp K (1 : Fin 3) := by
        rw [hA]
        exact (ι jm).2
      have h1 := bRowT_mul_left hAS ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹)
      have h2 := bRowT_conj hdQ hXQ
      have h3 : bRowT (X * A) = Matrix.vecMul (bRowT X) (mat 2 K (α g)) := by
        rw [hA, hιE jm g hjm, coe_complSpEquiv_apply]
        exact bRowT_mul_spEmbed X (α g)
      calc bRowT X = bRowT ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) := h2.symm
        _ = bRowT (A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹)) := h1.symm
        _ = bRowT (X * A) := by rw [hrel]
        _ = Matrix.vecMul (bRowT X) (mat 2 K (α g)) := h3
    have hfix : bRowT X = 0 := by
      have hA := key _ (elt_positiveLong_mem_longRootSp2 0 1)
      have hB := key _ (elt_negativeLong_mem_longRootSp2 0 1)
      rw [h, F4Pilot.tauSp_elt, F4Pilot.fieldSp_elt, one_pow, map_one] at hA hB
      have hτA : F4Pilot.tauIdx (.positiveLong (0 : Fin 2)) = .positiveSum 0 1 (by decide) := rfl
      have hτB : F4Pilot.tauIdx (.negativeLong (0 : Fin 2)) = .negativeSum 0 1 (by decide) := rfl
      rw [hτA] at hA
      rw [hτB] at hB
      have hw0 := eq_zero_of_vecMul_elt_sum (vecMul_mat_conj hA) (vecMul_mat_conj hB)
      have hs2 : mat 2 K s * mat 2 K s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      calc bRowT X = Matrix.vecMul (bRowT X) (mat 2 K s * mat 2 K s⁻¹) := by
            rw [hs2, Matrix.vecMul_one]
        _ = Matrix.vecMul (Matrix.vecMul (bRowT X) (mat 2 K s)) (mat 2 K s⁻¹) := by
            rw [Matrix.vecMul_vecMul]
        _ = 0 := by rw [hw0, Matrix.zero_vecMul]
    have hXZ := eq_siegDiag_of_bRowT_eq_zero hXQ hfix
    have hΛC : transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) ≤
        centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)) :=
      sup_le transvRadical_le_centralizer complSp_le_centralizer_siegDiag
    have hcen : ∀ y : (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) :
        Subgroup (StatedSp 3 K)), qq * y = y * qq := by
      intro y
      apply β.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hX, hXZ]
      exact (commute_siegDiag_of_mem_centralizer (hΛC (β y).2) _).symm
    have hrow : ∀ g : StatedSp 2 K, bRowT (siegPair K (1 : Fin 3) 2 1) =
        Matrix.vecMul (bRowT (siegPair K (1 : Fin 3) 2 1)) (mat 2 K g) := by
      intro g
      have hEg := (complSpEquiv (K := K) (m := 2) 1 g).2
      have hc : siegPair K (1 : Fin 3) 2 1 * (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) =
          (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) * siegPair K (1 : Fin 3) 2 1 := by
        have h' := congrArg Subtype.val (hcen ⟨_, mem_sup_right hEg⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hqq] at h'
        exact h'
      calc bRowT (siegPair K (1 : Fin 3) 2 1) =
          bRowT ((complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) *
            siegPair K (1 : Fin 3) 2 1) := (bRowT_mul_left hEg _).symm
        _ = bRowT (siegPair K (1 : Fin 3) 2 1 *
            (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K)) := by rw [hc]
        _ = Matrix.vecMul (bRowT (siegPair K (1 : Fin 3) 2 1)) (mat 2 K g) := by
            rw [coe_complSpEquiv_apply]
            exact bRowT_mul_spEmbed _ g
    have h0 := eq_zero_of_vecMul_elt_sum (hrow _).symm (hrow _).symm
    have h1 := congrFun h0 (Sum.inr 1)
    rw [bRowT_siegPair_one_two, Pi.zero_apply] at h1
    exact one_ne_zero h1

theorem spLongRootF5_b1_zero : SpLongRootF5 K 0 .b1 := fun β hβ =>
  exists_conj_of_leviAutOfAut_transvRadical_zero (disjoint_spCoreRadical_spCoreLevi (n := 0) .b1)
    (spCoreLevi_le_normalizer_spCoreRadical (n := 0) .b1) β hβ

theorem spLongRootF5_zero_of_four_le (hK : 4 ≤ Nat.card K) (κ : SpTwoCentral) :
    SpLongRootF5 K 0 κ :=
  spLongRootF5_zero hK spLongRootF5_b1_zero κ

theorem spLongRootF5_of_four_le_card {n : ℕ} (hK : 4 ≤ Nat.card K) (κ : SpTwoCentral) :
    SpLongRootF5 K n κ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact spLongRootF5_zero_of_four_le hK κ
  · exact spLongRootF5_of_one_le hK hn κ

end F5

section LemmaB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [Finite K] [CharP K 2]

theorem exists_conj_eq_mul_spRep_le_centralizer_mulEquiv_of_four_le_card
    (hset : SeitzSetting G L) {n : ℕ} (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp (n + 3) K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((longRootSp2 K (n + 3) 0).map e.symm.toMonoidHom).map L.subtype) :
    ∃ (g : G) (κ : SpTwoCentral), g⁻¹ * t * g = t * (e.symm (spRep n κ) : G) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓
          centralizer ({t * (e.symm (spRep n κ) : G)} : Set G) ∧
        Nonempty (P ≃* ((complSp K (0 : Fin (n + 3))).map e.symm.toMonoidHom).map L.subtype) :=
  exists_conj_eq_mul_spRep_le_centralizer_mulEquiv hset hK (spLongRootF5_of_four_le_card hK) e ht
    hKt hXodd hXJ

end LemmaB

end CFSG.SeitzReduction.SymplecticPilot
