module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviBlocks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLiftSub
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.Quasithin.Background.KnownMultOdd

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Proj

variable {K : Type} [Field K] {k : ℕ}

variable (K k) in
@[expose] noncomputable def barW : Subgroup (projectiveSL (2 + k) K) :=
  ((proj (2 + k) K).comp
    (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K)).range

variable (K k) in
@[expose] noncomputable def barL : Subgroup (projectiveSL (2 + k) K) :=
  ((proj (2 + k) K).comp
    (blkSL₂ : SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin (2 + k)) K)).range

theorem barW_commute_barL {x y : projectiveSL (2 + k) K} (hx : x ∈ barW K k) (hy : y ∈ barL K k) :
    x * y = y * x := by
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := hy
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, blkSL₁_commute_blkSL₂]

theorem blkSL₁_tr₂_sq [CharP K 2] (i j : Fin 2) (hij : i ≠ j) :
    (blkSL₁ (tr₂ (K := K) i j hij) : SpecialLinearGroup (Fin (2 + k)) K) ^ 2 = 1 := by
  rw [← map_pow]
  have h : (tr₂ (K := K) i j hij) ^ 2 = 1 := by
    rw [sq]
    apply Subtype.ext
    change (1 + single i j (1 : K)) * (1 + single i j 1) = 1
    have hEE : single i j (1 : K) * single i j 1 = 0 := by simp [hij.symm]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hEE, add_zero, add_assoc, ← single_add, CharTwo.add_self_eq_zero,
      single_zero, add_zero]
  rw [h, map_one]

theorem commute_of_proj_commute [CharP K 2] {n : ℕ} {g t : SpecialLinearGroup (Fin n) K}
    (ht : t ^ 2 = 1) (h : proj n K g * proj n K t = proj n K t * proj n K g) : g * t = t * g := by
  set u := g * t * g⁻¹ * t⁻¹ with hu
  have hu1 : proj n K u = 1 := by
    rw [hu, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have huZ : u ∈ center (SpecialLinearGroup (Fin n) K) :=
    (scalars_eq_center n K).le (proj_eq_one_iff.mp hu1)
  have hut : g * t * g⁻¹ = u * t := by rw [hu]; group
  have hu2 : u ^ 2 = 1 := by
    have h1 : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, ht, mul_one, mul_inv_cancel]
    rw [hut, (show Commute u t from (mem_center_iff.mp huZ t).symm).mul_pow, ht, mul_one] at h1
    exact h1
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hu1)
  have hc1 : u = 1 := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · exact Subsingleton.elim _ _
    have h2 := congrArg (fun x : Matrix (Fin n) (Fin n) K => x i i) (congrArg Subtype.val hu2)
    simp only [Matrix.SpecialLinearGroup.coe_pow, hc, scalar_apply, diagonal_pow,
      diagonal_apply_eq, Pi.pow_apply, Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h2
    have hc2 : (c : K) = 1 := by
      have h3 : ((c : K) - 1) ^ 2 = 0 := by
        rw [sub_sq, h2, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
          CharTwo.add_self_eq_zero]
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
    apply Subtype.ext
    rw [hc, hc2, map_one]
    rfl
  calc g * t = u * t * g := by rw [← hut]; group
    _ = t * g := by rw [hc1, one_mul]

theorem exists_blk_of_commute_proj [CharP K 2] {x : projectiveSL (2 + k) K}
    (h₁ : x * proj (2 + k) K (blkSL₁ (tr₂ (K := K) 0 1 (by decide))) =
      proj (2 + k) K (blkSL₁ (tr₂ (K := K) 0 1 (by decide))) * x)
    (h₂ : x * proj (2 + k) K (blkSL₁ (tr₂ (K := K) 1 0 (by decide))) =
      proj (2 + k) K (blkSL₁ (tr₂ (K := K) 1 0 (by decide))) * x) :
    ∃ g : SpecialLinearGroup (Fin (2 + k)) K, proj (2 + k) K g = x ∧
      ∃ (c : K) (D : Matrix (Fin k) (Fin k) K),
        (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c • 1) D := by
  obtain ⟨g, rfl⟩ := proj_surjective (2 + k) K x
  exact ⟨g, rfl, exists_blk_of_commute (commute_of_proj_commute (blkSL₁_tr₂_sq _ _ _) h₁)
    (commute_of_proj_commute (blkSL₁_tr₂_sq _ _ _) h₂)⟩

theorem exists_blk_of_commute_barW [CharP K 2] {x : projectiveSL (2 + k) K}
    (hx : ∀ w ∈ barW K k, x * w = w * x) :
    ∃ g : SpecialLinearGroup (Fin (2 + k)) K, proj (2 + k) K g = x ∧
      ∃ (c : K) (D : Matrix (Fin k) (Fin k) K),
        (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c • 1) D :=
  exists_blk_of_commute_proj (hx _ ⟨_, rfl⟩) (hx _ ⟨_, rfl⟩)

theorem mem_normalizer_barL [CharP K 2] {x : projectiveSL (2 + k) K}
    (hx : ∀ w ∈ barW K k, x * w = w * x) :
    x ∈ normalizer (barL K k : Set (projectiveSL (2 + k) K)) := by
  obtain ⟨g, rfl, c, D, hg⟩ := exists_blk_of_commute_barW hx
  have key : ∀ y ∈ barL K k, proj (2 + k) K g * y * (proj (2 + k) K g)⁻¹ ∈ barL K k := by
    rintro _ ⟨S, rfl⟩
    obtain ⟨S', hS'⟩ := conj_mem_range_blkSL₂ hg S
    refine ⟨S', ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [hS', map_mul, map_mul, map_inv]
  refine mem_normalizer_iff.mpr fun y => ⟨key y, fun hy => ?_⟩
  have hxi : ∀ w ∈ barW K k, (proj (2 + k) K g)⁻¹ * w = w * (proj (2 + k) K g)⁻¹ := by
    intro w hw
    have := hx w hw
    calc (proj (2 + k) K g)⁻¹ * w = (proj (2 + k) K g)⁻¹ * (w * proj (2 + k) K g) *
        (proj (2 + k) K g)⁻¹ := by group
      _ = (proj (2 + k) K g)⁻¹ * (proj (2 + k) K g * w) * (proj (2 + k) K g)⁻¹ := by rw [this]
      _ = w * (proj (2 + k) K g)⁻¹ := by group
  obtain ⟨g', hg'eq, c', D', hg'⟩ := exists_blk_of_commute_barW hxi
  obtain ⟨S, hS⟩ := hy
  obtain ⟨S', hS'⟩ := conj_mem_range_blkSL₂ hg' S
  refine ⟨S', ?_⟩
  simp only [MonoidHom.comp_apply] at hS ⊢
  rw [hS', map_mul, map_mul, map_inv, hg'eq, hS]
  group

theorem commutatorElement_mem_barL [CharP K 2] {x y : projectiveSL (2 + k) K}
    (hx : ∀ w ∈ barW K k, x * w = w * x) (hy : ∀ w ∈ barW K k, y * w = w * y) :
    ⁅x, y⁆ ∈ barL K k := by
  obtain ⟨g, rfl, c, D, hg⟩ := exists_blk_of_commute_barW hx
  obtain ⟨g', rfl, c', D', hg'⟩ := exists_blk_of_commute_barW hy
  obtain ⟨S, hS⟩ := commutatorElement_mem_range_blkSL₂ hg hg'
  refine ⟨S, ?_⟩
  simp only [MonoidHom.comp_apply]
  rw [hS, map_commutatorElement]

variable (K k) in
@[expose] noncomputable def barWEquiv (hk : 1 ≤ k) : SpecialLinearGroup (Fin 2) K ≃* barW K k :=
  MonoidHom.ofInjective (blkSL₁_injective_proj (K := K) hk)

variable (K k) in
@[expose] noncomputable def barLEquiv : SpecialLinearGroup (Fin k) K ≃* barL K k :=
  MonoidHom.ofInjective (blkSL₂_injective_proj (K := K) (k := k))

theorem commutator_range_of_perfect {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hG : commutator G = ⊤) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hG]

theorem commutator_barW (h4 : ∃ s : Finset K, s.card = 4) :
    ⁅barW K k, barW K k⁆ = barW K k :=
  commutator_range_of_perfect _
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl
      (Or.inr h4)).commutator_eq_top

theorem commutator_barL (hk : 2 ≤ k) (h4 : ∃ s : Finset K, s.card = 4) :
    ⁅barL K k, barL K k⁆ = barL K k :=
  commutator_range_of_perfect _
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := k) hk
      (by
        rcases Nat.lt_or_ge k 3 with h | h
        · exact Or.inr h4
        · exact Or.inl h)).commutator_eq_top

theorem isQuasisimple_SL (hk : 2 ≤ k) (h4 : ∃ s : Finset K, s.card = 4) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin k) K) := by
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    exact CFSG.RankThree.Classical.isQuasisimple_SL2 h4
  · exact CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup h

theorem isQuasisimple_barL (hk : 2 ≤ k) (h4 : ∃ s : Finset K, s.card = 4) :
    CFSG.IsQuasisimple (barL K k) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (barLEquiv K k) (isQuasisimple_SL hk h4)

theorem isQuasisimple_barW (hk : 1 ≤ k) (h4 : ∃ s : Finset K, s.card = 4) :
    CFSG.IsQuasisimple (barW K k) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (barWEquiv K k hk) (isQuasisimple_SL le_rfl h4)

theorem center_SL2_eq_bot' [CharP K 2] : center (SpecialLinearGroup (Fin 2) K) = ⊥ :=
  CFSG.Timmesfeld.RankOne.center_SL2_eq_bot K

theorem card_center_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (center G) = Nat.card (center H) := by
  rw [← Subgroup.map_center_eq e]
  exact Nat.card_congr ((center G).equivMapOfInjective (e : G →* H) e.injective).toEquiv

theorem odd_card_center_SL [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (center (SpecialLinearGroup (Fin k) K))) := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  have hdvd : Nat.card (rootsOfUnity (max (Fintype.card (Fin k)) 1) K) ∣ Nat.card Kˣ :=
    Subgroup.card_subgroup_dvd_card _
  have hunits : Nat.card Kˣ = 2 ^ m - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  rw [hunits] at hdvd
  refine Odd.of_dvd_nat ?_ hdvd
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨j, hj⟩ : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  exact ⟨j - 1, by omega⟩

theorem odd_card_center_barL [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (center (barL K k))) := by
  rw [← card_center_congr (barLEquiv K k)]
  exact odd_card_center_SL hm hK

theorem psl2_sylow_isCyclic [Finite K] {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (r : ℕ)
    (hr : r.Prime) (hr2 : r ≠ 2) [Fact r.Prime]
    (Q : Sylow r (ProjectiveSpecialLinearGroup (Fin 2) K)) :
    IsCyclic (Q : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h7 : 7 ≤ Nat.card K
  · refine CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK h7 r hr2 ?_ Q
    rw [hK]
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
  · have hm2 : m = 2 := by
      by_contra hne
      have h3 : 3 ≤ m := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
      omega
    subst hm2
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have hdvd : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) ∣
        Nat.card (SpecialLinearGroup (Fin 2) K) :=
      Subgroup.card_quotient_dvd_card (center (SpecialLinearGroup (Fin 2) K))
    rw [CFSG.GorensteinWalter.sl2_card_formula K, hK4] at hdvd
    refine CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd (fun h => ?_) Q
    have h60 : r ^ 2 ∣ 60 := h.trans (by simpa using hdvd)
    have hle : r ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h60
    have hr7 : r ≤ 7 := by nlinarith
    interval_cases r <;> first | omega | (exfalso; norm_num at hr)

theorem eq_bot_of_isPGroup_two_of_odd {G : Type*} [Group G] {Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hodd : Odd (Nat.card Z)) [Finite Z] : Z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hZ
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact Subgroup.eq_bot_of_card_eq Z hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (even_two.mul_left _))

theorem nonempty_levLift_equiv_SL2 {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {P : Type} [Group P] {θ : ↥A →* P} (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hZ : Odd (Nat.card (center ↥A))) [Finite K] {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    {S : Subgroup P} (hperf : ⁅S, S⁆ = S) (eS : SpecialLinearGroup (Fin 2) K ≃* S) :
    Nonempty (↥(levLift θ S) ≃* SpecialLinearGroup (Fin 2) K) := by
  have : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hS1 : center ↥S = ⊥ := by
    rw [← Subgroup.map_center_eq eS, center_SL2_eq_bot', Subgroup.map_bot]
  set X := ↥(levLift θ S)
  have : Group.IsPerfect X := (Subgroup.isPerfect_iff).2 (commutator_levLift hker hθ hperf)
  let e₁ : X ⧸ center X ≃* ↥S ⧸ center ↥S := levLiftQuotEquiv hker hθ hperf
  let e₂ : ↥S ⧸ center ↥S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hS1).trans QuotientGroup.quotientBot
  let e : X ⧸ center X ≃* ProjectiveSpecialLinearGroup (Fin 2) K :=
    (e₁.trans e₂).trans (eS.symm.trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K).symm)
  have h2 := CFSG.Quasithin.isPGroup_two_of_mulEquiv_cyclic_odd_sylow (center X)
    le_rfl e fun r hr hr2 _ Q => psl2_sylow_isCyclic hm hK r hr hr2 Q
  have hodd : Odd (Nat.card (center X)) := by
    refine odd_card_center_levLift hker hθ hperf hZ ?_
    rw [hS1, Subgroup.card_bot]
    exact odd_one
  have hbot := eq_bot_of_isPGroup_two_of_odd h2 hodd
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans
    ((e₁.trans e₂).trans eS.symm)⟩

end Proj

end CFSG.ComponentClassification.RankTwoClassical
