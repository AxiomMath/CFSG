module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassCascade
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4Torus
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
open scoped commutatorElement

theorem f4Desc_lookup_eq_nil_of_iform :
    ∀ p q : Fin 48, 24 ≤ (p : ℕ) → 24 ≤ (q : ℕ) →
    iform (orbitCertRoot .F4 p) (orbitCertRoot .F4 q) = 0 →
    (f4OddCommutatorFactors.lookup ((p : ℕ), (q : ℕ))).getD [] = [] := by
  decide +kernel

@[expose] def f4DescFrameOK (J : List (Fin Tag.F4.rank)) (F : List ℕ) : Bool :=
  F.all fun p => decide (24 ≤ p ∧ p ≤ 47) &&
    J.all fun j => cascPairL .F4 j (orbitCertRoot .F4 p) == 0

@[expose] def f4DescDomCheck (J : List (Fin Tag.F4.rank)) (p : ℕ) : Bool :=
  (List.range 48).all fun q => !decide (24 ≤ q) || !cascCandB .F4 J (orbitCertRoot .F4 q) ||
    !decide (iform (orbitCertRoot .F4 q) (orbitCertRoot .F4 q) = 4) || q == p

theorem f4DescFrameOK_sound {J : List (Fin Tag.F4.rank)} {F : List ℕ}
    (h : f4DescFrameOK J F = true) :
    ∀ p ∈ F, (24 ≤ p ∧ p ≤ 47) ∧ ∀ j ∈ J, classKillPair j (orbitCertRoot .F4 p) = 0 := by
  intro p hp
  simp only [f4DescFrameOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h p hp
  exact ⟨h1, fun j hj => by rw [← cascPairL_eq]; exact h2 j hj⟩

variable {K : Type} [Field K]

theorem f4Desc_eq_one_of_mul_self [CharP K 2] {ε : K} (h : ε * ε = 1) : ε = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h' : (ε + 1) * (ε + 1) = 0 := by linear_combination h + (ε + 1) * h2
  rw [eq_neg_of_add_eq_zero_left (mul_self_eq_zero.1 h'), CharTwo.neg_eq]

section Basic


theorem f4Desc_conj_eq_of_mem_rootSpan {S : Set (Fin Tag.F4.rank → ℤ)} {h : ModGL .F4 K}
    (H : ∀ δ ∈ S, ∀ e : K, h * pinnedX .F4 K δ e * h⁻¹ = pinnedX .F4 K δ e) {z : ModGL .F4 K}
    (hz : z ∈ rootSpan .F4 K S) : h * z * h⁻¹ = z := by
  have hle : rootSpan .F4 K S ≤ Subgroup.centralizer {h} := by
    refine iSup₂_le fun δ hδ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨e, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc pinnedX .F4 K δ e * h = h * pinnedX .F4 K δ e * h⁻¹ * h := by rw [H δ hδ e]
      _ = h * pinnedX .F4 K δ e := by group
  have hzh := Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
  rw [← hzh]
  group

variable (K) in
@[expose] noncomputable def f4DescProd (F : List ℕ) : ModGL .F4 K :=
  (F.map fun p => f4x K p 1).prod

theorem f4DescProd_append (F F' : List ℕ) :
    f4DescProd K (F ++ F') = f4DescProd K F * f4DescProd K F' := by
  simp [f4DescProd]

theorem f4DescProd_singleton (p : ℕ) : f4DescProd K [p] = f4x K p 1 := by
  simp [f4DescProd]

theorem f4DescProd_mem_adjointGroup (F : List ℕ) : f4DescProd K F ∈ adjointGroup .F4 K :=
  list_prod_mem fun x hx => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_adjointGroup _ _

theorem f4DescProd_commute {g : ModGL .F4 K} (F : List ℕ)
    (h : ∀ p ∈ F, g * f4x K p 1 = f4x K p 1 * g) : g * f4DescProd K F = f4DescProd K F * g := by
  induction F with
  | nil => simp [f4DescProd]
  | cons p F ih =>
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    simp only [f4DescProd, List.map_cons, List.prod_cons] at ih' ⊢
    rw [← mul_assoc, hp, mul_assoc, ih', mul_assoc]

theorem f4Desc_single_mem_parabolicPosRoots {τ : Tag} {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∈ J) : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicPosRoots τ J :=
  ⟨⟨isRoot_single τ i, fun l hl => Pi.single_eq_of_ne (by rintro rfl; exact hl hi) 1⟩,
    isRoot_single τ i, by rw [height_single]; exact one_pos⟩

theorem f4Desc_iform_single_long {i : Fin Tag.F4.rank} (hlong : i ∈ classKillLongSimple .F4) :
    iform (Pi.single i 1 : Fin Tag.F4.rank → ℤ) (Pi.single i 1) = 4 := by
  rw [iform_single_single]
  revert i
  decide

end Basic

section CL4


theorem f4Desc_exists_word_dominant {τ : Tag} (J : Set (Fin τ.rank)) (N : ℕ) :
    ∀ γ ∈ parabolicPosRoots τ J, (∀ α, IsRoot τ α → height α ≤ height γ + N) →
      ∀ (c : K) (z : ModGL τ K), z ∈ rootSpan τ K (cascPerp τ J γ) →
        ∃ ω : List (Fin τ.rank), (∀ j ∈ ω, j ∈ J) ∧ ∃ γ' ∈ parabolicPosRoots τ J,
          (∀ j ∈ J, 0 ≤ classKillPair j γ') ∧ iform γ' γ' = iform γ γ ∧ ∃ ε : K, ε * ε = 1 ∧
            ∃ z' ∈ rootSpan τ K (cascPerp τ J γ'),
              (ω.map fun j => weylElt τ K j 1).prod * (pinnedX τ K γ c * z) *
                  ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ = pinnedX τ K γ' (ε * c) * z' := by
  induction N with
  | zero =>
    intro γ hγ hN c z hz
    refine ⟨[], by simp, γ, hγ, fun j hj => ?_, rfl, 1, one_mul 1, z, hz, by simp⟩
    by_contra hneg
    push Not at hneg
    have h1 := (cascade_reflect_mem_of_neg hj hγ hneg).2
    have h2 := hN _ (IsRoot.reflect j hγ.1.1)
    push_cast at h2
    linarith
  | succ N ih =>
    intro γ hγ hN c z hz
    by_cases hdom : ∀ j ∈ J, 0 ≤ classKillPair j γ
    · exact ⟨[], by simp, γ, hγ, hdom, rfl, 1, one_mul 1, z, hz, by simp⟩
    push Not at hdom
    obtain ⟨j, hj, hneg⟩ := hdom
    obtain ⟨hγ₁, hlt⟩ := cascade_reflect_mem_of_neg hj hγ hneg
    have hN₁ : ∀ α, IsRoot τ α → height α ≤ height (reflect τ j γ) + N := by
      intro α hα
      have := hN α hα
      push_cast at this ⊢
      linarith
    obtain ⟨ε₁, hε₁, hx⟩ := weylElt_mul_pinnedX_mul_inv K j hγ.1.1
    have hz₁ := cascade_conj_weylElt_mem_rootSpan (fun α hα => hα.1.1.1) j
      (fun α hα => cascade_reflect_mem_cascPerp hj hneg.ne hα) hz
    obtain ⟨ω, hω, γ', hγ', hdom', hlen, ε, hε, z', hz', he⟩ := ih _ hγ₁ hN₁ (ε₁ * c) _ hz₁
    refine ⟨ω ++ [j], fun j' hj' => ?_, γ', hγ', hdom', by rw [hlen, iform_reflect], ε * ε₁, ?_,
      z', hz', ?_⟩
    · rcases List.mem_append.1 hj' with h | h
      · exact hω j' h
      · rw [List.mem_singleton.1 h]
        exact hj
    · linear_combination (ε₁ * ε₁) * hε + hε₁
    · rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
        mul_assoc ε, ← he, ← hx c]
      group

theorem f4Desc_exists_prod_weylElt_conj_eq_dominant {τ : Tag} (J : Set (Fin τ.rank))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ parabolicPosRoots τ J) (c : K) {z : ModGL τ K}
    (hz : z ∈ rootSpan τ K (cascPerp τ J γ)) :
    ∃ ω : List (Fin τ.rank), (∀ j ∈ ω, j ∈ J) ∧ ∃ γ' ∈ parabolicPosRoots τ J,
      (∀ j ∈ J, 0 ≤ classKillPair j γ') ∧ iform γ' γ' = iform γ γ ∧ ∃ ε : K, ε * ε = 1 ∧
        ∃ z' ∈ rootSpan τ K (cascPerp τ J γ'),
          (ω.map fun j => weylElt τ K j 1).prod * (pinnedX τ K γ c * z) *
              ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ = pinnedX τ K γ' (ε * c) * z' := by
  obtain ⟨M, hM⟩ := cascade_exists_height_bound τ
  exact f4Desc_exists_word_dominant J M γ hγ (fun α hα => by linarith [hM α hα, hγ.2.2]) c z hz

end CL4


theorem f4DescDomCheck_sound {J : List (Fin Tag.F4.rank)} {p : ℕ} (h : f4DescDomCheck J p = true)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ parabolicPosRoots .F4 {j | j ∈ J})
    (hdom : ∀ j ∈ J, 0 ≤ classKillPair j γ) (hlen : iform γ γ = 4) :
    γ = orbitCertRoot .F4 p := by
  obtain ⟨q, hq, hq', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 γ).1 hγ.2
  have hc := cascCandB_eq_true hγ hdom
  simp only [f4DescDomCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
  rcases h q (by omega) with ((h1 | h1) | h1) | h1
  · exact absurd hq h1
  · rw [hc] at h1
    exact absurd h1 (by decide)
  · exact absurd hlen h1
  · rw [h1]

theorem f4Desc_commute_of_iform_eq_zero [CharP K 2] {γ δ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot .F4 γ ∧ 0 < height γ) (hδ : IsRoot .F4 δ ∧ 0 < height δ) (h0 : iform γ δ = 0)
    (c d : K) : pinnedX .F4 K γ c * pinnedX .F4 K δ d = pinnedX .F4 K δ d * pinnedX .F4 K γ c := by
  obtain ⟨p, hp, hp', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 γ).1 hγ
  obtain ⟨q, hq, hq', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 δ).1 hδ
  have hpq : p ≠ q := by
    rintro rfl
    have := iform_self_pos hγ.1.ne_zero
    omega
  have h := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K p q hp hp' hq hq' hpq c d
  have hl : (f4OddCommutatorFactors.lookup (p, q)).getD [] = [] :=
    f4Desc_lookup_eq_nil_of_iform ⟨p, by omega⟩ ⟨q, by omega⟩ hp hq h0
  rw [hl, List.map_nil, List.prod_nil] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem f4Desc_cascadeConjGroup_le_centralizer [CharP K 2] {J : Set (Fin Tag.F4.rank)}
    {θ : Fin Tag.F4.rank → ℤ} (hθ : IsRoot .F4 θ) (hθp : 0 < height θ)
    (hθJ : ∀ j ∈ J, classKillPair j θ = 0) (c : K) :
    cascadeConjGroup .F4 K J ≤ Subgroup.centralizer {pinnedX .F4 K θ c} := by
  refine sup_le (iSup₂_le fun δ hδ => (Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (f4Desc_commute_of_iform_eq_zero ⟨hθ, hθp⟩ hδ.2
      (cascade_iform_eq_zero_of_mem hθJ hδ) c d).symm
  · rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h := cascade_weylElt_conj_pinnedX hθ (hθJ j hj) c
    calc weylElt .F4 K j 1 * pinnedX .F4 K θ c
        = weylElt .F4 K j 1 * pinnedX .F4 K θ c * (weylElt .F4 K j 1)⁻¹ * weylElt .F4 K j 1 := by
          group
      _ = pinnedX .F4 K θ c * weylElt .F4 K j 1 := by rw [h]

theorem f4DescProd_commute_of_mem_cascadeConjGroup [CharP K 2] {J : List (Fin Tag.F4.rank)}
    {F : List ℕ} (hF : f4DescFrameOK J F = true) {g : ModGL .F4 K}
    (hg : g ∈ cascadeConjGroup .F4 K {j | j ∈ J}) : g * f4DescProd K F = f4DescProd K F * g := by
  refine f4DescProd_commute F fun p hp => ?_
  obtain ⟨hp24, hpJ⟩ := f4DescFrameOK_sound hF p hp
  obtain ⟨hr, hr'⟩ := f4_isRoot_pos hp24
  exact Subgroup.mem_centralizer_singleton_iff.1
    (f4Desc_cascadeConjGroup_le_centralizer hr hr' (fun j hj => hpJ j hj) 1 hg)

theorem f4Desc_exists_torus_conj [Finite K] [CharP K 2] {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot .F4 γ) {c : K} (hc : c ≠ 0) :
    ∃ h ∈ adjointGroup .F4 K, h * pinnedX .F4 K γ c * h⁻¹ = pinnedX .F4 K γ 1 ∧
      ∀ δ, IsRoot .F4 δ → iform γ δ = 0 → ∀ e : K,
        h * pinnedX .F4 K δ e * h⁻¹ = pinnedX .F4 K δ e := by
  obtain ⟨h, hC, -, hfix, he⟩ := exists_torus_conj_frame_prod noG2_F4 (F := [γ])
    (by simpa using hγ) (List.pairwise_singleton _ _) (fun _ => c) (by simpa using hc)
  refine ⟨h, hC, by simpa using he, fun δ hδ h0 e => hfix δ hδ (by simpa using h0) e⟩

theorem f4Desc_frameStep [Finite K] [CharP K 2] (J : List (Fin Tag.F4.rank)) (F : List ℕ)
    (hF : f4DescFrameOK J F = true) {i : Fin Tag.F4.rank} (hi : i ∈ J)
    (hlong : i ∈ classKillLongSimple .F4) {c : K} (hc : c ≠ 0) {u : ModGL .F4 K}
    (hu : u ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J} \ {Pi.single i 1}))
    (h2 : (pinnedX .F4 K (Pi.single i 1) c * u) ^ 2 = 1) :
    ∃ g ∈ adjointGroup .F4 K, ∃ γ ∈ parabolicPosRoots .F4 {j | j ∈ J},
      (∀ j ∈ J, 0 ≤ classKillPair j γ) ∧ iform γ γ = 4 ∧
        ∃ z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ cascNextL .F4 J γ}), z ^ 2 = 1 ∧
          g * (f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u)) * g⁻¹ =
            f4DescProd K F * pinnedX .F4 K γ 1 * z := by
  obtain ⟨p, hp, u'', hu'', -, he₂⟩ := exists_conj_eq_mul_of_classKillPerp_longSimple
    {j | j ∈ J} hi hlong hc hu h2
  rw [classKillPerp_eq_cascPerp] at hu''
  obtain ⟨ω, hω, γ, hγ, hdom, hlen, ε, hε, z, hz, he₃⟩ :=
    f4Desc_exists_prod_weylElt_conj_eq_dominant {j | j ∈ J}
      (f4Desc_single_mem_parabolicPosRoots (J := {j | j ∈ J}) hi) c hu''
  rw [f4Desc_eq_one_of_mul_self hε, one_mul] at he₃
  rw [f4Desc_iform_single_long hlong] at hlen
  set P := (ω.map fun j => weylElt .F4 K j 1).prod with hP
  obtain ⟨h, hhC, hh1, hhfix⟩ := f4Desc_exists_torus_conj (K := K) hγ.2.1 hc
  have hzperp : ∀ δ ∈ cascPerp .F4 {j | j ∈ J} γ, ∀ e : K,
      h * pinnedX .F4 K δ e * h⁻¹ = pinnedX .F4 K δ e :=
    fun δ hδ e => hhfix δ hδ.1.2.1 hδ.2 e
  have hzfix : h * z * h⁻¹ = z := f4Desc_conj_eq_of_mem_rootSpan hzperp hz
  have hFfix : h * f4DescProd K F * h⁻¹ = f4DescProd K F := by
    have hc' : h * f4DescProd K F = f4DescProd K F * h := by
      refine f4DescProd_commute F fun q hq => ?_
      obtain ⟨hq24, hqJ⟩ := f4DescFrameOK_sound hF q hq
      have h0 : iform γ (orbitCertRoot .F4 q) = 0 := by
        rw [iform_comm]
        exact cascade_iform_eq_zero_of_mem (fun j hj => hqJ j hj) hγ
      have := hhfix _ (f4_isRoot_pos hq24).1 h0 1
      calc h * f4x K q 1 = h * f4x K q 1 * h⁻¹ * h := by group
        _ = f4x K q 1 * h := by rw [f4x, this]
    rw [hc']
    group
  have hzJ' : z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ cascNextL .F4 J γ}) := by
    rw [setOf_mem_cascNextL]
    exact classDescent_rootSpan_mono (cascPerp_subset_of_dominant hdom) hz
  have hcomm : pinnedX .F4 K γ c * z = z * pinnedX .F4 K γ c := by
    have hle : rootSpan .F4 K (cascPerp .F4 {j | j ∈ J} γ) ≤
        Subgroup.centralizer {pinnedX .F4 K γ c} := by
      refine iSup₂_le fun δ hδ => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨e, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (f4Desc_commute_of_iform_eq_zero hγ.2 hδ.1.2 hδ.2 c e).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm
  have hconj : pinnedX .F4 K γ c * z =
      (P * p) * (pinnedX .F4 K (Pi.single i 1) c * u) * (P * p)⁻¹ := by
    rw [← he₃, ← he₂]
    group
  have hz2 : z ^ 2 = 1 := by
    have hx2 : (pinnedX .F4 K γ c * z) ^ 2 = 1 := by
      rw [hconj, conj_pow, h2, mul_one, mul_inv_cancel]
    have hxx := classKill_pinnedX_mul_self γ c
    calc z ^ 2 = pinnedX .F4 K γ c * pinnedX .F4 K γ c * (z * z) := by rw [hxx, one_mul, sq]
      _ = pinnedX .F4 K γ c * (z * pinnedX .F4 K γ c) * z := by rw [← hcomm]; group
      _ = (pinnedX .F4 K γ c * z) ^ 2 := by rw [sq]; group
      _ = 1 := hx2
  have hPg : P ∈ cascadeConjGroup .F4 K {j | j ∈ J} := prod_weylElt_mem_cascadeConjGroup hω
  have hpg : p ∈ cascadeConjGroup .F4 K {j | j ∈ J} :=
    rootSpan_le_cascadeConjGroup _ (classDescent_rootSpan_mono Set.sdiff_subset hp)
  have hPpC : P * p ∈ adjointGroup .F4 K :=
    cascadeConjGroup_le_adjointGroup _ (mul_mem hPg hpg)
  have hPpF : (P * p) * f4DescProd K F = f4DescProd K F * (P * p) :=
    f4DescProd_commute_of_mem_cascadeConjGroup hF (mul_mem hPg hpg)
  refine ⟨h * (P * p), mul_mem hhC hPpC, γ, hγ, hdom, hlen, z, hzJ', hz2, ?_⟩
  calc h * (P * p) * (f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u)) * (h * (P * p))⁻¹
      = h * ((P * p) * f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u) * (P * p)⁻¹) *
          h⁻¹ := by group
    _ = h * (f4DescProd K F * ((P * p) * (pinnedX .F4 K (Pi.single i 1) c * u) * (P * p)⁻¹)) *
          h⁻¹ := by rw [hPpF]; group
    _ = h * (f4DescProd K F * (pinnedX .F4 K γ c * z)) * h⁻¹ := by rw [← hconj]
    _ = (h * f4DescProd K F * h⁻¹) * (h * pinnedX .F4 K γ c * h⁻¹) * (h * z * h⁻¹) := by group
    _ = f4DescProd K F * pinnedX .F4 K γ 1 * z := by rw [hFfix, hh1, hzfix]

end CFSG.SeitzReduction
