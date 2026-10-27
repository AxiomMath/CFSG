module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListFrames
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassCascadeBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

theorem twistedE6_permLattice_single (i : Fin TwistTag.E6.tag.rank) :
    permLattice TwistTag.E6.perm (Pi.single i 1) = Pi.single (TwistTag.E6.perm i) 1 :=
  permLattice_single _ i

theorem twistedE6_perm_mem_iff {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) (l : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm l ∈ J ↔ l ∈ J := by
  refine ⟨fun h => ?_, hJ l⟩
  have := hJ _ h
  rwa [twistedE6_perm_perm] at this

theorem twistedE6_eq_single_of_perm {β : Fin TwistTag.E6.tag.rank → ℤ}
    {i : Fin TwistTag.E6.tag.rank}
    (h : permLattice TwistTag.E6.perm β = Pi.single (TwistTag.E6.perm i) 1) :
    β = Pi.single i 1 := by
  have h' := congrArg (permLattice TwistTag.E6.perm) h
  rwa [permLattice_twistedE6_perm_perm, twistedE6_permLattice_single, twistedE6_perm_perm] at h'

theorem twistedE6_single_ne_single_perm {i : Fin TwistTag.E6.tag.rank}
    (hi : TwistTag.E6.perm i ≠ i) :
    (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single (TwistTag.E6.perm i) 1 := by
  intro h
  have := congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi)] at this
  exact one_ne_zero this


theorem twistedE6_perm_mem_parabolicPosRoots {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ parabolicPosRoots TwistTag.E6.tag J) :
    permLattice TwistTag.E6.perm β ∈ parabolicPosRoots TwistTag.E6.tag J := by
  obtain ⟨⟨hr, hs⟩, -, hp⟩ := hβ
  have hr' := hr.permLattice TwistTag.E6.cartan_perm
  refine ⟨⟨hr', fun l hl => ?_⟩, hr', by rw [height_permLattice]; exact hp⟩
  simp only [permLattice, Function.comp_apply, twistedE6_perm_symm_apply]
  exact hs _ fun h => hl ((twistedE6_perm_mem_iff hJ l).1 h)

theorem twistHom_mem_rootSpan_of_perm [CharP K 2] (σ : K →+* K)
    {S S' : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β)
    (hSS' : ∀ β ∈ S, permLattice TwistTag.E6.perm β ∈ S') {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootSpan TwistTag.E6.tag K S) :
    twistHom TwistTag.E6 K σ z ∈ rootSpan TwistTag.E6.tag K S' := by
  have hle : rootSpan TwistTag.E6.tag K S ≤
      (rootSpan TwistTag.E6.tag K S').comap (twistHom TwistTag.E6 K σ) := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap,
      twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ (hS β hβ)]
    exact (le_iSup₂_of_le _ (hSS' β hβ) le_rfl :
      rootSubgroup TwistTag.E6.tag K _ ≤ rootSpan TwistTag.E6.tag K S')
      (Subgroup.subset_closure ⟨σ c, rfl⟩)
  exact hle hz

theorem twistedE6_coeff_eq_zero_of_simple {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hnd : L.Nodup) (hL : ∀ α ∈ L, ∃ j, α = Pi.single j 1) (f : (Fin TwistTag.E6.tag.rank → ℤ) → K)
    (hmem : (L.map fun α => pinnedX TwistTag.E6.tag K α (f α)).prod ∈
      rootSpan TwistTag.E6.tag K {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ β ∉ L}) :
    ∀ α ∈ L, f α = 0 := by
  have hL' : ∀ α ∈ L, IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα => by
    obtain ⟨j, rfl⟩ := hL α hα
    exact ⟨isRoot_single _ j, by rw [height_single]; exact one_pos⟩
  have habs : ∀ α, IsRoot TwistTag.E6.tag α ∧ 0 < height α →
      ∀ β ∈ {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ β ∉ L}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot TwistTag.E6.tag (a • α + b • β) →
          a • α + b • β ∈ {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ β ∉ L} := by
    intro α hα β hβ a b ha hb hr
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have h2 : 2 ≤ height (a • α + b • β) := by
      rw [height_nsmul_add_nsmul]; nlinarith [hα.2, hβ.2.1]
    refine ⟨hr, by omega, fun h => ?_⟩
    obtain ⟨j, hj⟩ := hL _ h
    rw [hj, height_single] at h2
    omega
  intro α hα
  exact classDescent_coeff_eq_zero_of_mem_rootSpan (fun β hβ => ⟨hβ.1, hβ.2.1⟩) habs hnd hL' f
    hmem α hα fun h => h.2.2 hα

theorem twistedE6_sigma_eq_of_fixed [CharP K 2] (σ : K →+* K)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : TwistTag.E6.perm i = i) {c : K}
    {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \ {Pi.single i 1}))
    (hΓ : pinnedX TwistTag.E6.tag K (Pi.single i 1) c * u ∈ twistedFixedGroup TwistTag.E6 K σ) :
    σ c = c := by
  have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hΓ).2
  rw [map_mul, twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ (isRoot_single _ i),
    twistedE6_permLattice_single, hi] at hF
  have hu' : twistHom TwistTag.E6 K σ u ∈
      rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \ {Pi.single i 1}) := by
    refine twistHom_mem_rootSpan_of_perm σ (fun β hβ => hβ.1.1.1) (fun β hβ => ?_) hu
    refine ⟨twistedE6_perm_mem_parabolicPosRoots hJ hβ.1, fun h => hβ.2 ?_⟩
    rw [Set.mem_singleton_iff] at h ⊢
    exact twistedE6_eq_single_of_perm (by rw [h, hi])
  have e : pinnedX TwistTag.E6.tag K (Pi.single i 1) (c - σ c) =
      twistHom TwistTag.E6 K σ u * u⁻¹ := by
    have h1 : pinnedX TwistTag.E6.tag K (Pi.single i 1) (σ c) *
        pinnedX TwistTag.E6.tag K (Pi.single i 1) (c - σ c) =
          pinnedX TwistTag.E6.tag K (Pi.single i 1) c := by
      rw [← pinnedX_add, add_sub_cancel]
    rw [eq_mul_inv_iff_mul_eq, ← mul_left_cancel_iff (a := pinnedX TwistTag.E6.tag K
      (Pi.single i 1) (σ c)), hF, ← mul_assoc, h1]
  have hmem : ([Pi.single i 1].map fun α => pinnedX TwistTag.E6.tag K α
      ((fun _ => c - σ c) α)).prod ∈
      rootSpan TwistTag.E6.tag K {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧
        β ∉ [Pi.single i 1]} := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [e]
    refine classDescent_rootSpan_mono ?_ (mul_mem hu' (inv_mem hu))
    rintro β ⟨hβ, hβi⟩
    exact ⟨hβ.2.1, hβ.2.2, by simpa using hβi⟩
  have h0 := twistedE6_coeff_eq_zero_of_simple (List.nodup_singleton _)
    (fun α hα => ⟨i, List.mem_singleton.1 hα⟩) _ hmem _ List.mem_cons_self
  exact (sub_eq_zero.1 h0).symm

theorem twistedE6_pair_mul (i : Fin TwistTag.E6.tag.rank) (a b a' b' : K) :
    pinnedX TwistTag.E6.tag K (Pi.single i 1) a *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) b *
      (pinnedX TwistTag.E6.tag K (Pi.single i 1) a' *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) b') =
      pinnedX TwistTag.E6.tag K (Pi.single i 1) (a + a') *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (b + b') := by
  have h := (commute_pinnedX_permLattice_twistedE6 (K := K) (isRoot_single TwistTag.E6.tag i)
    a' b).eq
  rw [twistedE6_permLattice_single] at h
  rw [pinnedX_add, pinnedX_add,
    show pinnedX TwistTag.E6.tag K (Pi.single i 1) a *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) b *
      (pinnedX TwistTag.E6.tag K (Pi.single i 1) a' *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) b') =
      pinnedX TwistTag.E6.tag K (Pi.single i 1) a *
        (pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) b *
          pinnedX TwistTag.E6.tag K (Pi.single i 1) a') *
        pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) b' by group, ← h]
  group

theorem twistedE6_eq_sigma_of_pair [CharP K 2] (σ : K →+* K)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : TwistTag.E6.perm i ≠ i) {c c' : K}
    {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}))
    (hΓ : pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
      pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) c' * u ∈
        twistedFixedGroup TwistTag.E6 K σ) :
    c' = σ c := by
  have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hΓ).2
  rw [map_mul, map_mul, twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ
      (isRoot_single _ i),
    twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ (isRoot_single _ _),
    twistedE6_permLattice_single, twistedE6_permLattice_single, twistedE6_perm_perm] at hF
  have hcomm := (commute_pinnedX_permLattice_twistedE6 (K := K) (isRoot_single TwistTag.E6.tag i)
    (σ c') (σ c)).eq
  rw [twistedE6_permLattice_single] at hcomm
  rw [← hcomm] at hF
  have hu' : twistHom TwistTag.E6 K σ u ∈ rootSpan TwistTag.E6.tag K
      (parabolicPosRoots TwistTag.E6.tag J \
        {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}) := by
    refine twistHom_mem_rootSpan_of_perm σ (fun β hβ => hβ.1.1.1) (fun β hβ => ?_) hu
    refine ⟨twistedE6_perm_mem_parabolicPosRoots hJ hβ.1, fun h => hβ.2 ?_⟩
    rcases h with h | h
    · right
      have h' := congrArg (permLattice TwistTag.E6.perm) h
      rw [permLattice_twistedE6_perm_perm, twistedE6_permLattice_single] at h'
      exact h'
    · left
      exact twistedE6_eq_single_of_perm (by rw [h])
  have e : pinnedX TwistTag.E6.tag K (Pi.single i 1) (c - σ c') *
      pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (c' - σ c) =
      twistHom TwistTag.E6 K σ u * u⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← mul_left_cancel_iff (a := pinnedX TwistTag.E6.tag K
      (Pi.single i 1) (σ c') * pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c)),
      hF, ← mul_assoc, twistedE6_pair_mul, add_sub_cancel, add_sub_cancel]
  set f : (Fin TwistTag.E6.tag.rank → ℤ) → K := fun β =>
    if β = Pi.single i 1 then c - σ c' else c' - σ c with hf
  have hne := twistedE6_single_ne_single_perm hi
  have hmem : ([Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1].map fun α =>
      pinnedX TwistTag.E6.tag K α (f α)).prod ∈
      rootSpan TwistTag.E6.tag K {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧
        β ∉ [Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1]} := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hf,
      hne.symm, ↓reduceIte]
    rw [e]
    refine classDescent_rootSpan_mono ?_ (mul_mem hu' (inv_mem hu))
    rintro β ⟨hβ, hβi⟩
    refine ⟨hβ.2.1, hβ.2.2, fun h => hβi ?_⟩
    simpa using h
  have h0 := twistedE6_coeff_eq_zero_of_simple
    (List.nodup_cons.2 ⟨by simpa using hne, List.nodup_singleton _⟩)
    (fun α hα => by
      rcases List.mem_pair.1 hα with rfl | rfl
      · exact ⟨i, rfl⟩
      · exact ⟨_, rfl⟩) f hmem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [hf, hne.symm, ↓reduceIte] at h0
  exact sub_eq_zero.1 h0

theorem twistedE6_exists_pinnedX_mul_of_closed {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ S)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ S) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSpan TwistTag.E6.tag K S) :
    ∃ c : K, ∃ u ∈ rootSpan TwistTag.E6.tag K (S \ {β}), x = pinnedX TwistTag.E6.tag K β c * u := by
  obtain ⟨k, γ, hγ⟩ := ((finite_setOf_isRoot TwistTag.E6.tag).subset
    fun δ (hδ : δ ∈ S \ {β}) => (hS δ hδ.1).1).fin_embedding
  set e : Fin (k + 1) → Fin TwistTag.E6.tag.rank → ℤ := Fin.cons β γ with he
  have heinj : Function.Injective e := Fin.cons_injective_iff.2
    ⟨fun h => by
      rw [hγ] at h
      exact h.2 rfl, γ.injective⟩
  have herange : Set.range e = S := by
    rw [he, Fin.range_cons, hγ, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hβ]
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hS hclosed e heinj herange).surjOn hx
  refine ⟨d 0, (List.ofFn fun l => pinnedX TwistTag.E6.tag K (γ l) (d l.succ)).prod, ?_, ?_⟩
  · refine list_prod_mem fun y hy => ?_
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hy
    have hl : γ l ∈ S \ {β} := hγ ▸ Set.mem_range_self l
    exact (le_iSup₂_of_le (γ l) hl le_rfl : rootSubgroup TwistTag.E6.tag K (γ l) ≤ _)
      (Subgroup.subset_closure ⟨d l.succ, rfl⟩)
  · rw [← hd]
    simp only [List.ofFn_succ, List.prod_cons, he, Fin.cons_zero, Fin.cons_succ]

theorem twistedE6_parabolic_diff_closed (J : Set (Fin TwistTag.E6.tag.rank))
    {T : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hT : ∀ β ∈ T, height β = 1) :
    ∀ α ∈ parabolicPosRoots TwistTag.E6.tag J \ T, ∀ β ∈ parabolicPosRoots TwistTag.E6.tag J \ T,
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • α + b • β) →
        a • α + b • β ∈ parabolicPosRoots TwistTag.E6.tag J \ T := by
  intro α hα β hβ a b ha hb hr
  refine ⟨classDescent_parabolicPosRoots_closed J α hα.1 β hβ.1 a b ha hb hr, fun h => ?_⟩
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have h2 : 2 ≤ height (a • α + b • β) := by
    rw [height_nsmul_add_nsmul]; nlinarith [hα.1.2.2, hβ.1.2.2]
  have := hT _ h
  omega

theorem twistedE6RelWeyl_conj_mem_rootSpan [CharP K 2] (ω : List (Fin TwistTag.E6.foldedTag.rank))
    {S S' : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β)
    (hSS' : ∀ β ∈ S, twistedE6RelAct ω β ∈ S') {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootSpan TwistTag.E6.tag K S) :
    twistedE6RelWeyl K ω * z * (twistedE6RelWeyl K ω)⁻¹ ∈ rootSpan TwistTag.E6.tag K S' := by
  have hle : rootSpan TwistTag.E6.tag K S ≤ (rootSpan TwistTag.E6.tag K S').comap
      (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      twistedE6RelWeyl_conj_pinnedX ω (hS β hβ) c]
    exact (le_iSup₂_of_le _ (hSS' β hβ) le_rfl :
      rootSubgroup TwistTag.E6.tag K _ ≤ rootSpan TwistTag.E6.tag K S')
      (Subgroup.subset_closure ⟨c, rfl⟩)
  exact hle hz

theorem twistedE6RelWeyl_mem_cascadeConjGroup {J : Set (Fin TwistTag.E6.tag.rank)}
    {ω : List (Fin TwistTag.E6.foldedTag.rank)}
    (hω : ∀ a ∈ ω, ∀ j ∈ TwistTag.E6.orbitWord a, j ∈ J) :
    twistedE6RelWeyl K ω ∈ cascadeConjGroup TwistTag.E6.tag K J :=
  prod_weylElt_mem_cascadeConjGroup fun j hj => by
    obtain ⟨a, ha, hj⟩ := List.mem_flatMap.1 hj
    exact hω a ha j hj

theorem twistedE6_commute_of_iform_eq_zero {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (h0 : iform α β = 0)
    (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) := by
  have hE6 : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  have hαα := cascade_iform_self hE6 hα
  have hββ := cascade_iform_self hE6 hβ
  refine commute_pinnedX_of_not_isRoot_add_E6 hα hβ (fun h => ?_) (fun h => ?_) (fun h => ?_) c d
  · rw [h, hββ] at h0
    exact two_ne_zero h0
  · rw [h, iform_neg_left, hββ] at h0
    norm_num at h0
  · have := cascade_iform_self hE6 h
    rw [iform_add_left, iform_add_right, iform_add_right, hαα, hββ, h0, iform_comm, h0] at this
    norm_num at this

@[expose] def TwistedE6FrameIn (P : Set (Fin TwistTag.E6.tag.rank → ℤ))
    (R : List (Fin TwistTag.E6.tag.rank → ℤ)) : Prop :=
  (R.flatMap twistedE6Unit).Nodup ∧
    (∀ β ∈ R.flatMap twistedE6Unit, IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ β ∈ P) ∧
    (R.flatMap twistedE6Unit).Pairwise (fun β β' => iform β β' = 0)

variable (K) in
@[expose] def TwistedE6LevelRes (σ : K →+* K) (G : Subgroup (ModGL TwistTag.E6.tag K))
    (P : Set (Fin TwistTag.E6.tag.rank → ℤ)) (z : ModGL TwistTag.E6.tag K) : Prop :=
  ∃ g ∈ G, g ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
    ∃ R : List (Fin TwistTag.E6.tag.rank → ℤ), TwistedE6FrameIn P R ∧
      ∃ c : (Fin TwistTag.E6.tag.rank → ℤ) → K,
        (∀ γ ∈ R, c γ ≠ 0 ∧ (permLattice TwistTag.E6.perm γ = γ → σ (c γ) = c γ)) ∧
          g * z * g⁻¹ = (R.map fun γ => twistedE6RelX K σ γ (c γ)).prod

theorem twistedE6LevelRes_one (σ : K →+* K) (G : Subgroup (ModGL TwistTag.E6.tag K))
    (P : Set (Fin TwistTag.E6.tag.rank → ℤ)) : TwistedE6LevelRes K σ G P 1 :=
  ⟨1, one_mem _, one_mem _, [], ⟨List.nodup_nil, by simp, List.Pairwise.nil⟩, fun _ => 0,
    by simp, by simp⟩

theorem TwistedE6LevelRes.mono {σ : K →+* K} {G G' : Subgroup (ModGL TwistTag.E6.tag K)}
    {P P' : Set (Fin TwistTag.E6.tag.rank → ℤ)} {z : ModGL TwistTag.E6.tag K}
    (h : TwistedE6LevelRes K σ G P z) (hG : G ≤ G') (hP : P ⊆ P') :
    TwistedE6LevelRes K σ G' P' z := by
  obtain ⟨g, hg, hgC, R, ⟨hnd, hpos, hpw⟩, c, hc, he⟩ := h
  exact ⟨g, hG hg, hgC, R, ⟨hnd, fun β hβ => ⟨(hpos β hβ).1, (hpos β hβ).2.1,
    hP (hpos β hβ).2.2⟩, hpw⟩, c, hc, he⟩

theorem twistedE6LevelRes_cons {σ : K →+* K} {G G' : Subgroup (ModGL TwistTag.E6.tag K)}
    {P P' : Set (Fin TwistTag.E6.tag.rank → ℤ)} {θ : Fin TwistTag.E6.tag.rank → ℤ} {c₀ : K}
    (hc₀ : c₀ ≠ 0) (hc₀σ : permLattice TwistTag.E6.perm θ = θ → σ c₀ = c₀)
    (hθnd : (twistedE6Unit θ).Nodup)
    (hθP : ∀ β ∈ twistedE6Unit θ, IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ β ∈ P ∧ β ∉ P')
    (hθpw : (twistedE6Unit θ).Pairwise (fun β β' => iform β β' = 0))
    (hθP' : ∀ β ∈ twistedE6Unit θ, ∀ δ ∈ P', iform β δ = 0) (hP' : P' ⊆ P) (hG' : G' ≤ G)
    (hcen : ∀ g ∈ G', g * twistedE6RelX K σ θ c₀ = twistedE6RelX K σ θ c₀ * g)
    {ℓ z g₀ : ModGL TwistTag.E6.tag K} (hg₀ : g₀ ∈ G)
    (hg₀C : g₀ ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (he : g₀ * ℓ * g₀⁻¹ = twistedE6RelX K σ θ c₀ * z) (hz : TwistedE6LevelRes K σ G' P' z) :
    TwistedE6LevelRes K σ G P ℓ := by
  obtain ⟨g', hg', hg'C, R', ⟨hnd', hpos', hpw'⟩, c', hc', he'⟩ := hz
  have hmemU : θ ∈ twistedE6Unit θ := by
    by_cases h : permLattice TwistTag.E6.perm θ = θ <;> simp [twistedE6Unit, h]
  have hθR' : θ ∉ R' := fun h => (hθP θ hmemU).2.2.2
    (hpos' θ (List.mem_flatMap.2 ⟨θ, h, hmemU⟩)).2.2
  refine ⟨g' * g₀, mul_mem (hG' hg') hg₀, mul_mem hg'C hg₀C, θ :: R', ⟨?_, ?_, ?_⟩,
    Function.update c' θ c₀, fun γ hγ => ?_, ?_⟩
  · rw [List.flatMap_cons]
    refine List.nodup_append.2 ⟨hθnd, hnd', fun a ha b hb hab => ?_⟩
    subst hab
    exact (hθP a ha).2.2.2 (hpos' a hb).2.2
  · intro β hβ
    rw [List.flatMap_cons, List.mem_append] at hβ
    rcases hβ with hβ | hβ
    · exact ⟨(hθP β hβ).1, (hθP β hβ).2.1, (hθP β hβ).2.2.1⟩
    · exact ⟨(hpos' β hβ).1, (hpos' β hβ).2.1, hP' (hpos' β hβ).2.2⟩
  · rw [List.flatMap_cons]
    exact List.pairwise_append.2 ⟨hθpw, hpw', fun a ha b hb => hθP' a ha b (hpos' b hb).2.2⟩
  · rcases List.mem_cons.1 hγ with rfl | hγ
    · rw [Function.update_self]
      exact ⟨hc₀, hc₀σ⟩
    · have hne : γ ≠ θ := fun h => hθR' (h ▸ hγ)
      rw [Function.update_of_ne hne]
      exact hc' γ hγ
  · have hmap : (R'.map fun γ => twistedE6RelX K σ γ (Function.update c' θ c₀ γ)) =
        R'.map fun γ => twistedE6RelX K σ γ (c' γ) :=
      List.map_congr_left fun γ hγ => by
        have hne : γ ≠ θ := fun h => hθR' (h ▸ hγ)
        rw [Function.update_of_ne hne]
    rw [List.map_cons, List.prod_cons, Function.update_self, hmap, ← he']
    have hc := hcen g' hg'
    calc g' * g₀ * ℓ * (g' * g₀)⁻¹ = g' * (g₀ * ℓ * g₀⁻¹) * g'⁻¹ := by group
      _ = g' * twistedE6RelX K σ θ c₀ * z * g'⁻¹ := by rw [he]; group
      _ = twistedE6RelX K σ θ c₀ * (g' * z * g'⁻¹) := by rw [hc]; group

end CFSG.SeitzReduction
