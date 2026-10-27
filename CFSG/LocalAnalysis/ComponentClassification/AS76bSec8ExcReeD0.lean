module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcD0Gen
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeClass
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeRankOne

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam weylOne_conj_fam weylTwo_conj_fam
  weylCheck1 weylCheck2)
open CFSG.LieType.Ree.LargeReeCover (f4i)

@[expose] def vecEq (u v : Fin F4.tag.rank → ℤ) : Bool :=
  (List.finRange 4).all fun k => u k == v k

theorem eq_of_vecEq {u v : Fin F4.tag.rank → ℤ} (h : vecEq u v = true) : u = v := by
  funext k
  simp only [vecEq, List.all_eq_true, beq_iff_eq] at h
  exact h k (List.mem_finRange k)

@[expose] def sRoot (r : ℕ) (ε : Bool) : Fin F4.tag.rank → ℤ :=
  if ε then -orbitCertRoot F4.tag r else orbitCertRoot F4.tag r

@[expose] def signCheck (i j : ℕ) (ωi ωj : List (Fin F4.tag.rank)) : Bool :=
  Nat.ble 24 i && Nat.ble i 47 && Nat.ble 24 j && Nat.ble j 47 && !(i == j) &&
    (commFactors i j).isEmpty &&
    vecEq (ωi.foldr (reflect F4.tag) (sRoot i true)) (sRoot i false) &&
    vecEq (ωi.foldr (reflect F4.tag) (sRoot j false)) (sRoot j false) &&
    vecEq (ωi.foldr (reflect F4.tag) (sRoot j true)) (sRoot j true) &&
    vecEq (ωj.foldr (reflect F4.tag) (sRoot j true)) (sRoot j false) &&
    vecEq (ωj.foldr (reflect F4.tag) (sRoot i false)) (sRoot i false)

@[expose] def wordG : List (Fin F4.tag.rank) :=
  F4.fixedOrbitWord ⟨1, by decide⟩ ++ F4.fixedOrbitWord ⟨0, by decide⟩ ++
    F4.fixedOrbitWord ⟨1, by decide⟩

@[expose] def wordN : List (Fin F4.tag.rank) :=
  F4.fixedOrbitWord ⟨0, by decide⟩ ++ F4.fixedOrbitWord ⟨1, by decide⟩ ++
    F4.fixedOrbitWord ⟨0, by decide⟩

@[expose] def wordT1 (r : ℕ) : List (Fin F4.tag.rank) :=
  if r = 24 then [f4i 3] else [f4i 0]

@[expose] def wordT2 (r : ℕ) : List (Fin F4.tag.rank) :=
  if r = 41 then wordG ++ [f4i 3] ++ wordG.reverse else wordG ++ [f4i 0] ++ wordG.reverse

@[expose] def wordZ1 (r : ℕ) : List (Fin F4.tag.rank) :=
  if r = 25 then [f4i 2] else if r = 27 then [f4i 1] else if r = 28 then [f4i 1, f4i 2, f4i 1]
    else [f4i 2, f4i 1, f4i 2]

@[expose] def wordZ2 (r : ℕ) : List (Fin F4.tag.rank) :=
  wordN ++ (if r = 32 then [f4i 1] else if r = 35 then [f4i 2]
    else if r = 44 then [f4i 1, f4i 2, f4i 1] else [f4i 2, f4i 1, f4i 2]) ++ wordN.reverse

theorem signCheck_t :
    ∀ i ∈ [24, 33], ∀ j ∈ [41, 45], signCheck i j (wordT1 i) (wordT2 j) = true := by
  decide +kernel

theorem signCheck_z : ∀ i ∈ [25, 27, 28, 30], ∀ j ∈ [32, 35, 44, 47],
    signCheck i j (wordZ1 i) (wordZ2 j) = true := by
  decide +kernel

theorem word_images : (∀ ε, vecEq (wordG.foldr (reflect F4.tag) (sRoot 24 ε)) (sRoot 41 ε) = true) ∧
    (∀ ε, vecEq (wordG.foldr (reflect F4.tag) (sRoot 33 ε)) (sRoot 45 ε) = true) ∧
    (∀ ε, vecEq (wordN.foldr (reflect F4.tag) (sRoot 25 ε)) (sRoot 35 ε) = true) ∧
    (∀ ε, vecEq (wordN.foldr (reflect F4.tag) (sRoot 27 ε)) (sRoot 32 ε) = true) ∧
    (∀ ε, vecEq (wordN.foldr (reflect F4.tag) (sRoot 28 ε)) (sRoot 44 ε) = true) ∧
    (∀ ε, vecEq (wordN.foldr (reflect F4.tag) (sRoot 30 ε)) (sRoot 47 ε) = true) := by
  decide +kernel

theorem fixedOrbitRootList_pos :
    (∀ α ∈ F4.fixedOrbitRootList ⟨0, by decide⟩,
      vecEq α (sRoot 24 false) = true ∨ vecEq α (sRoot 33 false) = true) ∧
    (∀ α ∈ F4.fixedOrbitRootList ⟨1, by decide⟩,
      vecEq α (sRoot 25 false) = true ∨ vecEq α (sRoot 27 false) = true ∨
        vecEq α (sRoot 28 false) = true ∨ vecEq α (sRoot 30 false) = true) := by
  decide +kernel

theorem isRoot_sRoot
    {r : ℕ} (h1 : 24 ≤ r) (h2 : r ≤ 47) (ε : Bool) : IsRoot F4.tag (sRoot r ε) := by
  have hr := (sylowRoot_pos h1 h2).1
  cases ε
  · exact hr
  · exact IsRoot.neg hr

section Weyl

variable {K : Type} [Field K] [CharP K F4.prime]

theorem wordRep_conj_pinnedX
    (ω : List (Fin F4.tag.rank)) {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (c : K) :
    canonicalRep (coxeterSystem F4.tag) K ((coxeterSystem F4.tag).wordProd ω) *
        pinnedX F4.tag K α c *
          (canonicalRep (coxeterSystem F4.tag) K ((coxeterSystem F4.tag).wordProd ω))⁻¹ =
      pinnedX F4.tag K (ω.foldr (reflect F4.tag) α) c := by
  rw [canonicalRep_mul_pinnedX_mul_inv_of_two F4_two_eq_zero _ hα, CFSG.LieType.Ree.wordProd_smul]

theorem commute_pinnedX_of_word
    (ω : List (Fin F4.tag.rank)) {α β α' β' : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α)
    (hβ : IsRoot F4.tag β) (hα' : ω.foldr (reflect F4.tag) α = α')
    (hβ' : ω.foldr (reflect F4.tag) β = β') {c d : K}
    (h : Commute (pinnedX F4.tag K α' c) (pinnedX F4.tag K β' d)) :
    Commute (pinnedX F4.tag K α c) (pinnedX F4.tag K β d) := by
  set n := canonicalRep (coxeterSystem F4.tag) K ((coxeterSystem F4.tag).wordProd ω) with hn
  have e1 := wordRep_conj_pinnedX ω hα c
  have e2 := wordRep_conj_pinnedX ω hβ d
  rw [hα'] at e1
  rw [hβ'] at e2
  rw [← e1, ← e2] at h
  have h1 := h.eq
  unfold Commute SemiconjBy
  calc pinnedX F4.tag K α c * pinnedX F4.tag K β d =
      n⁻¹ * (n * pinnedX F4.tag K α c * n⁻¹ * (n * pinnedX F4.tag K β d * n⁻¹)) * n := by group
    _ = n⁻¹ * (n * pinnedX F4.tag K β d * n⁻¹ * (n * pinnedX F4.tag K α c * n⁻¹)) * n := by
      rw [h1]
    _ = pinnedX F4.tag K β d * pinnedX F4.tag K α c := by group

theorem commute_of_signCheck
    {i j : ℕ} {ωi ωj : List (Fin F4.tag.rank)} (h : signCheck i j ωi ωj = true) (ε₁ ε₂ : Bool)
    (c d : K) : Commute (pinnedX F4.tag K (sRoot i ε₁) c) (pinnedX F4.tag K (sRoot j ε₂) d) := by
  simp only [signCheck, Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi1, hi2⟩, hj1⟩, hj2⟩, hij⟩, hc⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hR : ∀ ε, IsRoot F4.tag (sRoot i ε) := isRoot_sRoot hi1 hi2
  have hS : ∀ ε, IsRoot F4.tag (sRoot j ε) := isRoot_sRoot hj1 hj2
  have base : ∀ c d : K, Commute (pinnedX F4.tag K (sRoot i false) c)
      (pinnedX F4.tag K (sRoot j false) d) := fun c d =>
    sylowX_commute_of_commFactors (K := K) ⟨hi1, hi2⟩ ⟨hj1, hj2⟩ hij hc c d
  have ff : ∀ c d : K, Commute (pinnedX F4.tag K (sRoot i false) c)
      (pinnedX F4.tag K (sRoot j true) d) := fun c d =>
    commute_pinnedX_of_word ωj (hR false) (hS true) (eq_of_vecEq h5) (eq_of_vecEq h4)
      (base c d)
  cases ε₁ <;> cases ε₂
  · exact base c d
  · exact ff c d
  · exact commute_pinnedX_of_word ωi (hR true) (hS false) (eq_of_vecEq h1) (eq_of_vecEq h2)
      (base c d)
  · exact commute_pinnedX_of_word ωi (hR true) (hS true) (eq_of_vecEq h1) (eq_of_vecEq h3)
      (ff c d)

end Weyl

section Gens

variable (K : Type) [Field K]

@[expose] def gens (I : List ℕ) :
    Set (ModGL F4.tag K) :=
  {y | ∃ r ∈ I, ∃ ε : Bool, ∃ c : K, pinnedX F4.tag K (sRoot r ε) c = y}

end Gens

theorem isRoot_foldr_reflect {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) :
    ∀ ω : List (Fin F4.tag.rank), IsRoot F4.tag (ω.foldr (reflect F4.tag) α)
  | [] => hα
  | i :: ω => IsRoot.reflect i (isRoot_foldr_reflect hα ω)

section Conj

variable {K : Type} [Field K] [CharP K F4.prime]

theorem weyl_conj_pinnedX
    (j : Fin F4.fixedOrbitCount) {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (c : K) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) * pinnedX F4.tag K α c *
        (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j))⁻¹ =
      pinnedX F4.tag K ((F4.fixedOrbitWord j).foldr (reflect F4.tag) α) c := by
  rw [canonicalRep_mul_pinnedX_mul_inv_of_two F4_two_eq_zero _ hα, fixedOrbitElement_smul]

theorem gConj_pinnedX
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (c : K) :
    (weylTwo K * weylOne K * weylTwo K) * pinnedX F4.tag K α c *
        (weylTwo K * weylOne K * weylTwo K)⁻¹ =
      pinnedX F4.tag K (wordG.foldr (reflect F4.tag) α) c := by
  have h1 := weyl_conj_pinnedX (K := K) ⟨1, by decide⟩ hα c
  have h2 := weyl_conj_pinnedX (K := K) ⟨0, by decide⟩
    (isRoot_foldr_reflect hα (F4.fixedOrbitWord ⟨1, by decide⟩)) c
  have h3 := weyl_conj_pinnedX (K := K) ⟨1, by decide⟩
    (isRoot_foldr_reflect (isRoot_foldr_reflect hα (F4.fixedOrbitWord ⟨1, by decide⟩))
      (F4.fixedOrbitWord ⟨0, by decide⟩)) c
  rw [wordG, List.foldr_append, List.foldr_append]
  calc (weylTwo K * weylOne K * weylTwo K) * pinnedX F4.tag K α c *
        (weylTwo K * weylOne K * weylTwo K)⁻¹ =
      weylTwo K * (weylOne K * (weylTwo K * pinnedX F4.tag K α c * (weylTwo K)⁻¹) *
        (weylOne K)⁻¹) * (weylTwo K)⁻¹ := by group
    _ = _ := by rw [weylTwo, weylOne, h1, h2, h3]

theorem nConj_pinnedX
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (c : K) :
    (weylOne K * weylTwo K * weylOne K) * pinnedX F4.tag K α c *
        (weylOne K * weylTwo K * weylOne K)⁻¹ =
      pinnedX F4.tag K (wordN.foldr (reflect F4.tag) α) c := by
  have h1 := weyl_conj_pinnedX (K := K) ⟨0, by decide⟩ hα c
  have h2 := weyl_conj_pinnedX (K := K) ⟨1, by decide⟩
    (isRoot_foldr_reflect hα (F4.fixedOrbitWord ⟨0, by decide⟩)) c
  have h3 := weyl_conj_pinnedX (K := K) ⟨0, by decide⟩
    (isRoot_foldr_reflect (isRoot_foldr_reflect hα (F4.fixedOrbitWord ⟨0, by decide⟩))
      (F4.fixedOrbitWord ⟨1, by decide⟩)) c
  rw [wordN, List.foldr_append, List.foldr_append]
  calc (weylOne K * weylTwo K * weylOne K) * pinnedX F4.tag K α c *
        (weylOne K * weylTwo K * weylOne K)⁻¹ =
      weylOne K * (weylTwo K * (weylOne K * pinnedX F4.tag K α c * (weylOne K)⁻¹) *
        (weylTwo K)⁻¹) * (weylOne K)⁻¹ := by group
    _ = _ := by rw [weylTwo, weylOne, h1, h2, h3]

theorem commute_closure_gens
    {I J : List ℕ} {ωI ωJ : ℕ → List (Fin F4.tag.rank)}
    (h : ∀ i ∈ I, ∀ j ∈ J, signCheck i j (ωI i) (ωJ j) = true) :
    ∀ x ∈ closure (gens K I), ∀ y ∈ closure (gens K J), x * y = y * x :=
  CFSG.LieType.Chevalley.closure_commute (by
    rintro _ ⟨i, hi, ε₁, c, rfl⟩ _ ⟨j, hj, ε₂, d, rfl⟩
    exact (commute_of_signCheck (h i hi j hj) ε₁ ε₂ c d).eq)

omit [CharP K F4.prime] in
theorem rootSpan_le_closure_gens
    {S : Set (Fin F4.tag.rank → ℤ)} {I : List ℕ}
    (h : ∀ α ∈ S, ∃ r ∈ I, ∃ ε, sRoot r ε = α) : rootSpan F4.tag K S ≤ closure (gens K I) := by
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, closure_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨r, hr, ε, rfl⟩ := h α hα
  exact subset_closure ⟨r, hr, ε, c, rfl⟩

end Conj

section Blocks

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem reeLocalBlock_le_closure_gens
    (j : Fin F4.fixedOrbitCount) {I : List ℕ}
    (h : ∀ α ∈ F4.fixedOrbitRootList j, ∃ r ∈ I, sRoot r false = α) :
    F4.reeLocalBlock K m j ≤ closure (gens K I) := by
  refine sup_le (inf_le_left.trans (rootSpan_le_closure_gens ?_))
    (inf_le_left.trans (rootSpan_le_closure_gens ?_))
  · intro α hα
    rw [fixedOrbitRoots_eq_list] at hα
    obtain ⟨r, hr, e⟩ := h α hα
    exact ⟨r, hr, false, e⟩
  · rintro _ ⟨β, hβ, rfl⟩
    rw [fixedOrbitRoots_eq_list] at hβ
    obtain ⟨r, hr, e⟩ := h β hβ
    refine ⟨r, hr, true, ?_⟩
    rw [← e]
    rfl

theorem rankOneGroupOne_le_gens
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    rankOneGroupOne K m ≤ closure (gens K [24, 33]) := by
  rw [← (CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model
    hm hK).1.1]
  refine reeLocalBlock_le_closure_gens _ fun α hα => ?_
  rcases fixedOrbitRootList_pos.1 α hα with h | h
  · exact ⟨24, by simp, (eq_of_vecEq h).symm⟩
  · exact ⟨33, by simp, (eq_of_vecEq h).symm⟩

theorem rankOneGroupTwo_le_gens
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    rankOneGroupTwo K m ≤ closure (gens K [25, 27, 28, 30]) := by
  rw [← (CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model
    hm hK).2.1]
  refine reeLocalBlock_le_closure_gens _ fun α hα => ?_
  rcases fixedOrbitRootList_pos.2 α hα with h | h | h | h
  · exact ⟨25, by simp, (eq_of_vecEq h).symm⟩
  · exact ⟨27, by simp, (eq_of_vecEq h).symm⟩
  · exact ⟨28, by simp, (eq_of_vecEq h).symm⟩
  · exact ⟨30, by simp, (eq_of_vecEq h).symm⟩

theorem map_gConj_le
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (rankOneGroupOne K m).map (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom ≤
      closure (gens K [41, 45]) := by
  refine (map_mono (rankOneGroupOne_le_gens hm hK)).trans ?_
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨r, hr, ε, c, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨hg24, hg33, -⟩ := word_images
  have hconj : ∀ s, 24 ≤ s → s ≤ 47 →
      (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom
          (pinnedX F4.tag K (sRoot s ε) c) =
        pinnedX F4.tag K (wordG.foldr (reflect F4.tag) (sRoot s ε)) c := fun s h1 h2 => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, gConj_pinnedX (isRoot_sRoot h1 h2 ε)]
  rcases hr with rfl | rfl
  · rw [hconj 24 (by norm_num) (by norm_num), eq_of_vecEq (hg24 ε)]
    exact subset_closure ⟨41, by simp, ε, c, rfl⟩
  · rw [hconj 33 (by norm_num) (by norm_num), eq_of_vecEq (hg33 ε)]
    exact subset_closure ⟨45, by simp, ε, c, rfl⟩

theorem map_nConj_le
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (rankOneGroupTwo K m).map (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom ≤
      closure (gens K [32, 35, 44, 47]) := by
  refine (map_mono (rankOneGroupTwo_le_gens hm hK)).trans ?_
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨r, hr, ε, c, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, -, h25, h27, h28, h30⟩ := word_images
  have hconj : ∀ s, 24 ≤ s → s ≤ 47 →
      (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom
          (pinnedX F4.tag K (sRoot s ε) c) =
        pinnedX F4.tag K (wordN.foldr (reflect F4.tag) (sRoot s ε)) c := fun s h1 h2 => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, nConj_pinnedX (isRoot_sRoot h1 h2 ε)]
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hconj 25 (by norm_num) (by norm_num), eq_of_vecEq (h25 ε)]
    exact subset_closure ⟨35, by simp, ε, c, rfl⟩
  · rw [hconj 27 (by norm_num) (by norm_num), eq_of_vecEq (h27 ε)]
    exact subset_closure ⟨32, by simp, ε, c, rfl⟩
  · rw [hconj 28 (by norm_num) (by norm_num), eq_of_vecEq (h28 ε)]
    exact subset_closure ⟨44, by simp, ε, c, rfl⟩
  · rw [hconj 30 (by norm_num) (by norm_num), eq_of_vecEq (h30 ε)]
    exact subset_closure ⟨47, by simp, ε, c, rfl⟩

theorem commute_rankOneGroupOne_conj
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∀ d ∈ (rankOneGroupOne K m).map (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom,
      ∀ r ∈ rankOneGroupOne K m, d * r = r * d := fun d hd r hr =>
  (commute_closure_gens signCheck_t r (rankOneGroupOne_le_gens hm hK hr) d
    (map_gConj_le hm hK hd)).symm

theorem commute_rankOneGroupTwo_conj
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∀ d ∈ (rankOneGroupTwo K m).map (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom,
      ∀ r ∈ rankOneGroupTwo K m, d * r = r * d := fun d hd r hr =>
  (commute_closure_gens signCheck_z r (rankOneGroupTwo_le_gens hm hK hr) d
    (map_nConj_le hm hK hd)).symm

end Blocks

section D0

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem d0Data_t
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (ht : sylowL m K 1 ∈ F4.reeGamma K m) :
    D0Data (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m) ((tK m K).subgroupOf (F4.reeGamma K m)) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨-, -, -, -, -, ht1, ht2, ht3, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  obtain ⟨hR₁s, hR₁nc⟩ := isSimpleGroup_rankOneGroupOne hm hK
  have hR₁C : rankOneGroupOne K m ≤ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
    rw [ht1]
    exact le_sup_right
  have hQC : tKernel K m ≤ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
    rw [ht1]
    exact le_sup_left
  have hR₁Γ : rankOneGroupOne K m ≤ F4.reeGamma K m := hR₁C.trans inf_le_left
  have hQΓ : tKernel K m ≤ F4.reeGamma K m := hQC.trans inf_le_left
  have hgΓ : weylTwo K * weylOne K * weylTwo K ∈ F4.reeGamma K m :=
    mul_mem (mul_mem weylTwo_mem weylOne_mem) weylTwo_mem
  set L := (rankOneGroupOne K m).map
    (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom with hL
  have hLΓ : L ≤ F4.reeGamma K m := by
    rintro _ ⟨r, hr, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hgΓ (hR₁Γ hr)) (inv_mem hgΓ)
  set e := (rankOneGroupOne K m).equivMapOfInjective
    (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom
    (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).injective with he
  have : IsSimpleGroup L := e.symm.isSimpleGroup
  have hLnc : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hR₁nc
    refine ⟨e x, e y, fun h => hxy ?_⟩
    have h1 := congrArg e.symm h
    rwa [MulEquiv.map_mul, MulEquiv.map_mul, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply] at h1
  have htL : tK m K ≤ L := by
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨sylowA m K c, subset_closure (Set.mem_union_left _
      (Set.mem_union_left _ (sylowA_mem_U1 hK c))), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc weylTwo K * weylOne K * weylTwo K * sylowA m K c *
          (weylTwo K * weylOne K * weylTwo K)⁻¹ =
        weylTwo K * (weylOne K * (weylTwo K * fam m K 0 c * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
          (weylTwo K)⁻¹ := by
          show _ = weylTwo K * (weylOne K * (weylTwo K * sylowA m K c * (weylTwo K)⁻¹) *
            (weylOne K)⁻¹) * (weylTwo K)⁻¹
          group
      _ = fam m K 11 c := by
        rw [weylTwo_conj_fam (n := 0) (n' := 9) (by decide) c,
          weylOne_conj_fam (n := 9) (n' := 10) (by decide) c,
          weylTwo_conj_fam (n := 10) (n' := 11) (by decide) c]
  have hQ2 : IsPGroup 2 (tKernel K m) :=
    (centralizerT_kernel hm hK).2.1.of_equiv (subgroupOfEquivOfLe le_sup_left)
  refine d0Data_of_semidirect ht ht1 (le_normalizer_of_normal_subgroupOf ht3 hQC hR₁C) ht2 hQ2
    (commute_rankOneGroupOne_conj hm hK) hLΓ hQΓ hLnc htL ?_ ?_
  · intro a ha b hb
    obtain ⟨c, rfl⟩ := (mem_tK hK).1 ha
    obtain ⟨d, rfl⟩ := (mem_tK hK).1 hb
    rw [sylowL_mul hK, sylowL_mul hK, add_comm]
  · intro v hv w hw
    obtain ⟨c, rfl⟩ := (mem_tK hK).1 hw
    exact mem_centralizer_singleton_iff.1 (tKernel_le_centralizer hK c hv)

theorem d0Data_z
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (hz : centralZ K m 1 ∈ F4.reeGamma K m) :
    D0Data (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m) ((zK m K).subgroupOf (F4.reeGamma K m)) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨hz1, hz2, hz3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  obtain ⟨hR₂s, hR₂nc⟩ := isSimpleGroup_rankOneGroupTwo hm hK
  have hR₂C : rankOneGroupTwo K m ≤ F4.reeGamma K m ⊓ centralizer {centralZ K m 1} := by
    rw [hz1]
    exact le_sup_right
  have hVC : F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ≤
      F4.reeGamma K m ⊓ centralizer {centralZ K m 1} := by
    rw [hz1]
    exact le_sup_left
  have hR₂Γ : rankOneGroupTwo K m ≤ F4.reeGamma K m := hR₂C.trans inf_le_left
  have hVΓ := hVC.trans inf_le_left
  have hnΓ : weylOne K * weylTwo K * weylOne K ∈ F4.reeGamma K m :=
    mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem
  set D := (rankOneGroupTwo K m).map
    (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom with hD
  have hDΓ : D ≤ F4.reeGamma K m := by
    rintro _ ⟨r, hr, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hnΓ (hR₂Γ hr)) (inv_mem hnΓ)
  set e := (rankOneGroupTwo K m).equivMapOfInjective
    (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom
    (MulAut.conj (weylOne K * weylTwo K * weylOne K)).injective with he
  have : IsSimpleGroup D := e.symm.isSimpleGroup
  have hDnc : ∃ a b : D, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hR₂nc
    refine ⟨e x, e y, fun h => hxy ?_⟩
    have h1 := congrArg e.symm h
    rwa [MulEquiv.map_mul, MulEquiv.map_mul, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply] at h1
  have hzD : zK m K ≤ D := by
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨sylowB m K 0 c, subset_closure (Set.mem_union_left _
      (Set.mem_union_left _ (sylowB_mem_U2 hK 0 c))), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, weyl_conj_sylowB_zero,
      sylowH_zero_eq_centralZ]
  have hV2 : IsPGroup 2 (F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) :=
    (centralizerZ_kernel hm hK).2.1.of_equiv (subgroupOfEquivOfLe le_sup_left)
  refine d0Data_of_semidirect hz hz1 (le_normalizer_of_normal_subgroupOf hz3 hVC hR₂C) hz2 hV2
    (commute_rankOneGroupTwo_conj hm hK) hDΓ hVΓ hDnc hzD ?_ ?_
  · intro a ha b hb
    obtain ⟨c, rfl⟩ := (mem_zK hK).1 ha
    obtain ⟨d, rfl⟩ := (mem_zK hK).1 hb
    rw [centralZ_mul hK, centralZ_mul hK, add_comm]
  · intro v hv w hw
    obtain ⟨c, rfl⟩ := (mem_zK hK).1 hw
    exact mem_centralizer_singleton_iff.1 (complement_le_centralizer hm hK c hv)

end D0

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
